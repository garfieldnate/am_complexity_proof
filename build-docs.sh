#!/usr/bin/env bash
# build-docs.sh — compile Lean files then link and run the Verso doc generator.
#
# Why this script exists:
#   The generate-docs executable links ~8400 Lean object files. The total
#   command-line length (~1.4MB) exceeds macOS's ARG_MAX (1MB), so
#   `lake exe generate-docs` always fails at the clang/ld step.
#   This script works around that by:
#     1. Building all .o files via lake (without the final link),
#     2. Bundling them into a single .a archive via llvm-ar in batches
#        (the LLVM @file parser has its own ~1.4MB limit, so we use xargs),
#     3. Linking with the Lean toolchain's clang + macOS SDK paths.
#     4. Running the resulting binary to emit _out/html-multi/.

set -e

REPO="$(cd "$(dirname "$0")" && pwd)"
TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.29.1"
LEAN_CLANG="$TOOLCHAIN/bin/clang"
LLVM_AR="$TOOLCHAIN/bin/llvm-ar"
SDK="$(xcrun --show-sdk-path)"

OBJ_RSP="$(mktemp /tmp/lean_objs_XXXXXX.rsp)"
# Generate a unique path but do NOT pre-create the archive file; llvm-ar must
# create it itself (rcS on a 0-byte file from mktemp produces a corrupt archive).
ARCHIVE="/tmp/lean_objs_$$.a"
trap "rm -f '$OBJ_RSP' '$ARCHIVE'" EXIT

# 1. Build all Lean modules (but the link step will fail — that's expected).
echo "==> Building Lean modules (link failure is expected)..."
lake build generate-docs 2>&1 || true

# 2. Collect all .c.o.export object files from the build cache.
#    (Parsing the lake trace doesn't work on incremental builds because the
#    trace is only emitted when the link step actually runs.)
echo "==> Collecting object files..."
find "$REPO/.lake/build/ir" "$REPO/.lake/packages" \
  -name '*.c.o.export' \
  > "$OBJ_RSP"

COUNT=$(wc -l < "$OBJ_RSP" | tr -d ' ')
echo "    Found $COUNT object files."

# 3. Bundle into one archive using batched llvm-ar calls (avoids the ~1.4MB limit).
echo "==> Creating archive..."
"$LLVM_AR" rcS "$ARCHIVE"
tr '\n' '\0' < "$OBJ_RSP" | xargs -0 -n 500 "$LLVM_AR" q "$ARCHIVE"
"$LLVM_AR" s "$ARCHIVE"

# 4. Link the final binary.
echo "==> Linking generate-docs..."
OUT="$REPO/.lake/build/bin/generate-docs"
mkdir -p "$(dirname "$OUT")"

MACOSX_DEPLOYMENT_TARGET=15.0 "$LEAN_CLANG" \
  -o "$OUT" \
  "$REPO/.lake/packages/MD4Lean/.lake/build/lib/libleanmd4c.a" \
  -L "$TOOLCHAIN/lib/lean" \
  -L "$TOOLCHAIN/lib" \
  -L "$SDK/usr/lib" \
  -lleancpp -lInit -lStd -lLean -lleanrt -lc++ -lLake -lgmp -luv \
  -Wl,-dead_strip \
  "$ARCHIVE"

# 5. Run the doc generator.
echo "==> Generating HTML docs..."
cd "$REPO"
"$OUT"

echo ""
echo "Done!  To view with interactive hovers, serve over HTTP:"
echo "  cd '$REPO/_out/html-multi' && python3 -m http.server 8000"
echo "  then open http://localhost:8000"
echo ""
echo "(Opening directly as file:// blocks the JS modules and CDN scripts.)"
