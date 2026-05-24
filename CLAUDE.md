# Claude Code Instructions

## Building the proof

```bash
lake build
```

## Building the Verso HTML documentation

**Never run `lake exe generate-docs` directly** — it will always fail on macOS.

Use `./build-docs.sh` instead.  The script:
1. Runs `lake build generate-docs` (the link step fails, that's expected).
2. Collects the object-file list from the build trace.
3. Bundles all ~8 400 `.c.o.export` files into a single `.a` archive via
   `llvm-ar q` in batches of 500 (using `xargs -0 -n 500`).
4. Links with the Lean toolchain's clang plus `-L $(xcrun --show-sdk-path)/usr/lib`.
5. Runs the binary to emit `_out/html-multi/`.

**Why the workaround is necessary:**
- macOS `ARG_MAX` = 1 MB; the full link command is ~1.4 MB.
- LLVM's `@file` response-file parser (in clang, ld64.lld, and llvm-ar) silently
  breaks above ~1.4 MB: it stops tokenizing and treats the overflow as a single
  filename.
- Lake cannot execute shell-script wrappers for `LEAN_CC` (it needs a Mach-O
  binary, not a script).

**If the Lean toolchain is upgraded**, update the `TOOLCHAIN` path in
`build-docs.sh` to match the new toolchain directory.

## Doc source files

```
Doc.lean                  root Verso document (imports all chapters)
Doc/Introduction.lean     The Complexity Class #P
Doc/Background.lean       The AM Algorithm
Doc/VertexCover.lean      Part I: #VERTEX-COVER ≤ #⋃℘
Doc/Hardness.lean         Part II: #⋃℘ ≤ Exact AM Scoring
DocMain.lean              Verso entry point (manualMain)
```
