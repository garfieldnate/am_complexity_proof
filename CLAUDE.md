# Claude Code Instructions

## Building the proof

```bash
lake build
```

## Documentation

Human-readable documentation lives in `blueprint/src/content.tex` and compiles
to a PDF via LeanBlueprint.  To rebuild:

```bash
cd blueprint && make pdf
# output: blueprint/print/print.pdf
```
