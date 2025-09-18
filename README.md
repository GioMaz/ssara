# SSARA

SSARA (**S**tatic **S**ingle **A**ssignment **R**egister **A**ssignment) is an implementation of a partially verified SSA-based register assignment algorithm.
Given a program written in JAIR (**J**ust **A**nother **I**ntermediate **R**epresentation), the result is an x64 program.
Some sample programs can be found in `core/Color.v`.

## Building

```bash
dune build
```

## Running

```bash
./_build/default/extract/main.exe
```

