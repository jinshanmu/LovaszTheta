# The sharp Lovász theta constant for two random graph models

- [Manuscript PDF](LaTeX/lovasz-theta.pdf) and [LaTeX source](LaTeX/lovasz-theta.tex)
- [Lean formalization](Lean/) with the [main theorem](Lean/LovaszTheta/Limit.lean)

## Build the manuscript

Run `latexmk -pdf lovasz-theta.tex` from `LaTeX/`.

## Check the formalization

With [Elan](https://github.com/leanprover/elan) installed, Lake uses the Lean
version pinned in [lean-toolchain](Lean/lean-toolchain).

```sh
cd Lean
lake exe cache get
lake build --wfail
lake lint
```
