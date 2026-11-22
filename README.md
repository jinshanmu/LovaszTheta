# The sharp Lovász theta constant for two random graph models

- [Manuscript PDF](LaTeX/lovasz-theta.pdf) and [LaTeX source](LaTeX/lovasz-theta.tex)
- [Preprint PDF](Preprint/lovasz-theta-preprint.pdf) and [LaTeX source](Preprint/lovasz-theta-preprint.tex)
- [Lean formalization](Lean/) with the [main theorem](Lean/LovaszTheta/Limit.lean)

## Build the manuscript

Run `latexmk -pdf lovasz-theta.tex` from `LaTeX/`.

For the preprint layout, extract `Definitions/` from the LaTeX ZIP inside the template
download into `Preprint/`. Run `latexmk -pdf lovasz-theta-preprint.tex` from that
directory. [Preprints.org template download](https://www.preprints.org/instructions-for-authors)

## Check the formalization

With [Elan](https://github.com/leanprover/elan) installed, Lake uses the Lean
version pinned in [lean-toolchain](Lean/lean-toolchain).

```sh
cd Lean
lake exe cache get
lake build --wfail
lake lint
```
