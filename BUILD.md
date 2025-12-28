# Build Instructions

To build the PDF from the Literate Agda file, you need a working LaTeX installation with specific packages.

## Prerequisites

1.  **Agda**: You already have this working.
2.  **LaTeX**: You need a TeX distribution (like MacTeX or TeX Live).
3.  **Required Packages**: The Agda LaTeX backend requires several packages.

## Installing Missing Packages

The build failed because `xifthen.sty` was missing. You likely need to install the following packages:

```bash
sudo tlmgr install xifthen xcolor polytable etoolbox calc environ xparse xkeyval
```

If you are using MacTeX BasicTeX, you might need to update `tlmgr` first:

```bash
sudo tlmgr update --self
```

## Building the Paper

Once the dependencies are installed, run the build script:

```bash
./.github/scripts/build_paper.sh
```

This will:
1.  Compile `FirstDistinction.lagda.tex` to `latex/FirstDistinction.tex`.
2.  Run `xelatex` (or `pdflatex`) to generate `FirstDistinction.pdf`.
