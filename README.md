# First Distinction

A machine-verified derivation from logical distinction to K₄.

## What This Is

A single literate Agda file (`FirstDistinction.lagda.tex`) that derives the
complete graph K₄ as the unique structure surviving an eliminative filter—starting
from nothing but a binary distinction (a type with two provably unequal,
covering elements).

The file is simultaneously:
- **a proof artifact** — every theorem compiles under `--safe --without-K`
- **a book** — the same source produces a ~500-page PDF via `agda --latex` + XeLaTeX

No standard library.  No postulates.  No axiom K.  No external imports beyond
`Agda.Primitive`.

## The Chain

| # | Survivor | Eliminated |
|---|----------|------------|
| 1 | Distinction (two-element type with coverage) | Vacuous carriers, partial classifications |
| 2 | Four endomorphisms (constL, constR, id, dual) | K₁, K₂, K₃ — orphan cases |
| 3 | Drift acyclicity (ranked well-foundedness) | Cyclic hierarchies, infinite descent |
| 4 | Presentation fixpoint (canonical observable base) | Non-canonical representations |
| 5 | **K₄** (complete graph on 4 vertices) | All proper subgraphs and supergraphs |

From K₄'s combinatorial invariants (V=4, E=6, d=3, χ=2, κ=8, Spec={0,4,4,4}),
the book derives arithmetic (ℕ, ℤ, ℚ, ℝ) and evaluates computed quantities
that can be compared with measured physics constants.  The computation is theorem;
the comparison is interpretation.

## Verify

```
agda --safe --without-K --no-libraries FirstDistinction.lagda.tex
```

Requires Agda ≥ 2.6.4.  Nothing else.

## Build the PDF

```
agda --latex FirstDistinction.lagda.tex
cd latex
xelatex FirstDistinction.tex
xelatex FirstDistinction.tex   # second pass for cross-references
```

## Structure

```
FirstDistinction.lagda.tex   ← the entire book + proof (single file)
.github/workflows/
  release-ci.yml             ← CI: Agda verification + PDF build + GitHub Release
```

## Companion Documents

- **Companion paper** (pure K₄ derivation, 5 pages) — for TYPES / LICS / CSL
- **Physics summary** (computed invariants, 4 pages) — for physicists evaluating the numerical claims

Both are maintained in the [Void](https://github.com/de-johannes/Void) repository.

## License

All rights reserved.  The Agda source is the proof artifact; verification is
encouraged.
