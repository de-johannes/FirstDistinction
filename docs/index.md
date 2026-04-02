---
layout: default
title: First Distinction
---

<div class="hero">
  <div class="k4-symbol">
    <svg viewBox="0 0 100 100" class="tetrahedron">
      <g stroke="currentColor" stroke-width="1.5" fill="none">
        <line x1="50" y1="15" x2="20" y2="75"/>
        <line x1="50" y1="15" x2="80" y2="75"/>
        <line x1="50" y1="15" x2="50" y2="55"/>
        <line x1="20" y1="75" x2="80" y2="75"/>
        <line x1="20" y1="75" x2="50" y2="55"/>
        <line x1="80" y1="75" x2="50" y2="55"/>
        <circle cx="50" cy="15" r="3" fill="currentColor"/>
        <circle cx="20" cy="75" r="3" fill="currentColor"/>
        <circle cx="80" cy="75" r="3" fill="currentColor"/>
        <circle cx="50" cy="55" r="3" fill="currentColor"/>
      </g>
    </svg>
  </div>
  <p class="tagline">One distinction. One filter. One survivor.</p>
</div>

---

## Abstract

Logic admits a single irreducible datum: a distinction --- true or false. Any system that produces a contradiction under its own requirements cannot persist.

**First Distinction** applies that constraint formally and mechanically. Each step is verified in Agda --- no external axioms, no postulates, no assumptions beyond what logical consistency demands. Every structure is justified solely by the elimination of alternatives that fail.

What remains is $K_4$: the complete graph on four vertices. It is not introduced as a model or hypothesis. It is the minimal structure that elimination cannot touch.

The combinatorial invariants of $K_4$ --- vertex count, edge topology, spectral decomposition, Euler characteristic --- are necessities of the derivation. Their numerical values can then be compared with independently measured constants of physics, including $\alpha^{-1} \approx 137$. That comparison is not part of the derivation; it is the interpretive question this work places before the reader.

---

## The Elimination Protocol

The argument has a single irreversible spine. At every step, alternatives are tested and destroyed. $K_4$ is what remains after every row has been executed.

| # | Survivor | Why it survives | What was eliminated |
|---|---|---|---|
| 1 | Distinction ($D_0$) | The bare act of separating $\ell$ from $r$. A formal system that cannot distinguish true from false is vacuous. | Vacuous carriers, carriers without boundary witnesses, carriers where $\ell = r$. |
| 2 | Two-class coverage | Every element of the carrier equals $\ell$ or $r$. No unclassified residue remains. | Hidden elements, partial classifications, carriers with $>2$ equivalence classes. |
| 3 | Four endomorphisms | Coverage forces $\|\mathrm{End}(S)\| = 2 \times 2 = 4$. Each case is mutually distinct. | $K_1$ (cannot host 4 distinct maps), $K_2$ (collapses constant maps), $K_3$ (one case always orphaned). |
| 4 | Drift acyclicity | Applying classification to classification produces a level tower. Its reachability relation is well-founded. | Cyclic level structures, infinite descending chains, non-well-founded hierarchies. |
| 5 | Presentation fixpoint | Every reachability witness reduces to a canonical finite form. The observable that measures proofs factors through a unique base. | Non-canonical representations, observables depending on proof-internal choices, redundant witnesses. |
| 6 | $K_4$ | The complete graph on four vertices is the unique fixpoint. No proper subgraph survives all five constraints. | Every proper subgraph, every supergraph, every non-complete topology on four vertices. |
| 7 | Derived arithmetic | $K_4$ forces counting (naturals), orientation (integers), spectral ratios (rationals), limit closure (reals). | Number systems not grounded in $K_4$ structure, algebraic laws contradicting the spectral data. |
| 8 | Physics record | The invariants of $K_4$ yield $\alpha^{-1} = 137$ by evaluation. No free parameter. | Any alternative constant requiring a different graph or a tunable parameter. |

---

## The Six Parts

**Part I --- Foundation.** Equality, pairing, negation, decidability, and the natural numbers. Each is shown to be the unique survivor when the alternative is tested for consistency and fails.

**Part II --- Drift and Reachability.** Classification applied to classification produces a level tower. The reach proofs track that ascent. Acyclicity is a theorem.

**Part III --- Heteromorphisms and Presentation.** Maps between distinct carriers are classified. The same four cases survive. Presentation theorems reduce every reachability fact to a finite canonical witness.

**Part IV --- Observables and Fixpoint.** Only quantities determined by structure rather than proof-choice qualify as observables. They collapse to a unique canonical form. The surviving graph is $K_4$.

**Part V --- Derived Arithmetic.** Integers arise from orientation. Rationals arise from spectral ratios. Reals close the Cauchy gaps. The Laplacian of $K_4$ yields spectrum $\\{0, 4, 4, 4\\}$. From the invariants: $\alpha^{-1} = 137$.

**Part VI --- Physics from $K_4$.** The invariant ledger is assembled into a verified physics representation record. Every field is a graph-theoretic computation, every constraint closes with `refl`. The discrete record is then extended through a continuum bridge to decimal-precision comparisons with measured constants.

---

## Invariants of the Survivor

$K_4$ carries the following forced invariants, each verified by definitional equality in Agda:

| Invariant | Value | Verification |
|---|---|---|
| Vertices $V$ | $4$ | `refl` |
| Edges $E$ | $6$ | `refl` |
| Faces $F$ | $4$ | `refl` |
| Vertex degree $d$ | $3$ | `refl` |
| Euler characteristic $\chi$ | $2$ | `refl` |
| Laplacian spectrum | $\\{0, 4, 4, 4\\}$ | eigenvector classification |
| Eigenspace split | $1 : 3$ | `refl` |
| Clifford dimension $2^V$ | $16$ | `refl` |
| Spectral width $\kappa$ | $8$ | `refl` |
| Hierarchy exponent $V \cdot E - \chi$ | $22$ | `refl` |
| $\alpha^{-1}$ | $137$ | `refl` |

The three-fold eigenspace degeneracy is not imported from physics. It is read off the Laplacian: the operator $L = 4I - J$ has kernel dimension one and image dimension three. The ratio $3{:}1$ is a spectral fact of $K_4$.

---

## Theorem vs. Interpretation

The book draws a sharp boundary.

**Theorem** --- the construction, the eliminations, the surviving $K_4$ structure, the derived arithmetic, and the invariant evaluations. All machine-checked. All verified under `--safe --without-K --no-libraries`.

**Interpretation** --- that the computed quantities are the quantities of our universe. That $\alpha^{-1} = 137$ is the fine-structure constant. That the $3{:}1$ eigenspace split is the dimension of space vs. time.

The mathematics does not depend on the physics being accepted. If every physical interpretation were rejected, the formal derivation would remain proved. The physical identification is an empirical proposal, not a logical claim.

---

## The Book as Artifact

| | |
|---|---|
| **Source** | [FirstDistinction.lagda.tex](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.lagda.tex) |
| **Author** | Johannes Michael Wielsch |
| **Date** | April 2026 |
| **Lines** | 24,806 |
| **Structure** | 6 Parts · 50 Chapters · 208 Sections |
| **Code blocks** | 375 |
| **Compiler flags** | `--safe --without-K --no-libraries` |
| **DOI** | [10.5281/zenodo.17826218](https://doi.org/10.5281/zenodo.17826218) |
| **PDF** | Built by CI (see [Releases](https://github.com/de-johannes/FirstDistinction/releases)) |

The source is a single literate Agda/LaTeX file. Prose and machine-checked proofs are one document. The compiler is the referee.

---

## Figures

*Click any image to view full size.*

<a href="{{ '/assets/images/fig4_genesis.png' | relative_url }}"><img src="{{ '/assets/images/fig4_genesis.png' | relative_url }}" alt="The eliminative chain from distinction to K₄"></a>

**The emergence chain.** Distinction, coverage, four endomorphisms, drift acyclicity, presentation fixpoint --- $K_4$ is the endpoint, not the starting point.

<a href="{{ '/assets/images/fig1_eigenvectors_d3.png' | relative_url }}"><img src="{{ '/assets/images/fig1_eigenvectors_d3.png' | relative_url }}" alt="Eigenvectors of the K₄ Laplacian"></a>

**Spectral structure.** The Laplacian $L = 4I - J$ has eigenvalues $0$ and $4$. The three-dimensional eigenspace is a forced consequence of the graph, not an imported physical assumption.

<a href="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}"><img src="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}" alt="Only K₄ yields 137"></a>

**Uniqueness of $\alpha^{-1} = 137$.** Among all complete graphs, only $K_4$ produces this value from its combinatorial invariants. The number is not fitted; it is evaluated.

<a href="{{ '/assets/images/fig6_summary.png' | relative_url }}"><img src="{{ '/assets/images/fig6_summary.png' | relative_url }}" alt="Summary of the derivation"></a>

**The full ledger.** From one distinction to a closed physics record --- every step machine-verified.

---

## Verify

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.lagda.tex
```

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml)
[![DOI](https://zenodo.org/badge/1108945544.svg)](https://doi.org/10.5281/zenodo.17826218)

If it compiles, the proof is valid.

---

## AI Disclosure

This work was developed by one person over 12 months, using six AI systems as tools (Claude Opus, Claude Sonnet, ChatGPT, Gemini, Sonar-R1, DeepSeek-R1). Agda enforces logical consistency without exception. No AI output survives unless the type checker accepts it.

---

<div class="footer-links">
  <a href="https://github.com/de-johannes/FirstDistinction">GitHub</a>
  <a href="https://github.com/de-johannes/FirstDistinction/releases">Releases</a>
</div>