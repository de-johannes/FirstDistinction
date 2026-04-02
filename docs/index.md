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
  <p class="tagline">4 vertices. 6 edges. Everything else follows.</p>
</div>

---

## The Claim

**Try to deny that distinction exists.**

To say "there is no distinction" — you must distinguish that statement from its opposite.
To think "nothing is different from anything" — you must differentiate that thought from other thoughts.

**You cannot deny distinction without using distinction.**

The First Distinction (D₀) cannot be coherently rejected. Its denial presupposes it.

From this single self-evident premise, we construct **K₄** — the complete graph on 4 vertices — and derive its spectral and structural invariants. These invariants produce numbers that match physical constants to high precision.

The entire derivation — 24,806 lines, 6 parts, 48 chapters — is formalized as a single literate Agda book that compiles under `--safe --without-K`. No postulates, no holes, machine-checked.

---

## The Book

**First Distinction** is a literate Agda/LaTeX book (504 pages) containing both the formal proof and its explanation:

| | |
|---|---|
| **Source** | [FirstDistinction.lagda.tex](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.lagda.tex) |
| **Lines** | 24,806 |
| **Structure** | 6 Parts · 48 Chapters · 207 Sections |
| **Code blocks** | 375 |
| **Flags** | `--safe --without-K --no-libraries` |
| **PDF** | Built automatically by CI (see [Releases](https://github.com/de-johannes/FirstDistinction/releases)) |

---

## Why K₄?

**First Distinction** constructs K₄ from a single premise:

> Something is distinguishable from something.

The structure follows from the construction itself:

1. **D₀ distinguishes itself from ¬D₀** → 2 vertices
2. **This distinction distinguishes itself from its absence** → 3 vertices
3. **Self-reference closes the structure** → 4 vertices, fully connected

The construction cannot stop at 3 — self-reference demands completion. It cannot continue to 5 — there is no fifth constructible step. **K₄ is not chosen. It is necessary.**

---

## What is computed?

The following are **mathematical theorems** (Agda `--safe --without-K`):

| Quantity | K₄ Formula | Result | Physical Match |
|----------|------------|--------|----------------|
| Dimension | λ=4 multiplicity | **d = 3** | ✓ 3 spatial |
| Time | Drift asymmetry | **1** | ✓ 1 temporal |
| Signature | Symmetric/asymmetric | **(−,+,+,+)** | ✓ matches GR |
| Coupling | dim × χ | **κ = 8** | ✓ matches 8πG |
| Gyromagnetic | \|Bool\| | **g = 2** | ✓ Dirac value |
| Spectral formula | λ³χ + deg² + 4/111 | **137.036036** | ≈ α⁻¹ (0.0007%) |
| Anomaly | 1/(α⁻¹ × E) | **1/822** | ≈ (g-2)/2 (~5%) |
| Epoch count | 5 × 4¹⁰⁰ | **N** | ≈ τ/t_P (0.44%) |
| Matter density | (V-1)/(E+V) + 1/(E²+κ²) | **Ωₘ = 0.31** | ≈ 0.3111 (0.35%) |
| Baryon ratio | 1/E with loops | **Ωᵦ/Ωₘ = 1/6** | ≈ 0.1574 (1.19%) |
| Spectral index | 1 - 1/(V×E) + loops | **ns = 0.9633** | ≈ 0.9665 (0.33%) |
| Λ (§14d) | 3/N² | **~10⁻¹²²** | ✓ order of magnitude |
| Quantum correction | -E×deg - χ/κ + (κ + Ω/V) log(m) | **ε(m)** | R²=0.9994 (§29) |

**These formulas are not fits.** They are spectral and structural invariants of K₄ — properties the graph necessarily possesses. The mathematical computations are proven. That they correspond to physical reality is a hypothesis supported by remarkable numerical agreement.

---

## Visual Evidence

*Click any image to view full size.*

<a href="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}"><img src="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}" alt="K₄ Uniqueness"></a>

**Only K₄ produces a value near 137.** K₃ gives 22. K₅ gives 1,266. This is not fine-tuning — it's the unique solution.

<a href="{{ '/assets/images/fig4_genesis.png' | relative_url }}"><img src="{{ '/assets/images/fig4_genesis.png' | relative_url }}" alt="Genesis Chain"></a>

**Each step is forced.** D₁ distinguishes D₀ from its absence. D₂ witnesses the (D₀, D₁) pair. D₃ closes the structure. K₄ is not chosen — it is necessary.

<a href="{{ '/assets/images/fig6_summary.png' | relative_url }}"><img src="{{ '/assets/images/fig6_summary.png' | relative_url }}" alt="Summary"></a>

---

## Check it yourself

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.lagda.tex
```

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/release-ci.yml)

The code is the claim. If it compiles, the proof is valid.

---

## Honesty

**What IS proven (Agda `--safe`):**
- K₄ emerges from self-referential distinction
- The K₄ spectral formula produces 137.036...
- The structural formula produces N = 5 × 4¹⁰⁰
- All computations are verified by the type-checker

**What is HYPOTHESIS:**
- That these mathematical objects ARE the physical constants
- That K₄ structure IS the geometry of our universe
- That the numerical agreements are not coincidental

The mathematics is machine-verified. The physics interpretation requires experiment.

If you find an error, [open an issue](https://github.com/de-johannes/FirstDistinction/issues).

---

## AI Disclosure

This work was created over 12 months by one person using six different AI systems (Claude Opus, Claude Sonnet, ChatGPT, Gemini, Sonar-R1, DeepSeek-R1). Agda doesn't lie — if it compiles under `--safe --without-K`, the proof is valid.

---

<div class="footer-links">
  <a href="https://github.com/de-johannes/FirstDistinction">GitHub</a>
  <a href="https://github.com/de-johannes/FirstDistinction/releases">Releases</a>
</div>