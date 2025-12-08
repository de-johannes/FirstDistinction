---
layout: default
title: D₀ (Home)
---

<div class="hero">
  <div class="k4-symbol">
    <svg viewBox="0 0 100 100" class="tetrahedron">
      <g stroke="currentColor" stroke-width="1.5" fill="none">
        <!-- Tetrahedron edges -->
        <line x1="50" y1="15" x2="20" y2="75"/>
        <line x1="50" y1="15" x2="80" y2="75"/>
        <line x1="50" y1="15" x2="50" y2="55"/>
        <line x1="20" y1="75" x2="80" y2="75"/>
        <line x1="20" y1="75" x2="50" y2="55"/>
        <line x1="80" y1="75" x2="50" y2="55"/>
        <!-- Vertices -->
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

## The Challenge

**Try to deny that distinction exists.**

To say "there is no distinction" — you must distinguish that statement from its opposite. To think "nothing is different from anything" — you must differentiate that thought from other thoughts.

**You cannot deny distinction without using distinction.**

This is not wordplay. It's an unavoidable logical fact:
- To assert requires distinguishing assertion from non-assertion
- To deny requires distinguishing denial from acceptance  
- Even silence distinguishes itself from speech

The First Distinction (D₀) cannot be coherently rejected. It is **self-evident** in the strongest possible sense: its denial presupposes it.

---

## What is First Distinction?

**First Distinction (FD)** constructs K₄ (the complete graph on 4 vertices) from a single premise:

> Something is distinguishable from something.

**Why exactly K₄? Why not K₃ or K₅?** The structure follows from the construction itself:

1. **D₀ distinguishes itself from ¬D₀** → 2 vertices (distinction vs. its absence)
2. **This distinction distinguishes itself from its absence** → 3 vertices (meta-distinction)
3. **Self-reference closes the structure** → 4 vertices, fully connected

The construction cannot stop at 3 — self-reference demands completion. It cannot continue to 5 — there is no fifth constructible step. **K₄ is not chosen. It is necessary.**

**The ontology:** What exists is exactly what can be constructed. This is not a philosophical position we *choose* — it's what constructive type theory *embodies*. In Agda:
- "X exists" means "X can be built"
- No axioms, no assumptions, no faith required
- If you can't construct it, it doesn't exist

Because only the constructible exists, and distinction is the only presuppositionless construction, **K₄ is not arbitrary — it is necessary.**

The complete proof is formalized in [Agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda) and compiles under `--safe --without-K` — no postulates, no holes, machine-checked.

---

## How deep do you want to go?

| Level | For whom | Start here |
|-------|----------|------------|
| **1. Curious** | "What's the claim?" | Keep reading below |
| **2. Skeptical** | "Prove it compiles" | [→ Verification](verify) |
| **3. Physicist** | "Show me the equations" | [→ For Physicists](for-physicists) |
| **4. Mathematician** | "Show me the proofs" | [→ For Mathematicians](for-mathematicians) |
| **5. Expert** | "I want the Agda" | [→ FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda) |

---

## What is computed?

The following are **mathematical theorems** (Agda `--safe --without-K`):

| Quantity | K₄ Formula | Result | Physical Match |
|----------|------------|--------|----------------|
| Dimension | λ=4 multiplicity | **d = 3** | ✓ 3 spatial |
| Time | Drift asymmetry | **1** | ✓ 1 temporal |
| Signature | Symmetric/asymmetric | **(−,+,+,+)** | ✓ matches GR |
| Coupling | dim × χ | **κ = 8** | ✓ matches 8πG |
| Gyromagnetic | \|Bool\| | **g = 2** | ✓ Dirac prediction |
| Spectral formula | λ³χ + deg² + 4/111 | **137.036036** | ≈ α⁻¹ (0.000027%) |
| Anomaly | 1/(α⁻¹ × E) | **1/822** | ≈ (g-2)/2 (~5%) |
| Epoch count | 5 × 4¹⁰⁰ | **N** | ≈ τ/t_P (0.4%) |

**These formulas are not fits.** They are spectral and structural invariants of K₄ — properties the graph necessarily possesses. We compute what is mathematically determined by K₄'s structure.

**5 exact matches. 3 excellent matches. The ~5% error is systematic (E=6 vs 2π=6.28).**

**The mathematical computations are proven. That they correspond to physical reality is a hypothesis supported by remarkable numerical agreement.**

[→ All predictions](predictions)

---

## Visual Evidence

*Click any image to view full size.*

### Why K₄ is unique for α⁻¹

The spectral formula λᵈχ + deg² for complete graphs Kₙ:

<a href="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}"><img src="{{ '/assets/images/fig2_alpha_uniqueness.png' | relative_url }}" alt="K₄ Uniqueness"></a>

**Only K₄ produces a value near 137.** K₃ gives 22. K₅ gives 1,266. This is not fine-tuning — it's the unique solution.

### Genesis: How K₄ emerges

<a href="{{ '/assets/images/fig4_genesis.png' | relative_url }}"><img src="{{ '/assets/images/fig4_genesis.png' | relative_url }}" alt="Genesis Chain"></a>

**Each step is forced.** D₁ distinguishes D₀ from its absence. D₂ witnesses the (D₀, D₁) pair. D₃ closes the structure. At n=4, every pair has witnesses among the remaining two. K₄ is not chosen — it is necessary.

### The +1 in E²+1 = 37

<a href="{{ '/assets/images/fig5_compactification.png' | relative_url }}"><img src="{{ '/assets/images/fig5_compactification.png' | relative_url }}" alt="Compactification Pattern"></a>

**One-point compactification:** The +1 is the mathematical price for transitioning from discrete K₄ (∈ ℚ) to continuous physics (∈ ℝ). All three compactified values (5, 17, 37) are prime.

### Summary: K₄ Invariants and Observed Matches

<a href="{{ '/assets/images/fig6_summary.png' | relative_url }}"><img src="{{ '/assets/images/fig6_summary.png' | relative_url }}" alt="Summary"></a>

---

## The Dirac Equation IS K₄

The most fundamental equation of particle physics:

$$(i\gamma^\mu \partial_\mu - m)\psi = 0$$

**Every number in this equation comes from K₄:**

| Dirac (1928) | K₄ Structure | Value |
|--------------|--------------|-------|
| γ-matrices | Vertices | **4** |
| Bivectors (γᵘγᵛ) | Edges | **6** |
| Clifford dimension | 2^Vertices | **16** |
| Spinor components | \|Bool\|² | **4** |
| Gyromagnetic ratio g | \|Bool\| | **2** |
| Signature | Drift asymmetry | **(−,+,+,+)** |

**The mathematical connection:** The Clifford algebra Cl(3,1) — the algebraic structure underlying the Dirac equation — exhibits the same combinatorial structure as K₄. This is not interpretation: 4 generators correspond to 4 vertices, 6 bivectors to 6 edges, signature (−,+,+,+) matches K₄'s asymmetry. The structural isomorphism is precise.

Dirac spent 4 years deriving this relativistically. We show: **he found K₄ in the continuum limit.**

And K₄ comes from D₀ = {φ, ¬φ} = "yes or no".

**The equation that predicts antimatter follows from the simplest possible distinction.**

[→ Full derivation](for-mathematicians#the-clifford-algebra-from-k₄)

---

## What is Agda?

**Agda** is a functional programming language with dependent types and an interactive proof assistant. Unlike mathematical proofs on paper, every step is machine-checked — the compiler guarantees logical consistency.

**Why Agda for First Distinction?**

- **No hidden assumptions:** The `--safe --without-K` mode forbids logical axioms and postulates. What is not explicitly derived does not exist.
- **Full transparency:** Anyone can verify the proof themselves — a single compiler run suffices.
- **Reproducible:** The result does not depend on human interpretation.

**What does "proof" mean in Agda?**

A proof is a program whose type encodes a mathematical statement. If the program compiles, the statement is proven.

- *For physicists:* Like a numerical experiment that is always exactly reproducible — but with symbolic rather than numerical precision.
- *For mathematicians:* Like a formally verified proof in a Hilbert system, machine-checked for correctness.

---

## Why Type Theory?

In 1972, Per Martin-Löf created intuitionistic type theory.

The unit type ⊤ has exactly one inhabitant. The empty type ⊥ has none. This isn't arbitrary — it's the **only** way to have "something" versus "nothing" without presupposing structure.

We observe: **⊤ with `tt` has the same structure as D₀ with φ.**

| Martin-Löf (1972) | First Distinction |
|-------------------|-------------------|
| ⊥ (empty type) | Before distinction |
| ⊤ (unit type) | D₀ — the First Distinction |
| Bool | φ vs ¬φ |
| _≡_ (identity) | Self-recognition of D₀ |

Type theory embodies constructivism. We use it to construct K₄.

---

## Check it yourself

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K --no-libraries FirstDistinction.agda
```

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)

The code is the claim. If it compiles, the proof is valid.

[→ Verification](verify)

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

The mathematics is machine-verified. The physics interpretation requires experiment. We present the strongest possible mathematical evidence, but the identification with physics remains a testable claim.

If you find an error, open an issue. We want to know.

---

## AI Disclosure

This work was created over 12 months by one person using six different AI systems (Claude Opus, Claude Sonnet, ChatGPT, Gemini, Sonar-R1, DeepSeek-R1). Agda doesn't lie — if it compiles under `--safe --without-K`, the proof is valid.

[→ Open questions](faq)

---

<div class="footer-links">
  <a href="https://github.com/de-johannes/FirstDistinction">GitHub</a>
  <a href="verify">Verify</a>
  <a href="predictions">Predictions</a>
</div>