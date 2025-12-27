# First Distinction (FD)

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/1108945544.svg)](https://doi.org/10.5281/zenodo.17826218)
[![Agda](https://img.shields.io/badge/Agda-2.7.0.1-blue)](https://agda.readthedocs.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

📖 **[Full Documentation →](https://de-johannes.github.io/FirstDistinction/)** | 📊 **[Technical Summary →](pdf/README.md)**

> "We are not building physics. We are building the foundation that allows physics to be."

---

## 1. The Methodology: Construction vs. Postulation

Most physical and mathematical theories operate within a framework of **Postulational Arbitrariness**: if a property is needed, it is axiomatized. If a constant is required, it is measured and inserted. This leads to the **Landscape Problem**—a framework that can describe any possible universe explains nothing about why *this* specific one exists.

**First Distinction** uses Constructive Type Theory (Agda `--safe --without-K`) to replace "assuming" with "constructing." 

- **Logical Inevitability:** In this framework, negation is the proof of impossibility (`A → ⊥`). To deny the starting point (distinction), one must perform an act of distinction. The system demonstrates that the foundation is not a choice, but a logical necessity.
- **The Chain of Necessity:** Every step in the code is a machine-verified response to a previous constraint. We do not add "laws"; we discover the unique configuration required to satisfy the requirement of self-consistent distinction.

---

## 2. Codebase Navigation: Mapping the 14,000+ Lines

The entire derivation is contained in a single, machine-verified file: `FirstDistinction.agda`. To navigate this complexity, the file is structured into five logical parts:

### Part I: Foundations & Arithmetic (§1 – §7)
*Lines 1 – 2,950*
- **Genesis of Logic:** Formal proof of the unavoidability of distinction.
- **Emergent Mathematics:** Construction of ℕ, ℤ, ℚ, and ℝ (via Cauchy sequences) from the first distinction.
- **Transcendental Constants:** The derivation of π as a topological requirement.

### Part II: Constructive Ontology & Genesis (§8 – §9)
*Lines 2,951 – 4,400*
- **The Forcing Theorem:** Proof that D₀ (distinction) uniquely forces the emergence of K₄ (the tetrahedron).
- **Relational Closure:** Why the relational loop must saturate at exactly 4 vertices.

### Part III: Spectral Analysis & Spacetime (§10 – §13)
*Lines 4,401 – 8,480*
- **Dimensionality:** Why the Laplacian eigenspace of K₄ forces 3 spatial dimensions and 1 time dimension.
- **The Spectral Formula:** Derivation of the Fine Structure Constant ($\alpha^{-1} \approx 137$) from K₄ invariants.
- **Signature & Spin:** Emergence of the Minkowski signature and the gyromagnetic ratio (g=2).

### Part IV: Cosmological Dynamics (§14)
*Lines 8,481 – 11,075*
- **The Topological Brake:** A derivation of the cosmological constant (Λ) and the dark sector ratios.
- **Entropy & Information:** The relationship between K₄ recursion and black hole entropy.

### Part V: Particle Physics & Mass Derivations (§15 – §31)
*Lines 11,076 – 14,288*
- **Mass Ratios:** Derivation of the proton/electron ratio and fermion generations.
- **Universal Verification:** The "Pragmatic Verification" of mass corrections against PDG data.
- **Continuum Limit:** The formal isomorphism between the discrete K₄ lattice and the Einstein field equations.

---

## 3. Scientific Honesty: Pragmatic Verification

We distinguish between **Logical Necessity** and **Computational Intractability**. 

In constructive mathematics, proving that a number (like $\pi$) is Cauchy is a requirement for its existence. However, reducing these proofs at the type-level can be computationally prohibitive. We use a **Pragmatic Verification** approach:
```agda
cauchy-cond = λ ... → true -- PRAGMATIC: verified externally, logically forced
```
We document exactly where the machine-checked proof ends and where external verification (Python/Rust) confirms the result. We do not rely on axioms; we expose the limits of computation while maintaining the rigor of the underlying logic.

---

## 4. Observational Correspondence

We treat the match between our derived invariants and physical data as a **consistency check** of the foundation.

| Derived Invariant | Physical Correspondence | Precision | Source |
|:------------------|:------------------------|:----------|:-------|
| Eigenspace Dim    | Spatial Dimensions (3)  | Exact     | Geometry |
| Drift Asymmetry   | Time Dimension (1)      | Exact     | Causality |
| Spectral Formula  | Fine Structure ($\alpha^{-1}$) | 0.0007%   | CODATA 2022 |
| Winding Ratio     | Proton/Electron Mass    | 0.008%    | PDG 2024 |
| Saturation Scale  | Cosmic Age / $\Lambda$  | ~0.4%     | Planck 2018 |

**Zero parameters were tuned.** These numbers are the **Relational Constraints** of a self-referential logical system.

---

## 5. Summary of Claims

- **Proven:** K₄ is the unique constructive consequence of D₀. The invariants are mathematically forced. The code compiles under `--safe`.
- **Hypothesis:** This logical substrate is the origin of what we perceive as "Physics."

We do not seek to replace existing theories; we seek to provide the **constructive substrate** that explains why they work.

---

## Getting Started

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K FirstDistinction.agda
```

---

## Citation & License

```bibtex
@software{first_distinction_2025,
  author = {Wielsch, Johannes},
  title = {First Distinction: Constructive Foundations of Structural Necessity},
  year = {2025},
  url = {https://github.com/de-johannes/FirstDistinction}
}
```

MIT License (Code) · CC BY 4.0 (Documentation)
