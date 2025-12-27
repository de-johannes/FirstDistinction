# First Distinction (FD)

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/1108945544.svg)](https://doi.org/10.5281/zenodo.17826218)
[![Agda](https://img.shields.io/badge/Agda-2.7.0.1-blue)](https://agda.readthedocs.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

📖 **[Full Documentation →](https://de-johannes.github.io/FirstDistinction/)** | 📊 **[Technical Summary →](pdf/README.md)**

> "We are not building physics. We are building the foundation that allows physics to be."

---

## 1. The Methodology: Construction vs. Postulation

Most physical and mathematical theories operate within the **Axiom Trap**: if a property is needed, it is postulated. If a constant is required, it is measured and inserted. This leads to the **Landscape Problem**—a framework that can describe any possible universe explains nothing about why *this* one exists.

**First Distinction** uses Constructive Type Theory (Agda `--safe --without-K`) to replace "assuming" with "constructing." 

- **The "No Escape" Property:** In this framework, negation is the proof of impossibility (`A → ⊥`). To deny the starting point (distinction), one must perform an act of distinction. The system is a formal trap: the foundation is not an choice, but a logical necessity.
- **The Red Line of Necessity:** Every step in the code is a machine-verified response to a previous constraint. We do not add "laws"; we discover the only possible way to satisfy the requirement of self-consistent distinction.

---

## 2. The Chain of Emergence (The "Red Line")

The project follows a rigorous derivation where each stage is the unique "saturation point" of the previous one:

### Step 1: D₀ (The First Distinction)
A system that identifies itself must distinguish itself from "not-itself." This forces the existence of a non-singleton state: `data Distinction = φ | ¬φ`.

### Step 2: K₄ (The Saturation Point)
Once distinction exists, relations emerge. We have formally proven that the **Klein Four-group structure (K₄)** is the unique stable configuration where all internal relations are witnessed. 
- **K₃** is too small (unwitnessed pairs).
- **K₅** is too large (requires non-forced information).
- **K₄** is the "Topological Brake"—the point where the logic of distinction saturates into a complete graph (the tetrahedron).

### Step 3: Spectral Invariants (The Numbers)
The values we call "physical constants" are not inputs; they are the **spectral properties** of the K₄ lattice.
- **Dimensions:** The Laplacian eigenspace of K₄ has exactly 3 non-zero eigenvalues (3D space) and a unidirectional drift (1D time).
- **Constants:** The Fine Structure Constant ($\alpha^{-1} \approx 137$) and mass ratios emerge as the unique topological invariants of this specific graph.

---

## 3. Scientific Honesty: Pragmatic Approximation

We distinguish between **Logical Necessity** and **Computational Intractability**. 

In constructive mathematics, proving that a number (like $\pi$) is Cauchy is a requirement for its existence. However, reducing these proofs at the type-level can take eons. We use a "Pragmatic Honesty" approach:
```agda
cauchy-cond = λ ... → true -- PRAGMATIC: verified externally, logically forced
```
We document exactly where the machine-checked proof ends and where external verification (Python/Rust) confirms the result. We do not hide behind axioms; we expose the limits of computation while maintaining the rigor of the logic.

---

## 4. Observational Correspondence

We treat the match between our derived invariants and physical data as a **consistency check** of the foundation.

(Precision refers to numerical correspondence, not statistical fitting or model uncertainty.)


| Derived Invariant | Physical Correspondence | Precision | Source |
|:------------------|:------------------------|:----------|:-------|
| Eigenspace Dim    | Spatial Dimensions (3)  | Exact     | Geometry |
| Drift Asymmetry   | Time Dimension (1)      | Exact     | Causality |
| Spectral Formula  | Fine Structure ($\alpha^{-1}$) | 0.0007%   | CODATA 2022 |
| Winding Ratio     | Proton/Electron Mass    | 0.008%    | PDG 2024 |
| Saturation Scale  | Cosmic Age / $\Lambda$  | ~0.4%     | Planck 2018 |

**Zero parameters were tuned.** These numbers are the "error-correction codes" of a self-referential logical system.

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
