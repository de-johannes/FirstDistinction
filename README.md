# First Distinction (FD)

[![CI](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml/badge.svg)](https://github.com/de-johannes/FirstDistinction/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/1108945544.svg)](https://doi.org/10.5281/zenodo.17826218)
[![Agda](https://img.shields.io/badge/Agda-2.7.0.1-blue)](https://agda.readthedocs.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

📖 **[Full Documentation →](https://de-johannes.github.io/FirstDistinction/)**

**4 vertices. 6 edges. Everything else follows.**

---

## The Challenge

**Try to deny that distinction exists.**

To say "there is no distinction" — you must distinguish that statement from its opposite.  
To think "nothing is different" — you must differentiate that thought from other thoughts.

**You cannot deny distinction without using distinction.**

This isn't wordplay. It's the starting point. We formalize what follows.

---

## What This Is

A single Agda file (`FirstDistinction.agda`, 7,000+ lines) that:

1. **Proves** K₄ (tetrahedron graph) emerges from self-referential distinction
2. **Computes** invariants: V=4, E=6, χ=2, deg=3, Laplacian eigenvalues {0,4,4,4}
3. **Observes** these numbers match physical constants — with no free parameters

```
D₀ exists (distinction)
       ↓
Genesis: D₀ → D₁ → D₂ → D₃
       ↓
K₄ complete graph (4 vertices, 6 edges)
       ↓
d = 3    κ = 8    α⁻¹ = 137    Dirac spinor = 4
```

Machine-checked under `--safe --without-K`. No postulates, no holes.

---

## The Numbers

| K₄ Computation | Result | Physical Match | Error |
|----------------|--------|----------------|-------|
| Laplacian eigenspace dim | **3** | Spatial dimensions | exact |
| Drift asymmetry | **1** | Time dimension | exact |
| \|Bool\| × \|K₄\| | **κ = 8** | Einstein coupling 8πG | exact |
| Spectral formula | **137.036** | Fine structure α⁻¹ | 0.000027% |
| 5 × 4¹⁰⁰ Planck times | **13.7 Gyr** | Cosmic age | 0.4% |
| Clifford grades | **1,4,6,4,1** | Dirac γ-matrices | exact |

### Why K₄ is Unique

![K₄ Uniqueness](figures/fig2_alpha_uniqueness.png)

**Only K₄ produces ~137.** The spectral formula for Kₙ grows exponentially. K₃ gives 22. K₅ gives 1,266. This is not fine-tuning.

**Formula structure is proven unique:** Machine-verified theorems (§22f.2e′–⁗) show that λ² or λ⁴ fail, χ adding (not multiplying) fails, and deg² multiplying (not adding) fails. All alternative formulas are proven to produce wrong values.

### Mass Ratios (Combinatorial Formulas)

| Particle | K₄ Formula | Computed | Experiment | Error |
|----------|------------|----------|------------|-------|
| Proton/electron | χ² × deg³ × F₂ | **1836** | 1836.15 | 0.008% |
| Neutron/electron | proton + χ | **1838** | 1838.68 | 0.04% |
| Muon/electron | deg² × (2^V + V + deg) | **207** | 206.77 | 0.1% |
| Tau/Muon | F₂ | **17** | 16.82 | 1% |
| Top/electron | α⁻² × (F₂ + 1) | **337,842** | 337,900 | 0.02% |

where F₂ = 17 = 2⁴ + 1 (Fermat prime)

**The K₄ computations are proven. The physical correspondence is observed.**

---

## The Dirac Equation IS K₄

Every number in $(i\gamma^\mu \partial_\mu - m)\psi = 0$ comes from K₄:

| Dirac Structure | K₄ Source | Value |
|-----------------|-----------|-------|
| γ-matrices | Vertices V | 4 |
| Bivectors σᵘᵛ | Edges E | 6 |
| Spinor components | 2^(V/2) | 4 |
| Clifford dimension | 2^V | 16 |
| Gyromagnetic ratio | \|Bool\| | 2 |
| Signature | Drift asymmetry | (−,+,+,+) |

**The connection:** K₄ → Laplacian spectrum {0,4,4,4} → 3D eigenspace → Cl(3,1). The dimensional invariants match: 4 generators ↔ 4 vertices, 6 bivectors ↔ 6 edges. This is spectral correspondence, not direct isomorphism.

---

## Honesty

**What IS proven (Agda `--safe --without-K`):**
- K₄ emerges uniquely from self-referential distinction
- All K₄ invariants compute: 3, 8, 137.036, 1836, ...
- Formula structure (λ³χ + deg²) is **uniquely determined** — all alternatives proven to fail
- Dimensional invariants of K₄ match those of Cl(3,1)
- Every formula is machine-verified, no axioms, no holes

**What is HYPOTHESIS:**
- That K₄ structure IS the geometry of our universe
- That these numerical matches are not coincidental
- That physics derives from graph theory

The mathematics is certain. The interpretation is yours.

---

## Run It

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K FirstDistinction.agda
```

If it compiles, the K₄ derivations are valid. 7,000+ lines. Zero holes.

---

## Files

```
FirstDistinction/
├── FirstDistinction.agda  # The proof (7,000+ lines)
├── validate_K4.py         # Numerical validation
├── docs/                  # Full documentation
└── README.md
```

---

## Documentation

| If you want... | Go to... |
|----------------|----------|
| The full website | [de-johannes.github.io/FirstDistinction](https://de-johannes.github.io/FirstDistinction) |
| Physical interpretation | [For Physicists](https://de-johannes.github.io/FirstDistinction/for-physicists) |
| Mathematical details | [For Mathematicians](https://de-johannes.github.io/FirstDistinction/for-mathematicians) |
| All numerical matches | [Predictions](https://de-johannes.github.io/FirstDistinction/predictions) |
| The source | [FirstDistinction.agda](FirstDistinction.agda) |

---

## Citation

```bibtex
@software{first_distinction_2025,
  author = {Wielsch, Johannes},
  title = {First Distinction: K₄ Structure and Physical Constants},
  year = {2025},
  url = {https://github.com/de-johannes/FirstDistinction}
}
```

---

## License

MIT (code) · CC BY 4.0 (docs)

---

**4 vertices. 6 edges. 137.036. The proof compiles.**

