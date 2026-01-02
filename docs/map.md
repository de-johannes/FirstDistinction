# Dependency Map: First Distinction → Physics

This document traces the logical dependencies from the foundational axiom (D₀) through
to the physical constants. Each arrow (→) indicates "is required for" or "flows into".

## The Emergence Chain

```
                        ┌─────────────────────────────────────────────────────────────┐
                        │                    LEVEL 0: AXIOM                           │
                        │                                                             │
                        │                        D₀                                   │
                        │                  (First Distinction)                        │
                        │                    Line ~238                                │
                        └─────────────────────────────────────────────────────────────┘
                                                  │
                                                  ▼
                        ┌─────────────────────────────────────────────────────────────┐
                        │                 LEVEL 1: BOOTSTRAPPING                      │
                        │                                                             │
                        │    D₀ → D₁ (polarity) → D₂ (relation) → D₃ (closure)       │
                        │              Lines ~265, ~303, ~5250                        │
                        │                                                             │
                        │         ¬¬D₀ (unavoidability, line ~356)                   │
                        └─────────────────────────────────────────────────────────────┘
                                                  │
                                                  ▼
┌─────────────────────────────────────────────────────────────────────────────────────────────────┐
│                               LEVEL 2: GRAPH EMERGENCE                                          │
│                                                                                                 │
│   D₀,D₁,D₂,D₃ ←→ K4 vertices                                                                   │
│                                                                                                 │
│   ┌─────────────────────────────────────────────────────────────────────────────────────┐       │
│   │  MASTER THEOREM: theorem-4-unique-fixpoint (Line ~6259)                             │       │
│   │  ∀ n : ℕ → memory(n) = 6 → deg(n) = 3 → n = 4                                       │       │
│   │                                                                                     │       │
│   │  This is THE uniqueness proof. Everything below depends on it.                      │       │
│   └─────────────────────────────────────────────────────────────────────────────────────┘       │
│                                                                                                 │
│   K4-V = 4         (vertices, line ~5886)                                                       │
│   K4-E = 6         (edges, line ~5889)                                                          │
│   K4-deg = 3       (degree, line ~5895)                                                         │
│   K4-chi = 2       (Euler characteristic, line ~5898)                                           │
│                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────┘
                                    │
            ┌───────────────────────┼───────────────────────┬───────────────────────┐
            ▼                       ▼                       ▼                       ▼
┌─────────────────────┐ ┌─────────────────────┐ ┌─────────────────────┐ ┌─────────────────────┐
│  LEVEL 3a: SPECTRA  │ │  LEVEL 3b: DIMENSION│ │  LEVEL 3c: TIME     │ │  LEVEL 3d: TOPOLOGY │
│                     │ │                     │ │                     │ │                     │
│  λ = K4-V = 4       │ │  d = K4-deg = 3     │ │  t = K4-V - d = 1   │ │  χ = K4-chi = 2     │
│  (spectral gap)     │ │  (EmbeddingDimension│ │  (time-dimensions)  │ │  (Euler char)       │
│  Line ~7083         │ │  Line ~7268)        │ │  Line ~8872         │ │  Line ~5898         │
│                     │ │                     │ │                     │ │                     │
│  λ₄ eigenmodes: 3   │ │  3D space forced    │ │  1 time forced      │ │  χ = V - E + F      │
│                     │ │  d ≠ 2, d ≠ 4       │ │  t ≠ 0, t ≠ 2       │ │                     │
└─────────────────────┘ └─────────────────────┘ └─────────────────────┘ └─────────────────────┘
            │                       │                       │                       │
            └───────────────────────┴───────────────────────┴───────────────────────┘
                                                │
                                                ▼
┌─────────────────────────────────────────────────────────────────────────────────────────────────┐
│                               LEVEL 4: COUPLING CONSTANTS                                       │
│                                                                                                 │
│   ┌─────────────────────────────────────────────────────────────────────────────────────┐       │
│   │  α⁻¹ = λ^deg · χ + deg² = 4³ · 2 + 9 = 137    (Line ~13xxx)                        │       │
│   │                                                                                     │       │
│   │  Uses: λ (spectral gap), deg (K4-deg), χ (Euler char)                              │       │
│   └─────────────────────────────────────────────────────────────────────────────────────┘       │
│                                                                                                 │
│   κ = 2 · V = 2 · 4 = 8                           (Line ~5205)                                  │
│   Uses: V (K4-V)                                                                                │
│                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────┘
                                                │
                                                ▼
┌─────────────────────────────────────────────────────────────────────────────────────────────────┐
│                               LEVEL 5: PARTICLE MASSES                                          │
│                                                                                                 │
│   proton/electron = 6π⁵ = 1836                    (Line ~14xxx)                                 │
│   Uses: π (from K4 geometry), integers from K4 topology                                         │
│                                                                                                 │
│   muon/electron = 3π⁴/2 = 207                                                                   │
│   Uses: π, K4 winding numbers                                                                   │
│                                                                                                 │
│   tau/muon = F₂ = 17  (Fermat prime)                                                           │
│   Uses: F₂ index from K4 structure                                                              │
│                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────┘
                                                │
                                                ▼
┌─────────────────────────────────────────────────────────────────────────────────────────────────┐
│                               LEVEL 6: COSMOLOGY                                                │
│                                                                                                 │
│   Universal Correction ε(Λ) = log-correction                                                    │
│   Uses: K4 structure, α, cosmological scale                                                     │
│                                                                                                 │
│   Hubble parameter, dark energy fraction, etc.                                                  │
│                                                                                                 │
└─────────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Dependency Table

| Constant | Formula | Depends On | Line |
|----------|---------|------------|------|
| **K4-V** | 4 | D₀→D₃ genesis | ~5886 |
| **K4-E** | 6 | K4-V (complete graph) | ~5889 |
| **K4-deg** | K4-V - 1 = 3 | K4-V | ~5895 |
| **K4-chi** | V - E + F = 2 | K4-V, K4-E | ~5898 |
| **λ (spectral gap)** | 4 | K4-V (Laplacian eigenvalue) | ~7083 |
| **EmbeddingDimension** | K4-deg = 3 | K4-deg | ~7268 |
| **time-dimensions** | K4-V - EmbeddingDimension = 1 | K4-V, d | ~8872 |
| **κ** | 2 · K4-V = 8 | K4-V | ~5205 |
| **α⁻¹** | λ^deg · χ + deg² = 137 | λ, deg, χ | ~13xxx |
| **proton mass ratio** | 6π⁵ = 1836 | π (from K4) | ~14xxx |

## Critical Observation: Current Text Order vs. Logical Order

### Current Structure (lines):
1. ~238: D₀ definition ✓
2. ~2446: α comparison with PDG (USES α before it's derived!)
3. ~5886: K4-V, K4-E, etc. defined
4. ~6259: **theorem-4-unique-fixpoint** (MASTER THEOREM) ← Should be earlier!
5. ~7268: EmbeddingDimension
6. ~8872: time-dimensions
7. ~13xxx: α formula
8. ~14xxx: masses

### Recommended Order:
1. **Part I: Genesis** (D₀ → D₃)
2. **Part II: Graph Emergence** (K4 invariants + MASTER THEOREM)
3. **Part III: Spectral Analysis** (λ, eigenmodes)
4. **Part IV: Spacetime** (d=3, t=1)
5. **Part V: Coupling Constants** (α, κ)
6. **Part VI: Masses**
7. **Part VII: Cosmology**
8. **Part VIII: Validation** (comparison with PDG)

The current structure has validation (PDG comparison) mixed in early, before the derivations
are complete. This is confusing for readers and obscures the logical flow.

## The Minimal Dependency Chain

```
D₀ → ¬¬D₀ → genesis(4) → K4-V=4 → K4-E=6, K4-deg=3, K4-chi=2
                                          │
                                          ▼
                              theorem-4-unique-fixpoint
                              "n=4 is the unique solution"
                                          │
                    ┌─────────────────────┼─────────────────────┐
                    ▼                     ▼                     ▼
                  λ = 4              d = deg = 3            χ = 2
                    │                     │                     │
                    └─────────────────────┼─────────────────────┘
                                          ▼
                              α⁻¹ = λ^d · χ + d² = 137
                                          │
                                          ▼
                              proton = 6π⁵ = 1836
```

This is the irreducible core: **15 lines of logic** produce the fundamental constants.
