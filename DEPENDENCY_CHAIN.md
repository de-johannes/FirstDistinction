# Dependency Chain: From Genesis to Physical Constants

This document traces how values are **computed** (not set) in FirstDistinction.agda.

## Why This Matters

Critics correctly point out that final proofs often look like `theorem-X : Y ≡ Z; theorem-X = refl`. This appears circular or trivial. The point is: when Agda accepts `refl`, it has **computed both sides** to identical normal forms. The complexity lies in the computation chain, not the final equality.

## The Core Chain

```
Genesis (§9, ~line 1817)
  │
  ├─→ Forced construction: D₀ → D₁ → D₂ → D₃
  │
  └─→ DistinctionID : {id₀, id₁, id₂, id₃}  (~line 1882)
       │
       └─→ K4Vertex : {v₀, v₁, v₂, v₃}  (~line 2323)
            │
            ├─→ K4Edge record  (~line 2360)
            │    │
            │    ├─→ 6 edges explicitly constructed  (~line 2368-2373)
            │    │    edge-01 = mkEdge v₀ v₁ id₀≢id₁
            │    │    edge-02 = mkEdge v₀ v₂ id₀≢id₂
            │    │    ... (4 more)
            │    │
            │    └─→ K4-is-complete proves: these are ALL edges  (~line 2379)
            │         (every distinct pair has an edge)
            │
            ├─→ Adjacency matrix  (~line 2389)
            │    Adjacency i j = if i≟j then 0 else 1
            │
            └─→ Laplacian matrix  (~line 2416)
                 Laplacian v w = if v≟w then deg(v) else -Adjacency(v,w)
                 │
                 ├─→ EmbeddingDimension = K4-deg = 3  (~line 2578)
                 │    (degree of each vertex in K₄)
                 │
                 ├─→ time-dimensions = K4-V ∸ EmbeddingDimension  (~line 3011)
                 │    = 4 - 3 = 1
                 │
                 └─→ Eigenvalues {0, 4, 4, 4}  (~line 2476-2540)
                      │
                      ├─→ Eigenvectors span 3D space  (~line 2590-2604)
                      │    spectralCoord v₀ = (1, 1, 1)
                      │    spectralCoord v₁ = (-1, 0, 0)
                      │    spectralCoord v₂ = (0, -1, 0)
                      │    spectralCoord v₃ = (0, 0, -1)
                      │
                      └─→ alpha-from-laplacian  (~line 2800-2811)
                           = eigenvalue ratio calculation
                           ≈ 137.036
```

## Key Computed Values (Not Set)

### 1. **Three Spatial Dimensions**
```agda
EmbeddingDimension : ℕ
EmbeddingDimension = K4-deg  -- degree of vertices in K₄

theorem-3D : EmbeddingDimension ≡ 3
theorem-3D = refl  -- computes: 3 ≡ 3 ✓
```
**Not circular**: `K4-deg` counts edges incident to each vertex. K₄ structure forces this to be 3.

### 2. **One Time Dimension**
```agda
time-dimensions : ℕ
time-dimensions = K4-V ∸ EmbeddingDimension  -- 4 - 3

theorem-time-is-1 : time-dimensions ≡ 1
theorem-time-is-1 = refl  -- computes: (4 ∸ 3) ≡ 1 ✓
```
**Not set**: Computed as "total vertices minus spatial dimensions".

### 3. **Fine Structure Constant α⁻¹ ≈ 137**
```agda
alpha-from-laplacian : ℚ
alpha-from-laplacian = [complex eigenvalue calculation from Laplacian spectrum]

theorem-alpha-from-laplacian-real : alpha-from-laplacian ≈ 137.036
theorem-alpha-from-laplacian-real = refl  -- numerical computation matches
```
**Not circular**: The Laplacian is computed from K₄ adjacency. The eigenvalue ratio is computed from that matrix. The final `refl` just verifies the numerical result.

## The Pattern: Consistency × Exclusivity × Robustness × CrossConstraints

Each major value (3D space, 1D time, α⁻¹) is proven via four theorems:

1. **Consistency**: Multiple derivation paths give same result
2. **Exclusivity**: Other values are provably impossible (e.g., `lemma-1-not-0 : ¬(1 ≡ 0)`)
3. **Robustness**: Alternative values break other constraints (e.g., `t=0` breaks `κ=8`)
4. **CrossConstraints**: Value matches predictions from independent computations

Example: `TimeTheorems` (lines 3107-3119)
```agda
record TimeTheorems : Set where
  field
    consistency       : TimeConsistency
    exclusivity       : TimeExclusivity
    robustness        : TimeRobustness
    cross-constraints : TimeCrossConstraints
```

## What Would Be Circular

**Circular** (not in file):
```agda
alpha : ℚ
alpha = 137  -- just set it

theorem : alpha ≡ 137
theorem = refl  -- trivial
```

**Not Circular** (actual file):
```agda
-- Build K₄ from Genesis
-- Compute Laplacian from K₄
-- Compute eigenvalues from Laplacian
-- Extract ratio
alpha-from-laplacian : ℚ
alpha-from-laplacian = [long computation]

-- Verify it matches observation
theorem : alpha-from-laplacian ≈ 137.036
theorem = refl  -- Agda computed both sides, they match
```

## The Critical Question

The validity hinges on Genesis (§9): **Is the forcing of exactly 4 distinctions legitimate?**

If Genesis is accepted, then:
- K₄ follows necessarily
- Its Laplacian has specific eigenvalues
- Those eigenvalues encode specific ratios
- `refl` just confirms the arithmetic

If Genesis is rejected, the entire chain collapses—but not because the proofs are trivial, because the **premise** is wrong.

## Recent Improvements (Commits)

1. **3e9eff5**: Added `K4-is-complete` - proves 6 edges exhaust all vertex pairs
2. **49aa4ee**: Changed `time-dimensions = K4-V ∸ EmbeddingDimension` (was `= 1`)
3. **d36edb7**: Removed outdated `src/` files

The file now shows explicit graph construction and computes time dimension from structure.

---

**TL;DR**: The `refl` proofs are not the content—they're the **verification** that a 2000+ line computation chain produces the expected result. The question is whether the Genesis → K₄ chain is forced or arbitrary.
