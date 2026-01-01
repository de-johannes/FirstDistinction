---
layout: default
title: For Mathematicians
---

# For Mathematicians

A formal derivation in constructive type theory.

---

## The Logical Framework

First Distinction is a theorem-proving exercise in Agda under maximal restrictions:

```
--safe           No unsafe pragmas
--without-K      No uniqueness of identity proofs
```

Every object exists only if constructed. No axioms, no postulates, no holes.

---

## Why `refl` Is Not Trivial

A common criticism: "All your proofs are just `theorem-X : Y == Z; theorem-X = refl`. That's circular!"

**This misunderstands what `refl` does.**

When Agda accepts `refl`, it has **computed both sides to identical normal forms**. The complexity lies in the computation chain, not the final equality.

**What would be circular (NOT in the file):**
```agda
alpha : Q
alpha = 137  -- just set it

theorem : alpha == 137
theorem = refl  -- trivial, circular
```

**What actually happens (in the file):**
```agda
-- Build K4 from Genesis (~2000 lines of construction)
-- Compute Laplacian from K4 adjacency
-- Compute eigenvalues from Laplacian  
-- Extract spectral ratio

alpha-from-laplacian : Q
alpha-from-laplacian = [long computation chain]

theorem : alpha-from-laplacian approx 137.036
theorem = refl  -- Agda computed both sides, they match
```

The `refl` is the **verification**, not the content. The content is the 2000+ line computation chain.

See [DEPENDENCY_CHAIN.md](https://github.com/de-johannes/FirstDistinction/blob/main/DEPENDENCY_CHAIN.md) for the complete trace.

---

## The Single Premise

```agda
data Distinction : Set where
  phi  : Distinction
  not-phi : Distinction
```

This is isomorphic to Bool but with semantic intent: phi and not-phi are the two poles of the first distinction D0.

**Claim:** This premise is unavoidable.

**Proof:** To deny "distinction exists," you must distinguish that denial from its opposite. The denial presupposes what it denies.

```agda
record Unavoidable (P : Set) : Set where
  field
    to-assert : P
    to-deny   : (P -> Empty) -> P

unavoidability : Unavoidable Distinction
unavoidability = record
  { to-assert = phi
  ; to-deny   = lambda _ -> phi
  }
```

---

## The Derivation Chain

```
D0 (First Distinction)
 |
 +-- D1 (Polarity: phi vs not-phi)
 |
 +-- D2 (Relation: D0 is not D1)
 |    |
 |    +-- K3 (triangle)
 |
 +-- D3 (Forced by irreducible pair (D0, D2))
 |    |
 |    +-- K4 (tetrahedron) -- STABLE
 |
 +-- Laplacian L of K4
 |    |
 |    +-- Eigenvalues {0, 4, 4, 4}
 |    |    |
 |    |    +-- d = 3 (multiplicity of lambda = 4)
 |    |
 |    +-- Ricci scalar R = Tr(L) = 12
 |
 +-- Drift irreversibility
      |
      +-- t = 1 (time dimension)
           |
           +-- Signature (-, +, +, +)
```

Every arrow is a theorem with a `refl` proof.

---

## Core Constructions

### Natural Numbers

```agda
data N : Set where
  zero : N
  suc  : N -> N

_+_ : N -> N -> N
zero  + n = n
suc m + n = suc (m + n)
```

All ring laws proven: commutativity, associativity, distributivity.

### Integers as Setoid Quotient

```agda
record Z : Set where
  constructor mkZ
  field
    pos : N
    neg : N

_equiv_ : Z -> Z -> Set
mkZ a b equiv mkZ c d = (a + d) == (c + b)
```

This is process-based: integers are signed winding numbers.

### Rationals as Field

```agda
record Q : Set where
  constructor _/_
  field
    num : Z
    den : N-positive
```

All 17 field axioms proven:

| Axiom | Status |
|-------|--------|
| equiv-refl | Proven |
| equiv-sym | Proven |
| equiv-trans | Proven |
| +Q-comm | Proven |
| +Q-assoc | Proven |
| +Q-identity-left | Proven |
| +Q-identity-right | Proven |
| +Q-inverse-left | Proven |
| +Q-inverse-right | Proven |
| *Q-comm | Proven |
| *Q-assoc | Proven |
| *Q-identity-left | Proven |
| *Q-identity-right | Proven |
| *Q-distrib-left | Proven |
| *Q-distrib-right | Proven |
| +Q-cong | Proven |
| *Q-cong | Proven |

### The Memory Function

```agda
triangular : N -> N
triangular zero    = zero
triangular (suc n) = n + triangular n

memory : N -> N
memory = triangular

theorem-K4-edges : memory 4 == 6
theorem-K4-edges = refl
```

### The Captures Relation

The key to K4 stability: all pairs are captured.

```agda
captures? : GenesisID -> GenesisPair -> Bool
captures? id pair = is-reflexive pair or is-defining id pair

theorem-K4-stable : All pairs captured
```

A pair is captured if:
1. Reflexive: (Di, Di) captured by Di itself
2. Defining: (D0, D1) captured by D2, (D0, D2) captured by D3

---

## Key Theorems

### K4 Uniqueness

**Theorem:** K4 is the unique stable graph under the captures relation.

**Proof sketch:**
1. K3 is unstable: pair (D0, D2) is irreducible
2. K4 is stable: all 6 pairs captured
3. K5 cannot form: no forcing mechanism beyond K4

```agda
K3-unstable : IrreduciblePair pair-D0D2
K3-unstable = theorem-D0D2-is-irreducible

K4-stable : All-captured
K4-stable = theorem-all-K4-pairs-captured
```

### Dimension Theorem

**Theorem:** d = 3 follows from the multiplicity of eigenvalue lambda = 4.

The K4 Laplacian has eigenvalues {0, 4, 4, 4}. The eigenvalue 4 has multiplicity 3, giving 3 linearly independent eigenvectors spanning a 3-dimensional space.

```agda
theorem-dimension-3 : eigenvalue-multiplicity 4 == 3
theorem-dimension-3 = refl
```

### Signature Theorem

**Theorem:** The metric signature is (-, +, +, +).

Edges are symmetric (bidirectional): contribute +1.
Drift is asymmetric (irreversible): contributes -1.

```agda
theorem-signature : signature == (neg, pos, pos, pos)
theorem-signature = refl
```

---

## The Four-Part Proof Pattern

Each major value (3D space, 1D time, alpha) is proven via four independent constraints:

| Part | Purpose | Example for d=3 |
|------|---------|-----------------|
| **Consistency** | Multiple derivations agree | Eigenspace dim = vertex degree = 3 |
| **Exclusivity** | Other values impossible | d=2 breaks K4 embedding |
| **Robustness** | Value survives perturbation | d=3 stable under edge removal |
| **CrossConstraints** | Matches independent derivations | d=3 matches Clifford algebra dim |

```agda
record DimensionTheorems : Set where
  field
    consistency       : DimensionConsistency
    exclusivity       : DimensionExclusivity  
    robustness        : DimensionRobustness
    cross-constraints : DimensionCrossConstraints
```

This pattern appears 10 times in the codebase, covering: dimension, time, signature, kappa, alpha, g-factor, mass ratios, and more.

---

## The Alpha Formula

Two independent derivations produce the same number.

### Spectral Derivation

```
alpha-inverse = lambda^3 * chi + deg^2 + V / (deg * (E^2 + 1))
```

With K4 values:
- lambda = 4 (spectral gap)
- chi = 2 (Euler characteristic)
- deg = 3 (vertex degree)
- V = 4, E = 6

Calculation:
- 4^3 * 2 = 128
- 3^2 = 9
- 4 / (3 * 37) = 4/111

Result: 128 + 9 + 0.036 = 137.036

```agda
theorem-alpha-integer : alpha-integer == 137
theorem-alpha-integer = refl
```

### Cross-Validation

The same result from operad structure:
- Product of categorical arities: 2 * 4 * 2 * 4 = 64
- Sum of algebraic arities: 3 + 3 + 2 + 1 = 9
- Result: 64 * 2 + 9 = 137

---

## Proof Statistics

| Metric | Value |
|--------|-------|
| Total lines | 7,938 |
| Named theorems | ~700 |
| Four-part proof structures | 10 |
| Forcing theorems | 4 |
| Postulates | 0 |
| Holes | 0 |

---

## The Type-Theoretic Foundation

### Distinction Hierarchy

The construction proceeds through strict levels:

```agda
D₀ : Set       -- Primordial distinction (●)
D₁ : Set       -- Polarized distinction (↑, ↓)  
D₂ : Set       -- Relational distinction (composable pairs)
```

Each level **carries its predecessor witness**:
- Every D₁ term contains D₀ via `extract₀ : D₁ → D₀`
- Every D₂ term contains D₁ via `extract₁ : D₂ → D₀`

This is not narrative layering—it's typed dependency enforced by the type checker.

### Graph Emergence from Types

The K4 graph emerges as the unique solution to stability constraints:

**Vertices**: The four distinguishable states form naturally from:
```agda
V₁ : Vertex  -- from ●
V₂ : Vertex  -- from ↑  
V₃ : Vertex  -- from ↓
V₄ : Vertex  -- from closure (uniqueness of the fourth)
```

**Edges**: Complete connectivity is forced by:
- Reflexivity demands self-loops would trivialize structure
- Asymmetry forbidden (would reintroduce hierarchy)
- Therefore: maximal simple graph on 4 vertices = K4

### Spectral Analysis

The Laplacian of K4:
```
L = D - A
where D = diag(3,3,3,3)  (degree matrix)
      A = adjacency matrix (1s off-diagonal)
```

**Eigenvalue computation** (all via `refl`):
```agda
eigenvalue-0 : λ₀ ≡ 0
eigenvalue-1 : λ₁ ≡ 4  (multiplicity 3)
```

The **3-fold degeneracy** of λ = 4 is not coincidental—it's the **dimension of space**.

---

## What IS Proven vs Hypothesis

### PROVEN (Agda --safe --without-K)

- K4 emerges as the unique stable graph
- Eigenvalue multiplicities determine d = 3 + 1
- The formulas compute specific numbers
- All mathematical derivations are machine-verified
- Complete number hierarchy ℕ to ℤ to ℚ
- Every D₂ term carries D₁ witness (structural typing)
- Every D₁ term carries D₀ witness (ontological grounding)

### HYPOTHESIS (not checkable by Agda)

- That K4 structure IS physical spacetime
- That 137.036 IS alpha inverse
- That the numerical matches have physical meaning
- That eigenvalue degeneracy IS spatial dimension

The mathematics is proven. The physics correspondence is hypothesis.

---

## Source Code

The complete proof: [FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda)

```bash
git clone https://github.com/de-johannes/FirstDistinction.git
cd FirstDistinction
agda --safe --without-K FirstDistinction.agda
```

Compilation equals validity.

---

[Back](./) | [For Physicists](for-physicists)
