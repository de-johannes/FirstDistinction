{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4CoupledLaplacian where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.FiniteSumsZ
open import Disciplines.Math.IntegersLaws
open import Disciplines.Graph.K4Coupling
open import Disciplines.Graph.K4MatrixLaplacian

{-
CHAPTER 14G: Laplacian On Two Coupled K₄ Copies (Fin4×Two)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14E (Fin4 Laplacian as operator), Chapter 14F (coupling elimination)
AGDA MODULES: Disciplines.Graph.K4CoupledLaplacian
DEGREES OF FREEDOM ELIMINATED: ad hoc “8-vertex Laplacian” presentations
-}

Vec8ℤ : Set
Vec8ℤ = Vec4ℤ × Vec4ℤ

left4 : Vec8ℤ → Vec4ℤ
left4 = fst

right4 : Vec8ℤ → Vec4ℤ
right4 = snd

Vec8Eq : Vec8ℤ → Vec8ℤ → Set
Vec8Eq u v = Vec4Eq (left4 u) (left4 v) × Vec4Eq (right4 u) (right4 v)

_+Vec8ℤ_ : Vec8ℤ → Vec8ℤ → Vec8ℤ
(u +Vec8ℤ v) = (left4 u +Vec4ℤ left4 v) , (right4 u +Vec4ℤ right4 v)

negVec8ℤ : Vec8ℤ → Vec8ℤ
negVec8ℤ v = (λ i → negℤ (left4 v i)) , (λ i → negℤ (right4 v i))

fourVec8ℤ : Vec8ℤ → Vec8ℤ
fourVec8ℤ v = fourVec4ℤ (left4 v) , fourVec4ℤ (right4 v)

sum8ℤ : Vec8ℤ → ℤ
sum8ℤ v = sumFin4ℤ (left4 v) +ℤ sumFin4ℤ (right4 v)

J8Vec8ℤ : Vec8ℤ → Vec8ℤ
J8Vec8ℤ v = (λ _ → sum8ℤ v) , (λ _ → sum8ℤ v)

-- 8·x is forced as 4·x + 4·x.

eightTimesℤ : ℤ → ℤ
eightTimesℤ x = fourTimesℤ x +ℤ fourTimesℤ x

eightVec4ℤ : Vec4ℤ → Vec4ℤ
eightVec4ℤ v i = eightTimesℤ (v i)

K8LaplacianVec8ℤ : Vec8ℤ → Vec8ℤ
K8LaplacianVec8ℤ v =
  (λ i → eightTimesℤ (left4 v i) +ℤ negℤ (sum8ℤ v)) ,
  (λ i → eightTimesℤ (right4 v i) +ℤ negℤ (sum8ℤ v))

-- Disjoint union coupling (no cross-edges): block-diagonal Laplacian.

laplacianEmptyVec8ℤ : Vec8ℤ → Vec8ℤ
laplacianEmptyVec8ℤ v = laplacianVec4ℤ (left4 v) , laplacianVec4ℤ (right4 v)

-- Full join coupling (all cross-edges): the graph is K₈.
-- A forced operator form: on each block, add the four cross-degree term and subtract the other-block global sum.

laplacianFullVec8ℤ : Vec8ℤ → Vec8ℤ
laplacianFullVec8ℤ v =
  (λ i → laplacianVec4ℤ (left4 v) i +ℤ fourTimesℤ (left4 v i) +ℤ negℤ (sumFin4ℤ (right4 v))) ,
  (λ i → laplacianVec4ℤ (right4 v) i +ℤ fourTimesℤ (right4 v i) +ℤ negℤ (sumFin4ℤ (left4 v)))

{-
## Block Structure And Forced K₈ Form

### Law 14G.0: Empty Coupling Laplacian Is Block-Diagonal
**Necessity Proof:** `laplacianEmptyVec8ℤ` is defined componentwise as `L` on each `Vec4ℤ` block.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-0-empty-block (lines 84-86)
**Consequence:** Eliminates any mixing freedom when no cross-edges exist.
-}

law14G-0-empty-block : (v : Vec8ℤ) →
  Vec8Eq (laplacianEmptyVec8ℤ v) (laplacianVec4ℤ (left4 v) , laplacianVec4ℤ (right4 v))
law14G-0-empty-block v = (λ _ → refl) , (λ _ → refl)

{-
### Law 14G.1: Full Coupling Laplacian Collapses To The K₈ Spectral Form
**Necessity Proof:** By Law 14E.10 on each block,
`L₄ x i = 4·xᵢ - Σ₄ x`. Substituting into the full-coupling definition yields
`(4·xᵢ - Σ₄ x) + 4·xᵢ - Σ₄(other) = 8·xᵢ - Σ₈(v)`.
Reassociation is forced by `+ℤ-assoc`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-1-full-is-K8 (lines 98-149)
**Consequence:** Eliminates presentation freedom: the complete-join coupling is the unique complete graph Laplacian form.
-}

law14G-1-full-is-K8 : (v : Vec8ℤ) →
  Vec8Eq (laplacianFullVec8ℤ v) (K8LaplacianVec8ℤ v)
law14G-1-full-is-K8 v =
  let
    sL = sumFin4ℤ (left4 v)
    sR = sumFin4ℤ (right4 v)

    left-proof : (i : Fin4) →
      laplacianVec4ℤ (left4 v) i +ℤ fourTimesℤ (left4 v i) +ℤ negℤ sR ≡
      eightTimesℤ (left4 v i) +ℤ negℤ (sum8ℤ v)
    left-proof i =
      trans
        (cong (λ t → t +ℤ fourTimesℤ (left4 v i) +ℤ negℤ sR)
              (law14E-10-laplacian-four-minus-sumAll (left4 v) i))
        (trans
          (+ℤ-assoc (fourTimesℤ (left4 v i) +ℤ negℤ sL) (fourTimesℤ (left4 v i)) (negℤ sR))
          (trans
            (+ℤ-assoc (fourTimesℤ (left4 v i)) (negℤ sL) (fourTimesℤ (left4 v i) +ℤ negℤ sR))
            (trans
              (cong (λ t → fourTimesℤ (left4 v i) +ℤ t)
                    (swapHeadℤ (negℤ sL) (fourTimesℤ (left4 v i)) (negℤ sR)))
              (trans
                (sym (+ℤ-assoc (fourTimesℤ (left4 v i)) (fourTimesℤ (left4 v i)) (negℤ sL +ℤ negℤ sR)))
                (trans
                  (cong (λ t → (fourTimesℤ (left4 v i) +ℤ fourTimesℤ (left4 v i)) +ℤ t)
                        (sym (neg-+ℤ sL sR)))
                  refl)))))

    right-proof : (i : Fin4) →
      laplacianVec4ℤ (right4 v) i +ℤ fourTimesℤ (right4 v i) +ℤ negℤ sL ≡
      eightTimesℤ (right4 v i) +ℤ negℤ (sum8ℤ v)
    right-proof i =
      trans
        (cong (λ t → t +ℤ fourTimesℤ (right4 v i) +ℤ negℤ sL)
              (law14E-10-laplacian-four-minus-sumAll (right4 v) i))
        (trans
          (+ℤ-assoc (fourTimesℤ (right4 v i) +ℤ negℤ sR) (fourTimesℤ (right4 v i)) (negℤ sL))
          (trans
            (+ℤ-assoc (fourTimesℤ (right4 v i)) (negℤ sR) (fourTimesℤ (right4 v i) +ℤ negℤ sL))
            (trans
              (cong (λ t → fourTimesℤ (right4 v i) +ℤ t)
                    (swapHeadℤ (negℤ sR) (fourTimesℤ (right4 v i)) (negℤ sL)))
              (trans
                (sym (+ℤ-assoc (fourTimesℤ (right4 v i)) (fourTimesℤ (right4 v i)) (negℤ sR +ℤ negℤ sL)))
                (trans
                  (cong (λ t → (fourTimesℤ (right4 v i) +ℤ fourTimesℤ (right4 v i)) +ℤ t)
                        (trans
                          (sym (neg-+ℤ sR sL))
                          (cong negℤ (+ℤ-comm sR sL))))
                  refl)))))
  in
  left-proof , right-proof

{-
## Coupling Elimination → Laplacian Survivors

This section connects Chapter 14F (elimination of cross-coupling predicates) to
the only Laplacian operator forms already forced in this module.

### Law 14G.2: An Iso-Invariant Coupling With One Edge Forces All Cross-Edges
**Necessity Proof:** This is Law 14F.0 transported into the Laplacian chapter: under
`CrossInv`, one witness `C a₀ b₀` cannot retain vertex labels.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-2-edge-forces-all-cross (lines 164-167)
**Consequence:** Eliminates intermediate couplings before any operator layer is applied.
-}

law14G-2-edge-forces-all-cross : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → C a0 b0)) →
  (a b : EndoCase) → C a b
law14G-2-edge-forces-all-cross = law14F-0-edge-forces-all

{-
### Law 14G.3: An Iso-Invariant Coupling With One Non-Edge Forces No Cross-Edges
**Necessity Proof:** This is Law 14F.1 transported into the Laplacian chapter: under
`CrossInv`, any alleged edge transports to any chosen pair.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-3-nonedge-forces-no-cross (lines 177-180)
**Consequence:** Eliminates intermediate couplings before any operator layer is applied.
-}

law14G-3-nonedge-forces-no-cross : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → ¬ (C a0 b0))) →
  (a b : EndoCase) → ¬ (C a b)
law14G-3-nonedge-forces-no-cross = law14F-1-nonedge-forces-none

{-
### Law 14G.4: Edge-Case Coupling Forces The K₈ Laplacian Form
**Necessity Proof:** By Law 14G.2 the edge-case coupling collapses to the complete join.
Then Law 14G.1 forces the K₈ operator form.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-4-edge-case-forces-K8 (lines 190-193)
**Consequence:** Eliminates all “full coupling” Laplacian presentations to the unique K₈ form.
-}

law14G-4-edge-case-forces-K8 : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → C a0 b0)) →
  (v : Vec8ℤ) → Vec8Eq (laplacianFullVec8ℤ v) (K8LaplacianVec8ℤ v)
law14G-4-edge-case-forces-K8 C inv edgeWitness v = law14G-1-full-is-K8 v

{-
### Law 14G.5: Non-Edge-Case Coupling Forces The Block-Diagonal Laplacian Form
**Necessity Proof:** By Law 14G.3 the non-edge-case coupling collapses to disjoint union.
Then Law 14G.0 is definitional.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-5-nonedge-case-forces-block (lines 203-207)
**Consequence:** Eliminates all “empty coupling” Laplacian presentations to the unique block form.
-}

law14G-5-nonedge-case-forces-block : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → ¬ (C a0 b0))) →
  (v : Vec8ℤ) → Vec8Eq (laplacianEmptyVec8ℤ v)
                      (laplacianVec4ℤ (left4 v) , laplacianVec4ℤ (right4 v))
law14G-5-nonedge-case-forces-block C inv nonEdgeWitness v = law14G-0-empty-block v

{-
## Canonical Survivor Parameterization

The coupling layer is forced to retain exactly one bit of information: whether the
cross-coupling is empty or full. This is represented as a two-constructor datatype.

### Law 14G.6: The Survivor Coupling Kind Has Exactly Two Cases
**Necessity Proof:** The only iso-invariant cross-couplings surviving Chapter 14F are
`CrossEmpty` and `CrossFull`; any intermediate predicate is eliminated by Laws 14F.0–14F.1.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-6-survivor-cases (lines 226-228)
**Consequence:** Eliminates any remaining degrees of freedom in selecting a coupling.
-}

data CouplingSurvivor : Set where
  survivor-empty : CouplingSurvivor
  survivor-full  : CouplingSurvivor

law14G-6-survivor-cases : (k : CouplingSurvivor) → (k ≡ survivor-empty) ⊎ (k ≡ survivor-full)
law14G-6-survivor-cases survivor-empty = inj₁ refl
law14G-6-survivor-cases survivor-full  = inj₂ refl

survivorCoupling : CouplingSurvivor → Coupling
survivorCoupling survivor-empty = CrossEmpty
survivorCoupling survivor-full  = CrossFull

laplacianSurvivorVec8ℤ : CouplingSurvivor → Vec8ℤ → Vec8ℤ
laplacianSurvivorVec8ℤ survivor-empty = laplacianEmptyVec8ℤ
laplacianSurvivorVec8ℤ survivor-full  = laplacianFullVec8ℤ

{-
### Law 14G.7: The Empty Survivor Forces Block-Diagonal Laplacian
**Necessity Proof:** `laplacianSurvivorVec8ℤ survivor-empty` is definitional `laplacianEmptyVec8ℤ`,
and Law 14G.0 fixes its unique block form.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-7-survivor-empty-block (lines 246-249)
**Consequence:** Eliminates any alternate operator form for the empty survivor.
-}

law14G-7-survivor-empty-block : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v)
        (laplacianVec4ℤ (left4 v) , laplacianVec4ℤ (right4 v))
law14G-7-survivor-empty-block v = law14G-0-empty-block v

{-
### Law 14G.8: The Full Survivor Forces The K₈ Laplacian Form
**Necessity Proof:** `laplacianSurvivorVec8ℤ survivor-full` is definitional `laplacianFullVec8ℤ`,
and Law 14G.1 forces collapse to the K₈ operator form.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-8-survivor-full-K8 (lines 259-261)
**Consequence:** Eliminates any alternate operator form for the full survivor.
-}

law14G-8-survivor-full-K8 : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v)
law14G-8-survivor-full-K8 v = law14G-1-full-is-K8 v

{-
## K₈ Operator Algebra (Forced)

This section derives the operator identities forced by the K₈-form already fixed in Law 14G.1.
No additional structure is introduced; all equalities are pointwise equalities in `Vec8Eq`.

### Law 14G.9: `J₈ ∘ J₈ = 8 · J₈`
**Necessity Proof:** `J8Vec8ℤ v` is definitional constant with value `sum8ℤ v`. Applying `J` again forces summing
an 8-constant vector, which collapses to `eightTimesℤ (sum8ℤ v)`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-9-JJ-eightJ (lines 291-293)
**Consequence:** Eliminates freedom in the global-sum operator on 8 vertices.
-}

constVec8ℤ : ℤ → Vec8ℤ
constVec8ℤ x = constVec4ℤ x , constVec4ℤ x

zeroVec8ℤ : Vec8ℤ
zeroVec8ℤ = constVec8ℤ 0ℤ

eightVec8ℤ : Vec8ℤ → Vec8ℤ
eightVec8ℤ v = eightVec4ℤ (left4 v) , eightVec4ℤ (right4 v)

sum8-const : (x : ℤ) → sum8ℤ (constVec8ℤ x) ≡ eightTimesℤ x
sum8-const x = refl

sum8-J8 : (v : Vec8ℤ) → sum8ℤ (J8Vec8ℤ v) ≡ eightTimesℤ (sum8ℤ v)
sum8-J8 v = refl

law14G-9-JJ-eightJ : (v : Vec8ℤ) →
  Vec8Eq (J8Vec8ℤ (J8Vec8ℤ v)) (eightVec8ℤ (J8Vec8ℤ v))
law14G-9-JJ-eightJ v = (λ _ → sum8-J8 v) , (λ _ → sum8-J8 v)

{-
### Law 14G.10: `L₈ = 8·I − J₈`
**Necessity Proof:** This is definitional from `K8LaplacianVec8ℤ` and `J8Vec8ℤ`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-10-L-eight-minus-J (lines 302-304)
**Consequence:** Eliminates representational freedom in the K₈ Laplacian operator.
-}

law14G-10-L-eight-minus-J : (v : Vec8ℤ) →
  Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v +Vec8ℤ negVec8ℤ (J8Vec8ℤ v))
law14G-10-L-eight-minus-J v = (λ _ → refl) , (λ _ → refl)

{-
### Law 14G.11: `8·v = L₈ v + J₈ v`
**Necessity Proof:** Pointwise, `(8·vᵢ − Σ₈ v) + Σ₈ v` collapses by `+ℤ-inv-left` and `+ℤ-zero-right`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-11-eight-decomposes (lines 313-330)
**Consequence:** Eliminates the last additive degree of freedom: `L` and `J` form a forced decomposition.
-}

law14G-11-eight-decomposes : (v : Vec8ℤ) →
  Vec8Eq (K8LaplacianVec8ℤ v +Vec8ℤ J8Vec8ℤ v) (eightVec8ℤ v)
law14G-11-eight-decomposes v =
  let s = sum8ℤ v in
  ( λ i →
      trans
        (+ℤ-assoc (eightTimesℤ (left4 v i)) (negℤ s) s)
        (trans
          (cong (λ t → eightTimesℤ (left4 v i) +ℤ t) (+ℤ-inv-left s))
          (+ℤ-zero-right (eightTimesℤ (left4 v i))))
  ) ,
  ( λ i →
      trans
        (+ℤ-assoc (eightTimesℤ (right4 v i)) (negℤ s) s)
        (trans
          (cong (λ t → eightTimesℤ (right4 v i) +ℤ t) (+ℤ-inv-left s))
          (+ℤ-zero-right (eightTimesℤ (right4 v i))))
  )

{-
### Law 14G.12: Global Sum Of The K₈ Laplacian Is Forced To Be Zero
**Necessity Proof:** Summing `8·vᵢ − Σ₈ v` over 8 vertices forces `8·Σ₈ v − 8·Σ₈ v`, which collapses by `+ℤ-inv-right`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-12-sumL8-0 (lines 389-458)
**Consequence:** Forces `J₈ (L₈ v) = 0` and eliminates any leftover drift term.
-}

eightTimes-+ℤ : (x y : ℤ) → eightTimesℤ (x +ℤ y) ≡ eightTimesℤ x +ℤ eightTimesℤ y
eightTimes-+ℤ x y =
  let fx = fourTimesℤ x in
  let fy = fourTimesℤ y in
  trans
    (cong (λ t → t +ℤ t) (fourTimes-+ℤ x y))
    (trans
      (+ℤ-assoc fx fy (fx +ℤ fy))
      (trans
        (cong (λ t → fx +ℤ t) (swapHeadℤ fy fx fy))
        (trans
          (sym (+ℤ-assoc fx fx (fy +ℤ fy)))
          refl)))

eightTimes-neg : (x : ℤ) → eightTimesℤ (negℤ x) ≡ negℤ (eightTimesℤ x)
eightTimes-neg x =
  trans
    (cong (λ t → t +ℤ t) (sym (neg-fourTimesℤ x)))
    (trans
      (sym (neg-+ℤ (fourTimesℤ x) (fourTimesℤ x)))
      refl)

sumFin4-eightTimes : (v : Vec4ℤ) →
  sumFin4ℤ (λ i → eightTimesℤ (v i)) ≡ eightTimesℤ (sumFin4ℤ v)
sumFin4-eightTimes v =
  let vt : Vec4ℤ
      vt i = fourTimesℤ (v i)
  in
  trans
    (sumFin4-+Vec4ℤ vt vt)
    (trans
      (cong (λ t → t +ℤ t) (sumFin4-fourTimes v))
      refl)

sum8-eightVec8 : (v : Vec8ℤ) → sum8ℤ (eightVec8ℤ v) ≡ eightTimesℤ (sum8ℤ v)
sum8-eightVec8 v =
  let sL = sumFin4ℤ (left4 v) in
  let sR = sumFin4ℤ (right4 v) in
  trans
    (cong
      (λ t → t +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
      (sumFin4-eightTimes (left4 v)))
    (trans
      (cong
        (λ t → eightTimesℤ sL +ℤ t)
        (sumFin4-eightTimes (right4 v)))
      (trans
        (sym (eightTimes-+ℤ sL sR))
        refl))

law14G-12-sumL8-0 : (v : Vec8ℤ) → sum8ℤ (K8LaplacianVec8ℤ v) ≡ 0ℤ
law14G-12-sumL8-0 v =
  let
    s  = sum8ℤ v
    sL = sumFin4ℤ (left4 v)
    sR = sumFin4ℤ (right4 v)

    leftPart  = λ i → eightTimesℤ (left4 v i) +ℤ negℤ s
    rightPart = λ i → eightTimesℤ (right4 v i) +ℤ negℤ s

    stepL : sumFin4ℤ leftPart ≡ sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)
    stepL = sumFin4-addConst (λ i → eightTimesℤ (left4 v i)) (negℤ s)

    stepR : sumFin4ℤ rightPart ≡ sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)
    stepR = sumFin4-addConst (λ i → eightTimesℤ (right4 v i)) (negℤ s)

    step₁ : sum8ℤ (K8LaplacianVec8ℤ v) ≡
            (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
            (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s))
    step₁ =
      trans
        (cong (λ t → t +ℤ sumFin4ℤ rightPart) stepL)
        (cong (λ t → (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ t) stepR)

    step₂ : (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
            (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)) ≡
            (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) +ℤ
            (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s))
    step₂ =
      trans
        (+ℤ-assoc (sumFin4ℤ (λ i → eightTimesℤ (left4 v i))) (fourTimesℤ (negℤ s))
                 (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)))
        (trans
          (cong (λ t → sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ t)
                (swapHeadℤ (fourTimesℤ (negℤ s)) (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
                           (fourTimesℤ (negℤ s))))
          (sym (+ℤ-assoc (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)))
                         (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
                         (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)))))

    step₃ : sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) ≡ eightTimesℤ sL
    step₃ = sumFin4-eightTimes (left4 v)

    step₄ : sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) ≡ eightTimesℤ sR
    step₄ = sumFin4-eightTimes (right4 v)

    step₅ : (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) ≡
            eightTimesℤ s
    step₅ =
      trans
        (cong (λ t → t +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) step₃)
        (trans
          (cong (λ t → eightTimesℤ sL +ℤ t) step₄)
          (sym (eightTimes-+ℤ sL sR)))

    step₆ : (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)) ≡ negℤ (eightTimesℤ s)
    step₆ =
      trans
        (cong (λ t → t +ℤ t) (sym (neg-fourTimesℤ s)))
        (sym (neg-+ℤ (fourTimesℤ s) (fourTimesℤ s)))
  in
  trans
    step₁
    (trans
      step₂
      (trans
        (cong (λ t → t +ℤ (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s))) step₅)
        (trans
          (cong (λ t → eightTimesℤ s +ℤ t) step₆)
          (+ℤ-inv-right (eightTimesℤ s)))))

{-
### Law 14G.13: `J₈ (L₈ v) = 0`
**Necessity Proof:** `J8Vec8ℤ (K8LaplacianVec8ℤ v)` is constant with value `sum8ℤ (K8LaplacianVec8ℤ v)`, which is
forced to be `0` by Law 14G.12.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-13-JL-zero (lines 468-471)
**Consequence:** Forces the image of `L₈` into the sum-zero subspace.
-}

law14G-13-JL-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (K8LaplacianVec8ℤ v)) zeroVec8ℤ
law14G-13-JL-zero v =
  let sum0 = law14G-12-sumL8-0 v in
  (λ _ → sum0) , (λ _ → sum0)

{-
### Law 14G.14: `L₈ (J₈ v) = 0`
**Necessity Proof:** Pointwise, `L₈ (J₈ v) = 8·Σ − Σ(J₈ v)`. By `sum8-J8`, the two terms coincide and cancel.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-14-LJ-zero (lines 480-493)
**Consequence:** Eliminates mixed operator freedom: `L` and `J` annihilate each other.
-}

law14G-14-LJ-zero : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (J8Vec8ℤ v)) zeroVec8ℤ
law14G-14-LJ-zero v =
  let s = sum8ℤ v in
  let sj = sum8-J8 v in
  ( λ _ →
      trans
        (cong (λ t → eightTimesℤ s +ℤ negℤ t) sj)
        (+ℤ-inv-right (eightTimesℤ s))
  ) ,
  ( λ _ →
      trans
        (cong (λ t → eightTimesℤ s +ℤ negℤ t) sj)
        (+ℤ-inv-right (eightTimesℤ s))
  )

{-
### Law 14G.15: `L₈ ∘ L₈ = 8 · L₈`
**Necessity Proof:** Pointwise, `L₈ (L₈ v) = 8·(L₈ v) − Σ(L₈ v)`. The sum term vanishes by Law 14G.12.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-15-LL-eightL (lines 502-514)
**Consequence:** Eliminates remaining operator algebra freedom on K₈.
-}

law14G-15-LL-eightL : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
law14G-15-LL-eightL v =
  let sum0 = law14G-12-sumL8-0 v in
  ( λ i →
      trans
        (cong (λ t → eightTimesℤ (left4 (K8LaplacianVec8ℤ v) i) +ℤ negℤ t) sum0)
        (+ℤ-zero-right (eightTimesℤ (left4 (K8LaplacianVec8ℤ v) i)))
  ) ,
  ( λ i →
      trans
        (cong (λ t → eightTimesℤ (right4 (K8LaplacianVec8ℤ v) i) +ℤ negℤ t) sum0)
        (+ℤ-zero-right (eightTimesℤ (right4 (K8LaplacianVec8ℤ v) i)))
  )

{-
## K₈ Spectral Corollaries (Forced)

This section ports the K₄ “sum-zero ⇔ eigenvalue n” and “constants are 0-eigenvectors” consequences to the forced K₈ form.

### Law 14G.16: Sum-Zero Vectors Are Forced 8-Eigenvectors
**Necessity Proof:** Pointwise, `L₈ v = 8·vᵢ - Σ₈ v`. If `Σ₈ v = 0`, the second term vanishes by `+ℤ-zero-right`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-16-sum0-eigen8 (lines 527-538)
**Consequence:** Eliminates spectral freedom: sum-zero forces eigenvalue 8.
-}

law14G-16-sum0-eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v)
law14G-16-sum0-eigen8 v sum0 =
  ( λ i →
      trans
        (cong (λ s → eightTimesℤ (left4 v i) +ℤ negℤ s) sum0)
        (+ℤ-zero-right (eightTimesℤ (left4 v i)))
  ) ,
  ( λ i →
      trans
        (cong (λ s → eightTimesℤ (right4 v i) +ℤ negℤ s) sum0)
        (+ℤ-zero-right (eightTimesℤ (right4 v i)))
  )

{-
### Law 14G.17: Pointwise 8-Eigenvectors Force Sum-Zero
**Necessity Proof:** Evaluating the eigen-equation at one index forces cancellation of the `8·vᵢ` term,
leaving `negℤ (Σ₈ v) = 0`, hence `Σ₈ v = 0` by `negℤ-zero→zero`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-17-eigen8→sum0 (lines 548-555)
**Consequence:** Eliminates the remaining direction: pointwise eigenvalue 8 forces the sum-zero predicate.
-}

law14G-17-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-17-eigen8→sum0 v eigen8 =
  let a = eightTimesℤ (left4 v g0) in
  let s = sum8ℤ v in
  let eq₀ : a +ℤ negℤ s ≡ a
      eq₀ = fst eigen8 g0
  in
  negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)

{-
### Law 14G.18: Sum-Zero Vectors Are Exactly The Pointwise 8-Eigenspace
**Necessity Proof:** One direction is Law 14G.16. The converse is Law 14G.17.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-18-sum0→eigen8 (lines 565-566)
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-18-eigen8→sum0 (lines 568-569)
**Consequence:** Eliminates freedom in the spectral predicate: sum-zero and pointwise 8-eigen coincide.
-}

law14G-18-sum0→eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v)
law14G-18-sum0→eigen8 = law14G-16-sum0-eigen8

law14G-18-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-18-eigen8→sum0 = law14G-17-eigen8→sum0

{-
### Law 14G.19: Constant Vectors Are Forced 0-Eigenvectors
**Necessity Proof:** For `v = constVec8ℤ x`, `Σ₈ v` is forced to be `8·x`, so `L₈ (const x) = 8·x - 8·x`,
which collapses by `+ℤ-inv-right`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-19-const-eigen0 (lines 579-590)
**Consequence:** Eliminates the 0-eigenspace degree of freedom: constants are forced into the kernel.
-}

law14G-19-const-eigen0 : (x : ℤ) → Vec8Eq (K8LaplacianVec8ℤ (constVec8ℤ x)) zeroVec8ℤ
law14G-19-const-eigen0 x =
  ( λ _ →
      trans
        (cong (λ s → eightTimesℤ x +ℤ negℤ s) (sum8-const x))
        (+ℤ-inv-right (eightTimesℤ x))
  ) ,
  ( λ _ →
      trans
        (cong (λ s → eightTimesℤ x +ℤ negℤ s) (sum8-const x))
        (+ℤ-inv-right (eightTimesℤ x))
  )

{-
### Law 14G.20: Kernel Condition As Pointwise Constraint `L₈ v = 0 ⇔ 8·v = J₈ v`
**Necessity Proof:** Pointwise, `L₈ v i = 8·vᵢ - Σ₈ v`. If this vanishes, adding `Σ₈ v` forces cancellation
of `(-Σ₈ v) + Σ₈ v` by `+ℤ-inv-left`, yielding `8·vᵢ = Σ₈ v`. Conversely, substituting `8·vᵢ = Σ₈ v` yields
`Σ₈ v - Σ₈ v`, eliminated by `+ℤ-inv-right`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-20-L0→eightEqJ (lines 602-636)
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-20-eightEqJ→L0 (lines 638-650)
**Consequence:** Eliminates freedom in kernel/image predicates for K₈ without importing function extensionality.
-}

law14G-20-L0→eightEqJ : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) zeroVec8ℤ → Vec8Eq (eightVec8ℤ v) (J8Vec8ℤ v)
law14G-20-L0→eightEqJ v L0 =
  let s = sum8ℤ v in
  ( λ i →
      let a = eightTimesℤ (left4 v i) in
      let eq₀ : a +ℤ negℤ s ≡ 0ℤ
          eq₀ = fst L0 i
      in
      let step₁ : (a +ℤ negℤ s) +ℤ s ≡ 0ℤ +ℤ s
          step₁ = cong (λ t → t +ℤ s) eq₀
          step₂ : a +ℤ (negℤ s +ℤ s) ≡ 0ℤ +ℤ s
          step₂ = trans (sym (+ℤ-assoc a (negℤ s) s)) step₁
          step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ s
          step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left s))) step₂
      in
      trans
        (trans (sym (+ℤ-zero-right a)) step₃)
        (+ℤ-zero-left s)
  ) ,
  ( λ i →
      let a = eightTimesℤ (right4 v i) in
      let eq₀ : a +ℤ negℤ s ≡ 0ℤ
          eq₀ = snd L0 i
      in
      let step₁ : (a +ℤ negℤ s) +ℤ s ≡ 0ℤ +ℤ s
          step₁ = cong (λ t → t +ℤ s) eq₀
          step₂ : a +ℤ (negℤ s +ℤ s) ≡ 0ℤ +ℤ s
          step₂ = trans (sym (+ℤ-assoc a (negℤ s) s)) step₁
          step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ s
          step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left s))) step₂
      in
      trans
        (trans (sym (+ℤ-zero-right a)) step₃)
        (+ℤ-zero-left s)
  )

law14G-20-eightEqJ→L0 : (v : Vec8ℤ) → Vec8Eq (eightVec8ℤ v) (J8Vec8ℤ v) → Vec8Eq (K8LaplacianVec8ℤ v) zeroVec8ℤ
law14G-20-eightEqJ→L0 v eightEqJ =
  let s = sum8ℤ v in
  ( λ i →
      trans
        (cong (λ t → t +ℤ negℤ s) (fst eightEqJ i))
        (+ℤ-inv-right s)
  ) ,
  ( λ i →
      trans
        (cong (λ t → t +ℤ negℤ s) (snd eightEqJ i))
        (+ℤ-inv-right s)
  )

{-
### Law 14G.21: Image Vectors Are Forced 8-Eigenvectors
**Necessity Proof:** Any image vector has the form `w = L₈ v`. Then `L₈ w = L₈ (L₈ v)`, which is forced to equal
`8·(L₈ v) = 8·w` by Law 14G.15.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-21-image⊆eigen8 (lines 660-661)
**Consequence:** Eliminates false “image = all sum-zero” freedom over ℤ: the image satisfies the eigen-constraint.
-}

law14G-21-image⊆eigen8 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
law14G-21-image⊆eigen8 = law14G-15-LL-eightL

{-
### Law 14G.22: Sum-Zero Vectors Become Image Vectors After Forced 8-Scaling
**Necessity Proof:** If `Σ₈ w = 0`, then Law 14G.16 forces `L₈ w = 8·w`. Therefore `8·w` is in the image, witnessed
by choosing the preimage `v = w`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-22-sum0→eightInImage (lines 671-672)
**Consequence:** Eliminates the remaining arithmetic freedom: image-membership is forced only up to the 8-scaling.
-}

law14G-22-sum0→eightInImage : (w : Vec8ℤ) → sum8ℤ w ≡ 0ℤ → Σ Vec8ℤ (λ v → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ w))
law14G-22-sum0→eightInImage w sum0 = w , law14G-16-sum0-eigen8 w sum0

{-
## Transport Lemmas (Forced)

This section supplies the minimal congruence witnesses needed to transport scalar statements (`sum8ℤ`) and vector statements (`Vec8Eq`).
-}

Vec8Eq-refl : (v : Vec8ℤ) → Vec8Eq v v
Vec8Eq-refl v = (λ _ → refl) , (λ _ → refl)

Vec8Eq-sym : {u v : Vec8ℤ} → Vec8Eq u v → Vec8Eq v u
Vec8Eq-sym eq =
  (λ i → sym (fst eq i)) ,
  (λ i → sym (snd eq i))

Vec8Eq-trans : {u v w : Vec8ℤ} → Vec8Eq u v → Vec8Eq v w → Vec8Eq u w
Vec8Eq-trans eq₁ eq₂ =
  (λ i → trans (fst eq₁ i) (fst eq₂ i)) ,
  (λ i → trans (snd eq₁ i) (snd eq₂ i))

sumFin4-cong : (f g : Vec4ℤ) → Vec4Eq f g → sumFin4ℤ f ≡ sumFin4ℤ g
sumFin4-cong f g eq =
  trans
    (cong (λ a → sum4ℤ a (f g1) (f g2) (f g3)) (eq g0))
    (trans
      (cong (λ b → sum4ℤ (g g0) b (f g2) (f g3)) (eq g1))
      (trans
        (cong (λ c → sum4ℤ (g g0) (g g1) c (f g3)) (eq g2))
        (cong (λ d → sum4ℤ (g g0) (g g1) (g g2) d) (eq g3))))

sum8-cong : (u v : Vec8ℤ) → Vec8Eq u v → sum8ℤ u ≡ sum8ℤ v
sum8-cong u v eq =
  cong (λ t → t +ℤ sumFin4ℤ (right4 u)) (sumFin4-cong (left4 u) (left4 v) (fst eq))
  ▸ λ pL →
  trans pL
    (cong (λ t → sumFin4ℤ (left4 v) +ℤ t) (sumFin4-cong (right4 u) (right4 v) (snd eq)))
  where
    infixl 1 _▸_
    _▸_ : {A B : Set} → A → (A → B) → B
    x ▸ k = k x

eightVec8-cong : (u v : Vec8ℤ) → Vec8Eq u v → Vec8Eq (eightVec8ℤ u) (eightVec8ℤ v)
eightVec8-cong u v eq =
  (λ i → cong eightTimesℤ (fst eq i)) ,
  (λ i → cong eightTimesℤ (snd eq i))

K8Laplacian-cong : (u v : Vec8ℤ) → Vec8Eq u v → Vec8Eq (K8LaplacianVec8ℤ u) (K8LaplacianVec8ℤ v)
K8Laplacian-cong u v eq =
  let sEq : sum8ℤ u ≡ sum8ℤ v
      sEq = sum8-cong u v eq
      nsEq : negℤ (sum8ℤ u) ≡ negℤ (sum8ℤ v)
      nsEq = cong negℤ sEq
  in
  ( λ i →
      let aEq : eightTimesℤ (left4 u i) ≡ eightTimesℤ (left4 v i)
          aEq = cong eightTimesℤ (fst eq i)
      in
      trans
        (cong (λ t → t +ℤ negℤ (sum8ℤ u)) aEq)
        (cong (λ t → eightTimesℤ (left4 v i) +ℤ t) nsEq)
  ) ,
  ( λ i →
      let aEq : eightTimesℤ (right4 u i) ≡ eightTimesℤ (right4 v i)
          aEq = cong eightTimesℤ (snd eq i)
      in
      trans
        (cong (λ t → t +ℤ negℤ (sum8ℤ u)) aEq)
        (cong (λ t → eightTimesℤ (right4 v i) +ℤ t) nsEq)
  )

{-
## Full Survivor: Forced Spectral Consequences

This section transports the K₈ spectral laws to the full coupling survivor via the forced identification in Law 14G.8.

### Law 14G.23: Global Sum Of The Full-Survivor Laplacian Is Forced To Be Zero
**Necessity Proof:** Law 14G.8 forces `laplacianSurvivorVec8ℤ survivor-full v = L₈ v` as `Vec8Eq`. By congruence of `sum8ℤ`,
the scalar sums coincide. Law 14G.12 forces the K₈ sum to be `0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-23-sumL-survivor-full-0 (lines 755-759)
**Consequence:** Eliminates drift freedom for the full survivor without re-expanding the coupled definition.
-}

law14G-23-sumL-survivor-full-0 : (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ
law14G-23-sumL-survivor-full-0 v =
  trans
    (sum8-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) (law14G-8-survivor-full-K8 v))
    (law14G-12-sumL8-0 v)

{-
### Law 14G.24: `J₈ (L_survivor-full v) = 0`
**Necessity Proof:** `J8Vec8ℤ w` is constant with value `sum8ℤ w`. Law 14G.23 forces `sum8ℤ (L_survivor-full v) = 0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-24-JL-survivor-full-zero (lines 768-771)
**Consequence:** Forces the full survivor image into the sum-zero subspace.
-}

law14G-24-JL-survivor-full-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ
law14G-24-JL-survivor-full-zero v =
  let sum0 = law14G-23-sumL-survivor-full-0 v in
  (λ _ → sum0) , (λ _ → sum0)

{-
### Law 14G.25: For The Full Survivor, Sum-Zero Vectors Are Forced 8-Eigenvectors
**Necessity Proof:** Law 14G.8 forces `L_survivor-full v = L₈ v` in `Vec8Eq`. Law 14G.16 forces `L₈ v = 8·v` under `sum8ℤ v = 0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-25-survivor-full-sum0→eigen8 (lines 780-784)
**Consequence:** Eliminates spectral freedom for the full survivor.
-}

law14G-25-survivor-full-sum0→eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)
law14G-25-survivor-full-sum0→eigen8 v sum0 =
  Vec8Eq-trans
    (law14G-8-survivor-full-K8 v)
    (law14G-16-sum0-eigen8 v sum0)

{-
### Law 14G.26: For The Full Survivor, Pointwise 8-Eigenvectors Force Sum-Zero
**Necessity Proof:** If `L_survivor-full v = 8·v`, then substituting the forced identification `L_survivor-full v = L₈ v` yields
`L₈ v = 8·v`, and Law 14G.17 forces `sum8ℤ v = 0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-26-survivor-full-eigen8→sum0 (lines 794-799)
**Consequence:** Eliminates the converse direction for the full survivor.
-}

law14G-26-survivor-full-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-26-survivor-full-eigen8→sum0 v eigen8 =
  law14G-17-eigen8→sum0 v
    (Vec8Eq-trans
      (Vec8Eq-sym (law14G-8-survivor-full-K8 v))
      eigen8)

{-
## Empty Survivor: Forced Block Spectral Consequences

The empty survivor is forced to be block-diagonal (Law 14G.7), so its consequences are forced by the K₄ laws on each block.

### Law 14G.27: Global Sum Of The Empty-Survivor Laplacian Is Forced To Be Zero
**Necessity Proof:** `sum8ℤ (L_empty v)` splits into `sumFin4ℤ (L₄ left) + sumFin4ℤ (L₄ right)`. Each term is forced to be `0`
by Law 14E.28.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-27-sumL-survivor-empty-0 (lines 813-819)
**Consequence:** Eliminates drift freedom for the empty survivor.
-}

law14G-27-sumL-survivor-empty-0 : (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ
law14G-27-sumL-survivor-empty-0 v =
  trans
    (cong (λ t → t +ℤ sumFin4ℤ (laplacianVec4ℤ (right4 v))) (law14E-28-sumLaplacian0 (left4 v)))
    (trans
      (cong (λ t → 0ℤ +ℤ t) (law14E-28-sumLaplacian0 (right4 v)))
      (+ℤ-zero-left 0ℤ))

{-
### Law 14G.28: `J₈ (L_survivor-empty v) = 0`
**Necessity Proof:** `J8Vec8ℤ w` is constant with value `sum8ℤ w`. Law 14G.27 forces that sum to be `0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-28-JL-survivor-empty-zero (lines 828-831)
**Consequence:** Forces the empty survivor image into the sum-zero subspace.
-}

law14G-28-JL-survivor-empty-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ
law14G-28-JL-survivor-empty-zero v =
  let sum0 = law14G-27-sumL-survivor-empty-0 v in
  (λ _ → sum0) , (λ _ → sum0)

{-
### Law 14G.29: Blockwise Sum-Zero Forces Pointwise 4-Eigen For The Empty Survivor
**Necessity Proof:** On each block, `sumFin4ℤ x = 0` forces `L₄ x = 4·x` by Law 14E.11. Packing both blocks yields `Vec8Eq`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-29-survivor-empty-sum0→eigen4 (lines 840-844)
**Consequence:** Eliminates the spectral predicate for the empty survivor: both block sums must vanish to force eigenvalue 4.
-}

law14G-29-survivor-empty-sum0→eigen4 : (v : Vec8ℤ) → sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)
law14G-29-survivor-empty-sum0→eigen4 v sum0L sum0R =
  ( λ i → law14E-11-sum0-eigen4 (left4 v) i sum0L ) ,
  ( λ i → law14E-11-sum0-eigen4 (right4 v) i sum0R )

{-
### Law 14G.30: Pointwise 4-Eigen For The Empty Survivor Forces Blockwise Sum-Zero
**Necessity Proof:** If `L_empty v = 4·v`, then each block satisfies the K₄ eigen equation, and Law 14E.19 forces
the block sum to be `0`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-30-survivor-empty-eigen4→sum0 (lines 854-858)
**Consequence:** Eliminates the converse direction without importing extensionality.
-}

law14G-30-survivor-empty-eigen4→sum0 : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) →
  (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ)
law14G-30-survivor-empty-eigen4→sum0 v eigen4 =
  law14E-19-eigen4→sum0 (left4 v) (fst eigen4) ,
  law14E-19-eigen4→sum0 (right4 v) (snd eigen4)

{-
### Law 14G.31: Split Constants Are Forced 0-Eigenvectors Of The Empty Survivor
**Necessity Proof:** Each block is a constant vector, hence a 0-eigenvector by Law 14E.13.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-31-splitConst-eigen0-empty (lines 870-873)
**Consequence:** Forces the kernel of the empty survivor to contain both independent constant blocks.
-}

constVec8Splitℤ : ℤ → ℤ → Vec8ℤ
constVec8Splitℤ x y = constVec4ℤ x , constVec4ℤ y

law14G-31-splitConst-eigen0-empty : (x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
law14G-31-splitConst-eigen0-empty x y =
  ( λ i → law14E-13-const-eigen0 x i ) ,
  ( λ i → law14E-13-const-eigen0 y i )

{-
### Law 14G.32: Image Vectors Of The Empty Survivor Are Forced Blockwise 4-Eigenvectors
**Necessity Proof:** On each block, `L₄ (L₄ v) = 4·(L₄ v)` is forced by Law 14E.29.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-32-imageEmpty⊆eigen4 (lines 882-887)
**Consequence:** Eliminates any remaining operator freedom for the empty survivor image.
-}

law14G-32-imageEmpty⊆eigen4 : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
        (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v))
law14G-32-imageEmpty⊆eigen4 v =
  ( λ i → law14E-29-LL-fourL (left4 v) i ) ,
  ( λ i → law14E-29-LL-fourL (right4 v) i )

{-
### Law 14G.33: Blockwise Sum-Zero Vectors Become Image Vectors After Forced 4-Scaling
**Necessity Proof:** If both block sums are `0`, Law 14G.29 forces `L_empty v = 4·v`, hence `4·v` is in the image with
preimage `v`.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-33-sum0→fourInImage-empty (lines 897-899)
**Consequence:** Eliminates arithmetic freedom for the empty survivor image up to the forced scalar `4`.
-}

law14G-33-sum0→fourInImage-empty : (v : Vec8ℤ) → sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ →
  Σ Vec8ℤ (λ w → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty w) (fourVec8ℤ v))
law14G-33-sum0→fourInImage-empty v sum0L sum0R = v , law14G-29-survivor-empty-sum0→eigen4 v sum0L sum0R

{-
## Survivor Spectral Packages (Forced)

This section bundles the already-forced consequences into two compact “packages” for later reuse.

### Law 14G.34: Full Survivor Image Vectors Are Forced 8-Eigenvectors
**Necessity Proof:** Reduce `L_full` to `L₈` via Law 14G.8 and use congruence of `K8LaplacianVec8ℤ` and `eightVec8ℤ`.
Then apply Law 14G.15.
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-34-survivor-full-image⊆eigen8 (lines 913-933)
**Consequence:** Eliminates the remaining operator-algebra freedom for the full survivor image.
-}

law14G-34-survivor-full-image⊆eigen8 : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
        (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
law14G-34-survivor-full-image⊆eigen8 v =
  let eqV : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v)
      eqV = law14G-8-survivor-full-K8 v
      eqLL : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
                   (K8LaplacianVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
      eqLL = law14G-8-survivor-full-K8 (laplacianSurvivorVec8ℤ survivor-full v)
      step₁ : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
                     (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v))
      step₁ =
        Vec8Eq-trans
          eqLL
          (K8Laplacian-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) eqV)
      step₂ : Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
      step₂ = law14G-15-LL-eightL v
      step₃ : Vec8Eq (eightVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
      step₃ = Vec8Eq-sym (eightVec8-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) eqV)
  in
  Vec8Eq-trans step₁ (Vec8Eq-trans step₂ step₃)

{-
### Law 14G.35: Full Survivor Spectral Package (Drift / JL / Sum0⇔Eigen8 / Image⊆Eigen8)
**Necessity Proof:** Each component is already forced (Laws 14G.23–14G.26 and Law 14G.34).
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-35-survivor-full-spectral-package (lines 942-953)
**Consequence:** Eliminates future proof boilerplate: the full survivor’s forced spectral behavior is available as a single witness.
-}

law14G-35-survivor-full-spectral-package : (v : Vec8ℤ) →
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ) ×
  ((sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ)) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
         (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)))
law14G-35-survivor-full-spectral-package v =
  law14G-23-sumL-survivor-full-0 v ,
  (law14G-24-JL-survivor-full-zero v ,
   ((law14G-25-survivor-full-sum0→eigen8 v , law14G-26-survivor-full-eigen8→sum0 v) ,
    law14G-34-survivor-full-image⊆eigen8 v))

{-
### Law 14G.36: Empty Survivor Spectral Package (Drift / JL / BlockSum0⇔Eigen4 / SplitConstKer / Image⊆Eigen4)
**Necessity Proof:** Each component is already forced (Laws 14G.27–14G.33).
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-36-survivor-empty-spectral-package (lines 962-975)
**Consequence:** Eliminates future proof boilerplate for the block-diagonal survivor.
-}

law14G-36-survivor-empty-spectral-package : (v : Vec8ℤ) →
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ) ×
  ((sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) → (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ))) ×
  ((x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
         (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)))
law14G-36-survivor-empty-spectral-package v =
  law14G-27-sumL-survivor-empty-0 v ,
  (law14G-28-JL-survivor-empty-zero v ,
   ((law14G-29-survivor-empty-sum0→eigen4 v , law14G-30-survivor-empty-eigen4→sum0 v) ,
    (law14G-31-splitConst-eigen0-empty ,
     law14G-32-imageEmpty⊆eigen4 v)))

{-
### Law 14G.37: Survivor Spectral Package By Forced Case Split
**Necessity Proof:** `CouplingSurvivor` has exactly the two forced cases (Law 14G.6). In each case the corresponding
package is already forced (Laws 14G.35 and 14G.36).
  **Formal Reference:** K4CoupledLaplacian.agda.law14G-37-survivor-spectral-package-byCases (lines 1002-1003)
**Consequence:** Eliminates downstream branching overhead: later chapters consume a single survivor-indexed package.
-}

SurvivorSpectralPackage : CouplingSurvivor → Vec8ℤ → Set
SurvivorSpectralPackage survivor-full v =
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ) ×
  ((sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ)) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
         (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)))
SurvivorSpectralPackage survivor-empty v =
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ) ×
  ((sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) → (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ))) ×
  ((x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
         (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)))

law14G-37-survivor-spectral-package-byCases : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSpectralPackage k v
law14G-37-survivor-spectral-package-byCases k v with law14G-6-survivor-cases k
... | inj₁ refl = law14G-36-survivor-empty-spectral-package v
... | inj₂ refl = law14G-35-survivor-full-spectral-package v

-- Helper projections: downstream chapters consume `SurvivorSpectralPackage` without re-associating products.

survivorPkg-sumL0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → sum8ℤ (laplacianSurvivorVec8ℤ k v) ≡ 0ℤ
survivorPkg-sumL0 {survivor-full} pkg = fst pkg
survivorPkg-sumL0 {survivor-empty} pkg = fst pkg

survivorPkg-JL0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ k v)) zeroVec8ℤ
survivorPkg-JL0 {survivor-full} pkg = fst (snd pkg)
survivorPkg-JL0 {survivor-empty} pkg = fst (snd pkg)

SurvivorSum0 : CouplingSurvivor → Vec8ℤ → Set
SurvivorSum0 survivor-full v = sum8ℤ v ≡ 0ℤ
SurvivorSum0 survivor-empty v = (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ)

SurvivorEigen : (k : CouplingSurvivor) → Vec8ℤ → Set
SurvivorEigen survivor-full v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)
SurvivorEigen survivor-empty v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)

survivorPkg-sum0→eigen : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorSum0 k v → SurvivorEigen k v
survivorPkg-sum0→eigen {survivor-full} (_ , (_ , ((sum0→eigen , _) , _))) sum0 = sum0→eigen sum0
survivorPkg-sum0→eigen {survivor-empty} (_ , (_ , ((sum0→eigen , _) , _))) (sum0L , sum0R) = sum0→eigen sum0L sum0R

survivorPkg-eigen→sum0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorEigen k v → SurvivorSum0 k v
survivorPkg-eigen→sum0 {survivor-full} (_ , (_ , ((_ , eigen→sum0) , _))) eigen = eigen→sum0 eigen
survivorPkg-eigen→sum0 {survivor-empty} (_ , (_ , ((_ , eigen→sum0) , _))) eigen = eigen→sum0 eigen

SurvivorImageEigen : (k : CouplingSurvivor) → Vec8ℤ → Set
SurvivorImageEigen survivor-full v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
        (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
SurvivorImageEigen survivor-empty v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
        (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v))

survivorPkg-image⊆eigen : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorImageEigen k v
survivorPkg-image⊆eigen {survivor-full} (_ , (_ , (_ , image⊆))) = image⊆
survivorPkg-image⊆eigen {survivor-empty} (_ , (_ , (_ , (_ , image⊆)))) = image⊆

survivorPkg-splitConstKernel : {v : Vec8ℤ} →
  SurvivorSpectralPackage survivor-empty v → (x y : ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
survivorPkg-splitConstKernel (_ , (_ , (_ , (splitConstKer , _)))) = splitConstKer

-- Convenience layer: callers provide only `(k v)`; the package witness is forced by Law 14G.37.

survivorPkg : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSpectralPackage k v
survivorPkg = law14G-37-survivor-spectral-package-byCases

survivor-sumL0 : (k : CouplingSurvivor) (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ k v) ≡ 0ℤ
survivor-sumL0 k v = survivorPkg-sumL0 (survivorPkg k v)

survivor-JL0 : (k : CouplingSurvivor) (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ k v)) zeroVec8ℤ
survivor-JL0 k v = survivorPkg-JL0 (survivorPkg k v)

survivor-sum0→eigen : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSum0 k v → SurvivorEigen k v
survivor-sum0→eigen k v sum0 = survivorPkg-sum0→eigen (survivorPkg k v) sum0

survivor-eigen→sum0 : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorEigen k v → SurvivorSum0 k v
survivor-eigen→sum0 k v eigen = survivorPkg-eigen→sum0 (survivorPkg k v) eigen

survivor-image⊆eigen : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorImageEigen k v
survivor-image⊆eigen k v = survivorPkg-image⊆eigen (survivorPkg k v)

survivor-splitConstKernel : (v : Vec8ℤ) (x y : ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
survivor-splitConstKernel v x y = survivorPkg-splitConstKernel {v} (survivorPkg survivor-empty v) x y
