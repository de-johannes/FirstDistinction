{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4MatrixLaplacian where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.FiniteSumsZ
open import Disciplines.Math.IntegersLaws
open import Disciplines.Graph.K4Counting
open import Disciplines.Graph.K4Laplacian

{-
CHAPTER 14E: Laplacian As Finite-Index Operator (Fin4)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14A (Fin3/Fin4), Chapter 14B (Fin4 ↔ EndoCase), Chapter 14 (neighbor triple)
AGDA MODULES: Disciplines.Graph.K4MatrixLaplacian
DEGREES OF FREEDOM ELIMINATED: ad hoc “matrix” layer without canonical indexing
-}

Vec4ℤ : Set
Vec4ℤ = Fin4 → ℤ

Actℤ : Set
Actℤ = ℤ → ℤ

zeroAct : Actℤ
zeroAct _ = 0ℤ

idAct : Actℤ
idAct x = x

negAct : Actℤ
negAct = negℤ

threeAct : Actℤ
threeAct = threeTimesℤ

fourAct : Actℤ
fourAct = fourTimesℤ

data Coeffℤ : Set where
  c0  : Coeffℤ
  c1  : Coeffℤ
  c-1 : Coeffℤ
  c3  : Coeffℤ

coeffAct : Coeffℤ → Actℤ
coeffAct c0 = zeroAct
coeffAct c1 = idAct
coeffAct c-1 = negAct
coeffAct c3 = threeAct

Mat4Coeffℤ : Set
Mat4Coeffℤ = Fin4 → Fin4 → Coeffℤ

liftCoeffMatℤ : Mat4Coeffℤ → (Fin4 → Fin4 → Actℤ)
liftCoeffMatℤ m i j = coeffAct (m i j)

Mat4Actℤ : Set
Mat4Actℤ = Fin4 → Fin4 → Actℤ

others : Fin4 → Fin3 → Fin4
others g0 f0 = g1
others g0 f1 = g2
others g0 f2 = g3
others g1 f0 = g0
others g1 f1 = g2
others g1 f2 = g3
others g2 f0 = g0
others g2 f1 = g1
others g2 f2 = g3
others g3 f0 = g0
others g3 f1 = g1
others g3 f2 = g2

sumFin4Aroundℤ : Fin4 → (Fin4 → ℤ) → ℤ
sumFin4Aroundℤ i f = sum4ℤ (f i) (f (others i f0)) (f (others i f1)) (f (others i f2))

sumOthersℤ : Vec4ℤ → Fin4 → ℤ
sumOthersℤ v i = Disciplines.Math.FiniteSumsZ.sumFin3ℤ (λ k → v (others i k))

laplacianVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianVec4ℤ v i = threeTimesℤ (v i) +ℤ negℤ (sumOthersℤ v i)

applyLaplacianPreActℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyLaplacianPreActℤ m v i =
  m i i (v i) +ℤ
  negℤ (Disciplines.Math.FiniteSumsZ.sumFin3ℤ (λ k → m i (others i k) (v (others i k))))

laplacianPreMatActℤ : Mat4Actℤ
laplacianPreMatActℤ i j with Fin4-decEq i j
... | inj₁ _ = threeAct
... | inj₂ _ = idAct

laplacianMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianMatVec4ℤ = applyLaplacianPreActℤ laplacianPreMatActℤ

vecFromEndo : (EndoCase → ℤ) → Vec4ℤ
vecFromEndo f i = f (vertexAt i)

endoFromVec : Vec4ℤ → (EndoCase → ℤ)
endoFromVec v x = v (vertexIndex x)

{-
## Compatibility With EndoCase Laplacian

### Law 14E.0: EndoCase-Laplacian Factors Through Fin4 Indexing
**Necessity Proof:** `vertexAt` exhausts `EndoCase` by case classification, and `others`
exhausts the three non-self indices by case classification on `Fin4`. Since `Adj` in the
canonical K₄ graph is definitional inequality, the neighbor sum is forced to be the sum
over the three non-self indices.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-0-laplacian-factor (lines 119-124)
**Consequence:** Eliminates representational freedom between “vertex functions” and
“indexed vectors”: the Laplacian is the same operator under the forced iso.
-}

law14E-0-laplacian-factor : (f : EndoCase → ℤ) → (x : EndoCase) →
  laplacianVec4ℤ (vecFromEndo f) (vertexIndex x) ≡ laplacianℤ f x
law14E-0-laplacian-factor f case-constL = refl
law14E-0-laplacian-factor f case-constR = refl
law14E-0-laplacian-factor f case-id = refl
law14E-0-laplacian-factor f case-dual = refl

{-
### Law 14E.1: Laplacian Is The Unique Fin4 Action-Matrix With Diagonal 3 And Off-Diagonal −1
**Necessity Proof:** `Fin4` classifies into exactly four cases, and `Fin4-decEq` forces a
single split into the diagonal and its complement. K₄ adjacency is definitional
inequality, therefore the off-diagonal neighborhood is forced to be exactly the three
indices enumerated by `others`. The Laplacian operator is forced to be “diagonal action”
plus “negated sum over the three off-diagonal indices”.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-1-matrix-agrees (lines 138-143)
**Consequence:** Eliminates freedom in the operator layer: the Laplacian is fixed as a
canonical pre-subtraction action-matrix on `Vec4ℤ`.
-}

law14E-1-matrix-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-1-matrix-agrees v g0 = refl
law14E-1-matrix-agrees v g1 = refl
law14E-1-matrix-agrees v g2 = refl
law14E-1-matrix-agrees v g3 = refl

applyMat4ActDiagOthersℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActDiagOthersℤ m v i =
  m i i (v i) +ℤ
  Disciplines.Math.FiniteSumsZ.sumFin3ℤ (λ k → m i (others i k) (v (others i k)))

applyMat4ActRowSumℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActRowSumℤ m v i = sumFin4Aroundℤ i (λ j → m i j (v j))

applyMat4ActGlobalSumℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActGlobalSumℤ m v i = sumFin4ℤ (λ j → m i j (v j))

applyMat4CoeffGlobalSumℤ : Mat4Coeffℤ → Vec4ℤ → Vec4ℤ
applyMat4CoeffGlobalSumℤ m v i = sumFin4ℤ (λ j → coeffAct (m i j) (v j))

laplacianPostMatActℤ : Mat4Actℤ
laplacianPostMatActℤ i j with Fin4-decEq i j
... | inj₁ _ = threeAct
... | inj₂ _ = negAct

laplacianPostMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianPostMatVec4ℤ = applyMat4ActDiagOthersℤ laplacianPostMatActℤ

laplacianRowSumMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianRowSumMatVec4ℤ = applyMat4ActRowSumℤ laplacianPostMatActℤ

laplacianGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianGlobalMatVec4ℤ = applyMat4ActGlobalSumℤ laplacianPostMatActℤ

laplacianCoeffMatℤ : Mat4Coeffℤ
laplacianCoeffMatℤ i j with Fin4-decEq i j
... | inj₁ _ = c3
... | inj₂ _ = c-1

laplacianCoeffGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianCoeffGlobalMatVec4ℤ = applyMat4CoeffGlobalSumℤ laplacianCoeffMatℤ

{-
### Law 14E.3: Row-Sum Application Is Forced By `others`
**Necessity Proof:** The only possible “sum over all four indices” compatible with the forced split into
the diagonal index and the three off-diagonal indices is the canonical enumeration
`(i , others i f0 , others i f1 , others i f2)`. Therefore the row-sum operator is definitionally
the diagonal term plus the forced three-term off-diagonal sum.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-3-row-sum-unfolds (lines 192-194)
**Consequence:** Eliminates the last presentation freedom in “matrix application”: row-application is fixed
as a canonical ordered four-term sum.
-}

law14E-3-row-sum-unfolds : (m : Mat4Actℤ) → (v : Vec4ℤ) → (i : Fin4) →
  applyMat4ActRowSumℤ m v i ≡ applyMat4ActDiagOthersℤ m v i
law14E-3-row-sum-unfolds m v i = refl

{-
### Law 14E.4: The Canonical Fin4 Row Enumeration Collapses To The Global Fin4 Sum
**Necessity Proof:** `Fin4` classifies into exactly four cases. For each case, `others` is forced and
enumerates the remaining three indices. The only remaining freedom is the order of the four-term sum.
That freedom is eliminated by the forced ℤ permutation lemmas for `sum4ℤ` (built from `+ℤ-assoc` and `+ℤ-comm`).
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-4-sumFin4Around-eq-sumFin4 (lines 205-216)
**Consequence:** Eliminates residual presentation freedom between “row-sum around i” and the canonical global `sumFin4ℤ`.
-}

law14E-4-sumFin4Around-eq-sumFin4 : (f : Fin4 → ℤ) → (i : Fin4) →
  sumFin4Aroundℤ i f ≡ sumFin4ℤ f
law14E-4-sumFin4Around-eq-sumFin4 f g0 = refl
law14E-4-sumFin4Around-eq-sumFin4 f g1 = sum4ℤ-swap01 (f g1) (f g0) (f g2) (f g3)
law14E-4-sumFin4Around-eq-sumFin4 f g2 =
  trans (sum4ℤ-swap01 (f g2) (f g0) (f g1) (f g3))
        (sum4ℤ-swap12 (f g0) (f g2) (f g1) (f g3))
law14E-4-sumFin4Around-eq-sumFin4 f g3 =
  trans
    (trans (sum4ℤ-swap01 (f g3) (f g0) (f g1) (f g2))
           (sum4ℤ-swap12 (f g0) (f g3) (f g1) (f g2)))
    (sum4ℤ-swap23 (f g0) (f g1) (f g3) (f g2))

{-
### Law 14E.2: Laplacian Is The Unique Fin4 Action-Matrix With Diagonal 3 And Off-Diagonal −1 (Negation Inside The Neighbor Sum)
**Necessity Proof:** The neighbor indexing `others` forces a fixed three-term exhaustion of the off-diagonal indices.
The only remaining degree of freedom is whether negation is applied termwise or as a single wrapper over the forced neighbor sum.
This freedom is eliminated by the forced ℤ normal-form lemma `neg-sumFin3ℤ`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-2-matrix-neg-in-agrees (lines 227-240)
**Consequence:** Eliminates the residual “placement of negation” freedom inside the matrix layer.
-}

law14E-2-matrix-neg-in-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianPostMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-2-matrix-neg-in-agrees v g0 =
  cong (λ t → threeTimesℤ (v g0) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g0 k))))
law14E-2-matrix-neg-in-agrees v g1 =
  cong (λ t → threeTimesℤ (v g1) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g1 k))))
law14E-2-matrix-neg-in-agrees v g2 =
  cong (λ t → threeTimesℤ (v g2) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g2 k))))
law14E-2-matrix-neg-in-agrees v g3 =
  cong (λ t → threeTimesℤ (v g3) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g3 k))))

{-
### Law 14E.5: Global Matrix Row-Sum Is Forced
**Necessity Proof:** The action of a matrix-row on a vector is forced to be a finite sum of four terms.
By Law 14E.4, the only freedom in representing that sum ("around i" versus global) is eliminated.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-5-rowSum-eq-globalSum (lines 250-253)
**Consequence:** Eliminates representational freedom between "row-enumerated" and "global" matrix application.
-}

law14E-5-rowSum-eq-globalSum : (m : Mat4Actℤ) → (v : Vec4ℤ) → (i : Fin4) →
  applyMat4ActRowSumℤ m v i ≡ applyMat4ActGlobalSumℤ m v i
law14E-5-rowSum-eq-globalSum m v i =
  law14E-4-sumFin4Around-eq-sumFin4 (λ j → m i j (v j)) i

{-
### Law 14E.6: Laplacian As Global Fin4 Matrix-Row Sum
**Necessity Proof:** By Law 14E.5, the global row-sum presentation is equal to the forced row-enumeration.
By Law 14E.3, the row-enumeration unfolds to the diagonal-plus-offdiagonal presentation.
By Law 14E.2, that presentation is the Laplacian.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-6-global-matrix-agrees (lines 264-269)
**Consequence:** Eliminates the last remaining difference between the Laplacian-operator and a global finite-index matrix action.
-}

law14E-6-global-matrix-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianGlobalMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-6-global-matrix-agrees v i =
  trans (sym (law14E-5-rowSum-eq-globalSum laplacianPostMatActℤ v i))
        (trans (law14E-3-row-sum-unfolds laplacianPostMatActℤ v i)
               (law14E-2-matrix-neg-in-agrees v i))

{-
### Law 14E.7: Coefficient-Matrix Presentation Collapses To Action-Matrix Presentation
**Necessity Proof:** The coefficient set `Coeffℤ` exhausts exactly the four forced actions needed here:
`0`, `1`, `−1` (negation), and `3` (three-times). Therefore lifting a coefficient matrix via `coeffAct`
is forced to coincide with the corresponding action-matrix split by `Fin4-decEq`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-7-coeff-lift-agrees (lines 280-297)
**Consequence:** Eliminates the last "Actℤ is not a ℤ-entry" freedom: the Laplacian matrix is a genuine ℤ-coefficient matrix.
-}

law14E-7-coeff-lift-agrees : (i j : Fin4) →
  liftCoeffMatℤ laplacianCoeffMatℤ i j ≡ laplacianPostMatActℤ i j
law14E-7-coeff-lift-agrees g0 g0 = refl
law14E-7-coeff-lift-agrees g0 g1 = refl
law14E-7-coeff-lift-agrees g0 g2 = refl
law14E-7-coeff-lift-agrees g0 g3 = refl
law14E-7-coeff-lift-agrees g1 g0 = refl
law14E-7-coeff-lift-agrees g1 g1 = refl
law14E-7-coeff-lift-agrees g1 g2 = refl
law14E-7-coeff-lift-agrees g1 g3 = refl
law14E-7-coeff-lift-agrees g2 g0 = refl
law14E-7-coeff-lift-agrees g2 g1 = refl
law14E-7-coeff-lift-agrees g2 g2 = refl
law14E-7-coeff-lift-agrees g2 g3 = refl
law14E-7-coeff-lift-agrees g3 g0 = refl
law14E-7-coeff-lift-agrees g3 g1 = refl
law14E-7-coeff-lift-agrees g3 g2 = refl
law14E-7-coeff-lift-agrees g3 g3 = refl

{-
### Law 14E.8: Laplacian As Global ℤ-Coefficient Matrix Row-Sum
**Necessity Proof:** For each fixed row-index `i : Fin4`, the global sum `sumFin4ℤ` expands to four concrete terms.
In each term, `Fin4-decEq` reduces by case classification, forcing `laplacianCoeffMatℤ` and `laplacianPostMatActℤ`
to act identically (Law 14E.7). Therefore the global coefficient-matrix application is forced to equal the global
action-matrix application.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-8-coeff-global-eq-act-global (lines 309-314)
**Consequence:** Eliminates any remaining separation between "matrix with ℤ entries" and the Laplacian operator layer.
-}

law14E-8-coeff-global-eq-act-global : (v : Vec4ℤ) → (i : Fin4) →
  laplacianCoeffGlobalMatVec4ℤ v i ≡ laplacianGlobalMatVec4ℤ v i
law14E-8-coeff-global-eq-act-global v g0 = refl
law14E-8-coeff-global-eq-act-global v g1 = refl
law14E-8-coeff-global-eq-act-global v g2 = refl
law14E-8-coeff-global-eq-act-global v g3 = refl

{-
### Law 14E.9: Laplacian Is The Unique Global ℤ-Coefficient Matrix Action
**Necessity Proof:** By Law 14E.8, the global coefficient-matrix action equals the global action-matrix action.
By Law 14E.6, the global action-matrix action equals the Laplacian.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-9-coeff-global-agrees (lines 324-328)
**Consequence:** Eliminates the final representational freedom: Laplacian = global ℤ-matrix row-sum.
-}

law14E-9-coeff-global-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianCoeffGlobalMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-9-coeff-global-agrees v i =
  trans (law14E-8-coeff-global-eq-act-global v i)
        (law14E-6-global-matrix-agrees v i)

sumFin4Around-split : (v : Vec4ℤ) → (i : Fin4) →
  sumFin4Aroundℤ i v ≡ v i +ℤ sumOthersℤ v i
sumFin4Around-split v g0 = refl
sumFin4Around-split v g1 = refl
sumFin4Around-split v g2 = refl
sumFin4Around-split v g3 = refl

fourTimes-split : (x : ℤ) → fourTimesℤ x ≡ x +ℤ threeTimesℤ x
fourTimes-split x = refl

{-
### Law 14E.10: Laplacian Equals 4·vᵢ Minus The Global Sum
**Necessity Proof:** The K₄ Laplacian is definitional `3·vᵢ - Σ_{j≠i} vⱼ`. The global sum is forced to split as
`vᵢ + Σ_{j≠i} vⱼ` by the forced enumeration `others`, and the only remaining freedom is cancellation of `vᵢ + (−vᵢ)`.
That cancellation is eliminated by the forced ℤ inverse law `+ℤ-inv-right`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-10-laplacian-four-minus-sumAll (lines 350-385)
**Consequence:** Eliminates residual freedom in the spectral form: the Laplacian is `4I - J` on Fin4 vectors.

-}

law14E-10-laplacian-four-minus-sumAll : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i) +ℤ negℤ (sumFin4ℤ v)
law14E-10-laplacian-four-minus-sumAll v i =
  let x = v i in
  let othersSum = sumOthersℤ v i in
  let around = sumFin4Aroundℤ i v in
  let a = threeTimesℤ x in
  let b = negℤ othersSum in
  let rhsAround = fourTimesℤ x +ℤ negℤ around in

  let rhsAround≡laplacian : rhsAround ≡ laplacianVec4ℤ v i
      rhsAround≡laplacian =
        trans
          (cong (λ t → t +ℤ negℤ around) (fourTimes-split x))
          (trans
            (cong (λ t → (x +ℤ a) +ℤ t) (trans (cong negℤ (sumFin4Around-split v i)) (neg-+ℤ x othersSum)))
            (trans
              (+ℤ-assoc x a (negℤ x +ℤ negℤ othersSum))
              (trans
                (cong (λ t → x +ℤ t) (sym (+ℤ-assoc a (negℤ x) (negℤ othersSum)))
                )
                (trans
                  (cong (λ t → x +ℤ ((t) +ℤ negℤ othersSum)) (+ℤ-comm a (negℤ x)))
                  (trans
                    (cong (λ t → x +ℤ t) (+ℤ-assoc (negℤ x) a (negℤ othersSum)))
                    (trans
                      (sym (+ℤ-assoc x (negℤ x) (a +ℤ negℤ othersSum)))
                      (trans
                        (cong (λ t → t +ℤ (a +ℤ negℤ othersSum)) (+ℤ-inv-right x))
                        (trans
                          (+ℤ-zero-left (a +ℤ negℤ othersSum))
                          refl))))))))
  in
  trans
    (sym rhsAround≡laplacian)
    (cong (λ s → fourTimesℤ x +ℤ negℤ s) (law14E-4-sumFin4Around-eq-sumFin4 v i))

{-
### Law 14E.11: Sum-Zero Vectors Are Forced Eigenvectors With Eigenvalue 4
**Necessity Proof:** Law 14E.10 forces `L v i = 4·vᵢ - Σ v`. If the global sum is `0`, the second term vanishes
by the forced identity law `+ℤ-zero-right`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-11-sum0-eigen4 (lines 396-403)
**Consequence:** Eliminates freedom in the spectrum: every sum-zero vector is a 4-eigenvector.

-}

law14E-11-sum0-eigen4 : (v : Vec4ℤ) → (i : Fin4) → sumFin4ℤ v ≡ 0ℤ →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-11-sum0-eigen4 v i sum0 =
  trans
    (law14E-10-laplacian-four-minus-sumAll v i)
    (trans
      (cong (λ s → fourTimesℤ (v i) +ℤ negℤ s) sum0)
      (+ℤ-zero-right (fourTimesℤ (v i))))

constVec4ℤ : ℤ → Vec4ℤ
constVec4ℤ x _ = x

JVec4ℤ : Vec4ℤ → Vec4ℤ
JVec4ℤ v _ = sumFin4ℤ v

onesCoeffMatℤ : Mat4Coeffℤ
onesCoeffMatℤ _ _ = c1

JCoeffGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
JCoeffGlobalMatVec4ℤ = applyMat4CoeffGlobalSumℤ onesCoeffMatℤ

sumFin4-const : (x : ℤ) → sumFin4ℤ (constVec4ℤ x) ≡ fourTimesℤ x
sumFin4-const x = refl

{-
### Law 14E.12: The All-Ones ℤ-Coefficient Matrix Forces The `J` Operator
**Necessity Proof:** The coefficient `c1` is forced to act as the identity on ℤ. Therefore the global coefficient-matrix
row-sum of the constant-`c1` matrix is definitionally the global sum `sumFin4ℤ v`, independent of the row-index.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-12-ones-matrix-is-J (lines 428-430)
**Consequence:** Eliminates freedom in the “all-ones matrix” layer: `J` is a concrete ℤ-coefficient matrix action.
-}

law14E-12-ones-matrix-is-J : (v : Vec4ℤ) → (i : Fin4) →
  JCoeffGlobalMatVec4ℤ v i ≡ JVec4ℤ v i
law14E-12-ones-matrix-is-J v i = refl

{-
### Law 14E.13: Constant Vectors Are Forced 0-Eigenvectors
**Necessity Proof:** Law 14E.10 forces `L v i = 4·vᵢ - Σ v`. For `v = constVec4ℤ x`, the global sum is forced to be
`4·x` by definitional expansion of `sumFin4ℤ`. Therefore `L (const x) i = 4·x - 4·x`, and the remaining freedom is eliminated
by the forced inverse law `+ℤ-inv-right`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-13-const-eigen0 (lines 441-448)
**Consequence:** Eliminates a spectral degree of freedom: the constant subspace is forced to be the 0-eigenspace of the Laplacian.
-}

law14E-13-const-eigen0 : (x : ℤ) → (i : Fin4) →
  laplacianVec4ℤ (constVec4ℤ x) i ≡ 0ℤ
law14E-13-const-eigen0 x i =
  trans
    (law14E-10-laplacian-four-minus-sumAll (constVec4ℤ x) i)
    (trans
      (cong (λ s → fourTimesℤ x +ℤ negℤ s) (sumFin4-const x))
      (+ℤ-inv-right (fourTimesℤ x)))

J-constant : (v : Vec4ℤ) → (i j : Fin4) → JVec4ℤ v i ≡ JVec4ℤ v j
J-constant v i j = refl

sumFin4-J : (v : Vec4ℤ) → sumFin4ℤ (JVec4ℤ v) ≡ fourTimesℤ (sumFin4ℤ v)
sumFin4-J v = refl

J-is-constVec : (v : Vec4ℤ) → (i : Fin4) → JVec4ℤ v i ≡ constVec4ℤ (sumFin4ℤ v) i
J-is-constVec v i = refl

{-
### Law 14E.17: `J` Scales Constant Vectors By 4
**Necessity Proof:** For `v = constVec4ℤ x`, the global sum `sumFin4ℤ v` is definitionally `fourTimesℤ x`.
Since `JVec4ℤ v i` is definitionally `sumFin4ℤ v`, `J (const x)` is forced to be the constant vector `fourTimesℤ x`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-17-J-const-four (lines 467-469)
**Consequence:** Eliminates freedom in the image of `J`: on constants, `J` is forced to act as multiplication by 4.
-}

law14E-17-J-const-four : (x : ℤ) → (i : Fin4) →
  JVec4ℤ (constVec4ℤ x) i ≡ fourTimesℤ x
law14E-17-J-const-four x i = sumFin4-const x

{-
### Law 14E.18: `J ∘ J = 4 · J` Is Forced
**Necessity Proof:** `JVec4ℤ (JVec4ℤ v) i` is definitionally `sumFin4ℤ (JVec4ℤ v)`, which expands to four copies of
`sumFin4ℤ v`, hence `fourTimesℤ (sumFin4ℤ v)`. But `JVec4ℤ v i` is definitionally `sumFin4ℤ v`, so the right-hand side
`fourTimesℤ (JVec4ℤ v i)` reduces to the same term.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-18-JJ-fourJ (lines 480-483)
**Consequence:** Eliminates freedom in operator algebra: repeated global-summing collapses to a forced scalar action on `J`.
-}

law14E-18-JJ-fourJ : (v : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (JVec4ℤ v) i ≡ fourTimesℤ (JVec4ℤ v i)
law14E-18-JJ-fourJ v i =
  trans (sumFin4-J v) refl

{-
### Law 14E.19: Pointwise 4-Eigenvectors Force Sum-Zero
**Necessity Proof:** By Law 14E.10, `L v g0 = 4·v₀ - Σ v`. If additionally `L v g0 = 4·v₀`, then the only surviving
difference is the constant term `− Σ v`. The freedom to hide that term inside a sum is eliminated by the forced
left-cancellation lemma `+ℤ-cancel-left`, yielding `negℤ (Σ v) = 0`. Finally `negℤ-zero→zero` eliminates the remaining
case freedom, forcing `Σ v = 0`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-19-eigen4→sum0 (lines 495-506)
**Consequence:** Eliminates spectral ambiguity: “eigenvalue 4 at all indices” is forced to imply the sum-zero condition.
-}

law14E-19-eigen4→sum0 : (v : Vec4ℤ) → ((i : Fin4) → laplacianVec4ℤ v i ≡ fourTimesℤ (v i)) →
  sumFin4ℤ v ≡ 0ℤ
law14E-19-eigen4→sum0 v eigen4 =
  let a = fourTimesℤ (v g0) in
  let s = sumFin4ℤ v in
  let eq₀ : a +ℤ negℤ s ≡ a
      eq₀ =
        trans
          (sym (law14E-10-laplacian-four-minus-sumAll v g0))
          (eigen4 g0)
  in
  negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)

{-
### Law 14E.20: Sum-Zero Vectors Are Exactly The Pointwise 4-Eigenspace
**Necessity Proof:** One direction is Law 14E.11. The converse is Law 14E.19.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-20-sum0→eigen4 (lines 516-518)
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-20-eigen4→sum0 (lines 520-522)
**Consequence:** Eliminates freedom in the spectral predicate: “sum-zero” and “pointwise 4-eigen” coincide as forced conditions.
-}

law14E-20-sum0→eigen4 : (v : Vec4ℤ) → sumFin4ℤ v ≡ 0ℤ → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-20-sum0→eigen4 v sum0 i = law14E-11-sum0-eigen4 v i sum0

law14E-20-eigen4→sum0 : (v : Vec4ℤ) → ((i : Fin4) → laplacianVec4ℤ v i ≡ fourTimesℤ (v i)) →
  sumFin4ℤ v ≡ 0ℤ
law14E-20-eigen4→sum0 = law14E-19-eigen4→sum0

{-
### Law 14E.21: Spectral Form As Operator Identity `L = 4I − J`
**Necessity Proof:** Law 14E.10 forces `L v i = 4·vᵢ - Σ v`. By definition, `JVec4ℤ v i` is exactly `Σ v` for any `i`.
Therefore the global-sum term is forced to be `JVec4ℤ v i`, eliminating any remaining representational difference.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-21-L-four-minus-J (lines 532-535)
**Consequence:** Eliminates freedom in the spectral operator form: the Laplacian is `4I − J` on `Vec4ℤ`.
-}

law14E-21-L-four-minus-J : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i) +ℤ negℤ (JVec4ℤ v i)
law14E-21-L-four-minus-J v i =
  trans (law14E-10-laplacian-four-minus-sumAll v i) refl

{-
### Law 14E.22: Kernel Condition As Pointwise Constraint `L v i = 0 ⇔ J v i = 4·vᵢ`
**Necessity Proof:** By Law 14E.21, `L v i` is definitionally the witness of the difference `4·vᵢ - J v i`.
If `L v i = 0`, adding `J v i` forces cancellation of `(-J v i) + J v i` by `+ℤ-inv-left`, yielding `4·vᵢ = J v i`.
Conversely, if `J v i = 4·vᵢ`, then `L v i = 4·vᵢ - 4·vᵢ`, and cancellation is eliminated by `+ℤ-inv-right`.
No function extensionality is imported: the equivalence is pointwise in the index `i`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-22-L0→fourEqJ (lines 549-566)
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-22-fourEqJ→L0 (lines 568-577)
**Consequence:** Eliminates freedom in the “kernel/image” predicates: `L v i = 0` is exactly the forced balancing constraint
between the constant `J`-image and the pointwise value `v i`.
-}

law14E-22-L0→fourEqJ : (v : Vec4ℤ) → (i : Fin4) → laplacianVec4ℤ v i ≡ 0ℤ →
  fourTimesℤ (v i) ≡ JVec4ℤ v i
law14E-22-L0→fourEqJ v i L0 =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  let eq₀ : a +ℤ negℤ j ≡ 0ℤ
      eq₀ = trans (sym (law14E-21-L-four-minus-J v i)) L0
  in
  let step₁ : (a +ℤ negℤ j) +ℤ j ≡ 0ℤ +ℤ j
      step₁ = cong (λ t → t +ℤ j) eq₀
      step₂ : a +ℤ (negℤ j +ℤ j) ≡ 0ℤ +ℤ j
      step₂ = trans (sym (+ℤ-assoc a (negℤ j) j)) step₁
      step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ j
      step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left j))) step₂
  in
  trans
    (sym (+ℤ-zero-right a))
    (trans step₃ (+ℤ-zero-left j))

law14E-22-fourEqJ→L0 : (v : Vec4ℤ) → (i : Fin4) → fourTimesℤ (v i) ≡ JVec4ℤ v i →
  laplacianVec4ℤ v i ≡ 0ℤ
law14E-22-fourEqJ→L0 v i fourEqJ =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  trans
    (law14E-21-L-four-minus-J v i)
    (trans
      (cong (λ t → a +ℤ t) (cong negℤ (sym fourEqJ)))
      (+ℤ-inv-right a))

Vec4Eq : Vec4ℤ → Vec4ℤ → Set
Vec4Eq v w = (i : Fin4) → v i ≡ w i

KernelL : Vec4ℤ → Set
KernelL v = (i : Fin4) → laplacianVec4ℤ v i ≡ 0ℤ

{-
### Law 14E.23: Global Spectral Form Is Forced Pointwise (`Vec4Eq`)
**Necessity Proof:** `Vec4Eq` is the forced replacement for function extensionality: equality of vectors is witnessed
by equalities at each index. Law 14E.21 provides that witness directly.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-23-L-eq-four-minus-J (lines 593-595)
**Consequence:** Eliminates freedom in “global operator identity” statements: they are forced families of pointwise laws.
-}

law14E-23-L-eq-four-minus-J : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ v) (λ i → fourTimesℤ (v i) +ℤ negℤ (JVec4ℤ v i))
law14E-23-L-eq-four-minus-J v i = law14E-21-L-four-minus-J v i

{-
### Law 14E.24: Kernel Condition Forces `4·vᵢ` To Be Index-Constant
**Necessity Proof:** If `L v i = 0` then Law 14E.22 forces `4·vᵢ = J v i`. By Law 14E.14, `J v i = J v j` for all indices.
Therefore `4·vᵢ = 4·vⱼ`. No injectivity of `4·_` is imported; the forced conclusion is exactly this equality.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-24-kernel→fourTimes-constant (lines 605-610)
**Consequence:** Eliminates remaining kernel freedom without division: every kernel vector has forced equal 4-multiples.
-}

law14E-24-kernel→fourTimes-constant : (v : Vec4ℤ) → KernelL v → (i j : Fin4) →
  fourTimesℤ (v i) ≡ fourTimesℤ (v j)
law14E-24-kernel→fourTimes-constant v ker i j =
  let fi = law14E-22-L0→fourEqJ v i (ker i) in
  let fj = law14E-22-L0→fourEqJ v j (ker j) in
  trans fi (trans refl (sym fj))

{-
### Law 14E.25: Global Kernel Condition Is Pointwise `J v i = 4·vᵢ`
**Necessity Proof:** This is Law 14E.22 packaged as a Π-family: for any index, `L v i = 0` is equivalent to `J v i = 4·vᵢ`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-25-kernel→fourEqJ (lines 620-622)
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-25-fourEqJ→kernel (lines 624-625)
**Consequence:** Eliminates freedom in kernel statements: kernel membership is forced to be this explicit pointwise constraint.
-}

law14E-25-kernel→fourEqJ : (v : Vec4ℤ) → KernelL v → (i : Fin4) →
  fourTimesℤ (v i) ≡ JVec4ℤ v i
law14E-25-kernel→fourEqJ v ker i = law14E-22-L0→fourEqJ v i (ker i)

law14E-25-fourEqJ→kernel : (v : Vec4ℤ) → ((i : Fin4) → fourTimesℤ (v i) ≡ JVec4ℤ v i) → KernelL v
law14E-25-fourEqJ→kernel v hyp i = law14E-22-fourEqJ→L0 v i (hyp i)

{-
### Law 14E.26: Kernel Condition Forces `Σ v = 4·vᵢ` For Every Index
**Necessity Proof:** In the kernel, Law 14E.25 forces `4·vᵢ = J v i`. But `J v i` is definitionally `Σ v`. Therefore
the global sum is forced to equal the four-times value at each index.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-26-kernel→sumEqFour (lines 635-642)
**Consequence:** Eliminates remaining degrees of freedom in kernel data: the kernel witness determines `Σ v` as `4·vᵢ`.
-}

law14E-26-kernel→sumEqFour : (v : Vec4ℤ) → KernelL v → (i : Fin4) →
  sumFin4ℤ v ≡ fourTimesℤ (v i)
law14E-26-kernel→sumEqFour v ker i =
  trans
    refl
    (trans
      (sym (law14E-25-kernel→fourEqJ v ker i))
      refl)

{-
### Law 14E.27: Pointwise Constraint `Σ v = 4·vᵢ` Forces Kernel Membership
**Necessity Proof:** The hypothesis `Σ v = 4·vᵢ` is definitionally the same as `J v i = 4·vᵢ`.
By Law 14E.25, that pointwise constraint forces kernel membership.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-27-sumEqFour→kernel (lines 652-654)
**Consequence:** Eliminates freedom in kernel characterization: kernel membership is forced by the single global-sum constraint.
-}

law14E-27-sumEqFour→kernel : (v : Vec4ℤ) → ((i : Fin4) → sumFin4ℤ v ≡ fourTimesℤ (v i)) → KernelL v
law14E-27-sumEqFour→kernel v hyp =
  law14E-25-fourEqJ→kernel v (λ i → sym (trans refl (hyp i)))

{-
### Law 14E.14: `J` Is A Forced Constant Operator
**Necessity Proof:** By definition, `JVec4ℤ v` ignores its index and returns the global sum `sumFin4ℤ v`.
Therefore `JVec4ℤ v i` and `JVec4ℤ v j` reduce to the same term for any indices.
  **Formal Reference:** K4MatrixLaplacian.agda.J-constant (lines 450-451)
**Consequence:** Eliminates index-dependence freedom: `J` has rank ≤ 1 because its output is forced constant.
-}

law14E-14-J-constant : (v : Vec4ℤ) → (i j : Fin4) →
  JVec4ℤ v i ≡ JVec4ℤ v j
law14E-14-J-constant = J-constant

{-
### Law 14E.15: Sum-Zero Is Forced To Be `J v = 0`
**Necessity Proof:** `JVec4ℤ v i` is definitionally `sumFin4ℤ v` for any index `i`. Therefore the equation
`sumFin4ℤ v ≡ 0` is the same statement as `JVec4ℤ v i ≡ 0`. No extensionality is imported: the witness is pointwise.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-15-sum0-to-J0 (lines 677-679)
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-15-J0-to-sum0 (lines 681-683)
**Consequence:** Eliminates freedom in the “sum-zero subspace” predicate: it is exactly the kernel condition for `J`.
-}

law14E-15-sum0-to-J0 : (v : Vec4ℤ) → (i : Fin4) → sumFin4ℤ v ≡ 0ℤ →
  JVec4ℤ v i ≡ 0ℤ
law14E-15-sum0-to-J0 v i sum0 = sum0

law14E-15-J0-to-sum0 : (v : Vec4ℤ) → JVec4ℤ v g0 ≡ 0ℤ →
  sumFin4ℤ v ≡ 0ℤ
law14E-15-J0-to-sum0 v J0 = J0

{-
### Law 14E.16: `L ∘ J = 0` Is Forced
**Necessity Proof:** By Law 14E.10, `L w i = 4·wᵢ - Σ w`. For `w = J v`, each coordinate is the same sum `s = Σ v`,
so `Σ (J v)` is forced to be `4·s` by definitional expansion of `sumFin4ℤ`. Therefore `L (J v) i = 4·s - 4·s`,
and the remaining cancellation freedom is eliminated by `+ℤ-inv-right`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-16-LJ-zero (lines 694-702)
**Consequence:** Eliminates freedom in the operator algebra: the Laplacian annihilates the `J`-image.
-}

law14E-16-LJ-zero : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (JVec4ℤ v) i ≡ 0ℤ
law14E-16-LJ-zero v i =
  let s = sumFin4ℤ v in
  trans
    (law14E-10-laplacian-four-minus-sumAll (JVec4ℤ v) i)
    (trans
      (cong (λ t → fourTimesℤ s +ℤ negℤ t) (sumFin4-J v))
      (+ℤ-inv-right (fourTimesℤ s)))

sumFin4-addConst : (v : Vec4ℤ) → (c : ℤ) →
  sumFin4ℤ (λ i → v i +ℤ c) ≡ sumFin4ℤ v +ℤ fourTimesℤ c
sumFin4-addConst v c =
  let
    a0 = v g0
    a1 = v g1
    a2 = v g2
    a3 = v g3
    r23 = (a2 +ℤ c) +ℤ (a3 +ℤ c)
    r1  = (a1 +ℤ c) +ℤ r23

    step₁ : (a0 +ℤ c) +ℤ r1 ≡ a0 +ℤ (c +ℤ r1)
    step₁ = +ℤ-assoc a0 c r1

    step₂ : r1 ≡ a1 +ℤ (c +ℤ r23)
    step₂ = +ℤ-assoc a1 c r23

    step₃ : c +ℤ r1 ≡ a1 +ℤ (c +ℤ (c +ℤ r23))
    step₃ =
      trans
        (cong (λ t → c +ℤ t) step₂)
        (swapHeadℤ c a1 (c +ℤ r23))

    step₄ : (a0 +ℤ c) +ℤ r1 ≡ a0 +ℤ (a1 +ℤ (c +ℤ (c +ℤ r23)))
    step₄ = trans step₁ (cong (λ t → a0 +ℤ t) step₃)

    step₅a : r23 ≡ a2 +ℤ (c +ℤ (a3 +ℤ c))
    step₅a = +ℤ-assoc a2 c (a3 +ℤ c)

    step₅b : c +ℤ r23 ≡ a2 +ℤ (c +ℤ (c +ℤ (a3 +ℤ c)))
    step₅b =
      trans
        (cong (λ t → c +ℤ t) step₅a)
        (swapHeadℤ c a2 (c +ℤ (a3 +ℤ c)))

    step₅c : c +ℤ (c +ℤ r23) ≡ a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))))
    step₅c =
      trans
        (cong (λ t → c +ℤ t) step₅b)
        (swapHeadℤ c a2 (c +ℤ (c +ℤ (a3 +ℤ c))))

    step₆ : a0 +ℤ (a1 +ℤ (c +ℤ (c +ℤ r23))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))))))
    step₆ = cong (λ t → a0 +ℤ (a1 +ℤ t)) step₅c

    step₇a : c +ℤ (a3 +ℤ c) ≡ a3 +ℤ (c +ℤ c)
    step₇a = swapHeadℤ c a3 c

    step₇b : c +ℤ (c +ℤ (a3 +ℤ c)) ≡ a3 +ℤ (c +ℤ (c +ℤ c))
    step₇b =
      trans
        (cong (λ t → c +ℤ t) step₇a)
        (swapHeadℤ c a3 (c +ℤ c))

    step₇c : c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))) ≡ a3 +ℤ (c +ℤ (c +ℤ (c +ℤ c)))
    step₇c =
      trans
        (cong (λ t → c +ℤ t) step₇b)
        (swapHeadℤ c a3 (c +ℤ (c +ℤ c)))

    step₈ : c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))) ≡ a3 +ℤ fourTimesℤ c
    step₈ = trans step₇c refl

    step₉ : a0 +ℤ (a1 +ℤ (a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c)))))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c)))
    step₉ = cong (λ t → a0 +ℤ (a1 +ℤ (a2 +ℤ t))) step₈

    step₁₀a : a2 +ℤ (a3 +ℤ fourTimesℤ c) ≡ (a2 +ℤ a3) +ℤ fourTimesℤ c
    step₁₀a = sym (+ℤ-assoc a2 a3 (fourTimesℤ c))

    step₁₀b : a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c)) ≡ (a1 +ℤ (a2 +ℤ a3)) +ℤ fourTimesℤ c
    step₁₀b =
      trans
        (cong (λ t → a1 +ℤ t) step₁₀a)
        (sym (+ℤ-assoc a1 (a2 +ℤ a3) (fourTimesℤ c)))

    step₁₀c : a0 +ℤ (a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c))) ≡ (a0 +ℤ (a1 +ℤ (a2 +ℤ a3))) +ℤ fourTimesℤ c
    step₁₀c =
      trans
        (cong (λ t → a0 +ℤ t) step₁₀b)
        (sym (+ℤ-assoc a0 (a1 +ℤ (a2 +ℤ a3)) (fourTimesℤ c)))
  in
  trans
    refl
    (trans
      step₄
      (trans
        step₆
        (trans
          step₉
          (trans
            step₁₀c
            refl))))

fourTimes-+ℤ : (x y : ℤ) → fourTimesℤ (x +ℤ y) ≡ fourTimesℤ x +ℤ fourTimesℤ y
fourTimes-+ℤ x y =
  trans
    (sym (sumFin4-const (x +ℤ y)))
    (trans
      (sumFin4-addConst (constVec4ℤ x) y)
      (trans
        (cong (λ t → t +ℤ fourTimesℤ y) (sumFin4-const x))
        refl))

sumFin4-fourTimes : (v : Vec4ℤ) →
  sumFin4ℤ (λ i → fourTimesℤ (v i)) ≡ fourTimesℤ (sumFin4ℤ v)
sumFin4-fourTimes v =
  let
    a0 = v g0
    a1 = v g1
    a2 = v g2
    a3 = v g3
  in
  sym
    (trans
      refl
      (trans
        (fourTimes-+ℤ a0 (a1 +ℤ (a2 +ℤ a3)))
        (trans
          (cong (λ t → fourTimesℤ a0 +ℤ t) (fourTimes-+ℤ a1 (a2 +ℤ a3)))
          (trans
            (cong (λ t → fourTimesℤ a0 +ℤ (fourTimesℤ a1 +ℤ t)) (fourTimes-+ℤ a2 a3))
            refl))))

{-
### Law 14E.28: Global Sum Of The Laplacian Is Forced To Be Zero
**Necessity Proof:** By Law 14E.10, each coordinate is `4·vᵢ - Σ v`. Summing over `Fin4` forces four copies of the constant
term `−Σ v`, hence `−4·Σ v`. The remaining term is forced to be `4·Σ v` by distributivity of `fourTimesℤ` over `sumFin4ℤ`,
eliminating all freedom by `+ℤ-inv-right`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-28-sumLaplacian0 (lines 835-889)
**Consequence:** Eliminates the final spectral degree of freedom: the image of `L` is forced to lie in the sum-zero subspace.
-}

law14E-28-sumLaplacian0 : (v : Vec4ℤ) →
  sumFin4ℤ (laplacianVec4ℤ v) ≡ 0ℤ
law14E-28-sumLaplacian0 v =
  let
    s = sumFin4ℤ v

    step0 :
      sumFin4ℤ (laplacianVec4ℤ v) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3)
    step0 =
      cong
        (λ t0 → sum4ℤ t0 (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g0)

    step1 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3)
    step1 =
      cong
        (λ t1 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) t1 (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g1)

    step2 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (laplacianVec4ℤ v g3)
    step2 =
      cong
        (λ t2 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) t2 (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g2)

    step3 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (fourTimesℤ (v g3) +ℤ negℤ s)
    step3 =
      cong
        (λ t3 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) t3)
        (law14E-10-laplacian-four-minus-sumAll v g3)

    rewriteSum :
      sumFin4ℤ (laplacianVec4ℤ v) ≡
      sumFin4ℤ (λ i → fourTimesℤ (v i) +ℤ negℤ s)
    rewriteSum =
      trans
        refl
        (trans step0 (trans step1 (trans step2 (trans step3 refl))))
  in
  trans
    rewriteSum
    (trans
      (sumFin4-addConst (λ i → fourTimesℤ (v i)) (negℤ s))
      (trans
        (cong (λ t → t +ℤ fourTimesℤ (negℤ s)) (sumFin4-fourTimes v))
        (trans
          (cong (λ t → fourTimesℤ s +ℤ t) (sym (neg-fourTimesℤ s)))
          (+ℤ-inv-right (fourTimesℤ s)))))

{-
### Law 14E.29: Minimal-Polynomial Consequence `L ∘ L = 4 · L` Is Forced
**Necessity Proof:** Law 14E.28 forces `Σ (L v) = 0`. By Law 14E.11, every sum-zero vector is a pointwise 4-eigenvector.
Applying that law to `L v` forces `L (L v) i = 4·(L v i)` for each index.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-29-LL-fourL (lines 899-902)
**Consequence:** Eliminates operator degrees of freedom: the Laplacian satisfies the forced polynomial `x(x-4)=0` on `Vec4ℤ`.
-}

law14E-29-LL-fourL : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (laplacianVec4ℤ v) i ≡ fourTimesℤ (laplacianVec4ℤ v i)
law14E-29-LL-fourL v i =
  law14E-11-sum0-eigen4 (laplacianVec4ℤ v) i (law14E-28-sumLaplacian0 v)

{-
### Law 14E.30: `J ∘ L = 0` Is Forced
**Necessity Proof:** Law 14E.28 forces `Σ (L v) = 0`. By Law 14E.15, the statement `Σ w = 0` is definitionally the same as
`J w i = 0` for any index. Therefore `J (L v) i = 0` is forced at each index.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-30-JL-zero (lines 912-915)
**Consequence:** Eliminates operator-algebra freedom: `J` annihilates the Laplacian image.
-}

law14E-30-JL-zero : (v : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (laplacianVec4ℤ v) i ≡ 0ℤ
law14E-30-JL-zero v i =
  law14E-15-sum0-to-J0 (laplacianVec4ℤ v) i (law14E-28-sumLaplacian0 v)

{-
### Law 14E.31: Operator Identity `L + J = 4I` Is Forced (Pointwise)
**Necessity Proof:** Law 14E.21 forces `L v i = 4·vᵢ - J v i`. Adding `J v i` eliminates the `(-J v i) + J v i` freedom by
the forced inverse law `+ℤ-inv-left`, leaving exactly `4·vᵢ`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-31-L-plus-J-eq-fourI (lines 925-936)
**Consequence:** Eliminates representation freedom between the “spectral” form `L = 4I − J` and the additive form `L + J = 4I`.
-}

law14E-31-L-plus-J-eq-fourI : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i +ℤ JVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-31-L-plus-J-eq-fourI v i =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  trans
    (cong (λ t → t +ℤ j) (law14E-21-L-four-minus-J v i))
    (trans
      (+ℤ-assoc a (negℤ j) j)
      (trans
        (cong (λ t → a +ℤ t) (+ℤ-inv-left j))
        (+ℤ-zero-right a)))

zeroVec4ℤ : Vec4ℤ
zeroVec4ℤ = constVec4ℤ 0ℤ

{-
### Law 14E.32: Global Operator Identity `Vec4Eq (L v + J v) (4 · v)` Is Forced
**Necessity Proof:** `Vec4Eq` is the forced replacement for extensionality. Law 14E.31 provides the required witness at each index.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-32-LplusJ-eq-fourI-Vec4Eq (lines 948-950)
**Consequence:** Eliminates degrees of freedom in “operator equation” statements: the additive spectral form holds as a forced Π-family.
-}

law14E-32-LplusJ-eq-fourI-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (λ i → laplacianVec4ℤ v i +ℤ JVec4ℤ v i) (λ i → fourTimesℤ (v i))
law14E-32-LplusJ-eq-fourI-Vec4Eq v i = law14E-31-L-plus-J-eq-fourI v i

{-
### Law 14E.33: Vector Form Of `L ∘ J = 0` Is Forced
**Necessity Proof:** Law 14E.16 provides the pointwise witness `L (J v) i = 0`. Packing these witnesses yields `Vec4Eq` to `0`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-33-LJ-zero-Vec4Eq (lines 959-961)
**Consequence:** Eliminates freedom in composing operators: the `J`-image is forced into the kernel of `L`.
-}

law14E-33-LJ-zero-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (JVec4ℤ v)) zeroVec4ℤ
law14E-33-LJ-zero-Vec4Eq v i = law14E-16-LJ-zero v i

{-
### Law 14E.34: Vector Form Of `J ∘ L = 0` Is Forced
**Necessity Proof:** Law 14E.30 provides the pointwise witness `J (L v) i = 0`. Packing these witnesses yields `Vec4Eq` to `0`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-34-JL-zero-Vec4Eq (lines 970-972)
**Consequence:** Eliminates freedom in the image of `L`: every Laplacian output is forced sum-zero.
-}

law14E-34-JL-zero-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (JVec4ℤ (laplacianVec4ℤ v)) zeroVec4ℤ
law14E-34-JL-zero-Vec4Eq v i = law14E-30-JL-zero v i

{-
### Law 14E.35: `L` And `J` Commute As A Forced Zero-Composition
**Necessity Proof:** By Law 14E.16, `L (J v) i = 0`. By Law 14E.30, `J (L v) i = 0`. Therefore both composites are forced
equal pointwise, hence as a `Vec4Eq`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-35-LJ-commute (lines 982-985)
**Consequence:** Eliminates any residual ordering freedom: composing `L` and `J` in either order collapses to the same forced vector.
-}

law14E-35-LJ-commute : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (JVec4ℤ v)) (JVec4ℤ (laplacianVec4ℤ v))
law14E-35-LJ-commute v i =
  trans (law14E-16-LJ-zero v i) (sym (law14E-30-JL-zero v i))

{-
### Law 14E.36: Vector Form Of `L ∘ L = 4 · L` Is Forced
**Necessity Proof:** Law 14E.29 provides the pointwise witness. Packing yields the forced `Vec4Eq`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-36-LL-fourL-Vec4Eq (lines 994-996)
**Consequence:** Eliminates freedom in iterated Laplacian application: repeated application collapses to the forced scalar action.
-}

law14E-36-LL-fourL-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (laplacianVec4ℤ v)) (λ i → fourTimesℤ (laplacianVec4ℤ v i))
law14E-36-LL-fourL-Vec4Eq v i = law14E-29-LL-fourL v i

{-
### Law 14E.37: Vector Form Of `J ∘ J = 4 · J` Is Forced
**Necessity Proof:** Law 14E.18 provides the pointwise witness. Packing yields the forced `Vec4Eq`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-37-JJ-fourJ-Vec4Eq (lines 1005-1007)
**Consequence:** Eliminates freedom in iterated global-sum application: repeated `J` collapses to the forced scalar action.
-}

law14E-37-JJ-fourJ-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (JVec4ℤ (JVec4ℤ v)) (λ i → fourTimesℤ (JVec4ℤ v i))
law14E-37-JJ-fourJ-Vec4Eq v i = law14E-18-JJ-fourJ v i

fourVec4ℤ : Vec4ℤ → Vec4ℤ
fourVec4ℤ v i = fourTimesℤ (v i)

_+Vec4ℤ_ : Vec4ℤ → Vec4ℤ → Vec4ℤ
(v +Vec4ℤ w) i = v i +ℤ w i

{-
### Law 14E.38: The Image Of `L` Is Forced Sum-Zero And Forced 4-Eigen
**Necessity Proof:** Law 14E.28 forces `Σ (L v) = 0`. Law 14E.29 forces `L (L v) = 4 · (L v)` pointwise.
Packing these witnesses yields the forced conjunction.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-38-imageL-sum0-and-eigen4 (lines 1023-1026)
**Consequence:** Eliminates freedom in the “nonzero spectrum” side: every Laplacian output lies in the forced 4-eigenspace and is forced sum-zero.
-}

law14E-38-imageL-sum0-and-eigen4 : (v : Vec4ℤ) →
  (sumFin4ℤ (laplacianVec4ℤ v) ≡ 0ℤ) × ((i : Fin4) → laplacianVec4ℤ (laplacianVec4ℤ v) i ≡ fourTimesℤ (laplacianVec4ℤ v i))
law14E-38-imageL-sum0-and-eigen4 v =
  law14E-28-sumLaplacian0 v , law14E-29-LL-fourL v

{-
### Law 14E.39: The Image Of `J` Is Forced Constant And Forced 0-Eigen Under `L`
**Necessity Proof:** `J` is definitionally constant (Law 14E.14). Law 14E.16 forces `L (J v) = 0` pointwise.
Packing these witnesses yields the forced conjunction.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-39-imageJ-const-and-kernelL (lines 1036-1039)
**Consequence:** Eliminates freedom in the “zero spectrum” side: every `J`-output is constant and lies in the kernel of `L`.
-}

law14E-39-imageJ-const-and-kernelL : (v : Vec4ℤ) →
  (((i j : Fin4) → JVec4ℤ v i ≡ JVec4ℤ v j) × ((i : Fin4) → laplacianVec4ℤ (JVec4ℤ v) i ≡ 0ℤ))
law14E-39-imageJ-const-and-kernelL v =
  law14E-14-J-constant v , law14E-16-LJ-zero v

Decomp4 : Vec4ℤ → Set
Decomp4 v =
  Σ Vec4ℤ (λ u →
    Σ Vec4ℤ (λ w →
      (Vec4Eq (u +Vec4ℤ w) (fourVec4ℤ v)) ×
      (sumFin4ℤ u ≡ 0ℤ) ×
      ((i j : Fin4) → w i ≡ w j)))

{-
### Law 14E.40: Forced Scaled Decomposition `4 · v = (L v) + (J v)` With Canonical Components
**Necessity Proof:** Law 14E.32 forces `L v i + J v i = 4·vᵢ` pointwise, hence `Vec4Eq (L v + J v) (4·v)`.
Law 14E.28 forces `Σ (L v) = 0`. Law 14E.14 forces `J v` constant. Therefore choosing `u = L v` and `w = J v` is a forced witness of `Decomp4 v`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-40-decomp4-canonical (lines 1057-1063)
**Consequence:** Eliminates representational freedom in decomposition claims: the only canonical decomposition available without division is the forced scaled one.
-}

law14E-40-decomp4-canonical : (v : Vec4ℤ) → Decomp4 v
law14E-40-decomp4-canonical v =
  laplacianVec4ℤ v ,
  (JVec4ℤ v ,
    (law14E-32-LplusJ-eq-fourI-Vec4Eq v ,
     (law14E-28-sumLaplacian0 v ,
      law14E-14-J-constant v)))

sumFin3-+ℤ : (f g : Fin3 → ℤ) →
  Disciplines.Math.FiniteSumsZ.sumFin3ℤ (λ k → f k +ℤ g k) ≡
  Disciplines.Math.FiniteSumsZ.sumFin3ℤ f +ℤ Disciplines.Math.FiniteSumsZ.sumFin3ℤ g
sumFin3-+ℤ f g =
  let
    a0 = f f0
    a1 = f f1
    a2 = f f2
    b0 = g f0
    b1 = g f1
    b2 = g f2

    X = a1 +ℤ b1
    Y = a2 +ℤ b2
    R = b0 +ℤ b2

    step₁ : Disciplines.Math.FiniteSumsZ.sumFin3ℤ (λ k → f k +ℤ g k) ≡ a0 +ℤ (b0 +ℤ (X +ℤ Y))
    step₁ = +ℤ-assoc a0 b0 (X +ℤ Y)

    step₂ : a0 +ℤ (b0 +ℤ (X +ℤ Y)) ≡ a0 +ℤ (X +ℤ (b0 +ℤ Y))
    step₂ = cong (λ t → a0 +ℤ t) (swapHeadℤ b0 X Y)

    step₃ : a0 +ℤ (X +ℤ (b0 +ℤ Y)) ≡ a0 +ℤ (X +ℤ (a2 +ℤ R))
    step₃ = cong (λ t → a0 +ℤ (X +ℤ t)) (swapHeadℤ b0 a2 b2)

    step₄ : a0 +ℤ (X +ℤ (a2 +ℤ R)) ≡ a0 +ℤ (a1 +ℤ (b1 +ℤ (a2 +ℤ R)))
    step₄ = cong (λ t → a0 +ℤ t) (+ℤ-assoc a1 b1 (a2 +ℤ R))

    step₅ : a0 +ℤ (a1 +ℤ (b1 +ℤ (a2 +ℤ R))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (b1 +ℤ R)))
    step₅ = cong (λ t → a0 +ℤ (a1 +ℤ t)) (swapHeadℤ b1 a2 R)

    step₆ : a0 +ℤ (a1 +ℤ (a2 +ℤ (b1 +ℤ R))) ≡ a0 +ℤ ((a1 +ℤ a2) +ℤ (b1 +ℤ R))
    step₆ = cong (λ t → a0 +ℤ t) (sym (+ℤ-assoc a1 a2 (b1 +ℤ R)))

    step₇ : a0 +ℤ ((a1 +ℤ a2) +ℤ (b1 +ℤ R)) ≡ a0 +ℤ ((a1 +ℤ a2) +ℤ (b0 +ℤ (b1 +ℤ b2)))
    step₇ = cong (λ t → a0 +ℤ ((a1 +ℤ a2) +ℤ t)) (swapHeadℤ b1 b0 b2)

    step₈ : a0 +ℤ ((a1 +ℤ a2) +ℤ (b0 +ℤ (b1 +ℤ b2))) ≡ (a0 +ℤ (a1 +ℤ a2)) +ℤ (b0 +ℤ (b1 +ℤ b2))
    step₈ = sym (+ℤ-assoc a0 (a1 +ℤ a2) (b0 +ℤ (b1 +ℤ b2)))
  in
  trans
    refl
    (trans step₁
      (trans step₂
        (trans step₃
          (trans step₄
            (trans step₅
              (trans step₆
                (trans step₇
                  (trans step₈ refl))))))))

sumOthers-+Vec4ℤ : (v w : Vec4ℤ) → (i : Fin4) →
  sumOthersℤ (v +Vec4ℤ w) i ≡ sumOthersℤ v i +ℤ sumOthersℤ w i
sumOthers-+Vec4ℤ v w i =
  sumFin3-+ℤ (λ k → v (others i k)) (λ k → w (others i k))

sumFin4-+Vec4ℤ : (v w : Vec4ℤ) →
  sumFin4ℤ (λ i → v i +ℤ w i) ≡ sumFin4ℤ v +ℤ sumFin4ℤ w
sumFin4-+Vec4ℤ v w =
  let
    split0 : (x : Vec4ℤ) → sumFin4ℤ x ≡ x g0 +ℤ sumOthersℤ x g0
    split0 x =
      trans
        (sym (law14E-4-sumFin4Around-eq-sumFin4 x g0))
        (sumFin4Around-split x g0)

    v0 = v g0
    w0 = w g0
    sv = sumOthersℤ v g0
    sw = sumOthersℤ w g0

    step₁ : sumFin4ℤ (v +Vec4ℤ w) ≡ (v0 +ℤ w0) +ℤ sumOthersℤ (v +Vec4ℤ w) g0
    step₁ = trans (split0 (v +Vec4ℤ w)) refl

    step₂ : (v0 +ℤ w0) +ℤ sumOthersℤ (v +Vec4ℤ w) g0 ≡ (v0 +ℤ w0) +ℤ (sv +ℤ sw)
    step₂ = cong (λ t → (v0 +ℤ w0) +ℤ t) (sumOthers-+Vec4ℤ v w g0)

    step₃ : (v0 +ℤ w0) +ℤ (sv +ℤ sw) ≡ (v0 +ℤ sv) +ℤ (w0 +ℤ sw)
    step₃ =
      trans
        (+ℤ-assoc v0 w0 (sv +ℤ sw))
        (trans
          (cong (λ t → v0 +ℤ t) (swapHeadℤ w0 sv sw))
          (sym (+ℤ-assoc v0 sv (w0 +ℤ sw))))
  in
  trans
    (trans refl step₁)
    (trans
      step₂
      (trans
        step₃
        (trans
          (cong (λ t → t +ℤ (w0 +ℤ sw)) (sym (split0 v)))
          (cong (λ t → sumFin4ℤ v +ℤ t) (sym (split0 w))))))

{-
### Law 14E.41: `J` Preserves Pointwise Addition
**Necessity Proof:** `JVec4ℤ` is definitionally `sumFin4ℤ`. Therefore the statement is forced by the concrete 4-term sum
expansion and reassociation of `_+ℤ_`.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-41-J-add (lines 1168-1170)
**Consequence:** Eliminates freedom in the global-sum operator: `J` is forced to be additive.
-}

law14E-41-J-add : (v w : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (v +Vec4ℤ w) i ≡ JVec4ℤ v i +ℤ JVec4ℤ w i
law14E-41-J-add v w i = sumFin4-+Vec4ℤ v w

threeTimes-+ℤ : (x y : ℤ) → threeTimesℤ (x +ℤ y) ≡ threeTimesℤ x +ℤ threeTimesℤ y
threeTimes-+ℤ x y =
  sumFin3-+ℤ (λ _ → x) (λ _ → y)

{-
### Law 14E.42: `L` Preserves Pointwise Addition
**Necessity Proof:** `L v i` is definitionally `3·vᵢ - Σ_{j≠i} vⱼ`. The two summands are forced additive by explicit
expansion of `threeTimesℤ` and `sumFin3ℤ`, and the negation distributes by `neg-+ℤ`. Reassociation eliminates the remaining
parenthesization freedom.
  **Formal Reference:** K4MatrixLaplacian.agda.law14E-42-L-add (lines 1185-1217)
**Consequence:** Eliminates freedom in the Laplacian’s behavior under superposition: `L` is forced additive on `Vec4ℤ`.
-}

law14E-42-L-add : (v w : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (v +Vec4ℤ w) i ≡ laplacianVec4ℤ v i +ℤ laplacianVec4ℤ w i
law14E-42-L-add v w i =
  let
    A = threeTimesℤ (v i)
    B = threeTimesℤ (w i)
    C = negℤ (sumOthersℤ v i)
    D = negℤ (sumOthersℤ w i)

    step₁ : laplacianVec4ℤ (v +Vec4ℤ w) i ≡ (A +ℤ B) +ℤ negℤ (sumOthersℤ (v +Vec4ℤ w) i)
    step₁ = cong (λ t → t +ℤ negℤ (sumOthersℤ (v +Vec4ℤ w) i)) (threeTimes-+ℤ (v i) (w i))

    step₂ : negℤ (sumOthersℤ (v +Vec4ℤ w) i) ≡ C +ℤ D
    step₂ =
      trans
        (cong negℤ (sumOthers-+Vec4ℤ v w i))
        (neg-+ℤ (sumOthersℤ v i) (sumOthersℤ w i))

    step₃ : (A +ℤ B) +ℤ (C +ℤ D) ≡ (A +ℤ C) +ℤ (B +ℤ D)
    step₃ =
      trans
        (+ℤ-assoc A B (C +ℤ D))
        (trans
          (cong (λ t → A +ℤ t) (swapHeadℤ B C D))
          (sym (+ℤ-assoc A C (B +ℤ D))))
  in
  trans
    step₁
    (trans
      (cong (λ t → (A +ℤ B) +ℤ t) step₂)
      (trans
        step₃
        refl))
