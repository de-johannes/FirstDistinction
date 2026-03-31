{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K12IteratedOperatorAlgebra where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.FiniteSumsZ
open import Disciplines.Math.Endomorphisms.Iteration
open import Disciplines.Graph.K4MatrixLaplacian
open import Disciplines.Graph.K4TripleCoupledLaplacian

{-
CHAPTER 14K: K₁₂ Iteration And Operator Algebra (Classification Without Interpretation)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14H (K₁₂ operator laws), Chapter 14I (operator iteration)
AGDA MODULES: Disciplines.Graph.K12IteratedOperatorAlgebra
DEGREES OF FREEDOM ELIMINATED: ad hoc iteration behaviour beyond forced K₁₂ identities
-}

-- Transport lemmas for the pointwise equality used on vectors.

Vec12Eq-refl : (v : Vec12ℤ) → Vec12Eq v v
Vec12Eq-refl v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

Vec12Eq-sym : {u v : Vec12ℤ} → Vec12Eq u v → Vec12Eq v u
Vec12Eq-sym eq =
  (λ i → sym (fst eq i)) ,
  ((λ i → sym (fst (snd eq) i)) ,
   (λ i → sym (snd (snd eq) i)))

Vec12Eq-trans : {u v w : Vec12ℤ} → Vec12Eq u v → Vec12Eq v w → Vec12Eq u w
Vec12Eq-trans eq₁ eq₂ =
  (λ i → trans (fst eq₁ i) (fst eq₂ i)) ,
  ((λ i → trans (fst (snd eq₁) i) (fst (snd eq₂) i)) ,
   (λ i → trans (snd (snd eq₁) i) (snd (snd eq₂) i)))

sumFin4-cong : (f g : Vec4ℤ) → Vec4Eq f g → sumFin4ℤ f ≡ sumFin4ℤ g
sumFin4-cong f g eq =
  trans
    (cong (λ a → sum4ℤ a (f g1) (f g2) (f g3)) (eq g0))
    (trans
      (cong (λ b → sum4ℤ (g g0) b (f g2) (f g3)) (eq g1))
      (trans
        (cong (λ c → sum4ℤ (g g0) (g g1) c (f g3)) (eq g2))
        (cong (λ d → sum4ℤ (g g0) (g g1) (g g2) d) (eq g3))))

sum12-cong : (u v : Vec12ℤ) → Vec12Eq u v → sum12ℤ u ≡ sum12ℤ v
sum12-cong u v eq =
  trans
    (cong (λ t → t +ℤ (sumFin4ℤ (block₁ u) +ℤ sumFin4ℤ (block₂ u)))
         (sumFin4-cong (block₀ u) (block₀ v) (fst eq)))
    (cong (λ t → sumFin4ℤ (block₀ v) +ℤ t)
      (trans
        (cong (λ t → t +ℤ sumFin4ℤ (block₂ u))
              (sumFin4-cong (block₁ u) (block₁ v) (fst (snd eq))))
        (cong (λ t → sumFin4ℤ (block₁ v) +ℤ t)
              (sumFin4-cong (block₂ u) (block₂ v) (snd (snd eq))))))

-- Scaling endomorphism as an operator on Vec12ℤ.

twelveVec12-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (twelveVec12ℤ u) (twelveVec12ℤ v)
twelveVec12-cong u v eq =
  (λ i → cong twelveTimesℤ (fst eq i)) ,
  ((λ i → cong twelveTimesℤ (fst (snd eq) i)) ,
   (λ i → cong twelveTimesℤ (snd (snd eq) i)))

-- Congruence of the K₁₂ Laplacian under Vec12Eq.

K12Laplacian-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (K12LaplacianVec12ℤ u) (K12LaplacianVec12ℤ v)
K12Laplacian-cong u v eq =
  (λ i →
    let pBlock = cong twelveTimesℤ (fst eq i) in
    let pSum   = cong negℤ (sum12-cong u v eq) in
    trans (cong (λ t → twelveTimesℤ (block₀ u i) +ℤ t) pSum)
          (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)) ,
  ((λ i →
    let pBlock = cong twelveTimesℤ (fst (snd eq) i) in
    let pSum   = cong negℤ (sum12-cong u v eq) in
    trans (cong (λ t → twelveTimesℤ (block₁ u i) +ℤ t) pSum)
          (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)) ,
   (λ i →
    let pBlock = cong twelveTimesℤ (snd (snd eq) i) in
    let pSum   = cong negℤ (sum12-cong u v eq) in
    trans (cong (λ t → twelveTimesℤ (block₂ u i) +ℤ t) pSum)
          (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)))

{-
## Iteration (Forced)

### Law 14K.0: Two-Step Recurrence For L₁₂
**Necessity Proof:** Apply Law 14H.11 to the input `powEndo n L₁₂ v`.
**Formal Reference:** K12IteratedOperatorAlgebra.agda.law14K-0-LL-step (lines 99-102)
**Consequence:** Eliminates freedom in iterated application: every second step forces a 12-scaling.
-}

law14K-0-LL-step : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc (suc n)) K12LaplacianVec12ℤ v)
         (twelveVec12ℤ (powEndo (suc n) K12LaplacianVec12ℤ v))
law14K-0-LL-step n v = law14H-11-LL-twelveL (powEndo n K12LaplacianVec12ℤ v)

{-
### Law 14K.1: Iterated Laplacian Collapses To Iterated 12-Scaling
**Necessity Proof:** Induct on ℕ using Law 14K.0 and the forced congruence of `twelveVec12ℤ`.
**Formal Reference:** K12IteratedOperatorAlgebra.agda.law14K-1-Lpow-scaling (lines 111-121)
**Consequence:** Eliminates all higher-degree freedom: `L₁₂^(suc n)` is forced to be a 12-scaled `L₁₂`.
-}

law14K-1-Lpow-scaling : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc n) K12LaplacianVec12ℤ v)
         (powEndo n twelveVec12ℤ (K12LaplacianVec12ℤ v))
law14K-1-Lpow-scaling zero v = Vec12Eq-refl (K12LaplacianVec12ℤ v)
law14K-1-Lpow-scaling (suc n) v =
  Vec12Eq-trans
    (law14K-0-LL-step n v)
    (twelveVec12-cong
      (powEndo (suc n) K12LaplacianVec12ℤ v)
      (powEndo n twelveVec12ℤ (K12LaplacianVec12ℤ v))
      (law14K-1-Lpow-scaling n v))

{-
### Law 14K.2: Iterated Global-Sum Operator Collapses To Iterated 12-Scaling
**Necessity Proof:** Induct on ℕ using Law 14H.5 and the forced congruence of `twelveVec12ℤ`.
**Formal Reference:** K12IteratedOperatorAlgebra.agda.law14K-2-Jpow-scaling (lines 130-140)
**Consequence:** Eliminates freedom in `J`-iteration: every iterate is a forced 12-scaling of `J`.
-}

law14K-2-Jpow-scaling : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc n) J12Vec12ℤ v)
         (powEndo n twelveVec12ℤ (J12Vec12ℤ v))
law14K-2-Jpow-scaling zero v = Vec12Eq-refl (J12Vec12ℤ v)
law14K-2-Jpow-scaling (suc n) v =
  Vec12Eq-trans
    (law14H-5-JJ-twelveJ (powEndo n J12Vec12ℤ v))
    (twelveVec12-cong
      (powEndo (suc n) J12Vec12ℤ v)
      (powEndo n twelveVec12ℤ (J12Vec12ℤ v))
      (law14K-2-Jpow-scaling n v))
