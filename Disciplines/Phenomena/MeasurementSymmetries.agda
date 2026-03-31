{-# OPTIONS --safe --without-K #-}

module Disciplines.Phenomena.MeasurementSymmetries where

open import FirstDistinction
open import Disciplines.Phenomena.MeasurementAct

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

{-
CHAPTER 15C: Forced Symmetries Of Measurement Acts

ONTOLOGICAL STATUS: Derived (forced actions from already-forced maps and automorphisms)
DEPENDENCIES:
  - Law 7.2–7.3 (K₄Map witness existence and uniqueness)
  - swapTwo (forced Two symmetry)
  - Distinction-dual (forced nontrivial automorphism alternative)
AGDA MODULES: Disciplines.Phenomena.MeasurementSymmetries
DEGREES OF FREEDOM ELIMINATED: any non-permutation action of these symmetries on K₄ witnesses
-}

-- Outcome-symmetry: swap the Two output.
swapOut : {d : Distinction} → Measurement d → Measurement d
swapOut m x = swapTwo (m x)

-- Input-symmetry: precompose with the forced dual on the domain.
swapIn : (d : Distinction) → Measurement d → Measurement d
swapIn d m x = m (Distinction-dual d x)

swapOut-cong :
  {d : Distinction} {m n : Measurement d} →
  _≗_ {A = S d} {B = S Two-distinction} m n →
  _≗_ {A = S d} {B = S Two-distinction} (swapOut {d = d} m) (swapOut {d = d} n)
swapOut-cong p x = cong swapTwo (p x)

swapIn-cong :
  (d : Distinction) {m n : Measurement d} →
  _≗_ {A = S d} {B = S Two-distinction} m n →
  _≗_ {A = S d} {B = S Two-distinction} (swapIn d m) (swapIn d n)
swapIn-cong d p x = p (Distinction-dual d x)

-- The induced EndoCase permutations are forced by evaluation on the four constructors.

permOut : EndoCase → EndoCase
permOut case-constL = case-constR
permOut case-constR = case-constL
permOut case-id     = case-dual
permOut case-dual   = case-id

permIn : EndoCase → EndoCase
permIn case-constL = case-constL
permIn case-constR = case-constR
permIn case-id     = case-dual
permIn case-dual   = case-id

-- Outcome swap acts on interpreted measurement cases by permOut.
swapOut-interpret :
  (d : Distinction) →
  (c : EndoCase) →
  _≗_ {A = S d} {B = S Two-distinction}
    (swapOut {d = d} (K₄Map.interpret d Two-distinction c))
    (K₄Map.interpret d Two-distinction (permOut c))
swapOut-interpret d case-constL x = refl
swapOut-interpret d case-constR x = refl
swapOut-interpret d case-id x with cover d x
... | inj₁ _ = refl
... | inj₂ _ = refl
swapOut-interpret d case-dual x with cover d x
... | inj₁ _ = refl
... | inj₂ _ = refl

-- Input swap acts on interpreted measurement cases by permIn.
swapIn-interpret :
  (d : Distinction) →
  (c : EndoCase) →
  _≗_ {A = S d} {B = S Two-distinction}
    (swapIn d (K₄Map.interpret d Two-distinction c))
    (K₄Map.interpret d Two-distinction (permIn c))
swapIn-interpret d case-constL x = refl
swapIn-interpret d case-constR x = refl
swapIn-interpret d case-id =
  law7-1-map-determined d Two-distinction
    (swapIn d (K₄Map.interpret d Two-distinction case-id))
    (K₄Map.interpret d Two-distinction case-dual)
    eqℓ
    eqr
  where
    module K = K₄Map d Two-distinction
    open K

    eqℓ : swapIn d (interpret case-id) (ℓ d) ≡ interpret case-dual (ℓ d)
    eqℓ =
      trans
        (cong (interpret case-id) (Distinction-dual-ℓ d))
        (trans
          (LR-r)
          (sym (RL-ℓ)))

    eqr : swapIn d (interpret case-id) (r d) ≡ interpret case-dual (r d)
    eqr =
      trans
        (cong (interpret case-id) (Distinction-dual-r d))
        (trans
          (LR-ℓ)
          (sym (RL-r)))

swapIn-interpret d case-dual =
  law7-1-map-determined d Two-distinction
    (swapIn d (K₄Map.interpret d Two-distinction case-dual))
    (K₄Map.interpret d Two-distinction case-id)
    eqℓ
    eqr
  where
    module K = K₄Map d Two-distinction
    open K

    eqℓ : swapIn d (interpret case-dual) (ℓ d) ≡ interpret case-id (ℓ d)
    eqℓ =
      trans
        (cong (interpret case-dual) (Distinction-dual-ℓ d))
        (trans
          (RL-r)
          (sym (LR-ℓ)))

    eqr : swapIn d (interpret case-dual) (r d) ≡ interpret case-id (r d)
    eqr =
      trans
        (cong (interpret case-dual) (Distinction-dual-r d))
        (trans
          (RL-ℓ)
          (sym (LR-r)))

{-
### Law 15C.0: K₄Map Classification Respects Outcome Swap
**Necessity Proof:** The classifier is unique; therefore any map equality forces the witness permutation.
**Consequence:** Eliminates freedom: swapping outcomes must act as permOut on the K₄ witness.
-}

law15C-0-classify-swapOut :
  (d : Distinction) →
  (m : Measurement d) →
  K₄Map.classify d Two-distinction (swapOut {d = d} m)
  ≡ permOut (K₄Map.classify d Two-distinction m)
law15C-0-classify-swapOut d m =
  sym
    (K.classify-unique
      (swapOut {d = d} m)
      (permOut (K.classify m))
      witness)
  where
    module K = K₄Map d Two-distinction
    open K

    witness : interpret (permOut (classify m)) ≗ swapOut {d = d} m
    witness =
      ≗-trans
        (≗-sym (swapOut-interpret d (classify m)))
          (swapOut-cong {d = d} (classify-sound m))

{-
### Law 15C.1: K₄Map Classification Respects Input Swap
**Necessity Proof:** The classifier is unique; therefore any map equality forces the witness permutation.
**Consequence:** Eliminates freedom: swapping input polarity must act as permIn on the K₄ witness.
-}

law15C-1-classify-swapIn :
  (d : Distinction) →
  (m : Measurement d) →
  K₄Map.classify d Two-distinction (swapIn d m)
  ≡ permIn (K₄Map.classify d Two-distinction m)
law15C-1-classify-swapIn d m =
  sym
    (K.classify-unique
      (swapIn d m)
      (permIn (K.classify m))
      witness)
  where
    module K = K₄Map d Two-distinction
    open K

    witness : interpret (permIn (classify m)) ≗ swapIn d m
    witness =
      ≗-trans
        (≗-sym (swapIn-interpret d (classify m)))
        (swapIn-cong d (classify-sound m))
