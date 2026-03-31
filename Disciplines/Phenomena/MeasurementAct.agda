{-# OPTIONS --safe --without-K #-}

module Disciplines.Phenomena.MeasurementAct where

open import FirstDistinction

{-
CHAPTER 15B: Measurement Act (Two-Outcome Witness)

ONTOLOGICAL STATUS: Forced (as a special case of maps between distinctions)
DEPENDENCIES: Laws 7.1–7.3 (map boundary-determination and K₄Map witness)
AGDA MODULES: Disciplines.Phenomena.MeasurementAct
DEGREES OF FREEDOM ELIMINATED: freedom beyond four-case K₄Map behavior
-}

Measurement : Distinction → Set
Measurement d = S d → S Two-distinction

{-
### Law 15B.0: A Measurement Act Is Determined By Boundary Values
**Necessity Proof:** Specialize Law 7.1 to codomain Two-distinction.
**Consequence:** Eliminates degrees of freedom beyond (m ℓ, m r).
-}

law15B-0-measurement-determined :
  (d : Distinction) →
  (m₁ m₂ : Measurement d) →
  m₁ (ℓ d) ≡ m₂ (ℓ d) →
  m₁ (r d) ≡ m₂ (r d) →
  m₁ ≗ m₂
law15B-0-measurement-determined d =
  law7-1-map-determined d Two-distinction

{-
### Law 15B.1: Every Measurement Act Has A K₄ Witness
**Necessity Proof:** Specialize Law 7.2 to codomain Two-distinction.
**Consequence:** Forces a canonical four-case label witness for every measurement act.
-}

law15B-1-measurement-classification-sound :
  (d : Distinction) →
  (m : Measurement d) →
  Σ EndoCase (λ c → K₄Map.interpret d Two-distinction c ≗ m)
law15B-1-measurement-classification-sound d m =
  law7-2-k4map-classification-sound d Two-distinction m

{-
### Law 15B.2: Measurement Witness Is Unique
**Necessity Proof:** Specialize Law 7.3 to codomain Two-distinction.
**Consequence:** Eliminates ambiguity of the K₄ witness for a measurement act.
-}

law15B-2-measurement-classification-unique :
  (d : Distinction) →
  (m : Measurement d) →
  (c₁ c₂ : EndoCase) →
  K₄Map.interpret d Two-distinction c₁ ≗ m →
  K₄Map.interpret d Two-distinction c₂ ≗ m →
  c₁ ≡ c₂
law15B-2-measurement-classification-unique d m c₁ c₂ p q =
  law7-3-k4map-classification-unique d Two-distinction m c₁ c₂ p q
