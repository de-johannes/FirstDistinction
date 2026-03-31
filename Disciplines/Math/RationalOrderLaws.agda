{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalOrderLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws using (≤ℤ-refl)
open import Disciplines.Math.NatPlus
open import Disciplines.Math.Rationals

{-
CHAPTER 14V: Forced Laws Of Rational Order (Base)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14R (≤ℤ, <ℤ), Chapter 14S (≤ℚ, <ℚ), Chapter 14Q (ℕ⁺)
AGDA MODULES: Disciplines.Math.RationalOrderLaws
DEGREES OF FREEDOM ELIMINATED: non-positive denominators and missing order bridges
-}

{-
### Law 14V.0: Strict Order Forces Non-Strict Order

**Necessity Proof:** `<` is defined as `≤` paired with the negation of the reverse inequality.
**Formal Reference:** RationalOrderLaws.agda.ltQ_to_leQ (lines 41-42)
**Consequence:** Eliminates the freedom to treat strict order as independent of ≤.
-}

<ℤ→≤ℤ : {x y : ℤ} → x <ℤ y → x ≤ℤ y
<ℤ→≤ℤ p = fst p

<ℚ→≤ℚ : {x y : ℚ} → x <ℚ y → x ≤ℚ y
<ℚ→≤ℚ p = fst p

ltZ_to_leZ : {x y : ℤ} → x <ℤ y → x ≤ℤ y
ltZ_to_leZ {x} {y} p = <ℤ→≤ℤ {x} {y} p

ltQ_to_leQ : {x y : ℚ} → x <ℚ y → x ≤ℚ y
ltQ_to_leQ {x} {y} p = <ℚ→≤ℚ {x} {y} p

-- Setoid equality forces both ≤ directions.

≃ℚ→≤ℚˡ : {p q : ℚ} → p ≃ℚ q → p ≤ℚ q
≃ℚ→≤ℚˡ {a / b} {c / d} eq =
  ≤ℤ-resp-≡ʳ eq (≤ℤ-refl (a *ℤ ⁺toℤ d))

≃ℚ→≤ℚʳ : {p q : ℚ} → p ≃ℚ q → q ≤ℚ p
≃ℚ→≤ℚʳ {a / b} {c / d} eq =
  ≤ℤ-resp-≡ʳ (sym eq) (≤ℤ-refl (c *ℤ ⁺toℤ b))

{-
### Law 14V.1: Positive Naturals Are Strictly Positive Integers

**Necessity Proof:** `ℕ⁺` is forced as successor normal form, hence `⁺toℤ d` is always `+suc k`.
The order definition forces `0ℤ ≤ℤ (+suc k)` and forces `(+suc k) ≤ℤ 0ℤ` to be ⊥.
**Formal Reference:** RationalOrderLaws.agda.den-posℤ (lines 63-65)
**Consequence:** Eliminates the freedom to treat denominators as non-positive.
-}

den-posℤ : (d : ℕ⁺) → 0ℤ <ℤ ⁺toℤ d
den-posℤ (mkℕ⁺ k) =
  tt , (λ p → p)

-- A concrete instance used frequently as an ε-witness.

0ℤ<oneℤ : 0ℤ <ℤ oneℤ
0ℤ<oneℤ =
  tt , (λ p → p)

0ℚ<1ℚ : 0ℚ <ℚ 1ℚ
0ℚ<1ℚ =
  0ℤ<oneℤ

-- Extract the forced positivity of the numerator from 0 < a/b.

0ℚ<→0ℤ<num : (ε : ℚ) → 0ℚ <ℚ ε → 0ℤ <ℤ num ε
0ℚ<→0ℤ<num (a / b) p =
  let step₁ : 0ℤ <ℤ (a *ℤ ⁺toℤ one⁺)
      step₁ = p

      step₂ : 0ℤ <ℤ a
      step₂ = <ℤ-resp-≡ʳ (*ℤ-one-right a) step₁
  in
  step₂
