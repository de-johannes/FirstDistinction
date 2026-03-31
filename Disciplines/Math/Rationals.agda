{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.Rationals where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerAbs
open import Disciplines.Math.NatPlus
open import Disciplines.Math.IntegerOrder

{-
CHAPTER 14S: Rationals As Forced Quotients (No Division)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (ℤ), Chapter 14Q (ℕ⁺), Chapter 14M (*ℤ)
AGDA MODULES: Disciplines.Math.Rationals
DEGREES OF FREEDOM ELIMINATED: division as a primitive; rationals are forced to be cross-multiplication invariants
-}

record ℚ : Set where
  constructor _/_
  field
    num : ℤ
    den : ℕ⁺

open ℚ public

infix 4 _≃ℚ_

_≃ℚ_ : ℚ → ℚ → Set
(a / b) ≃ℚ (c / d) = (a *ℤ ⁺toℤ d) ≡ (c *ℤ ⁺toℤ b)

infixl 6 _+ℚ_ _-ℚ_
infixl 7 _*ℚ_

_+ℚ_ : ℚ → ℚ → ℚ
(a / b) +ℚ (c / d) = ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) / (b *⁺ d)

_*ℚ_ : ℚ → ℚ → ℚ
(a / b) *ℚ (c / d) = (a *ℤ c) / (b *⁺ d)

-ℚ_ : ℚ → ℚ
-ℚ (a / b) = negℤ a / b

_-ℚ_ : ℚ → ℚ → ℚ
p -ℚ q = p +ℚ (-ℚ q)

0ℚ 1ℚ : ℚ
0ℚ = 0ℤ / one⁺
1ℚ = oneℤ / one⁺

infix 4 _≤ℚ_ _<ℚ_

_≤ℚ_ : ℚ → ℚ → Set
(a / b) ≤ℚ (c / d) = (a *ℤ ⁺toℤ d) ≤ℤ (c *ℤ ⁺toℤ b)

_<ℚ_ : ℚ → ℚ → Set
(a / b) <ℚ (c / d) = (a *ℤ ⁺toℤ d) <ℤ (c *ℤ ⁺toℤ b)

-- Canonical distance on rationals: clear denominators, take absolute numerator, keep the forced product denominator.

distℚ : ℚ → ℚ → ℚ
distℚ (a / b) (c / d) = absℤ ((a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)) / (b *⁺ d)
