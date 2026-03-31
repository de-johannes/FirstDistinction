{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerOrder where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers

{-
CHAPTER 14R: Order On Integers As Forced Sign-Case Classification

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (ℤ normal forms), Chapter 8 (≤ on ℕ)
AGDA MODULES: Disciplines.Math.IntegerOrder
DEGREES OF FREEDOM ELIMINATED: ambiguous comparison of signed values
-}

infix 4 _≤ℤ_ _<ℤ_

_≤ℤ_ : ℤ → ℤ → Set
0ℤ ≤ℤ 0ℤ = ⊤
0ℤ ≤ℤ (+suc n) = ⊤
0ℤ ≤ℤ (-suc n) = ⊥
(+suc m) ≤ℤ 0ℤ = ⊥
(+suc m) ≤ℤ (+suc n) = suc m ≤ suc n
(+suc m) ≤ℤ (-suc n) = ⊥
(-suc m) ≤ℤ 0ℤ = ⊤
(-suc m) ≤ℤ (+suc n) = ⊤
(-suc m) ≤ℤ (-suc n) = suc n ≤ suc m

-- Forced strict order: x < y means x ≤ y and not y ≤ x.
-- This form avoids importing decidable comparisons.

_≰ℤ_ : ℤ → ℤ → Set
x ≰ℤ y = (x ≤ℤ y) → ⊥

_<ℤ_ : ℤ → ℤ → Set
_<ℤ_ x y = (x ≤ℤ y) × (y ≰ℤ x)
