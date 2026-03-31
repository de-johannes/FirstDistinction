{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerOrderPreorderLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.NatOrderLaws
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerOrder

{-
CHAPTER 14Y: Forced Preorder Laws For ≤ℤ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 8 (≤ on ℕ), Chapter 14R (≤ℤ)
AGDA MODULES: Disciplines.Math.IntegerOrderPreorderLaws
DEGREES OF FREEDOM ELIMINATED: inability to compose inequalities on ℤ
-}

≤ℤ-refl : (x : ℤ) → x ≤ℤ x
≤ℤ-refl 0ℤ = tt
≤ℤ-refl (+suc n) = ≤-refl (suc n)
≤ℤ-refl (-suc n) = ≤-refl (suc n)

≤ℤ-trans : {x y z : ℤ} → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
≤ℤ-trans {0ℤ} {0ℤ} {0ℤ} _ _ = tt
≤ℤ-trans {0ℤ} {0ℤ} {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} {0ℤ} { -suc n } _ ()
≤ℤ-trans {0ℤ} {+suc m} {0ℤ} _ ()
≤ℤ-trans {0ℤ} {+suc m} {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} {+suc m} { -suc n } _ ()
≤ℤ-trans {0ℤ} { -suc m } {0ℤ} _ _ = tt
≤ℤ-trans {0ℤ} { -suc m } {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} { -suc m } { -suc n } () _

≤ℤ-trans {+suc m} {0ℤ} {z} () _
≤ℤ-trans {+suc m} {+suc n} {0ℤ} p ()
≤ℤ-trans {+suc m} {+suc n} {+suc k} p q = ≤-trans p q
≤ℤ-trans {+suc m} {+suc n} { -suc k } _ ()
≤ℤ-trans {+suc m} { -suc n } {z} () _

≤ℤ-trans { -suc m } {0ℤ} {0ℤ} _ _ = tt
≤ℤ-trans { -suc m } {0ℤ} {+suc k} _ _ = tt
≤ℤ-trans { -suc m } {0ℤ} { -suc k } _ ()
≤ℤ-trans { -suc m } {+suc n} {0ℤ} _ ()
≤ℤ-trans { -suc m } {+suc n} {+suc k} _ _ = tt
≤ℤ-trans { -suc m } {+suc n} { -suc k } _ ()
≤ℤ-trans { -suc m } { -suc n } {0ℤ} _ _ = tt
≤ℤ-trans { -suc m } { -suc n } {+suc k} _ _ = tt
≤ℤ-trans { -suc m } { -suc n } { -suc k } p q = ≤-trans q p

-- A strict-order helper used later: x <ℤ y forces x ≤ℤ y.

<ℤ→≤ℤ : {x y : ℤ} → x <ℤ y → x ≤ℤ y
<ℤ→≤ℤ p = fst p

≤ℤ-antisym : {x y : ℤ} → x ≤ℤ y → y ≤ℤ x → x ≡ y
≤ℤ-antisym {0ℤ} {0ℤ} _ _ = refl
≤ℤ-antisym {0ℤ} {+suc n} _ ()
≤ℤ-antisym {0ℤ} { -suc n } () _
≤ℤ-antisym {+suc m} {0ℤ} () _
≤ℤ-antisym {+suc m} {+suc n} p q = cong +suc_ (suc-injective (≤-antisym p q))
≤ℤ-antisym {+suc m} { -suc n } () _
≤ℤ-antisym { -suc m } {0ℤ} _ ()
≤ℤ-antisym { -suc m } {+suc n} _ ()
≤ℤ-antisym { -suc m } { -suc n } p q = cong -suc_ (suc-injective (≤-antisym q p))
