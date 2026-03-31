{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.FiniteSumsZ where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers

{-
CHAPTER 14D: Finite Sums Over ℤ (No Parameters)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14A (Fin3/Fin4), Chapter 14C (ℤ operations)
AGDA MODULES: Disciplines.Math.FiniteSumsZ
DEGREES OF FREEDOM ELIMINATED: parameterized summation operators
-}

sum3ℤ : ℤ → ℤ → ℤ → ℤ
sum3ℤ a b c = a +ℤ (b +ℤ c)

sumFin3ℤ : (Fin3 → ℤ) → ℤ
sumFin3ℤ f = sum3ℤ (f f0) (f f1) (f f2)

sum4ℤ : ℤ → ℤ → ℤ → ℤ → ℤ
sum4ℤ a b c d = a +ℤ (b +ℤ (c +ℤ d))

sumFin4ℤ : (Fin4 → ℤ) → ℤ
sumFin4ℤ f = sum4ℤ (f g0) (f g1) (f g2) (f g3)

threeTimesℤ : ℤ → ℤ
threeTimesℤ x = x +ℤ (x +ℤ x)

fourTimesℤ : ℤ → ℤ
fourTimesℤ x = sum4ℤ x x x x
