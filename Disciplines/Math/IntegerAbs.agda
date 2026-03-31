{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerAbs where

open import FirstDistinction
open import Disciplines.Math.Integers

{-
CHAPTER 14Z: Absolute Value On ℤ As Forced Sign-Erasure

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (ℤ)
AGDA MODULES: Disciplines.Math.IntegerAbs
DEGREES OF FREEDOM ELIMINATED: non-canonical magnitude extraction
-}

absℤ : ℤ → ℤ
absℤ 0ℤ = 0ℤ
absℤ (+suc n) = +suc n
absℤ (-suc n) = +suc n
