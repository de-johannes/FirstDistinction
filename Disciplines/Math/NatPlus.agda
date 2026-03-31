{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.NatPlus where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerMultiplication

{-
CHAPTER 14Q: Positive Naturals As Forced Successors

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 8 (ℕ), Chapter 14M (*ℕ)
AGDA MODULES: Disciplines.Math.NatPlus
DEGREES OF FREEDOM ELIMINATED: division-by-zero and non-positive denominators in ℚ
-}

{-
### Law 14Q.0: ℕ⁺ Is Forced As “Successor Normal Form”
**Necessity Proof:** A denominator must never be zero. The unique eliminative normal form is “a natural with one forced successor”.
**Formal Reference:** NatPlus.agda.PosNat (lines 30-31)
**Consequence:** Eliminates the freedom to form a zero denominator.
-}

record ℕ⁺ : Set where
  constructor mkℕ⁺
  field
    pred : ℕ

PosNat : Set
PosNat = ℕ⁺

open ℕ⁺ public

⁺toℕ : ℕ⁺ → ℕ
⁺toℕ n = suc (pred n)

one⁺ : ℕ⁺
one⁺ = mkℕ⁺ zero

suc⁺ : ℕ⁺ → ℕ⁺
suc⁺ n = mkℕ⁺ (suc (pred n))

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
mkℕ⁺ a +⁺ mkℕ⁺ b = mkℕ⁺ (a +ℕ suc b)

{-
Multiplication on ℕ⁺ is forced by closure under multiplication and by the invariant
that values are successors.

(suc a) * (suc b) = suc (a*b + a + b)
-}

_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
mkℕ⁺ a *⁺ mkℕ⁺ b = mkℕ⁺ ((a *ℕ suc b) +ℕ b)

⁺toℤ : ℕ⁺ → ℤ
⁺toℤ (mkℕ⁺ k) = +suc k
