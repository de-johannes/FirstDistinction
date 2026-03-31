{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.Integers where

open import FirstDistinction

{-
CHAPTER 14C: Integers As Forced Normal Forms

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 8 (ℕ), Chapter 14A (finite sums interfaces)
AGDA MODULES: Disciplines.Math.Integers
DEGREES OF FREEDOM ELIMINATED: ambiguous representation of signed counting
-}

infixl 6 _+ℕ_

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

{-
`ℤ` is forced here as the unique normal form of a difference of naturals:
all pairs (a , b) collapse by eliminative cancellation of a common successor.
The cancellation process terminates structurally.
-}

data ℤ : Set where
  0ℤ    : ℤ
  +suc_ : ℕ → ℤ
  -suc_ : ℕ → ℤ

normalizeℤ : ℕ → ℕ → ℤ
normalizeℤ zero zero = 0ℤ
normalizeℤ (suc a) zero = +suc a
normalizeℤ zero (suc b) = -suc b
normalizeℤ (suc a) (suc b) = normalizeℤ a b

record Pairℕ : Set where
  constructor ⟪_,_⟫
  field
    pos : ℕ
    neg : ℕ

open Pairℕ public

toPairℤ : ℤ → Pairℕ
toPairℤ 0ℤ = ⟪ zero , zero ⟫
toPairℤ (+suc n) = ⟪ suc n , zero ⟫
toPairℤ (-suc n) = ⟪ zero , suc n ⟫

fromPairℤ : Pairℕ → ℤ
fromPairℤ p = normalizeℤ (pos p) (neg p)

infixl 6 _+ℤ_

_+ℤ_ : ℤ → ℤ → ℤ
x +ℤ y =
  let px = toPairℤ x in
  let py = toPairℤ y in
  normalizeℤ (pos px +ℕ pos py) (neg px +ℕ neg py)

negℤ : ℤ → ℤ
negℤ z =
  let p = toPairℤ z in
  normalizeℤ (neg p) (pos p)
