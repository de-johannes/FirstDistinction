{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerMultiplication where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws

{-
CHAPTER 14M: Integer Multiplication As Forced Repeated Addition

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (ℤ normal forms), Chapter 14F (additive laws)
AGDA MODULES: Disciplines.Math.IntegerMultiplication
DEGREES OF FREEDOM ELIMINATED: ambiguous “scaling” action on ℤ beyond repeated addition
-}

infixl 7 _*ℕ_

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ n = zero
suc m *ℕ n = n +ℕ (m *ℕ n)

*ℕ-one-right : (n : ℕ) → n *ℕ suc zero ≡ n
*ℕ-one-right zero = refl
*ℕ-one-right (suc n) = cong suc (*ℕ-one-right n)

*ℕ-zero-right : (n : ℕ) → n *ℕ zero ≡ zero
*ℕ-zero-right zero = refl
*ℕ-zero-right (suc n) = *ℕ-zero-right n

*ℕ-zero-left : (n : ℕ) → zero *ℕ n ≡ zero
*ℕ-zero-left n = refl

+ℕ-zero-left : (n : ℕ) → zero +ℕ n ≡ n
+ℕ-zero-left n = refl

Pairℕ-mul : Pairℕ → Pairℕ → Pairℕ
Pairℕ-mul p q =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  ⟪ (a *ℕ c) +ℕ (b *ℕ d) , (a *ℕ d) +ℕ (b *ℕ c) ⟫

oneℤ : ℤ
oneℤ = +suc zero

oneNat : ℕ
oneNat = suc zero

from-toPairℤ : (z : ℤ) → fromPairℤ (toPairℤ z) ≡ z
from-toPairℤ 0ℤ = refl
from-toPairℤ (+suc n) = refl
from-toPairℤ (-suc n) = refl

infixl 7 _*ℤ_

_*ℤ_ : ℤ → ℤ → ℤ
x *ℤ y = fromPairℤ (Pairℕ-mul (toPairℤ x) (toPairℤ y))

*ℤ-zero-left : (y : ℤ) → 0ℤ *ℤ y ≡ 0ℤ
*ℤ-zero-left y = refl

*ℤ-zero-right : (x : ℤ) → x *ℤ 0ℤ ≡ 0ℤ
*ℤ-zero-right 0ℤ = refl
*ℤ-zero-right (+suc n) =
  normalizeℤ-cong
    (trans
      (+ℕ-zero-right (suc n *ℕ zero))
      (*ℕ-zero-right (suc n)))
    (trans
      (+ℕ-zero-right (suc n *ℕ zero))
      (*ℕ-zero-right (suc n)))
*ℤ-zero-right (-suc n) =
  normalizeℤ-cong
    (*ℕ-zero-right (suc n))
    (*ℕ-zero-right (suc n))

*ℤ-one-right : (x : ℤ) → x *ℤ oneℤ ≡ x
*ℤ-one-right 0ℤ = refl
*ℤ-one-right (+suc n) =
  normalizeℤ-cong
    (trans
      (+ℕ-zero-right (suc n *ℕ oneNat))
      (*ℕ-one-right (suc n)))
    (trans
      (+ℕ-zero-right (suc n *ℕ zero))
      (*ℕ-zero-right (suc n)))
*ℤ-one-right (-suc n) =
  normalizeℤ-cong
    (*ℕ-zero-right (suc n))
    (trans
      (+ℕ-zero-left (suc n *ℕ oneNat))
      (*ℕ-one-right (suc n)))
