{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalOrderMultiplicationLaws where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws
open import Disciplines.Math.Rationals
open import Disciplines.Math.RationalOrderPreorderLaws

{-
CHAPTER 14V″: Forced Laws Of Rational Multiplication Monotonicity

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (*ℚ, ≤ℚ), Chapter 14W (≤ℤ transport), Chapter 14W′ (≤ℤ mul nonneg)
AGDA MODULES: Disciplines.Math.RationalOrderMultiplicationLaws
DEGREES OF FREEDOM ELIMINATED: inability to scale ≤ℚ bounds by nonnegative factors
-}

-- Setoid equality implies ≤ℚ.

≃ℚ→≤ℚˡ : {p q : ℚ} → p ≃ℚ q → p ≤ℚ q
≃ℚ→≤ℚˡ {p} {q} eq with p | q
... | a / b | c / d = ≤ℤ-resp-≡ʳ eq (≤ℤ-refl (a *ℤ ⁺toℤ d))

-- Extract 0 ≤ num from 0 ≤ a/b.

0≤ℚ→0≤ℤ-num : (q : ℚ) → 0ℚ ≤ℚ q → 0ℤ ≤ℤ num q
0≤ℚ→0≤ℤ-num (a / b) p =
  ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b))
    (≤ℤ-resp-≡ʳ (*ℤ-one-right a) p)

-- Commutativity of *ℚ (as ≃ℚ) is forced by commutativity of *ℤ and *⁺.

*ℚ-comm : (p q : ℚ) → (p *ℚ q) ≃ℚ (q *ℚ p)
*ℚ-comm (a / b) (c / d) =
  let
    denSwap : (d *⁺ b) ≡ (b *⁺ d)
    denSwap = *⁺-comm d b

    numSwap : (a *ℤ c) ≡ (c *ℤ a)
    numSwap = *ℤ-comm a c

    lhsStep : ((a *ℤ c) *ℤ ⁺toℤ (d *⁺ b)) ≡ ((a *ℤ c) *ℤ ⁺toℤ (b *⁺ d))
    lhsStep = cong (λ t → (a *ℤ c) *ℤ ⁺toℤ t) denSwap

    rhsStep : ((c *ℤ a) *ℤ ⁺toℤ (b *⁺ d)) ≡ ((a *ℤ c) *ℤ ⁺toℤ (b *⁺ d))
    rhsStep = cong (λ t → t *ℤ ⁺toℤ (b *⁺ d)) (sym numSwap)
  in
  trans lhsStep (sym rhsStep)

-- Helper: swap the middle two factors in a triple product.

mul-swap-middle : (x y z : ℤ) → (x *ℤ y) *ℤ z ≡ (x *ℤ z) *ℤ y
mul-swap-middle x y z =
  trans
    (*ℤ-assoc x y z)
    (trans
      (cong (λ t → x *ℤ t) (*ℤ-comm y z))
      (sym (*ℤ-assoc x z y)))

-- Monotonicity: multiplying on the right by a nonnegative rational preserves ≤ℚ.

≤ℚ-mul-nonneg-right : (x y z : ℚ) → x ≤ℚ y → 0ℚ ≤ℚ z → (x *ℚ z) ≤ℚ (y *ℚ z)
≤ℚ-mul-nonneg-right (a / b) (c / d) (e / f) x≤y zNonneg =
  let
    eNonneg : 0ℤ ≤ℤ e
    eNonneg = 0≤ℚ→0≤ℤ-num (e / f) zNonneg

    step₁ : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    step₁ = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) f x≤y

    step₂ : (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ e) ≤ℤ (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ e)
    step₂ = ≤ℤ-mul-nonneg-right ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) e step₁ eNonneg

    lhsEq : (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ e) ≡ ((a *ℤ e) *ℤ ⁺toℤ (d *⁺ f))
    lhsEq =
      trans
        (mul-swap-middle (a *ℤ ⁺toℤ d) (⁺toℤ f) e)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (mul-swap-middle a (⁺toℤ d) e))
          (trans
            (*ℤ-assoc (a *ℤ e) (⁺toℤ d) (⁺toℤ f))
            (cong (λ t → (a *ℤ e) *ℤ t) (sym (⁺toℤ-*⁺ d f)))))

    rhsEq : (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ e) ≡ ((c *ℤ e) *ℤ ⁺toℤ (b *⁺ f))
    rhsEq =
      trans
        (mul-swap-middle (c *ℤ ⁺toℤ b) (⁺toℤ f) e)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (mul-swap-middle c (⁺toℤ b) e))
          (trans
            (*ℤ-assoc (c *ℤ e) (⁺toℤ b) (⁺toℤ f))
            (cong (λ t → (c *ℤ e) *ℤ t) (sym (⁺toℤ-*⁺ b f)))))
  in
  ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step₂)

-- Monotonicity in the right argument: fixed nonnegative left factor.

≤ℚ-mul-nonneg-left : (x y z : ℚ) → x ≤ℚ y → 0ℚ ≤ℚ z → (z *ℚ x) ≤ℚ (z *ℚ y)
≤ℚ-mul-nonneg-left (a / b) (c / d) (e / f) x≤y zNonneg =
  let
    zx≤xz : ((e / f) *ℚ (a / b)) ≤ℚ ((a / b) *ℚ (e / f))
    zx≤xz =
      ≃ℚ→≤ℚˡ
        {p = (e / f) *ℚ (a / b)}
        {q = (a / b) *ℚ (e / f)}
        (*ℚ-comm (e / f) (a / b))

    xz≤yz : ((a / b) *ℚ (e / f)) ≤ℚ ((c / d) *ℚ (e / f))
    xz≤yz = ≤ℚ-mul-nonneg-right (a / b) (c / d) (e / f) x≤y zNonneg

    yz≤zy : ((c / d) *ℚ (e / f)) ≤ℚ ((e / f) *ℚ (c / d))
    yz≤zy =
      ≃ℚ→≤ℚˡ
        {p = (c / d) *ℚ (e / f)}
        {q = (e / f) *ℚ (c / d)}
        (*ℚ-comm (c / d) (e / f))
    
    middle : ((a / b) *ℚ (e / f)) ≤ℚ ((e / f) *ℚ (c / d))
    middle = ≤ℚ-trans {(a / b) *ℚ (e / f)} {(c / d) *ℚ (e / f)} {(e / f) *ℚ (c / d)} xz≤yz yz≤zy
  in
  ≤ℚ-trans {(e / f) *ℚ (a / b)} {(a / b) *ℚ (e / f)} {(e / f) *ℚ (c / d)} zx≤xz middle


