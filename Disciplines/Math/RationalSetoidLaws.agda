{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalSetoidLaws where

open import FirstDistinction
open import Disciplines.Math.Rationals
open import Disciplines.Math.NatPlus
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws

≃ℚ-refl : (p : ℚ) → p ≃ℚ p
≃ℚ-refl (a / b) = refl

≃ℚ-sym : {p q : ℚ} → p ≃ℚ q → q ≃ℚ p
≃ℚ-sym = sym

*ℤ-cancel-right-pos : (x y : ℤ) → (d : ℕ⁺) → (x *ℤ ⁺toℤ d) ≡ (y *ℤ ⁺toℤ d) → x ≡ y
*ℤ-cancel-right-pos x y d eq =
  ≤ℤ-antisym
    (≤ℤ-mul-pos-cancel-right x y d (≤ℤ-resp-≡ʳ eq (≤ℤ-refl (x *ℤ ⁺toℤ d))))
    (≤ℤ-mul-pos-cancel-right y x d (≤ℤ-resp-≡ʳ (sym eq) (≤ℤ-refl (y *ℤ ⁺toℤ d))))

≃ℚ-trans : {p q r : ℚ} → p ≃ℚ q → q ≃ℚ r → p ≃ℚ r
≃ℚ-trans {a / b} {c / d} {e / f} eq₁ eq₂ =
  let
    B : ℤ
    B = ⁺toℤ b

    D : ℤ
    D = ⁺toℤ d

    F : ℤ
    F = ⁺toℤ f

    step₁ : ((a *ℤ D) *ℤ F) ≡ ((c *ℤ B) *ℤ F)
    step₁ = cong (λ t → t *ℤ F) eq₁

    step₂ : ((c *ℤ F) *ℤ B) ≡ ((e *ℤ D) *ℤ B)
    step₂ = cong (λ t → t *ℤ B) eq₂

    swapCBF : ((c *ℤ B) *ℤ F) ≡ ((c *ℤ F) *ℤ B)
    swapCBF =
      trans
        (*ℤ-assoc c B F)
        (trans
          (cong (λ t → c *ℤ t) (*ℤ-comm B F))
          (sym (*ℤ-assoc c F B)))

    mid : ((a *ℤ D) *ℤ F) ≡ ((e *ℤ D) *ℤ B)
    mid = trans step₁ (trans swapCBF step₂)

    regroupL : ((a *ℤ D) *ℤ F) ≡ (a *ℤ F) *ℤ D
    regroupL =
      trans
        (*ℤ-assoc a D F)
        (trans
          (cong (λ t → a *ℤ t) (*ℤ-comm D F))
          (sym (*ℤ-assoc a F D)))

    regroupR : ((e *ℤ D) *ℤ B) ≡ (e *ℤ B) *ℤ D
    regroupR =
      trans
        (*ℤ-assoc e D B)
        (trans
          (cong (λ t → e *ℤ t) (*ℤ-comm D B))
          (sym (*ℤ-assoc e B D)))

    eqD : ((a *ℤ F) *ℤ D) ≡ ((e *ℤ B) *ℤ D)
    eqD = trans (sym regroupL) (trans mid regroupR)
  in
  *ℤ-cancel-right-pos (a *ℤ F) (e *ℤ B) d eqD
