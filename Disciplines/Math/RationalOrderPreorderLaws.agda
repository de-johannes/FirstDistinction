{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalOrderPreorderLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.Rationals

{-
CHAPTER 14V′: Forced Preorder Laws For ≤ℚ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (≤ℚ), Chapter 14Y (≤ℤ preorder), Chapter 14W (mul transport + cancellation)
AGDA MODULES: Disciplines.Math.RationalOrderPreorderLaws
DEGREES OF FREEDOM ELIMINATED: non-transitive rational order
-}

≤ℚ-refl : (q : ℚ) → q ≤ℚ q
≤ℚ-refl (a / b) = ≤ℤ-refl (a *ℤ ⁺toℤ b)

private
  swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
  swapScale x u v =
    trans
      (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
      (trans
        (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
        (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

≤ℚ-trans : {x y z : ℚ} → x ≤ℚ y → y ≤ℚ z → x ≤ℚ z
≤ℚ-trans {x} {y} {z} p q with x | y | z
... | a / b | c / d | e / f =
  let
    p' : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    p' = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) f p

    q' : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    q' = ≤ℤ-mul-pos-right (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) b q

    midEq : ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b)
    midEq = swapScale c b f

    p'' : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b)
    p'' = ≤ℤ-resp-≡ʳ midEq p'

    step : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    step = ≤ℤ-trans p'' q'

    lhsEq : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≡ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d)
    lhsEq = swapScale a d f

    rhsEq : ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    rhsEq = swapScale e d b

    step' : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ≤ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    step' = ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step)

    done : (a *ℤ ⁺toℤ f) ≤ℤ (e *ℤ ⁺toℤ b)
    done = ≤ℤ-mul-pos-cancel-right (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) d step'
  in
  done

_<→≰_ : {A : Set} → (A → Set) → (A → Set)
_<→≰_ P = λ a → P a → ⊥

_≰ℚ_ : ℚ → ℚ → Set
x ≰ℚ y = (x ≤ℚ y) → ⊥

≤<ℚ→<ℚ : {x y z : ℚ} → x ≤ℚ y → y <ℚ z → x <ℚ z
≤<ℚ→<ℚ {a / b} {c / d} {e / f} x≤y (y≤z , z≰y) =
  let
    x≤z : (a / b) ≤ℚ (e / f)
    x≤z = ≤ℚ-trans {a / b} {c / d} {e / f} x≤y y≤z

    z≰x : (e / f) ≰ℚ (a / b)
    z≰x z≤x = z≰y (≤ℚ-trans {e / f} {a / b} {c / d} z≤x x≤y)
  in
  x≤z , z≰x

<≤ℚ→<ℚ : {x y z : ℚ} → x <ℚ y → y ≤ℚ z → x <ℚ z
<≤ℚ→<ℚ {a / b} {c / d} {e / f} (x≤y , y≰x) y≤z =
  let
    x≤z : (a / b) ≤ℚ (e / f)
    x≤z = ≤ℚ-trans {a / b} {c / d} {e / f} x≤y y≤z

    z≰x : (e / f) ≰ℚ (a / b)
    z≰x z≤x =
      let
        y≤x : (c / d) ≤ℚ (a / b)
        y≤x = ≤ℚ-trans {c / d} {e / f} {a / b} y≤z z≤x
      in
      y≰x y≤x
  in
  x≤z , z≰x
