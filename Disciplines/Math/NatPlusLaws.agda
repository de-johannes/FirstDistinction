{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.NatPlusLaws where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.NatPlus

{-
CHAPTER 14X: Forced Laws Of ℕ⁺

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14Q (ℕ⁺), Chapter 14O (*ℕ laws)
AGDA MODULES: Disciplines.Math.NatPlusLaws
DEGREES OF FREEDOM ELIMINATED: asymmetric denominator multiplication in ℚ
-}

-- Commutativity of ℕ⁺ multiplication, forced from *ℕ commutativity.

*⁺-comm : (x y : ℕ⁺) → x *⁺ y ≡ y *⁺ x
*⁺-comm (mkℕ⁺ a) (mkℕ⁺ b) =
  cong mkℕ⁺ (trans lhsNorm (sym rhsNorm))
  where
    lhsNorm : (a *ℕ suc b) +ℕ b ≡ (a +ℕ b) +ℕ (a *ℕ b)
    lhsNorm =
      trans
        (cong (λ t → t +ℕ b) (*ℕ-suc-right-+ℕ a b))
        (trans
          (+ℕ-assoc a (a *ℕ b) b)
          (trans
            (cong (λ t → a +ℕ t) (+ℕ-comm (a *ℕ b) b))
            (sym (+ℕ-assoc a b (a *ℕ b)))))

    rhsNorm : (b *ℕ suc a) +ℕ a ≡ (a +ℕ b) +ℕ (a *ℕ b)
    rhsNorm =
      trans
        (cong (λ t → t +ℕ a) (*ℕ-suc-right-+ℕ b a))
        (trans
          (cong (λ t → (b +ℕ t) +ℕ a) (*ℕ-comm b a))
          (trans
            (+ℕ-assoc b (a *ℕ b) a)
            (trans
              (cong (λ t → b +ℕ t) (+ℕ-comm (a *ℕ b) a))
              (trans
                (swapHeadℕ b a (a *ℕ b))
                (sym (+ℕ-assoc a b (a *ℕ b)))))))

-- Embedding respects multiplication: (suc a)·(suc b) corresponds to the forced ℕ⁺ product.

⁺toℤ-*⁺ : (x y : ℕ⁺) → ⁺toℤ (x *⁺ y) ≡ (⁺toℤ x) *ℤ (⁺toℤ y)
⁺toℤ-*⁺ (mkℕ⁺ a) (mkℕ⁺ b) =
  sym prodEq
  where
    mulNatEq : (suc a *ℕ suc b) ≡ suc ((a *ℕ suc b) +ℕ b)
    mulNatEq =
      trans
        refl
        (cong suc (+ℕ-comm b (a *ℕ suc b)))

    prodEq : ((+suc a) *ℤ (+suc b)) ≡ (+suc ((a *ℕ suc b) +ℕ b))
    prodEq =
      trans
        (cong fromPairℤ (Pairℕ-mul-pos-pos (suc a) (suc b)))
        (trans
          (cong (λ t → normalizeℤ t zero) mulNatEq)
          refl)
