{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalTriangleWork where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerAbs
open import Disciplines.Math.IntegerAbsLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.Rationals

{-
CHAPTER 15B: Triangle Inequality Workbench (ℚ)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (ℚ + distℚ), Chapter 15A (absℤ laws), Chapter 14Y (≤ℤ preorder)
AGDA MODULES: Disciplines.Math.RationalTriangleWork
DEGREES OF FREEDOM ELIMINATED: none yet (workbench)
-}

-- This module is intentionally a staging area: it only contains statements we can
-- already force without introducing placeholders.
--
-- absℤ-subadditivity and compatibility of absℤ with multiplication by positive
-- factors (ℕ⁺) are now forced in IntegerAbsLaws; the remaining work for the full
-- ℚ triangle inequality is the denominator-clearing algebra.

-- A small forced consequence we can already prove: if distℚ p q is 0ℚ (≃ℚ), its numerator is 0ℤ.

numDistℚ : ℚ → ℚ → ℤ
numDistℚ (a / b) (c / d) = absℤ ((a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b))

numDistℚ-nonneg : (p q : ℚ) → 0ℤ ≤ℤ numDistℚ p q
numDistℚ-nonneg (a / b) (c / d) = absℤ-nonneg _

-- Core triangle step on cleared numerators (scaled to a common ℕ⁺ factor):
-- this is the ℤ-level inequality that the ℚ triangle inequality must reduce to.

numDistℚ-triangle-scaled : (p q r : ℚ) →
  (numDistℚ p r *ℤ ⁺toℤ (den q))
    ≤ℤ
  ((numDistℚ p q *ℤ ⁺toℤ (den r)) +ℤ (numDistℚ q r *ℤ ⁺toℤ (den p)))
numDistℚ-triangle-scaled (a / b) (c / d) (e / f) =
  ≤ℤ-resp-≡ˡ lhsAbs
    (≤ℤ-resp-≡ʳ rhsAbs
      absStep)
  where
    W : ℤ
    W = (a *ℤ ⁺toℤ f) +ℤ negℤ (e *ℤ ⁺toℤ b)

    U : ℤ
    U = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    V : ℤ
    V = (c *ℤ ⁺toℤ f) +ℤ negℤ (e *ℤ ⁺toℤ d)

    -- Reassociate and commute scaling factors so the middle term cancels.

    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    Wd : ℤ
    Wd = W *ℤ ⁺toℤ d

    Uf : ℤ
    Uf = U *ℤ ⁺toℤ f

    Vb : ℤ
    Vb = V *ℤ ⁺toℤ b

    cancelMid : (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f ≡ (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b
    cancelMid = swapScale c b f

    cancelEnd : (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d ≡ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b
    cancelEnd = swapScale e b d

    cancelHead : (a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
    cancelHead = swapScale a f d

    -- Algebra: W·d = U·f + V·b.

    Wd≡sum : Wd ≡ (Uf +ℤ Vb)
    Wd≡sum =
      trans WdForm (sym sumForm)
      where
        WdForm : Wd ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        WdForm =
          trans
            (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (negℤ (e *ℤ ⁺toℤ b)) (⁺toℤ d))
            (trans
              (cong (λ t → ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) +ℤ t)
                    (*ℤ-neg-left (e *ℤ ⁺toℤ b) (⁺toℤ d)))
              (trans
                (cong (λ t → t +ℤ negℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)) cancelHead)
                (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                      (cong negℤ cancelEnd))))

        UfForm : Uf ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
        UfForm =
          trans
            (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ f))
            (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                  (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ f)))

        VbForm : Vb ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        VbForm =
          trans
            (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (negℤ (e *ℤ ⁺toℤ d)) (⁺toℤ b))
            (cong (λ t → ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) +ℤ t)
                  (*ℤ-neg-left (e *ℤ ⁺toℤ d) (⁺toℤ b)))

        sumForm :
          (Uf +ℤ Vb) ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        sumForm =
          let
            Adf = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
            CbF = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f
            CfB = (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b
            EdB = (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b

            UfRhs = Adf +ℤ negℤ CbF
            VbRhs = CfB +ℤ negℤ EdB

            midRewrite : (negℤ CbF +ℤ CfB) ≡ (negℤ CfB +ℤ CfB)
            midRewrite =
              cong (λ t → negℤ t +ℤ CfB) cancelMid

            cancelMiddle : (negℤ CbF +ℤ CfB) ≡ 0ℤ
            cancelMiddle =
              trans midRewrite (+ℤ-inv-left CfB)

            sumCancel : (UfRhs +ℤ VbRhs) ≡ (Adf +ℤ negℤ EdB)
            sumCancel =
              trans
                (+ℤ-assoc Adf (negℤ CbF) VbRhs)
                (trans
                  (cong (λ t → Adf +ℤ t)
                        (sym (+ℤ-assoc (negℤ CbF) CfB (negℤ EdB))))
                  (trans
                    (cong (λ t → Adf +ℤ (t +ℤ negℤ EdB)) cancelMiddle)
                    (cong (λ t → Adf +ℤ t) (+ℤ-zero-left (negℤ EdB)))))
          in
          trans
            (cong (λ t → t +ℤ Vb) UfForm)
            (trans
              (cong (λ t → UfRhs +ℤ t) VbForm)
              sumCancel)

    -- abs(W·d) ≤ abs(U·f) + abs(V·b)
    absStep : absℤ Wd ≤ℤ (absℤ Uf +ℤ absℤ Vb)
    absStep =
      ≤ℤ-resp-≡ˡ (sym (cong absℤ Wd≡sum)) (absℤ-subadd Uf Vb)

    lhsAbs : absℤ Wd ≡ (absℤ W *ℤ ⁺toℤ d)
    lhsAbs =
      trans
        (absℤ-mul-pos-right W d)
        refl

    rhsAbs : (absℤ Uf +ℤ absℤ Vb) ≡ ((absℤ U *ℤ ⁺toℤ f) +ℤ (absℤ V *ℤ ⁺toℤ b))
    rhsAbs =
      trans
        (cong (λ t → t +ℤ absℤ Vb) (absℤ-mul-pos-right U f))
        (cong (λ t → (absℤ U *ℤ ⁺toℤ f) +ℤ t) (absℤ-mul-pos-right V b))
