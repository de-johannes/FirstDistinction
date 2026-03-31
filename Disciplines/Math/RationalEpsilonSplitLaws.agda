{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalEpsilonSplitLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderAdditionLaws
open import Disciplines.Math.Rationals
open import Disciplines.Math.RationalSetoidLaws
open import Disciplines.Math.RationalOrderLaws
open import Disciplines.Math.RationalOrderPreorderLaws
open import Disciplines.Math.RationalOrderAdditionLaws

{-
CHAPTER 14T′: Forced ε-Splitting Over ℚ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (ℚ), Chapter 14V (positivity extraction), Chapter 14W (strict mul transport)
AGDA MODULES: Disciplines.Math.RationalEpsilonSplitLaws
DEGREES OF FREEDOM ELIMINATED: inability to combine two strict Cauchy bounds into one
-}

-- A forced constant: 2 as ℕ⁺.

two⁺ : ℕ⁺
two⁺ = suc⁺ one⁺

halfDen : ℕ⁺ → ℕ⁺
halfDen b = two⁺ *⁺ b

quarterDen : ℕ⁺ → ℕ⁺
quarterDen b = two⁺ *⁺ (two⁺ *⁺ b)

εQuarter : ℚ → ℚ
εQuarter (a / b) = oneℤ / quarterDen b

εHalf : ℚ → ℚ
εHalf (a / b) = oneℤ / halfDen b

εQuarter-pos : (ε : ℚ) → 0ℚ <ℚ εQuarter ε
εQuarter-pos (a / b) =
  let
    qd : ℕ⁺
    qd = quarterDen b

    lhs0 : (0ℤ *ℤ ⁺toℤ qd) ≡ 0ℤ
    lhs0 = *ℤ-zero-left (⁺toℤ qd)

    one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
    one⁺ℤ≡oneℤ = refl

    rhs1 : (oneℤ *ℤ ⁺toℤ one⁺) ≡ oneℤ
    rhs1 = trans (cong (λ t → oneℤ *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right oneℤ)
  in
  <ℤ-resp-≡ˡ {x = 0ℤ} {y = 0ℤ *ℤ ⁺toℤ qd} {z = oneℤ *ℤ ⁺toℤ one⁺} (sym lhs0)
    (<ℤ-resp-≡ʳ {x = 0ℤ} {y = oneℤ} {z = oneℤ *ℤ ⁺toℤ one⁺} (sym rhs1) 0ℤ<oneℤ)

-- Main splitting lemma: for any ε>0, choose δ = 1/(4·den ε) so that δ+δ < ε.

-- Doubling the quarter-denominator rational yields the half-denominator rational (up to ≃ℚ).

εQuarter+εQuarter≃εHalf : (ε : ℚ) → (εQuarter ε +ℚ εQuarter ε) ≃ℚ (εHalf ε)
εQuarter+εQuarter≃εHalf (a / b) =
  let
    qd : ℕ⁺
    qd = quarterDen b

    hd : ℕ⁺
    hd = halfDen b

    lhsNum : ℤ
    lhsNum = (oneℤ *ℤ ⁺toℤ qd) +ℤ (oneℤ *ℤ ⁺toℤ qd)

    lhsDen : ℕ⁺
    lhsDen = qd *⁺ qd

    -- Goal: lhsNum * hd = 1 * lhsDen
    -- Expand lhsNum*hd using distributivity, and use qd = 2*(2*b) and hd = 2*b.

    qdSplit : ⁺toℤ qd ≡ (⁺toℤ two⁺) *ℤ ((⁺toℤ two⁺) *ℤ (⁺toℤ b))
    qdSplit =
      trans
        (⁺toℤ-*⁺ two⁺ (two⁺ *⁺ b))
        (cong (λ t → (⁺toℤ two⁺) *ℤ t) (⁺toℤ-*⁺ two⁺ b))

    hdSplit : ⁺toℤ hd ≡ (⁺toℤ two⁺) *ℤ (⁺toℤ b)
    hdSplit = ⁺toℤ-*⁺ two⁺ b

    lhsExpand : (lhsNum *ℤ ⁺toℤ hd) ≡ (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd +ℤ (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd
    lhsExpand =
      *ℤ-distrib-left-+ℤ (oneℤ *ℤ ⁺toℤ qd) (oneℤ *ℤ ⁺toℤ qd) (⁺toℤ hd)

    -- Replace 1·qd by qd.
    oneqd : (oneℤ *ℤ ⁺toℤ qd) ≡ ⁺toℤ qd
    oneqd = *ℤ-one-left (⁺toℤ qd)

    term : (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd ≡ (⁺toℤ qd) *ℤ ⁺toℤ hd
    term = cong (λ t → t *ℤ ⁺toℤ hd) oneqd

    rhs : (oneℤ *ℤ ⁺toℤ lhsDen) ≡ (⁺toℤ qd) *ℤ (⁺toℤ qd)
    rhs =
      trans
        (cong (λ t → oneℤ *ℤ t) (⁺toℤ-*⁺ qd qd))
        (trans
          (*ℤ-one-left ((⁺toℤ qd) *ℤ (⁺toℤ qd)))
          refl)

    twoℤ : ℤ
    twoℤ = ⁺toℤ two⁺

    twoℤ≡ : twoℤ ≡ oneℤ +ℤ oneℤ
    twoℤ≡ = refl

    qd≡twohd : qd ≡ two⁺ *⁺ hd
    qd≡twohd = refl

    qdAsTwoHd : ⁺toℤ qd ≡ twoℤ *ℤ ⁺toℤ hd
    qdAsTwoHd = trans (cong ⁺toℤ qd≡twohd) (⁺toℤ-*⁺ two⁺ hd)

    qdHd : ℤ
    qdHd = (⁺toℤ qd) *ℤ ⁺toℤ hd

    dupToMul2 : (qdHd +ℤ qdHd) ≡ qdHd *ℤ twoℤ
    dupToMul2 =
      trans
        (cong (λ t → t +ℤ qdHd) (sym (*ℤ-one-right qdHd)))
        (trans
          (cong (λ t → (qdHd *ℤ oneℤ) +ℤ t) (sym (*ℤ-one-right qdHd)))
          (trans
            (sym (*ℤ-distrib-right-+ℤ qdHd oneℤ oneℤ))
            (cong (λ t → qdHd *ℤ t) (sym twoℤ≡))))

    squareToMul2 : ((⁺toℤ qd) *ℤ (⁺toℤ qd)) ≡ qdHd *ℤ twoℤ
    squareToMul2 =
      trans
        (cong (λ t → (⁺toℤ qd) *ℤ t) qdAsTwoHd)
        (trans
          (sym (*ℤ-assoc (⁺toℤ qd) twoℤ (⁺toℤ hd)))
          (trans
            (cong (λ t → t *ℤ ⁺toℤ hd) (*ℤ-comm (⁺toℤ qd) twoℤ))
            (trans
              (*ℤ-assoc twoℤ (⁺toℤ qd) (⁺toℤ hd))
              (*ℤ-comm twoℤ ((⁺toℤ qd) *ℤ ⁺toℤ hd)))))

    -- Enough to show: 2·(qd·hd) = qd·qd, i.e. qd·(2b) duplicated equals qd squared.
    -- This holds by associativity/commutativity on the ℤ-embedded factors.

    goal : (lhsNum *ℤ ⁺toℤ hd) ≡ (oneℤ *ℤ ⁺toℤ lhsDen)
    goal =
      trans
        lhsExpand
        (trans
          (cong (λ t → t +ℤ t) term)
          (trans
            dupToMul2
            (trans (sym squareToMul2) (sym rhs))))
  in
  goal

-- Half-bound: 1/(2·den ε) is strictly below ε when ε>0.

εHalf<ε : (ε : ℚ) → 0ℚ <ℚ ε → εHalf ε <ℚ ε
εHalf<ε (a / b) εpos =
  let
    aPos : 0ℤ <ℤ a
    aPos = 0ℚ<→0ℤ<num (a / b) εpos

    one<2a-sum : oneℤ <ℤ (a +ℤ a)
    one<2a-sum = oneℤ<twoTimes-pos a aPos

    -- Rewrite (a+a) as a*2.
    twoℤ : ℤ
    twoℤ = ⁺toℤ two⁺

    twoℤ≡ : twoℤ ≡ oneℤ +ℤ oneℤ
    twoℤ≡ = refl

    aTimesTwo≡ : (a *ℤ twoℤ) ≡ (a +ℤ a)
    aTimesTwo≡ =
      trans
        (cong (λ t → a *ℤ t) twoℤ≡)
        (trans
          (*ℤ-distrib-right-+ℤ a oneℤ oneℤ)
          (trans
            (cong (λ t → t +ℤ (a *ℤ oneℤ)) (*ℤ-one-right a))
            (cong (λ t → a +ℤ t) (*ℤ-one-right a))))

    one<2a : oneℤ <ℤ (a *ℤ twoℤ)
    one<2a = <ℤ-resp-≡ʳ (sym aTimesTwo≡) one<2a-sum

    step₁ : (oneℤ *ℤ ⁺toℤ b) <ℤ ((a *ℤ twoℤ) *ℤ ⁺toℤ b)
    step₁ = <ℤ-mul-pos-right b one<2a

    lhsEq : (oneℤ *ℤ ⁺toℤ b) ≡ ⁺toℤ b
    lhsEq = *ℤ-one-left (⁺toℤ b)

    rhsEq : ((a *ℤ twoℤ) *ℤ ⁺toℤ b) ≡ (a *ℤ ⁺toℤ (two⁺ *⁺ b))
    rhsEq =
      trans
        (*ℤ-assoc a twoℤ (⁺toℤ b))
        (cong (λ t → a *ℤ t) (sym (⁺toℤ-*⁺ two⁺ b)))

    core : (oneℤ *ℤ ⁺toℤ b) <ℤ (a *ℤ ⁺toℤ (two⁺ *⁺ b))
    core = <ℤ-resp-≡ʳ rhsEq step₁
  in
  core

-- Final split: δ = 1/(4·den ε) has 0<δ and δ+δ < ε.

εQuarter-double<ε : (ε : ℚ) → 0ℚ <ℚ ε → (εQuarter ε +ℚ εQuarter ε) <ℚ ε
εQuarter-double<ε ε εpos =
  let
    eq : (εQuarter ε +ℚ εQuarter ε) ≃ℚ (εHalf ε)
    eq = εQuarter+εQuarter≃εHalf ε

    le : (εQuarter ε +ℚ εQuarter ε) ≤ℚ (εHalf ε)
    le = ≃ℚ→≤ℚˡ {p = εQuarter ε +ℚ εQuarter ε} {q = εHalf ε} eq

    halfLt : (εHalf ε) <ℚ ε
    halfLt = εHalf<ε ε εpos
  in
  ≤<ℚ→<ℚ {x = εQuarter ε +ℚ εQuarter ε} {y = εHalf ε} {z = ε} le halfLt

-- εQuarter ε < ε: follows from εQuarter ≤ εQuarter+εQuarter < ε.

εQuarter<ε : (ε : ℚ) → 0ℚ <ℚ ε → εQuarter ε <ℚ ε
εQuarter<ε ε εpos =
  let
    eq : εQuarter ε ≃ℚ εQuarter ε
    eq = ≃ℚ-refl (εQuarter ε)

    εqPos : 0ℚ <ℚ εQuarter ε
    εqPos = εQuarter-pos ε

    εqNonneg : 0ℚ ≤ℚ εQuarter ε
    εqNonneg = <ℚ→≤ℚ {x = 0ℚ} {y = εQuarter ε} εqPos

    εq≤εq+εq : εQuarter ε ≤ℚ (εQuarter ε +ℚ εQuarter ε)
    εq≤εq+εq = ≤ℚ-add-nonneg-right (εQuarter ε) (εQuarter ε) εqNonneg

    double<ε : (εQuarter ε +ℚ εQuarter ε) <ℚ ε
    double<ε = εQuarter-double<ε ε εpos
  in
  ≤<ℚ→<ℚ {x = εQuarter ε} {y = εQuarter ε +ℚ εQuarter ε} {z = ε} εq≤εq+εq double<ε
