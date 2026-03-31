{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalArchimedeanLaws where

open import FirstDistinction
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws using (+ℕ-zero-right)
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerAbsLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws using (≤ℤ-refl)
open import Disciplines.Math.IntegerOrderAdditionLaws
open import Disciplines.Math.Rationals
open import Disciplines.Math.RationalOrderLaws
open import Disciplines.Math.RationalOrderPreorderLaws
open import Disciplines.Math.RationalEpsilonSplitLaws

{-
CHAPTER 14V‴: Forced Archimedean Scaling Over ℚ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14V (order bridges), Chapter 14T′ (εHalf), Chapter 14W′ (mul transport nonneg)
AGDA MODULES: Disciplines.Math.RationalArchimedeanLaws
DEGREES OF FREEDOM ELIMINATED: inability to shrink by (suc n) factors
-}

-- Basic positivity witness: 0 < 1/b for any positive denominator b.

*⁺-one-right : (u : ℕ⁺) → (u *⁺ one⁺) ≡ u
*⁺-one-right (mkℕ⁺ p) =
  cong mkℕ⁺
    (trans
      (+ℕ-zero-right (p *ℕ suc zero))
      (*ℕ-one-right p))

oneOver-pos : (b : ℕ⁺) → 0ℚ <ℚ (oneℤ / b)
oneOver-pos b =
  let
    rhsEq : oneℤ ≡ (oneℤ *ℤ ⁺toℤ one⁺)
    rhsEq = sym (*ℤ-one-right oneℤ)

    base : 0ℤ <ℤ (oneℤ *ℤ ⁺toℤ one⁺)
    base = <ℤ-resp-≡ʳ {x = 0ℤ} {y = oneℤ} {z = (oneℤ *ℤ ⁺toℤ one⁺)} rhsEq 0ℤ<oneℤ
  in
  <ℤ-resp-≡ˡ
    {x = 0ℤ}
    {y = (0ℤ *ℤ ⁺toℤ b)}
    {z = (oneℤ *ℤ ⁺toℤ one⁺)}
    (sym (*ℤ-zero-left (⁺toℤ b)))
    base

-- Denominators are ≥ 1 in the integer order.

one≤⁺toℤ : (d : ℕ⁺) → oneℤ ≤ℤ ⁺toℤ d
one≤⁺toℤ (mkℕ⁺ k) = s≤s z≤n

-- If q≥0 then q ≤ num(q)/1.

nonneg-≤numOverOne : (q : ℚ) → 0ℚ ≤ℚ q → q ≤ℚ (num q / one⁺)
nonneg-≤numOverOne (a / b) qNonneg =
  let
    aNonneg : 0ℤ ≤ℤ a
    aNonneg =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsEq : (a *ℤ ⁺toℤ one⁺) ≡ a
        rhsEq = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)

        step₀ : 0ℤ ≤ℤ (a *ℤ ⁺toℤ one⁺)
        step₀ = ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b)) qNonneg
      in
      ≤ℤ-resp-≡ʳ rhsEq step₀

    one≤b : oneℤ ≤ℤ ⁺toℤ b
    one≤b = one≤⁺toℤ b

    step : (oneℤ *ℤ a) ≤ℤ ((⁺toℤ b) *ℤ a)
    step = ≤ℤ-mul-nonneg-right oneℤ (⁺toℤ b) a one≤b aNonneg

    lhsEq : (oneℤ *ℤ a) ≡ (a *ℤ ⁺toℤ one⁺)
    lhsEq = trans (*ℤ-one-left a) (sym (*ℤ-one-right a))

    rhsEq : ((⁺toℤ b) *ℤ a) ≡ (a *ℤ ⁺toℤ b)
    rhsEq = *ℤ-comm (⁺toℤ b) a

    core : (a *ℤ ⁺toℤ one⁺) ≤ℤ (a *ℤ ⁺toℤ b)
    core = ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step)
  in
  core

-- Any nonnegative rational is ≤ a successor-integer rational.

nonneg-bound-sucInt : (q : ℚ) → 0ℚ ≤ℚ q → Σ ℕ (λ m → q ≤ℚ (fromℕℤ (suc m) / one⁺))
nonneg-bound-sucInt (a / b) qNonneg =
  let
    aNonneg : 0ℤ ≤ℤ a
    aNonneg =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsEq : (a *ℤ ⁺toℤ one⁺) ≡ a
        rhsEq = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)

        step₀ : 0ℤ ≤ℤ (a *ℤ ⁺toℤ one⁺)
        step₀ = ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b)) qNonneg
      in
      ≤ℤ-resp-≡ʳ rhsEq step₀

    aNatPack : Σ ℕ (λ n → a ≡ fromℕℤ n)
    aNatPack = 0≤ℤ→fromℕℤ a aNonneg

    m : ℕ
    m = fst aNatPack

    a≡ : a ≡ fromℕℤ m
    a≡ = snd aNatPack

    q≤a/1 : (a / b) ≤ℚ (a / one⁺)
    q≤a/1 = nonneg-≤numOverOne (a / b) qNonneg

    a/1≤m/1 : (a / one⁺) ≤ℚ (fromℕℤ m / one⁺)
    a/1≤m/1 =
      ≤ℤ-resp-≡ʳ
        (cong (λ t → t *ℤ ⁺toℤ one⁺) a≡)
        (≤ℤ-refl (a *ℤ ⁺toℤ one⁺))

    m≤sucm : m ≤ suc m
    m≤sucm = ≤-step m

    fm≤fs : fromℕℤ m ≤ℤ fromℕℤ (suc m)
    fm≤fs = fromℕℤ-mono m≤sucm

    m/1≤sucm/1 : (fromℕℤ m / one⁺) ≤ℚ (fromℕℤ (suc m) / one⁺)
    m/1≤sucm/1 =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsOneEq : (n : ℕ) → (fromℕℤ n *ℤ ⁺toℤ one⁺) ≡ fromℕℤ n
        rhsOneEq n = trans (cong (λ t → fromℕℤ n *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right (fromℕℤ n))

        stepR : fromℕℤ m ≤ℤ (fromℕℤ (suc m) *ℤ ⁺toℤ one⁺)
        stepR = ≤ℤ-resp-≡ʳ (sym (rhsOneEq (suc m))) fm≤fs
      in
      ≤ℤ-resp-≡ˡ (sym (rhsOneEq m)) stepR
  in
  m ,
    (≤ℚ-trans {a / b} {a / one⁺} {fromℕℤ (suc m) / one⁺} q≤a/1
      (≤ℚ-trans {a / one⁺} {fromℕℤ m / one⁺} {fromℕℤ (suc m) / one⁺} a/1≤m/1 m/1≤sucm/1))

-- Archimedean scaling: there is δ>0 such that δ·(suc m) < ε.

δ-scale-suc : (ε : ℚ) → 0ℚ <ℚ ε → (m : ℕ) → Σ ℚ (λ δ → (0ℚ <ℚ δ) × ((δ *ℚ (fromℕℤ (suc m) / one⁺)) <ℚ ε))
δ-scale-suc ε εpos m =
  let
    k : ℕ⁺
    k = mkℕ⁺ m

    b : ℕ⁺
    b = den ε

    δ : ℚ
    δ = oneℤ / halfDen (k *⁺ b)

    δpos : 0ℚ <ℚ δ
    δpos = oneOver-pos (halfDen (k *⁺ b))

    factor : ℚ
    factor = fromℕℤ (suc m) / one⁺

    prod : ℚ
    prod = δ *ℚ factor

    -- prod ≃ εHalf ε, hence prod < ε.

    kZ : ℤ
    kZ = ⁺toℤ k

    kZ≡ : kZ ≡ fromℕℤ (suc m)
    kZ≡ = refl

    halfDenZ : (u : ℕ⁺) → ⁺toℤ (halfDen u) ≡ (⁺toℤ two⁺) *ℤ ⁺toℤ u
    halfDenZ u = ⁺toℤ-*⁺ two⁺ u

    rhsDenZ : ⁺toℤ (halfDen b) ≡ (⁺toℤ two⁺) *ℤ ⁺toℤ b
    rhsDenZ = halfDenZ b

    lhsDenZ : ⁺toℤ (halfDen (k *⁺ b)) ≡ (⁺toℤ two⁺) *ℤ ((⁺toℤ k) *ℤ ⁺toℤ b)
    lhsDenZ =
      trans
        (halfDenZ (k *⁺ b))
        (cong (λ t → (⁺toℤ two⁺) *ℤ t) (⁺toℤ-*⁺ k b))

    swap : (x y z : ℤ) → (x *ℤ (y *ℤ z)) ≡ (y *ℤ (x *ℤ z))
    swap x y z =
      trans
        (sym (*ℤ-assoc x y z))
        (trans
          (cong (λ t → t *ℤ z) (*ℤ-comm x y))
          (*ℤ-assoc y x z))

    denEq : (⁺toℤ (halfDen (k *⁺ b))) ≡ (fromℕℤ (suc m) *ℤ ⁺toℤ (halfDen b))
    denEq =
      trans
        lhsDenZ
        (trans
          (cong (λ t → (⁺toℤ two⁺) *ℤ (t *ℤ ⁺toℤ b)) (sym kZ≡))
          (trans
            (swap (⁺toℤ two⁺) (fromℕℤ (suc m)) (⁺toℤ b))
            (cong (λ t → (fromℕℤ (suc m)) *ℤ t) (sym rhsDenZ))))

    prod≃half : prod ≃ℚ (εHalf ε)
    prod≃half =
      let
        -- Unfold prod = (1 / (2*(k*b))) * (k / 1) = k / (2*(k*b)).
        lhsNum : ℤ
        lhsNum = oneℤ *ℤ fromℕℤ (suc m)

        lhsDen : ℕ⁺
        lhsDen = (halfDen (k *⁺ b)) *⁺ one⁺

        rhsNum : ℤ
        rhsNum = oneℤ

        rhsDen : ℕ⁺
        rhsDen = halfDen b

        -- Goal: lhsNum * rhsDen = rhsNum * lhsDen.
        lhsNumEq : lhsNum ≡ fromℕℤ (suc m)
        lhsNumEq = *ℤ-one-left (fromℕℤ (suc m))

        denOne : (halfDen (k *⁺ b)) *⁺ one⁺ ≡ halfDen (k *⁺ b)
        denOne = *⁺-one-right (halfDen (k *⁺ b))

        lhsDenEq : (⁺toℤ lhsDen) ≡ ⁺toℤ (halfDen (k *⁺ b))
        lhsDenEq = cong ⁺toℤ denOne

        cross : (lhsNum *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
        cross =
          trans
            (cong (λ t → t *ℤ ⁺toℤ rhsDen) lhsNumEq)
            (trans
              (sym denEq)
              (trans
                (sym (*ℤ-one-left (⁺toℤ (halfDen (k *⁺ b)))))
                (cong (λ t → oneℤ *ℤ t) (sym lhsDenEq))))
      in
      cross

    half<ε : (εHalf ε) <ℚ ε
    half<ε = εHalf<ε ε εpos

    prod<ε : prod <ℚ ε
    prod<ε =
      ≤<ℚ→<ℚ
        {x = prod} {y = εHalf ε} {z = ε}
        (≃ℚ→≤ℚˡ {p = prod} {q = εHalf ε} prod≃half)
        half<ε
  in
  δ , (δpos , prod<ε)
