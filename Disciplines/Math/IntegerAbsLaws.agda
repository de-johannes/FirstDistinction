{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerAbsLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerAbs
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws

{-
CHAPTER 15A: Forced Laws Of absℤ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14Z (absℤ), Chapter 14R (≤ℤ)
AGDA MODULES: Disciplines.Math.IntegerAbsLaws
DEGREES OF FREEDOM ELIMINATED: inconsistent interaction of abs with sign and order
-}

absℤ-zero : absℤ 0ℤ ≡ 0ℤ
absℤ-zero = refl

absℤ-neg : (z : ℤ) → absℤ (negℤ z) ≡ absℤ z
absℤ-neg 0ℤ = refl
absℤ-neg (+suc n) = refl
absℤ-neg (-suc n) = refl

absℤ-idem : (z : ℤ) → absℤ (absℤ z) ≡ absℤ z
absℤ-idem 0ℤ = refl
absℤ-idem (+suc n) = refl
absℤ-idem (-suc n) = refl

absℤ-nonneg : (z : ℤ) → 0ℤ ≤ℤ absℤ z
absℤ-nonneg 0ℤ = tt
absℤ-nonneg (+suc n) = tt
absℤ-nonneg (-suc n) = tt

-- Every integer is bounded above by its absolute value.

≤ℤ-absℤ : (z : ℤ) → z ≤ℤ absℤ z
≤ℤ-absℤ 0ℤ = tt
≤ℤ-absℤ (+suc n) = ≤-refl (suc n)
≤ℤ-absℤ (-suc n) = tt

absℤ-zero→zero : (z : ℤ) → absℤ z ≡ 0ℤ → z ≡ 0ℤ
absℤ-zero→zero 0ℤ _ = refl
absℤ-zero→zero (+suc n) ()
absℤ-zero→zero (-suc n) ()

-- Forced magnitude view: absℤ is the ℤ-embedding of a natural magnitude.

magℤ : ℤ → ℕ
magℤ 0ℤ = zero
magℤ (+suc n) = suc n
magℤ (-suc n) = suc n

fromℕℤ : ℕ → ℤ
fromℕℤ zero = 0ℤ
fromℕℤ (suc n) = +suc n

absℤ-fromℕℤ-magℤ : (z : ℤ) → absℤ z ≡ fromℕℤ (magℤ z)
absℤ-fromℕℤ-magℤ 0ℤ = refl
absℤ-fromℕℤ-magℤ (+suc n) = refl
absℤ-fromℕℤ-magℤ (-suc n) = refl

≤-resp-≡ʳ : {a b c : ℕ} → a ≤ b → b ≡ c → a ≤ c
≤-resp-≡ʳ {a} p eq = subst (λ t → a ≤ t) eq p

≤-weaken-sucʳ : {a b : ℕ} → a ≤ b → a ≤ suc b
≤-weaken-sucʳ {a} {b} p = ≤-trans p (≤-step b)

≤-weaken-suc²ʳ : {a b : ℕ} → a ≤ b → a ≤ suc (suc b)
≤-weaken-suc²ʳ p = ≤-weaken-sucʳ (≤-weaken-sucʳ p)

-- The magnitude of a normalized difference is bounded by the sum of inputs.

magNormalize≤sum : (a b : ℕ) → magℤ (normalizeℤ a b) ≤ (a +ℕ b)
magNormalize≤sum zero zero = ≤-refl zero
magNormalize≤sum (suc a) zero =
  ≤-resp-≡ʳ
    (≤-refl (suc a))
    (sym (+ℕ-zero-right (suc a)))
magNormalize≤sum zero (suc b) = ≤-refl (suc b)
magNormalize≤sum (suc a) (suc b) =
  ≤-resp-≡ʳ
    (≤-weaken-suc²ʳ (magNormalize≤sum a b))
    rhs
  where
    rhs : suc (suc (a +ℕ b)) ≡ (suc a +ℕ suc b)
    rhs = sym (cong suc (+ℕ-suc-right a b))

-- Magnitude is subadditive for +ℤ.

magℤ-+ℤ-subadd : (x y : ℤ) → magℤ (x +ℤ y) ≤ (magℤ x +ℕ magℤ y)
magℤ-+ℤ-subadd x y =
  ≤-resp-≡ʳ
    (magNormalize≤sum (pos px +ℕ pos py) (neg px +ℕ neg py))
    sumReassoc
  where
    px : Pairℕ
    px = toPairℤ x

    py : Pairℕ
    py = toPairℤ y

    cong₂ : {A B C : Set} → (f : A → B → C) → {a a' : A} → {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

    pairSumMag : (z : ℤ) → (pos (toPairℤ z) +ℕ neg (toPairℤ z)) ≡ magℤ z
    pairSumMag 0ℤ = refl
    pairSumMag (+suc n) = +ℕ-zero-right (suc n)
    pairSumMag (-suc n) = refl

    pairSumMagPx : (pos px +ℕ neg px) ≡ magℤ x
    pairSumMagPx = pairSumMag x

    pairSumMagPy : (pos py +ℕ neg py) ≡ magℤ y
    pairSumMagPy = pairSumMag y

    sumReassoc :
      ((pos px +ℕ pos py) +ℕ (neg px +ℕ neg py))
        ≡
      (magℤ x +ℕ magℤ y)
    sumReassoc =
      trans
        (shuffleℕ (pos px) (pos py) (neg px) (neg py))
        (cong₂ _+ℕ_ pairSumMagPx pairSumMagPy)

-- Transporting nat-≤ into ≤ℤ for nonnegative integers.

fromℕℤ-mono : {m n : ℕ} → m ≤ n → fromℕℤ m ≤ℤ fromℕℤ n
fromℕℤ-mono {zero} {zero} _ = tt
fromℕℤ-mono {zero} {suc n} _ = tt
fromℕℤ-mono {suc m} {zero} ()
fromℕℤ-mono {suc m} {suc n} p = p

fromℕℤ-+ℤ : (m n : ℕ) → fromℕℤ m +ℤ fromℕℤ n ≡ fromℕℤ (m +ℕ n)
fromℕℤ-+ℤ zero zero = refl
fromℕℤ-+ℤ zero (suc n) = refl
fromℕℤ-+ℤ (suc m) zero = refl
fromℕℤ-+ℤ (suc m) (suc n) = refl

-- Forced triangle core: abs is subadditive on ℤ.

absℤ-subadd : (x y : ℤ) → absℤ (x +ℤ y) ≤ℤ (absℤ x +ℤ absℤ y)
absℤ-subadd x y =
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) step₁)
  where
    step₁ : fromℕℤ (magℤ (x +ℤ y)) ≤ℤ fromℕℤ (magℤ x +ℕ magℤ y)
    step₁ = fromℕℤ-mono (magℤ-+ℤ-subadd x y)

    lhsEq : absℤ (x +ℤ y) ≡ fromℕℤ (magℤ (x +ℤ y))
    lhsEq = absℤ-fromℕℤ-magℤ (x +ℤ y)

    rhsEq : absℤ x +ℤ absℤ y ≡ fromℕℤ (magℤ x +ℕ magℤ y)
    rhsEq =
      trans
        (cong (λ t → t +ℤ absℤ y) (absℤ-fromℕℤ-magℤ x))
        (trans
          (cong (λ t → fromℕℤ (magℤ x) +ℤ t) (absℤ-fromℕℤ-magℤ y))
          (fromℕℤ-+ℤ (magℤ x) (magℤ y)))

absℤ-mul-pos-right : (z : ℤ) → (d : ℕ⁺) → absℤ (z *ℤ ⁺toℤ d) ≡ (absℤ z *ℤ ⁺toℤ d)
absℤ-mul-pos-right 0ℤ d =
  trans
    (cong absℤ (*ℤ-zero-left (⁺toℤ d)))
    (sym (*ℤ-zero-left (⁺toℤ d)))
absℤ-mul-pos-right (+suc n) (mkℕ⁺ k) =
  trans
    (trans (cong absℤ mulPosForm) refl)
    (sym mulPosForm)
  where
    t : ℕ
    t = k +ℕ (n *ℕ suc k)

    *ℕ-suc-suc : suc n *ℕ suc k ≡ suc t
    *ℕ-suc-suc = refl

    posEq : ((suc n *ℕ suc k) +ℕ (zero *ℕ zero)) ≡ suc t
    posEq =
      trans
        (+ℕ-zero-right (suc n *ℕ suc k))
        *ℕ-suc-suc

    negEq : ((suc n *ℕ zero) +ℕ (zero *ℕ suc k)) ≡ zero
    negEq =
      trans
        (cong (λ u → u +ℕ zero) (*ℕ-zero-right (suc n)))
        refl

    mulPosForm : (+suc n) *ℤ (+suc k) ≡ +suc t
    mulPosForm =
      trans
        (normalizeℤ-cong posEq negEq)
        refl

absℤ-mul-pos-right (-suc n) (mkℕ⁺ k) =
  trans
    (trans (cong absℤ mulNegForm) refl)
    (sym mulPosForm)
  where
    t : ℕ
    t = k +ℕ (n *ℕ suc k)

    *ℕ-suc-suc : suc n *ℕ suc k ≡ suc t
    *ℕ-suc-suc = refl

    posEq₀ : ((zero *ℕ suc k) +ℕ (suc n *ℕ zero)) ≡ zero
    posEq₀ =
      trans
        (cong (λ u → zero +ℕ u) (*ℕ-zero-right (suc n)))
        refl

    negEq₀ : ((zero *ℕ zero) +ℕ (suc n *ℕ suc k)) ≡ suc t
    negEq₀ =
      trans
        refl
        *ℕ-suc-suc

    mulNegForm : (-suc n) *ℤ (+suc k) ≡ -suc t
    mulNegForm =
      trans
        (normalizeℤ-cong posEq₀ negEq₀)
        refl

    -- RHS uses absℤ (-suc n) = +suc n.
    mulPosForm : (+suc n) *ℤ (+suc k) ≡ +suc t
    mulPosForm =
      trans
        (normalizeℤ-cong
          (trans
            (+ℕ-zero-right (suc n *ℕ suc k))
            *ℕ-suc-suc)
          (trans
            (cong (λ u → u +ℕ zero) (*ℕ-zero-right (suc n)))
            refl))
        refl

-- absℤ commutes with integer multiplication.
--
-- This is forced by exhaustive sign-case classification of ℤ.

absℤ-mul : (x y : ℤ) → absℤ (x *ℤ y) ≡ (absℤ x *ℤ absℤ y)
absℤ-mul 0ℤ y =
  let
    lhs : absℤ (0ℤ *ℤ y) ≡ absℤ 0ℤ
    lhs = cong absℤ (*ℤ-zero-left y)

    rhs : (absℤ 0ℤ *ℤ absℤ y) ≡ absℤ 0ℤ
    rhs = *ℤ-zero-left (absℤ y)
  in
  trans lhs (sym rhs)
absℤ-mul x 0ℤ =
  let
    lhs : absℤ (x *ℤ 0ℤ) ≡ absℤ 0ℤ
    lhs = cong absℤ (*ℤ-zero-right x)

    rhs : (absℤ x *ℤ absℤ 0ℤ) ≡ absℤ 0ℤ
    rhs =
      trans
        (cong (λ t → absℤ x *ℤ t) absℤ-zero)
        (*ℤ-zero-right (absℤ x))
  in
  trans lhs (sym rhs)
absℤ-mul (+suc m) (+suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n
  in
  trans (cong absℤ prodEq) (sym prodEq)
absℤ-mul (+suc m) (-suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans
    (cong absℤ (*ℤ-neg-right (+suc m) (+suc n)))
    (trans (absℤ-neg ((+suc m) *ℤ (+suc n))) absProd)
absℤ-mul (-suc m) (+suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans
    (cong absℤ (*ℤ-neg-left (+suc m) (+suc n)))
    (trans (absℤ-neg ((+suc m) *ℤ (+suc n))) absProd)
absℤ-mul (-suc m) (-suc n) =
  let
    mulEq : (-suc m) *ℤ (-suc n) ≡ (+suc m) *ℤ (+suc n)
    mulEq =
      trans
        (*ℤ-neg-right (negℤ (+suc m)) (+suc n))
        (trans
          (cong negℤ (*ℤ-neg-left (+suc m) (+suc n)))
          (negℤ-involutive ((+suc m) *ℤ (+suc n))))

    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans (cong absℤ mulEq) absProd

-- KEY LEMMA: If -b ≤ a and a ≤ b, then |a| ≤ b.
-- This is forced by exhaustive sign case classification.

absℤ-within-bound : (a b : ℤ) → (negℤ b) ≤ℤ a → a ≤ℤ b → absℤ a ≤ℤ b
absℤ-within-bound 0ℤ 0ℤ _ _ = tt
absℤ-within-bound 0ℤ (+suc n) _ _ = tt
absℤ-within-bound 0ℤ (-suc n) _ neg-bound = neg-bound  -- 0 ≤ℤ (-suc n) is vacuously false, so we can derive anything
absℤ-within-bound (+suc a) b _ upper = upper  -- |+suc a| = +suc a ≤ b
absℤ-within-bound (-suc a) b lower _ =
  -- |−suc a| = +suc a; we need +suc a ≤ b
  -- We have: -b ≤ -suc a
  -- i.e., -b ≤ℤ -suc a means negℤ (-suc a) ≤ℤ negℤ (negℤ b), i.e., +suc a ≤ℤ b
  ≤ℤ-resp-≡ʳ (negℤ-involutive b) (negℤ-antitone-≤ℤ lower)
