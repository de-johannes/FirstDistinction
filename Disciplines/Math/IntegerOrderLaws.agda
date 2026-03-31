{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerOrderLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.NatPlus

{-
CHAPTER 14W: Forced Laws Of Integer Order (Transport + Positivity)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14R (≤ℤ, <ℤ), Chapter 14M (*ℤ), Chapter 14Q (ℕ⁺)
AGDA MODULES: Disciplines.Math.IntegerOrderLaws
DEGREES OF FREEDOM ELIMINATED: missing transport and positivity closure needed for ℚ-order reasoning
-}

-- Transport of ≤ℤ along definitional equality.

≤ℤ-resp-≡ˡ : {x y z : ℤ} → x ≡ y → x ≤ℤ z → y ≤ℤ z
≤ℤ-resp-≡ˡ refl p = p

≤ℤ-resp-≡ʳ : {x y z : ℤ} → y ≡ z → x ≤ℤ y → x ≤ℤ z
≤ℤ-resp-≡ʳ refl p = p

<ℤ-resp-≡ˡ : {x y z : ℤ} → x ≡ y → x <ℤ z → y <ℤ z
<ℤ-resp-≡ˡ refl p = p

<ℤ-resp-≡ʳ : {x y z : ℤ} → y ≡ z → x <ℤ y → x <ℤ z
<ℤ-resp-≡ʳ refl p = p

-- Negation reverses order (antitone).

negℤ-antitone-≤ℤ : {x y : ℤ} → x ≤ℤ y → (negℤ y) ≤ℤ (negℤ x)
negℤ-antitone-≤ℤ {0ℤ} {0ℤ} _ = tt
negℤ-antitone-≤ℤ {0ℤ} {+suc n} _ = tt
negℤ-antitone-≤ℤ {0ℤ} { -suc n } ()
negℤ-antitone-≤ℤ {+suc m} {0ℤ} ()
negℤ-antitone-≤ℤ {+suc m} {+suc n} p = p
negℤ-antitone-≤ℤ {+suc m} { -suc n } ()
negℤ-antitone-≤ℤ { -suc m } {0ℤ} _ = tt
negℤ-antitone-≤ℤ { -suc m } {+suc n} _ = tt
negℤ-antitone-≤ℤ { -suc m } { -suc n } p = p

-- From 0 < z we can force z to be in the positive constructor case.

0<ℤ→pos : (z : ℤ) → 0ℤ <ℤ z → Σ ℕ (λ n → z ≡ +suc n)
0<ℤ→pos 0ℤ (p≤ , p≰) = ⊥-elim (p≰ p≤)
0<ℤ→pos (+suc n) _ = n , refl
0<ℤ→pos (-suc n) (() , _)

0<ℤ-pos : (n : ℕ) → 0ℤ <ℤ (+suc n)
0<ℤ-pos n = tt , (λ p → p)

-- Concrete multiplication of positive constructors stays positive.

*ℤ-pos-pos-eq : (m n : ℕ) → (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
*ℤ-pos-pos-eq m n =
  let posStep : (suc m *ℕ suc n) +ℕ (zero *ℕ zero) ≡ suc (n +ℕ (m *ℕ suc n))
      posStep =
        trans
          (cong (λ t → (suc m *ℕ suc n) +ℕ t) (*ℕ-zero-left zero))
          (trans
            (+ℕ-zero-right (suc m *ℕ suc n))
            refl)

      negStep : (suc m *ℕ zero) +ℕ (zero *ℕ suc n) ≡ zero
      negStep =
        trans
          (cong (λ t → t +ℕ (zero *ℕ suc n)) (*ℕ-zero-right (suc m)))
          (trans
            (cong (λ t → zero +ℕ t) (*ℕ-zero-left (suc n)))
            refl)
  in
  trans
    (normalizeℤ-cong posStep negStep)
    refl

0<ℤ-mul-pos-right : (z : ℤ) → (d : ℕ⁺) → 0ℤ <ℤ z → 0ℤ <ℤ (z *ℤ ⁺toℤ d)
0<ℤ-mul-pos-right z (mkℕ⁺ k) zpos =
  let zShape = 0<ℤ→pos z zpos
      m = fst zShape
      z≡ = snd zShape

      prod≡ : z *ℤ (+suc k) ≡ (+suc m) *ℤ (+suc k)
      prod≡ = cong (λ t → t *ℤ (+suc k)) z≡

      basePos : 0ℤ <ℤ ((+suc m) *ℤ (+suc k))
      basePos =
        <ℤ-resp-≡ʳ (sym (*ℤ-pos-pos-eq m k)) (0<ℤ-pos (k +ℕ (m *ℕ suc k)))

  in
  <ℤ-resp-≡ʳ (sym prod≡) basePos

-- Multiplication by a positive ℕ⁺ factor preserves ≤ℤ.

*ℤ-neg-pos-eq : (m k : ℕ) → (-suc m) *ℤ (+suc k) ≡ -suc (k +ℕ (m *ℕ suc k))
*ℤ-neg-pos-eq m k =
  trans
    (*ℤ-neg-left (+suc m) (+suc k))
    (trans
      (cong negℤ (*ℤ-pos-pos-eq m k))
      refl)

≤ℤ-mul-pos-right : (x y : ℤ) → (d : ℕ⁺) → x ≤ℤ y → (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
≤ℤ-mul-pos-right 0ℤ 0ℤ (mkℕ⁺ k) _ =
  subst
    (λ t → t ≤ℤ t)
    (sym (*ℤ-zero-left (+suc k)))
    tt
≤ℤ-mul-pos-right 0ℤ (+suc n) (mkℕ⁺ k) _ =
  let
    t = k +ℕ (n *ℕ suc k)
    eqL : 0ℤ ≡ 0ℤ *ℤ (+suc k)
    eqL = sym (*ℤ-zero-left (+suc k))

    eqR : (+suc t) ≡ ((+suc n) *ℤ (+suc k))
    eqR = sym (*ℤ-pos-pos-eq n k)

    base : 0ℤ ≤ℤ (+suc t)
    base = tt
  in
  subst (λ r → (0ℤ *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ (+suc t)) eqL base)
≤ℤ-mul-pos-right 0ℤ (-suc n) d ()
≤ℤ-mul-pos-right (+suc m) 0ℤ d ()
≤ℤ-mul-pos-right (+suc m) (+suc n) (mkℕ⁺ k) (s≤s p) =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    mulMono : (m *ℕ suc k) ≤ (n *ℕ suc k)
    mulMono = ≤-*ℕ-monoʳ p (suc k)

    addMono : t₁ ≤ t₂
    addMono = ≤-+ℕ-monoˡ mulMono k

    base : (+suc t₁) ≤ℤ (+suc t₂)
    base = s≤s addMono
  in
  ≤ℤ-resp-≡ˡ (sym (*ℤ-pos-pos-eq m k))
    (≤ℤ-resp-≡ʳ (sym (*ℤ-pos-pos-eq n k)) base)
≤ℤ-mul-pos-right (+suc m) (-suc n) d ()
≤ℤ-mul-pos-right (-suc m) 0ℤ (mkℕ⁺ k) _ =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    eqL : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    eqL = sym (*ℤ-neg-pos-eq m k)

    eqR : 0ℤ ≡ (0ℤ *ℤ (+suc k))
    eqR = sym (*ℤ-zero-left (+suc k))

    base : (-suc t₁) ≤ℤ 0ℤ
    base = tt
  in
  subst (λ r → ((-suc m) *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ 0ℤ) eqL base)
≤ℤ-mul-pos-right (-suc m) (+suc n) (mkℕ⁺ k) _ =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)
    eqL : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    eqL = sym (*ℤ-neg-pos-eq m k)

    eqR : (+suc t₂) ≡ ((+suc n) *ℤ (+suc k))
    eqR = sym (*ℤ-pos-pos-eq n k)

    base : (-suc t₁) ≤ℤ (+suc t₂)
    base = tt
  in
  subst (λ r → ((-suc m) *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ (+suc t₂)) eqL base)
≤ℤ-mul-pos-right (-suc m) (-suc n) (mkℕ⁺ k) (s≤s p) =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    mulMono : (n *ℕ suc k) ≤ (m *ℕ suc k)
    mulMono = ≤-*ℕ-monoʳ p (suc k)

    addMono : t₂ ≤ t₁
    addMono = ≤-+ℕ-monoˡ mulMono k

    base : (-suc t₁) ≤ℤ (-suc t₂)
    base = s≤s addMono
  in
  ≤ℤ-resp-≡ˡ (sym (*ℤ-neg-pos-eq m k))
    (≤ℤ-resp-≡ʳ (sym (*ℤ-neg-pos-eq n k)) base)

-- Cancellation: if (x·d) ≤ (y·d) for positive d, then x ≤ y.

≤ℤ-mul-pos-cancel-right : (x y : ℤ) → (d : ℕ⁺) → (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d) → x ≤ℤ y
≤ℤ-mul-pos-cancel-right 0ℤ 0ℤ (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right 0ℤ (+suc n) (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right 0ℤ (-suc n) (mkℕ⁺ k) p =
  let
    t : ℕ
    t = k +ℕ (n *ℕ suc k)

    rhsEq : ((-suc n) *ℤ (+suc k)) ≡ (-suc t)
    rhsEq = *ℤ-neg-pos-eq n k

    p0 : (0ℤ *ℤ (+suc k)) ≤ℤ ((-suc n) *ℤ (+suc k))
    p0 = p

    p1 : 0ℤ ≤ℤ ((-suc n) *ℤ (+suc k))
    p1 = subst (λ s → s ≤ℤ ((-suc n) *ℤ (+suc k))) (*ℤ-zero-left (+suc k)) p0

    p' : 0ℤ ≤ℤ (-suc t)
    p' = subst (λ r → 0ℤ ≤ℤ r) rhsEq p1
  in
  ⊥-elim p'
≤ℤ-mul-pos-cancel-right (+suc m) 0ℤ (mkℕ⁺ k) p =
  let
    t = k +ℕ (m *ℕ suc k)
    lhsPos : ((+suc m) *ℤ (+suc k)) ≡ +suc t
    lhsPos = *ℤ-pos-pos-eq m k

    p0 : ((+suc m) *ℤ (+suc k)) ≤ℤ (0ℤ *ℤ (+suc k))
    p0 = p

    p1 : ((+suc m) *ℤ (+suc k)) ≤ℤ 0ℤ
    p1 = subst (λ r → ((+suc m) *ℤ (+suc k)) ≤ℤ r) (*ℤ-zero-left (+suc k)) p0

    p' : (+suc t) ≤ℤ 0ℤ
    p' = subst (λ s → s ≤ℤ 0ℤ) lhsPos p1
  in
  ⊥-elim p'
≤ℤ-mul-pos-cancel-right (+suc m) (+suc n) (mkℕ⁺ k) p =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    lhsEq : (+suc t₁) ≡ ((+suc m) *ℤ (+suc k))
    lhsEq = sym (*ℤ-pos-pos-eq m k)

    rhsEq : (+suc t₂) ≡ ((+suc n) *ℤ (+suc k))
    rhsEq = sym (*ℤ-pos-pos-eq n k)

    step : (+suc t₁) ≤ℤ (+suc t₂)
    step =
      ≤ℤ-resp-≡ˡ (sym lhsEq)
        (≤ℤ-resp-≡ʳ (sym rhsEq) p)

    natStep : suc t₁ ≤ suc t₂
    natStep = step

    t₁≤t₂ : t₁ ≤ t₂
    t₁≤t₂ = ≤-+ℕ-cancelˡ (suc zero) t₁ t₂ natStep

    mulPart : (m *ℕ suc k) ≤ (n *ℕ suc k)
    mulPart = ≤-+ℕ-cancelˡ k (m *ℕ suc k) (n *ℕ suc k) t₁≤t₂

    base : m ≤ n
    base = ≤-*ℕ-cancelʳ-suc k mulPart
  in
  s≤s base
≤ℤ-mul-pos-cancel-right (+suc m) (-suc n) (mkℕ⁺ k) p =
  let
    t₁ : ℕ
    t₁ = k +ℕ (m *ℕ suc k)

    t₂ : ℕ
    t₂ = k +ℕ (n *ℕ suc k)

    lhsPos : ((+suc m) *ℤ (+suc k)) ≡ (+suc t₁)
    lhsPos = *ℤ-pos-pos-eq m k

    rhsNeg : ((-suc n) *ℤ (+suc k)) ≡ (-suc t₂)
    rhsNeg = *ℤ-neg-pos-eq n k

    p1 : ((+suc m) *ℤ (+suc k)) ≤ℤ (-suc t₂)
    p1 = ≤ℤ-resp-≡ʳ rhsNeg p

    p2 : (+suc t₁) ≤ℤ (-suc t₂)
    p2 = subst (λ s → s ≤ℤ (-suc t₂)) lhsPos p1
  in
  ⊥-elim p2
≤ℤ-mul-pos-cancel-right (-suc m) 0ℤ (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right (-suc m) (+suc n) (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right (-suc m) (-suc n) (mkℕ⁺ k) p =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    lhsEq : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    lhsEq = sym (*ℤ-neg-pos-eq m k)

    rhsEq : (-suc t₂) ≡ ((-suc n) *ℤ (+suc k))
    rhsEq = sym (*ℤ-neg-pos-eq n k)

    step : (-suc t₁) ≤ℤ (-suc t₂)
    step =
      ≤ℤ-resp-≡ˡ (sym lhsEq)
        (≤ℤ-resp-≡ʳ (sym rhsEq) p)

    natStep : suc t₂ ≤ suc t₁
    natStep = step

    t₂≤t₁ : t₂ ≤ t₁
    t₂≤t₁ = ≤-+ℕ-cancelˡ (suc zero) t₂ t₁ natStep

    mulPart : (n *ℕ suc k) ≤ (m *ℕ suc k)
    mulPart = ≤-+ℕ-cancelˡ k (n *ℕ suc k) (m *ℕ suc k) t₂≤t₁

    base : n ≤ m
    base = ≤-*ℕ-cancelʳ-suc k mulPart
  in
  s≤s base

-- Multiplication by a nonnegative (0 or positive) right factor preserves ≤ℤ.

≤ℤ-mul-nonneg-right : (x y z : ℤ) → x ≤ℤ y → 0ℤ ≤ℤ z → (x *ℤ z) ≤ℤ (y *ℤ z)
≤ℤ-mul-nonneg-right x y 0ℤ x≤y _ =
  subst (λ t → t ≤ℤ (y *ℤ 0ℤ)) (sym (*ℤ-zero-right x))
    (subst (λ t → 0ℤ ≤ℤ t) (sym (*ℤ-zero-right y)) tt)
≤ℤ-mul-nonneg-right x y (+suc k) x≤y _ =
  let
    d : ℕ⁺
    d = mkℕ⁺ k

    step : (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
    step = ≤ℤ-mul-pos-right x y d x≤y

    lhs : (x *ℤ (+suc k)) ≡ (x *ℤ ⁺toℤ d)
    lhs = refl

    rhs : (y *ℤ (+suc k)) ≡ (y *ℤ ⁺toℤ d)
    rhs = refl
  in
  ≤ℤ-resp-≡ˡ (sym lhs) (≤ℤ-resp-≡ʳ (sym rhs) step)
≤ℤ-mul-nonneg-right x y (-suc k) _ ()

<ℤ-mul-pos-right : {x y : ℤ} → (d : ℕ⁺) → x <ℤ y → (x *ℤ ⁺toℤ d) <ℤ (y *ℤ ⁺toℤ d)
<ℤ-mul-pos-right {x} {y} d (x≤y , y≰x) =
  let
    lePart : (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
    lePart = ≤ℤ-mul-pos-right x y d x≤y

    notRev : (y *ℤ ⁺toℤ d) ≰ℤ (x *ℤ ⁺toℤ d)
    notRev ydx≤xdx = y≰x (≤ℤ-mul-pos-cancel-right y x d ydx≤xdx)
  in
  lePart , notRev
