{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerOrderAdditionLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.IntegerAbsLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerOrderPreorderLaws

{-
CHAPTER 14Y′: Forced Additive Monotonicity For Nonnegative Integers

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 8 (≤ on ℕ), Chapter 14R (≤ℤ), Chapter 15A (fromℕℤ bridge)
AGDA MODULES: Disciplines.Math.IntegerOrderAdditionLaws
DEGREES OF FREEDOM ELIMINATED: missing order transport across + for nonnegative witnesses
-}

≤ℤ-fromℕℤ-+ℕ-monoˡ : {a b : ℕ} → a ≤ b → (c : ℕ) → fromℕℤ (c +ℕ a) ≤ℤ fromℕℤ (c +ℕ b)
≤ℤ-fromℕℤ-+ℕ-monoˡ p c = fromℕℤ-mono (≤-+ℕ-monoˡ p c)

≤ℤ-fromℕℤ-+ℕ-monoʳ : {a b : ℕ} → a ≤ b → (c : ℕ) → fromℕℤ (a +ℕ c) ≤ℤ fromℕℤ (b +ℕ c)
≤ℤ-fromℕℤ-+ℕ-monoʳ {a} {b} p c =
  let
    lhs : fromℕℤ (a +ℕ c) ≡ fromℕℤ (c +ℕ a)
    lhs = cong fromℕℤ (+ℕ-comm a c)

    rhs : fromℕℤ (b +ℕ c) ≡ fromℕℤ (c +ℕ b)
    rhs = cong fromℕℤ (+ℕ-comm b c)

    base : fromℕℤ (c +ℕ a) ≤ℤ fromℕℤ (c +ℕ b)
    base = ≤ℤ-fromℕℤ-+ℕ-monoˡ p c
  in
  ≤ℤ-resp-≡ˡ (sym lhs) (≤ℤ-resp-≡ʳ (sym rhs) base)

≤ℤ-+ℤ-monoʳ-nonneg : {m n : ℕ} → m ≤ n → (k : ℕ) → (fromℕℤ m +ℤ fromℕℤ k) ≤ℤ (fromℕℤ n +ℤ fromℕℤ k)
≤ℤ-+ℤ-monoʳ-nonneg {m} {n} p k =
  ≤ℤ-resp-≡ˡ (sym (fromℕℤ-+ℤ m k))
    (≤ℤ-resp-≡ʳ (sym (fromℕℤ-+ℤ n k))
      (≤ℤ-fromℕℤ-+ℕ-monoʳ p k))

-- Reflecting ≤ℤ back into nat-≤ for nonnegative integers.

≤ℤ-fromℕℤ-reflect : {m n : ℕ} → fromℕℤ m ≤ℤ fromℕℤ n → m ≤ n
≤ℤ-fromℕℤ-reflect {zero} {zero} _ = z≤n
≤ℤ-fromℕℤ-reflect {zero} {suc n} _ = z≤n
≤ℤ-fromℕℤ-reflect {suc m} {zero} ()
≤ℤ-fromℕℤ-reflect {suc m} {suc n} p = p

-- Nonnegativity eliminator: 0 ≤ z forces z to be of the fromℕℤ form.

0≤ℤ→fromℕℤ : (z : ℤ) → 0ℤ ≤ℤ z → Σ ℕ (λ n → z ≡ fromℕℤ n)
0≤ℤ→fromℕℤ 0ℤ _ = zero , refl
0≤ℤ→fromℕℤ (+suc n) _ = suc n , refl
0≤ℤ→fromℕℤ (-suc n) ()

-- Monotonicity of +ℤ for nonnegative-fromℕℤ arguments in both slots.

≤ℤ-+ℤ-mono-nonneg₂ : {m m' n n' : ℕ} → m ≤ m' → n ≤ n' →
  (fromℕℤ m +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n')
≤ℤ-+ℤ-mono-nonneg₂ {m} {m'} {n} {n'} m≤m' n≤n' =
  let
    step₁ : (fromℕℤ m +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n)
    step₁ = ≤ℤ-+ℤ-monoʳ-nonneg m≤m' n

    step₂ : (fromℕℤ m' +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n')
    step₂ =
      ≤ℤ-resp-≡ˡ (+ℤ-comm (fromℕℤ n) (fromℕℤ m'))
        (≤ℤ-resp-≡ʳ (+ℤ-comm (fromℕℤ n') (fromℕℤ m'))
          (≤ℤ-+ℤ-monoʳ-nonneg n≤n' m'))
  in
  ≤ℤ-trans step₁ step₂

-- Transport between normalizeℤ order and the forced cross-sum inequality on ℕ.

normalize≤→cross : (a b c d : ℕ) → normalizeℤ a b ≤ℤ normalizeℤ c d → (a +ℕ d) ≤ (c +ℕ b)
normalize≤→cross (suc a) (suc b) c d p =
  let ih : (a +ℕ d) ≤ (c +ℕ b)
      ih = normalize≤→cross a b c d p

      lifted : (suc (a +ℕ d)) ≤ (suc (c +ℕ b))
      lifted = s≤s ih

      rhsEq : (c +ℕ suc b) ≡ suc (c +ℕ b)
      rhsEq = +ℕ-suc-right c b
  in
  subst (λ t → (suc a +ℕ d) ≤ t) (sym rhsEq) lifted
normalize≤→cross a b (suc c) (suc d) p =
  let ih : (a +ℕ d) ≤ (c +ℕ b)
      ih = normalize≤→cross a b c d p

      lifted : (suc (a +ℕ d)) ≤ (suc (c +ℕ b))
      lifted = s≤s ih

      lhsEq : (a +ℕ suc d) ≡ suc (a +ℕ d)
      lhsEq = +ℕ-suc-right a d
  in
  subst (λ t → t ≤ (suc c +ℕ b)) (sym lhsEq) lifted

normalize≤→cross zero zero zero zero _ = z≤n
normalize≤→cross zero zero (suc c) zero _ = z≤n
normalize≤→cross zero zero zero (suc d) ()
normalize≤→cross (suc a) zero zero zero ()
normalize≤→cross (suc a) zero (suc c) zero p =
  let
    lhsEq : (suc a +ℕ zero) ≡ suc a
    lhsEq = cong suc (+ℕ-zero-right a)

    rhsEq : (suc c +ℕ zero) ≡ suc c
    rhsEq = cong suc (+ℕ-zero-right c)
  in
  subst (λ t → t ≤ (suc c +ℕ zero)) (sym lhsEq)
    (subst (λ t → (suc a) ≤ t) (sym rhsEq) p)
normalize≤→cross (suc a) zero zero (suc d) ()
normalize≤→cross zero (suc b) zero zero _ = z≤n
normalize≤→cross zero (suc b) (suc c) zero _ = z≤n
normalize≤→cross zero (suc b) zero (suc d) p = p

cross→normalize≤ : (a b c d : ℕ) → (a +ℕ d) ≤ (c +ℕ b) → normalizeℤ a b ≤ℤ normalizeℤ c d
cross→normalize≤ (suc a) (suc b) c d p with subst (λ t → (suc a +ℕ d) ≤ t) (+ℕ-suc-right c b) p
... | s≤s q = cross→normalize≤ a b c d q
cross→normalize≤ a b (suc c) (suc d) p with subst (λ t → t ≤ (suc c +ℕ b)) (+ℕ-suc-right a d) p
... | s≤s q = cross→normalize≤ a b c d q

cross→normalize≤ zero zero zero zero _ = tt
cross→normalize≤ zero zero (suc c) zero _ = tt
cross→normalize≤ zero zero zero (suc d) ()
cross→normalize≤ (suc a) zero zero zero ()
cross→normalize≤ (suc a) zero (suc c) zero p =
  let
    lhsEq : (suc a +ℕ zero) ≡ suc a
    lhsEq = cong suc (+ℕ-zero-right a)

    rhsEq : (suc c +ℕ zero) ≡ suc c
    rhsEq = cong suc (+ℕ-zero-right c)

    p' : (suc a) ≤ (suc c)
    p' =
      subst (λ t → t ≤ (suc c)) lhsEq
        (subst (λ t → (suc a +ℕ zero) ≤ t) rhsEq p)
  in
  p'
cross→normalize≤ (suc a) zero zero (suc d) ()
cross→normalize≤ zero (suc b) zero zero _ = tt
cross→normalize≤ zero (suc b) (suc c) zero _ = tt
cross→normalize≤ zero (suc b) zero (suc d) p = p

-- Monotonicity of +ℤ (general, forced by the normalize/cancel structure).

≤ℤ-+ℤ-monoʳ : {x y : ℤ} → x ≤ℤ y → (z : ℤ) → (x +ℤ z) ≤ℤ (y +ℤ z)
≤ℤ-+ℤ-monoʳ {x} {y} x≤y z =
  let
    px = toPairℤ x
    py = toPairℤ y
    pz = toPairℤ z

    ax = pos px
    bx = neg px
    ay = pos py
    by = neg py
    az = pos pz
    bz = neg pz

    x≤y' : normalizeℤ ax bx ≤ℤ normalizeℤ ay by
    x≤y' =
      ≤ℤ-resp-≡ʳ (sym (from-toPairℤ y))
        (≤ℤ-resp-≡ˡ (sym (from-toPairℤ x)) x≤y)

    crossXY : (ax +ℕ by) ≤ (ay +ℕ bx)
    crossXY = normalize≤→cross ax bx ay by x≤y'

    k : ℕ
    k = az +ℕ bz

    base : (k +ℕ (ax +ℕ by)) ≤ (k +ℕ (ay +ℕ bx))
    base = ≤-+ℕ-monoˡ crossXY k

    lhsEq : ((ax +ℕ az) +ℕ (by +ℕ bz)) ≡ (k +ℕ (ax +ℕ by))
    lhsEq =
      trans
        (shuffleℕ ax az by bz)
        (+ℕ-comm (ax +ℕ by) k)

    rhsEq : ((ay +ℕ az) +ℕ (bx +ℕ bz)) ≡ (k +ℕ (ay +ℕ bx))
    rhsEq =
      trans
        (shuffleℕ ay az bx bz)
        (+ℕ-comm (ay +ℕ bx) k)

    sumCross : ((ax +ℕ az) +ℕ (by +ℕ bz)) ≤ ((ay +ℕ az) +ℕ (bx +ℕ bz))
    sumCross =
      subst (λ t → t ≤ ((ay +ℕ az) +ℕ (bx +ℕ bz))) (sym lhsEq)
        (subst (λ t → (k +ℕ (ax +ℕ by)) ≤ t) (sym rhsEq) base)
  in
  cross→normalize≤ (ax +ℕ az) (bx +ℕ bz) (ay +ℕ az) (by +ℕ bz) sumCross

≤ℤ-+ℤ-monoˡ : {x y : ℤ} → x ≤ℤ y → (z : ℤ) → (z +ℤ x) ≤ℤ (z +ℤ y)
≤ℤ-+ℤ-monoˡ {x} {y} x≤y z =
  ≤ℤ-resp-≡ˡ (+ℤ-comm x z)
    (≤ℤ-resp-≡ʳ (+ℤ-comm y z)
      (≤ℤ-+ℤ-monoʳ x≤y z))

≤ℤ-+ℤ-mono : {x y u v : ℤ} → x ≤ℤ y → u ≤ℤ v → (x +ℤ u) ≤ℤ (y +ℤ v)
≤ℤ-+ℤ-mono {x} {y} {u} {v} x≤y u≤v =
  ≤ℤ-trans (≤ℤ-+ℤ-monoʳ x≤y u) (≤ℤ-+ℤ-monoˡ u≤v y)

≤ℤ-+ℤ-cancelʳ : (x y z : ℤ) → x ≤ℤ (z +ℤ y) → (x +ℤ negℤ y) ≤ℤ z
≤ℤ-+ℤ-cancelʳ x y z p =
  let
    step : (x +ℤ negℤ y) ≤ℤ ((z +ℤ y) +ℤ negℤ y)
    step = ≤ℤ-+ℤ-monoʳ p (negℤ y)

    rhsEq : ((z +ℤ y) +ℤ negℤ y) ≡ z
    rhsEq =
      trans
        (+ℤ-assoc z y (negℤ y))
        (trans
          (cong (λ t → z +ℤ t) (+ℤ-inv-right y))
          (+ℤ-zero-right z))
  in
  ≤ℤ-resp-≡ʳ rhsEq step

fromℕℤ-mul-⁺ : (n : ℕ) → (d : ℕ⁺) → (fromℕℤ n *ℤ ⁺toℤ d) ≡ fromℕℤ (n *ℕ ⁺toℕ d)
fromℕℤ-mul-⁺ zero d =
  trans
    (*ℤ-zero-left (⁺toℤ d))
    (cong fromℕℤ (sym (*ℕ-zero-left (⁺toℕ d))))
fromℕℤ-mul-⁺ (suc n) (mkℕ⁺ k) =
  let
    natForm : (suc n *ℕ suc k) ≡ suc (k +ℕ (n *ℕ suc k))
    natForm = refl

    rhs : fromℕℤ (suc n *ℕ suc k) ≡ +suc (k +ℕ (n *ℕ suc k))
    rhs = cong fromℕℤ natForm
  in
  trans
    (*ℤ-pos-pos-eq n k)
    (sym rhs)

oneℤ<twoTimes-pos : (z : ℤ) → 0ℤ <ℤ z → oneℤ <ℤ (z +ℤ z)
oneℤ<twoTimes-pos z zpos with 0<ℤ→pos z zpos
... | (m , z≡) =
  <ℤ-resp-≡ʳ (cong (λ t → t +ℤ t) (sym z≡)) (lePart , notRev)
  where
    twoTimes : (+suc m) +ℤ (+suc m) ≡ +suc (m +ℕ suc m)
    twoTimes =
      trans
        (fromℕℤ-+ℤ (suc m) (suc m))
        (cong fromℕℤ refl)

    lePart : oneℤ ≤ℤ ((+suc m) +ℤ (+suc m))
    lePart =
      let
        lePos : oneℤ ≤ℤ (+suc (m +ℕ suc m))
        lePos = s≤s z≤n
      in
        subst (λ t → oneℤ ≤ℤ t) (sym twoTimes) lePos

    no-suc≤zero : {t : ℕ} → suc t ≤ zero → ⊥
    no-suc≤zero ()

    impossible : (+suc (m +ℕ suc m)) ≤ℤ oneℤ → ⊥
    impossible (s≤s pNat) =
      let
        pNat' : suc (m +ℕ m) ≤ zero
        pNat' = subst (λ t → t ≤ zero) (+ℕ-suc-right m m) pNat
      in
      no-suc≤zero pNat'

    notRev : ((+suc m) +ℤ (+suc m)) ≰ℤ oneℤ
    notRev q = impossible (subst (λ t → t ≤ℤ oneℤ) twoTimes q)
