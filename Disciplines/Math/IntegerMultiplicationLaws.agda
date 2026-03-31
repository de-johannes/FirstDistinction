{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegerMultiplicationLaws where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.NatMultiplicationLaws

{-
CHAPTER 14P: Forced Laws Of Integer Multiplication

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14M (*ℤ via Pairℕ-mul), Chapter 14O (*ℕ laws), Chapter 14F (+ℤ laws)
AGDA MODULES: Disciplines.Math.IntegerMultiplicationLaws
DEGREES OF FREEDOM ELIMINATED: ambiguous interaction of *ℤ with +ℤ needed for operator spans
-}

-- This module is reserved for a future forced development of distributivity/associativity
-- laws for `_*ℤ_` as defined in Chapter 14M.

-- Pair-level addition (componentwise) and normalization, used to bridge `normalizeℤ`.

Pairℕ-add : Pairℕ → Pairℕ → Pairℕ
Pairℕ-add p q = ⟪ (pos p +ℕ pos q) , (neg p +ℕ neg q) ⟫

normalizePair : Pairℕ → Pairℕ
normalizePair ⟪ zero  , zero  ⟫ = ⟪ zero , zero ⟫
normalizePair ⟪ suc a , zero  ⟫ = ⟪ suc a , zero ⟫
normalizePair ⟪ zero  , suc b ⟫ = ⟪ zero , suc b ⟫
normalizePair ⟪ suc a , suc b ⟫ = normalizePair ⟪ a , b ⟫

normalizePair-right0 : (x : ℕ) → normalizePair ⟪ x , zero ⟫ ≡ ⟪ x , zero ⟫
normalizePair-right0 zero = refl
normalizePair-right0 (suc a) = refl

normalizePair-left0 : (y : ℕ) → normalizePair ⟪ zero , y ⟫ ≡ ⟪ zero , y ⟫
normalizePair-left0 zero = refl
normalizePair-left0 (suc b) = refl

fromPair-normalizePair : (p : Pairℕ) → fromPairℤ (normalizePair p) ≡ fromPairℤ p
fromPair-normalizePair ⟪ zero  , zero  ⟫ = refl
fromPair-normalizePair ⟪ suc a , zero  ⟫ = refl
fromPair-normalizePair ⟪ zero  , suc b ⟫ = refl
fromPair-normalizePair ⟪ suc a , suc b ⟫ = fromPair-normalizePair ⟪ a , b ⟫

toPair-normalizeℤ : (a b : ℕ) → toPairℤ (normalizeℤ a b) ≡ normalizePair ⟪ a , b ⟫
toPair-normalizeℤ zero zero = refl
toPair-normalizeℤ (suc a) zero = refl
toPair-normalizeℤ zero (suc b) = refl
toPair-normalizeℤ (suc a) (suc b) = toPair-normalizeℤ a b

toPair-fromPair : (p : Pairℕ) → toPairℤ (fromPairℤ p) ≡ normalizePair p
toPair-fromPair ⟪ a , b ⟫ = toPair-normalizeℤ a b

-- Pairℕ-mul distributes over Pairℕ-add (componentwise), forced by *ℕ distributivity.

Pairℕ-mul-distrib-right-add : (p q r : Pairℕ) →
  Pairℕ-mul p (Pairℕ-add q r) ≡ Pairℕ-add (Pairℕ-mul p q) (Pairℕ-mul p r)
Pairℕ-mul-distrib-right-add p q r =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  let e = pos r in
  let f = neg r in
  pair-ext
    (pos-proof a b c d e f)
    (neg-proof a b c d e f)
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

    pos-proof : (a b c d e f : ℕ) →
      ((a *ℕ (c +ℕ e)) +ℕ (b *ℕ (d +ℕ f)))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ ((a *ℕ e) +ℕ (b *ℕ f)))
    pos-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ (b *ℕ (d +ℕ f))) (*ℕ-distrib-right-+ℕ a c e))
        (trans
          (cong (λ t → (a *ℕ c +ℕ a *ℕ e) +ℕ t) (*ℕ-distrib-right-+ℕ b d f))
          (shuffleℕ (a *ℕ c) (a *ℕ e) (b *ℕ d) (b *ℕ f)))

    neg-proof : (a b c d e f : ℕ) →
      ((a *ℕ (d +ℕ f)) +ℕ (b *ℕ (c +ℕ e)))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ ((a *ℕ f) +ℕ (b *ℕ e)))
    neg-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ (b *ℕ (c +ℕ e))) (*ℕ-distrib-right-+ℕ a d f))
        (trans
          (cong (λ t → (a *ℕ d +ℕ a *ℕ f) +ℕ t) (*ℕ-distrib-right-+ℕ b c e))
          (shuffleℕ (a *ℕ d) (a *ℕ f) (b *ℕ c) (b *ℕ e)))

-- Minimal ℤ laws needed for operator-span composition.

*ℕ-one-left : (n : ℕ) → oneNat *ℕ n ≡ n
*ℕ-one-left n = +ℕ-zero-right n

*ℤ-one-left : (x : ℤ) → oneℤ *ℤ x ≡ x
*ℤ-one-left 0ℤ = refl
*ℤ-one-left (+suc n) =
  normalizeℤ-cong
    (trans
      (+ℕ-zero-right (oneNat *ℕ suc n))
      (*ℕ-one-left (suc n)))
    (trans
      (+ℕ-zero-right (oneNat *ℕ zero))
      (*ℕ-zero-right oneNat))
*ℤ-one-left (-suc n) =
  normalizeℤ-cong
    (trans
      (+ℕ-zero-right (oneNat *ℕ zero))
      (*ℕ-zero-right oneNat))
    (trans
      (+ℕ-zero-right (oneNat *ℕ suc n))
      (*ℕ-one-left (suc n)))

-- Pair-level left distributivity.

Pairℕ-mul-distrib-left-add : (p q r : Pairℕ) →
  Pairℕ-mul (Pairℕ-add p q) r ≡ Pairℕ-add (Pairℕ-mul p r) (Pairℕ-mul q r)
Pairℕ-mul-distrib-left-add p q r =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  let e = pos r in
  let f = neg r in
  pair-ext
    (pos-proof a b c d e f)
    (neg-proof a b c d e f)
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

    pos-proof : (a b c d e f : ℕ) →
      (((a +ℕ c) *ℕ e) +ℕ ((b +ℕ d) *ℕ f))
        ≡
      (((a *ℕ e) +ℕ (b *ℕ f)) +ℕ ((c *ℕ e) +ℕ (d *ℕ f)))
    pos-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ ((b +ℕ d) *ℕ f)) (*ℕ-distrib-left-+ℕ a c e))
        (trans
          (cong (λ t → ((a *ℕ e) +ℕ (c *ℕ e)) +ℕ t) (*ℕ-distrib-left-+ℕ b d f))
          (shuffleℕ (a *ℕ e) (c *ℕ e) (b *ℕ f) (d *ℕ f)))

    neg-proof : (a b c d e f : ℕ) →
      (((a +ℕ c) *ℕ f) +ℕ ((b +ℕ d) *ℕ e))
        ≡
      (((a *ℕ f) +ℕ (b *ℕ e)) +ℕ ((c *ℕ f) +ℕ (d *ℕ e)))
    neg-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ ((b +ℕ d) *ℕ e)) (*ℕ-distrib-left-+ℕ a c f))
        (trans
          (cong (λ t → ((a *ℕ f) +ℕ (c *ℕ f)) +ℕ t) (*ℕ-distrib-left-+ℕ b d e))
          (shuffleℕ (a *ℕ f) (c *ℕ f) (b *ℕ e) (d *ℕ e)))

-- Helper: `normalizePair` is stable under adding the same `k` to both components.

normalizePair-addDiag : (p : Pairℕ) → (k : ℕ) →
  normalizePair (Pairℕ-add p ⟪ k , k ⟫) ≡ normalizePair p
normalizePair-addDiag ⟪ a , b ⟫ zero =
  cong normalizePair (pair-ext (+ℕ-zero-right a) (+ℕ-zero-right b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
normalizePair-addDiag ⟪ a , b ⟫ (suc k) =
  trans
    (cong normalizePair (pair-ext (+ℕ-suc-right a k) (+ℕ-suc-right b k)))
    (trans
      refl
      (normalizePair-addDiag ⟪ a , b ⟫ k))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

-- Right-succ lemma for *ℕ via distributivity over +ℕ (suc n = n + 1).

+ℕ-one-right : (n : ℕ) → n +ℕ suc zero ≡ suc n
+ℕ-one-right n = trans (+ℕ-comm n (suc zero)) refl

*ℕ-suc-right : (a n : ℕ) → a *ℕ suc n ≡ (a *ℕ n) +ℕ a
*ℕ-suc-right a n =
  trans
    (cong (λ t → a *ℕ t) (sym (+ℕ-one-right n)))
    (trans
      (*ℕ-distrib-right-+ℕ a n (suc zero))
      (cong (λ t → (a *ℕ n) +ℕ t) (*ℕ-one-right a)))

*ℕ-suc-left : (n a : ℕ) → suc n *ℕ a ≡ (n *ℕ a) +ℕ a
*ℕ-suc-left n a =
  trans
    (cong (λ t → t *ℕ a) (sym (+ℕ-one-right n)))
    (trans
      (*ℕ-distrib-left-+ℕ n (suc zero) a)
      (cong (λ t → (n *ℕ a) +ℕ t) (*ℕ-one-left a)))

-- Cancelling a common successor in the right multiplicand only adds a diagonal pair in the product,
-- which is eliminated by `normalizePair`.

Pairℕ-mul-cancelRight : (p : Pairℕ) → (c d : ℕ) →
  normalizePair (Pairℕ-mul p ⟪ suc c , suc d ⟫) ≡ normalizePair (Pairℕ-mul p ⟪ c , d ⟫)
Pairℕ-mul-cancelRight p c d =
  let a = pos p in
  let b = neg p in
  -- Show the product differs by adding (a+b) on both components.
  trans
    (cong normalizePair (pair-ext (pos-step a b c d) (neg-step a b c d)))
    (normalizePair-addDiag (Pairℕ-mul p ⟪ c , d ⟫) (a +ℕ b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

    pos-step : (a b c d : ℕ) →
      ((a *ℕ suc c) +ℕ (b *ℕ suc d))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ (a +ℕ b))
    pos-step a b c d =
      trans
        (cong (λ t → t +ℕ (b *ℕ suc d)) (*ℕ-suc-right a c))
        (trans
          (cong (λ t → ((a *ℕ c) +ℕ a) +ℕ t) (*ℕ-suc-right b d))
          (trans
            (shuffleℕ (a *ℕ c) a (b *ℕ d) b)
            refl))

    neg-step : (a b c d : ℕ) →
      ((a *ℕ suc d) +ℕ (b *ℕ suc c))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ (a +ℕ b))
    neg-step a b c d =
      trans
        (cong (λ t → t +ℕ (b *ℕ suc c)) (*ℕ-suc-right a d))
        (trans
          (cong (λ t → ((a *ℕ d) +ℕ a) +ℕ t) (*ℕ-suc-right b c))
          (trans
            (shuffleℕ (a *ℕ d) a (b *ℕ c) b)
            refl))

-- Cancelling a common successor in the left multiplicand only adds a diagonal pair in the product,
-- which is eliminated by `normalizePair`.

Pairℕ-mul-cancelLeft : (q : Pairℕ) → (a b : ℕ) →
  normalizePair (Pairℕ-mul ⟪ suc a , suc b ⟫ q) ≡ normalizePair (Pairℕ-mul ⟪ a , b ⟫ q)
Pairℕ-mul-cancelLeft q a b =
  let c = pos q in
  let d = neg q in
  trans
    (cong normalizePair (pair-ext (pos-step a b c d) (neg-step a b c d)))
    (normalizePair-addDiag (Pairℕ-mul ⟪ a , b ⟫ q) (c +ℕ d))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

    pos-step : (a b c d : ℕ) →
      ((suc a *ℕ c) +ℕ (suc b *ℕ d))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ (c +ℕ d))
    pos-step a b c d =
      trans
        (cong (λ t → t +ℕ (suc b *ℕ d)) (*ℕ-suc-left a c))
        (trans
          (cong (λ t → ((a *ℕ c) +ℕ c) +ℕ t) (*ℕ-suc-left b d))
          (trans
            (shuffleℕ (a *ℕ c) c (b *ℕ d) d)
            refl))

    neg-step : (a b c d : ℕ) →
      ((suc a *ℕ d) +ℕ (suc b *ℕ c))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ (c +ℕ d))
    neg-step a b c d =
      trans
        (cong (λ t → t +ℕ (suc b *ℕ c)) (*ℕ-suc-left a d))
        (trans
          (cong (λ t → ((a *ℕ d) +ℕ d) +ℕ t) (*ℕ-suc-left b c))
          (trans
            (shuffleℕ (a *ℕ d) d (b *ℕ c) c)
            (cong (λ t → ((a *ℕ d) +ℕ (b *ℕ c)) +ℕ t) (+ℕ-comm d c))))

Pairℕ-mul-normalize-right : (p q : Pairℕ) →
  normalizePair (Pairℕ-mul p (normalizePair q)) ≡ normalizePair (Pairℕ-mul p q)
Pairℕ-mul-normalize-right p ⟪ zero  , zero  ⟫ = refl
Pairℕ-mul-normalize-right p ⟪ suc a , zero  ⟫ = refl
Pairℕ-mul-normalize-right p ⟪ zero  , suc b ⟫ = refl
Pairℕ-mul-normalize-right p ⟪ suc a , suc b ⟫ =
  trans
    (Pairℕ-mul-normalize-right p ⟪ a , b ⟫)
    (sym (Pairℕ-mul-cancelRight p a b))

Pairℕ-mul-normalize-left : (p q : Pairℕ) →
  normalizePair (Pairℕ-mul (normalizePair p) q) ≡ normalizePair (Pairℕ-mul p q)
Pairℕ-mul-normalize-left ⟪ zero  , zero  ⟫ q = refl
Pairℕ-mul-normalize-left ⟪ suc a , zero  ⟫ q = refl
Pairℕ-mul-normalize-left ⟪ zero  , suc b ⟫ q = refl
Pairℕ-mul-normalize-left ⟪ suc a , suc b ⟫ q =
  trans
    (Pairℕ-mul-normalize-left ⟪ a , b ⟫ q)
    (sym (Pairℕ-mul-cancelLeft q a b))

-- Products of canonical pairs (coming from `toPairℤ`) are already normalized.

Pairℕ-mul-toPair-normal : (x y : ℤ) →
  normalizePair (Pairℕ-mul (toPairℤ x) (toPairℤ y)) ≡ Pairℕ-mul (toPairℤ x) (toPairℤ y)
Pairℕ-mul-toPair-normal 0ℤ y = refl
Pairℕ-mul-toPair-normal (+suc n) 0ℤ =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ 0ℤ) ≡ ⟪ zero , zero ⟫
      mulEq =
        pair-ext
          (trans (cong (λ t → t +ℕ (zero *ℕ zero)) (*ℕ-zero-right (suc n))) refl)
          (trans (cong (λ t → t +ℕ (zero *ℕ zero)) (*ℕ-zero-right (suc n))) refl)
  in
  trans (cong normalizePair mulEq) (trans (normalizePair-right0 zero) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) 0ℤ =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ 0ℤ) ≡ ⟪ zero , zero ⟫
      mulEq =
        pair-ext
          (trans (cong (λ t → t +ℕ (suc n *ℕ zero)) refl) (*ℕ-zero-right (suc n)))
          (trans (cong (λ t → t +ℕ (suc n *ℕ zero)) refl) (*ℕ-zero-right (suc n)))
  in
  trans (cong normalizePair mulEq) (trans (normalizePair-right0 zero) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (+suc n) (+suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m)) ≡ ⟪ (suc n *ℕ suc m) , zero ⟫
      mulEq =
        pair-ext
          (+ℕ-zero-right (suc n *ℕ suc m))
          (trans
            (cong (λ t → t +ℕ (zero *ℕ suc m)) (*ℕ-zero-right (suc n)))
            refl)
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-right0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (+suc n) (-suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m)) ≡ ⟪ zero , (suc n *ℕ suc m) ⟫
      mulEq =
        pair-ext
          (trans
            (cong (λ t → t +ℕ (zero *ℕ suc m)) (*ℕ-zero-right (suc n)))
            refl)
          (+ℕ-zero-right (suc n *ℕ suc m))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-left0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) (+suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m)) ≡ ⟪ zero , (suc n *ℕ suc m) ⟫
      mulEq =
        pair-ext
          (trans
            (cong (λ t → (zero *ℕ suc m) +ℕ t) (*ℕ-zero-right (suc n)))
            (trans
              (cong (λ t → t +ℕ zero) (*ℕ-zero-left (suc m)))
              refl))
          (+ℕ-zero-left (suc n *ℕ suc m))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-left0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) (-suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m)) ≡ ⟪ (suc n *ℕ suc m) , zero ⟫
      mulEq =
        pair-ext
          (+ℕ-zero-left (suc n *ℕ suc m))
          (trans
            (cong (λ t → (zero *ℕ suc m) +ℕ t) (*ℕ-zero-right (suc n)))
            (trans
              (cong (λ t → t +ℕ zero) (*ℕ-zero-left (suc m)))
              refl))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-right0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

toPair-*ℤ : (x y : ℤ) → toPairℤ (x *ℤ y) ≡ Pairℕ-mul (toPairℤ x) (toPairℤ y)
toPair-*ℤ x y =
  trans
    (toPair-fromPair (Pairℕ-mul (toPairℤ x) (toPairℤ y)))
    (Pairℕ-mul-toPair-normal x y)

-- Addition on ℤ is definitional `fromPairℤ` of Pairℕ-add on canonical pairs.

toPair-+ℤ : (x y : ℤ) → toPairℤ (x +ℤ y) ≡ normalizePair (Pairℕ-add (toPairℤ x) (toPairℤ y))
toPair-+ℤ x y = toPair-fromPair (Pairℕ-add (toPairℤ x) (toPairℤ y))

-- Minimal ℤ laws needed for operator-span composition.

*ℤ-distrib-right-+ℤ : (x y z : ℤ) → x *ℤ (y +ℤ z) ≡ (x *ℤ y) +ℤ (x *ℤ z)
*ℤ-distrib-right-+ℤ x y z =
  let px = toPairℤ x in
  let py = toPairℤ y in
  let pz = toPairℤ z in
  let q  = Pairℕ-add py pz in
  let rhs : fromPairℤ (Pairℕ-add (Pairℕ-mul px py) (Pairℕ-mul px pz)) ≡ (x *ℤ y) +ℤ (x *ℤ z)
      rhs =
        trans
          (cong (λ t → fromPairℤ (Pairℕ-add t (Pairℕ-mul px pz))) (sym (toPair-*ℤ x y)))
          (trans
            (cong (λ t → fromPairℤ (Pairℕ-add (toPairℤ (x *ℤ y)) t)) (sym (toPair-*ℤ x z)))
            refl)
  in
  -- LHS: x * (y+z) = mul px (toPair (fromPair q)) = mul px (normalizePair q).
  trans
    (cong (λ t → fromPairℤ (Pairℕ-mul px t)) (toPair-+ℤ y z))
    (trans
      -- erase normalization inside multiplication by normalizing afterwards
      (trans
        (sym (fromPair-normalizePair (Pairℕ-mul px (normalizePair q))))
        (cong fromPairℤ (Pairℕ-mul-normalize-right px q)))
      (trans
        (trans
          (fromPair-normalizePair (Pairℕ-mul px q))
          (cong fromPairℤ (Pairℕ-mul-distrib-right-add px py pz)))
        rhs))

*ℤ-distrib-left-+ℤ : (x y z : ℤ) → (x +ℤ y) *ℤ z ≡ (x *ℤ z) +ℤ (y *ℤ z)
*ℤ-distrib-left-+ℤ x y z =
  let px = toPairℤ x in
  let py = toPairℤ y in
  let pz = toPairℤ z in
  let q  = Pairℕ-add px py in
  let rhs : fromPairℤ (Pairℕ-add (Pairℕ-mul px pz) (Pairℕ-mul py pz)) ≡ (x *ℤ z) +ℤ (y *ℤ z)
      rhs =
        trans
          (cong (λ t → fromPairℤ (Pairℕ-add t (Pairℕ-mul py pz))) (sym (toPair-*ℤ x z)))
          (trans
            (cong (λ t → fromPairℤ (Pairℕ-add (toPairℤ (x *ℤ z)) t)) (sym (toPair-*ℤ y z)))
            refl)
  in
  trans
    (cong (λ t → fromPairℤ (Pairℕ-mul t pz)) (toPair-+ℤ x y))
    (trans
      (trans
        (sym (fromPair-normalizePair (Pairℕ-mul (normalizePair q) pz)))
        (cong fromPairℤ (Pairℕ-mul-normalize-left q pz)))
      (trans
        (trans
          (fromPair-normalizePair (Pairℕ-mul q pz))
          (cong fromPairℤ (Pairℕ-mul-distrib-left-add px py pz)))
        rhs))

-- Canonical multiplication lemmas for pairs in the image of `toPairℤ`.

Pairℕ-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
Pairℕ-ext refl refl = refl

-- Commutativity at the Pairℕ level, forced by commutativity of *ℕ and +ℕ.

Pairℕ-mul-comm : (p q : Pairℕ) → Pairℕ-mul p q ≡ Pairℕ-mul q p
Pairℕ-mul-comm p q =
  Pairℕ-ext posEq negEq
  where
    ap = pos p
    bp = neg p
    cq = pos q
    dq = neg q

    posEq : ((ap *ℕ cq) +ℕ (bp *ℕ dq)) ≡ ((cq *ℕ ap) +ℕ (dq *ℕ bp))
    posEq =
      trans
        (cong (λ t → t +ℕ (bp *ℕ dq)) (*ℕ-comm ap cq))
        (trans
          (cong (λ t → (cq *ℕ ap) +ℕ t) (*ℕ-comm bp dq))
          refl)

    negEq : ((ap *ℕ dq) +ℕ (bp *ℕ cq)) ≡ ((cq *ℕ bp) +ℕ (dq *ℕ ap))
    negEq =
      trans
        (cong (λ t → t +ℕ (bp *ℕ cq)) (*ℕ-comm ap dq))
        (trans
          (cong (λ t → (dq *ℕ ap) +ℕ t) (*ℕ-comm bp cq))
          (+ℕ-comm (dq *ℕ ap) (cq *ℕ bp)))

Pairℕ-mul-pos-pos : (a b : ℕ) →
  Pairℕ-mul ⟪ a , zero ⟫ ⟪ b , zero ⟫ ≡ ⟪ a *ℕ b , zero ⟫
Pairℕ-mul-pos-pos a b =
  pair-ext
    (trans
      (cong (λ t → (a *ℕ b) +ℕ t) (*ℕ-zero-left zero))
      (+ℕ-zero-right (a *ℕ b)))
    (trans
      (cong (λ t → (a *ℕ zero) +ℕ t) (*ℕ-zero-left b))
      (trans
        (+ℕ-zero-right (a *ℕ zero))
        (*ℕ-zero-right a)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

Pairℕ-mul-pos-neg : (a b : ℕ) →
  Pairℕ-mul ⟪ a , zero ⟫ ⟪ zero , b ⟫ ≡ ⟪ zero , a *ℕ b ⟫
Pairℕ-mul-pos-neg a b =
  pair-ext
    (trans
      (cong (λ t → (a *ℕ zero) +ℕ t) (*ℕ-zero-left b))
      (trans
        (+ℕ-zero-right (a *ℕ zero))
        (*ℕ-zero-right a)))
    (trans
      (cong (λ t → (a *ℕ b) +ℕ t) (*ℕ-zero-left zero))
      (+ℕ-zero-right (a *ℕ b)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

Pairℕ-mul-neg-pos : (a b : ℕ) →
  Pairℕ-mul ⟪ zero , a ⟫ ⟪ b , zero ⟫ ≡ ⟪ zero , a *ℕ b ⟫
Pairℕ-mul-neg-pos a b =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (a *ℕ zero)) (*ℕ-zero-left b))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right a))
        refl))
    (+ℕ-zero-left (a *ℕ b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

Pairℕ-mul-neg-neg : (a b : ℕ) →
  Pairℕ-mul ⟪ zero , a ⟫ ⟪ zero , b ⟫ ≡ ⟪ a *ℕ b , zero ⟫
Pairℕ-mul-neg-neg a b =
  pair-ext
    (+ℕ-zero-left (a *ℕ b))
    (trans
      (cong (λ t → (zero *ℕ b) +ℕ t) (*ℕ-zero-right a))
      (trans
        (cong (λ t → t +ℕ zero) (*ℕ-zero-left b))
        (+ℕ-zero-left zero)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

{-
### Law 14P.0: Nonzero Positive Scalar Has No Torsion (Left)
**Necessity Proof:** `(+suc n *ℤ x ≡ 0ℤ)` forces the `Pairℕ-mul` component carrying `suc n *ℕ suc m` to be zero.
`*ℕ-pos-zero→zero` forces `suc m ≡ zero`, which is impossible.
**Formal Reference:** IntegerMultiplicationLaws.agda.*ℤ-pos-left-zero→zero (lines 559-609)
**Consequence:** Eliminates the possibility that a positive nonzero scalar annihilates a nonzero integer.
-}

*ℤ-pos-left-zero→zero : (n : ℕ) → (x : ℤ) → (+suc n *ℤ x ≡ 0ℤ) → x ≡ 0ℤ
*ℤ-pos-left-zero→zero n 0ℤ _ = refl
*ℤ-pos-left-zero→zero n (+suc m) mul0 =
  let
    eqPair : toPairℤ ((+suc n) *ℤ (+suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m)) ≡ ⟪ zero , zero ⟫
    step₁ = trans (sym (toPair-*ℤ (+suc n) (+suc m))) eqPair

    pos0-raw : pos (Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m))) ≡ zero
    pos0-raw = cong pos step₁

    pos0 : (suc n *ℕ suc m) ≡ zero
    pos0 =
      trans
        (sym (+ℕ-zero-right (suc n *ℕ suc m)))
        pos0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) pos0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

*ℤ-pos-left-zero→zero n (-suc m) mul0 =
  let
    eqPair : toPairℤ ((+suc n) *ℤ (-suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m)) ≡ ⟪ zero , zero ⟫
    step₁ = trans (sym (toPair-*ℤ (+suc n) (-suc m))) eqPair

    neg0-raw : neg (Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m))) ≡ zero
    neg0-raw = cong neg step₁

    neg0 : (suc n *ℕ suc m) ≡ zero
    neg0 =
      trans
        (sym (+ℕ-zero-right (suc n *ℕ suc m)))
        neg0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) neg0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

{-
### Law 14P.1: Multiplication Commutes With Additive Inverse (Right)
**Necessity Proof:** `y +ℤ negℤ y ≡ 0ℤ` forces `x *ℤ (y +ℤ negℤ y) ≡ 0ℤ`.
Right-distributivity forces `(x *ℤ y) +ℤ (x *ℤ negℤ y) ≡ 0ℤ`, and left-cancellation by `negℤ (x *ℤ y)` forces the unique solution.
**Formal Reference:** IntegerMultiplicationLaws.agda.*ℤ-neg-right (lines 626-657)
**Consequence:** Eliminates ambiguity in how `*ℤ` interacts with `negℤ` on the right.
-}
{-
### Law 14P.2: Multiplication Commutes With Additive Inverse (Left)
**Necessity Proof:** `negℤ x +ℤ x ≡ 0ℤ` forces `(negℤ x +ℤ x) *ℤ y ≡ 0ℤ`.
Left-distributivity forces `(negℤ x *ℤ y) +ℤ (x *ℤ y) ≡ 0ℤ`, and right-cancellation by `negℤ (x *ℤ y)` forces the unique solution.
**Formal Reference:** IntegerMultiplicationLaws.agda.*ℤ-neg-left (lines 659-690)
**Consequence:** Eliminates ambiguity in how `*ℤ` interacts with `negℤ` on the left.
-}

*ℤ-neg-right : (x y : ℤ) → x *ℤ (negℤ y) ≡ negℤ (x *ℤ y)
*ℤ-neg-right x y =
  let
    eq0 : y +ℤ negℤ y ≡ 0ℤ
    eq0 = +ℤ-inv-right y

    mul0 : x *ℤ (y +ℤ negℤ y) ≡ x *ℤ 0ℤ
    mul0 = cong (λ t → x *ℤ t) eq0

    expand : x *ℤ (y +ℤ negℤ y) ≡ (x *ℤ y) +ℤ (x *ℤ negℤ y)
    expand = *ℤ-distrib-right-+ℤ x y (negℤ y)

    eqSum : (x *ℤ y) +ℤ (x *ℤ negℤ y) ≡ 0ℤ
    eqSum = trans (sym expand) (trans mul0 (*ℤ-zero-right x))

    addNeg : negℤ (x *ℤ y) +ℤ ((x *ℤ y) +ℤ (x *ℤ negℤ y)) ≡ negℤ (x *ℤ y) +ℤ 0ℤ
    addNeg = cong (λ t → negℤ (x *ℤ y) +ℤ t) eqSum

    leftReduce : negℤ (x *ℤ y) +ℤ ((x *ℤ y) +ℤ (x *ℤ negℤ y)) ≡ x *ℤ negℤ y
    leftReduce =
      trans
        (sym (+ℤ-assoc (negℤ (x *ℤ y)) (x *ℤ y) (x *ℤ negℤ y)))
        (trans
          (cong (λ t → t +ℤ (x *ℤ negℤ y)) (+ℤ-inv-left (x *ℤ y)))
          (+ℤ-zero-left (x *ℤ negℤ y)))

    rightReduce : negℤ (x *ℤ y) +ℤ 0ℤ ≡ negℤ (x *ℤ y)
    rightReduce = +ℤ-zero-right (negℤ (x *ℤ y))
  in
  trans
    (sym leftReduce)
    (trans addNeg rightReduce)

*ℤ-neg-left : (x y : ℤ) → (negℤ x) *ℤ y ≡ negℤ (x *ℤ y)
*ℤ-neg-left x y =
  let
    eq0 : negℤ x +ℤ x ≡ 0ℤ
    eq0 = +ℤ-inv-left x

    mul0 : (negℤ x +ℤ x) *ℤ y ≡ 0ℤ *ℤ y
    mul0 = cong (λ t → t *ℤ y) eq0

    expand : (negℤ x +ℤ x) *ℤ y ≡ (negℤ x *ℤ y) +ℤ (x *ℤ y)
    expand = *ℤ-distrib-left-+ℤ (negℤ x) x y

    eqSum' : (negℤ x *ℤ y) +ℤ (x *ℤ y) ≡ 0ℤ
    eqSum' = trans (sym expand) (trans mul0 (*ℤ-zero-left y))

    addInv : ((negℤ x *ℤ y) +ℤ (x *ℤ y)) +ℤ negℤ (x *ℤ y) ≡ 0ℤ +ℤ negℤ (x *ℤ y)
    addInv = cong (λ t → t +ℤ negℤ (x *ℤ y)) eqSum'

    lhsReduce : ((negℤ x *ℤ y) +ℤ (x *ℤ y)) +ℤ negℤ (x *ℤ y) ≡ negℤ x *ℤ y
    lhsReduce =
      trans
        (+ℤ-assoc (negℤ x *ℤ y) (x *ℤ y) (negℤ (x *ℤ y)))
        (trans
          (cong (λ t → (negℤ x *ℤ y) +ℤ t) (+ℤ-inv-right (x *ℤ y)))
          (+ℤ-zero-right (negℤ x *ℤ y)))

    rhsReduce : 0ℤ +ℤ negℤ (x *ℤ y) ≡ negℤ (x *ℤ y)
    rhsReduce = +ℤ-zero-left (negℤ (x *ℤ y))
  in
  trans
    (sym lhsReduce)
    (trans addInv rhsReduce)

{-
### Law 14P.3: Nonzero Negative Scalar Has No Torsion (Left)
**Necessity Proof:** `(-suc n *ℤ x ≡ 0ℤ)` forces the `Pairℕ-mul` component carrying `suc n *ℕ suc m` to be zero.
`*ℕ-pos-zero→zero` forces `suc m ≡ zero`, which is impossible.
**Formal Reference:** IntegerMultiplicationLaws.agda.*ℤ-neg-left-zero→zero (lines 700-750)
**Consequence:** Eliminates the possibility that a negative nonzero scalar annihilates a nonzero integer.
-}

*ℤ-neg-left-zero→zero : (n : ℕ) → (x : ℤ) → (-suc n *ℤ x ≡ 0ℤ) → x ≡ 0ℤ
*ℤ-neg-left-zero→zero n 0ℤ _ = refl
*ℤ-neg-left-zero→zero n (+suc m) mul0 =
  let
    eqPair : toPairℤ ((-suc n) *ℤ (+suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m)) ≡ ⟪ zero , zero ⟫
    step₁ = trans (sym (toPair-*ℤ (-suc n) (+suc m))) eqPair

    neg0-raw : neg (Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m))) ≡ zero
    neg0-raw = cong neg step₁

    neg0 : (suc n *ℕ suc m) ≡ zero
    neg0 =
      trans
        (sym (+ℕ-zero-left (suc n *ℕ suc m)))
        neg0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) neg0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

*ℤ-neg-left-zero→zero n (-suc m) mul0 =
  let
    eqPair : toPairℤ ((-suc n) *ℤ (-suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m)) ≡ ⟪ zero , zero ⟫
    step₁ = trans (sym (toPair-*ℤ (-suc n) (-suc m))) eqPair

    pos0-raw : pos (Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m))) ≡ zero
    pos0-raw = cong pos step₁

    pos0 : (suc n *ℕ suc m) ≡ zero
    pos0 =
      trans
        (sym (+ℕ-zero-left (suc n *ℕ suc m)))
        pos0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) pos0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

Pairℕ-mul-zero-right : (p : Pairℕ) → Pairℕ-mul p ⟪ zero , zero ⟫ ≡ ⟪ zero , zero ⟫
Pairℕ-mul-zero-right ⟪ a , b ⟫ =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (b *ℕ zero)) (*ℕ-zero-right a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right b))
        refl))
    (trans
      (cong (λ t → t +ℕ (b *ℕ zero)) (*ℕ-zero-right a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right b))
        refl))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

Pairℕ-mul-zero-left : (p : Pairℕ) → Pairℕ-mul ⟪ zero , zero ⟫ p ≡ ⟪ zero , zero ⟫
Pairℕ-mul-zero-left ⟪ a , b ⟫ =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (zero *ℕ b)) (*ℕ-zero-left a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-left b))
        refl))
    (trans
      (cong (λ t → t +ℕ (zero *ℕ a)) (*ℕ-zero-left b))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-left a))
        refl))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → ⟪ x , y ⟫ ≡ ⟪ x' , y' ⟫
    pair-ext refl refl = refl

Pairℕ-mul-toPair-assoc : (x y z : ℤ) →
  Pairℕ-mul (Pairℕ-mul (toPairℤ x) (toPairℤ y)) (toPairℤ z)
    ≡
  Pairℕ-mul (toPairℤ x) (Pairℕ-mul (toPairℤ y) (toPairℤ z))
Pairℕ-mul-toPair-assoc 0ℤ y z = refl
Pairℕ-mul-toPair-assoc (+suc n) 0ℤ z =
  trans
    (cong (λ t → Pairℕ-mul t (toPairℤ z)) (Pairℕ-mul-zero-right ⟪ suc n , zero ⟫))
    (trans
      (Pairℕ-mul-zero-left (toPairℤ z))
      (sym
        (trans
          (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-zero-left (toPairℤ z)))
          (Pairℕ-mul-zero-right ⟪ suc n , zero ⟫))))
Pairℕ-mul-toPair-assoc (-suc n) 0ℤ z =
  trans
    (cong (λ t → Pairℕ-mul t (toPairℤ z)) (Pairℕ-mul-zero-right ⟪ zero , suc n ⟫))
    (trans
      (Pairℕ-mul-zero-left (toPairℤ z))
      (sym
        (trans
          (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-zero-left (toPairℤ z)))
          (Pairℕ-mul-zero-right ⟪ zero , suc n ⟫))))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul ⟪ suc n , zero ⟫ ⟪ suc m , zero ⟫))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-zero-right ⟪ suc m , zero ⟫))
        (Pairℕ-mul-zero-right ⟪ suc n , zero ⟫)))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul ⟪ suc n , zero ⟫ ⟪ zero , suc m ⟫))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-zero-right ⟪ zero , suc m ⟫))
        (Pairℕ-mul-zero-right ⟪ suc n , zero ⟫)))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul ⟪ zero , suc n ⟫ ⟪ suc m , zero ⟫))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-zero-right ⟪ suc m , zero ⟫))
        (Pairℕ-mul-zero-right ⟪ zero , suc n ⟫)))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul ⟪ zero , suc n ⟫ ⟪ zero , suc m ⟫))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-zero-right ⟪ zero , suc m ⟫))
        (Pairℕ-mul-zero-right ⟪ zero , suc n ⟫)))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ suc k , zero ⟫) (Pairℕ-mul-pos-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-pos-pos (suc m) (suc k)))
            (Pairℕ-mul-pos-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ zero , suc k ⟫) (Pairℕ-mul-pos-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-pos-neg (suc m) (suc k)))
            (Pairℕ-mul-pos-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ suc k , zero ⟫) (Pairℕ-mul-pos-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-neg-pos (suc m) (suc k)))
            (Pairℕ-mul-pos-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ zero , suc k ⟫) (Pairℕ-mul-pos-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ suc n , zero ⟫ t) (Pairℕ-mul-neg-neg (suc m) (suc k)))
            (Pairℕ-mul-pos-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ suc k , zero ⟫) (Pairℕ-mul-neg-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-pos-pos (suc m) (suc k)))
            (Pairℕ-mul-neg-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ zero , suc k ⟫) (Pairℕ-mul-neg-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-pos-neg (suc m) (suc k)))
            (Pairℕ-mul-neg-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ suc k , zero ⟫) (Pairℕ-mul-neg-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-neg-pos (suc m) (suc k)))
            (Pairℕ-mul-neg-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t ⟪ zero , suc k ⟫) (Pairℕ-mul-neg-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul ⟪ zero , suc n ⟫ t) (Pairℕ-mul-neg-neg (suc m) (suc k)))
            (Pairℕ-mul-neg-pos (suc n) ((suc m) *ℕ (suc k)))))))

*ℤ-assoc : (x y z : ℤ) → (x *ℤ y) *ℤ z ≡ x *ℤ (y *ℤ z)
*ℤ-assoc x y z =
  let lhs = (x *ℤ y) *ℤ z in
  let rhs = x *ℤ (y *ℤ z) in
  trans
    (sym (from-toPairℤ lhs))
    (trans
      (cong fromPairℤ
        (trans
          (trans
            (toPair-*ℤ (x *ℤ y) z)
            (cong (λ t → Pairℕ-mul t (toPairℤ z)) (toPair-*ℤ x y)))
          (trans
            (Pairℕ-mul-toPair-assoc x y z)
            (sym
              (trans
                (toPair-*ℤ x (y *ℤ z))
                (cong (λ t → Pairℕ-mul (toPairℤ x) t) (toPair-*ℤ y z)))))))
      (from-toPairℤ rhs))

*ℤ-comm : (x y : ℤ) → x *ℤ y ≡ y *ℤ x
*ℤ-comm x y = cong fromPairℤ (Pairℕ-mul-comm (toPairℤ x) (toPairℤ y))
