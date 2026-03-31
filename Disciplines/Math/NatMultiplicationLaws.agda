{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.NatMultiplicationLaws where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication

{-
CHAPTER 14O: Forced Laws Of Natural Multiplication

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14F (+ℕ laws), Chapter 14M (*ℕ definition)
AGDA MODULES: Disciplines.Math.NatMultiplicationLaws
DEGREES OF FREEDOM ELIMINATED: ambiguous interaction of *ℕ with +ℕ
-}

-- Left distributivity over +ℕ, forced because *ℕ is defined by recursion on the left argument.

*ℕ-distrib-left-+ℕ : (a b c : ℕ) → (a +ℕ b) *ℕ c ≡ (a *ℕ c) +ℕ (b *ℕ c)
*ℕ-distrib-left-+ℕ zero b c =
  trans
    refl
    (sym (+ℕ-zero-left (b *ℕ c)))
*ℕ-distrib-left-+ℕ (suc a) b c =
  trans
    refl
    (trans
      (cong (λ t → c +ℕ t) (*ℕ-distrib-left-+ℕ a b c))
      (sym (+ℕ-assoc c (a *ℕ c) (b *ℕ c))))

-- Right distributivity over +ℕ.

swapHeadℕ : (a b t : ℕ) → a +ℕ (b +ℕ t) ≡ b +ℕ (a +ℕ t)
swapHeadℕ a b t =
  trans
    (sym (+ℕ-assoc a b t))
    (trans
      (cong (λ s → s +ℕ t) (+ℕ-comm a b))
      (+ℕ-assoc b a t))

shuffleℕ : (b c x y : ℕ) → (b +ℕ c) +ℕ (x +ℕ y) ≡ (b +ℕ x) +ℕ (c +ℕ y)
shuffleℕ b c x y =
  trans
    (+ℕ-assoc b c (x +ℕ y))
    (trans
      (cong (λ t → b +ℕ t) (sym (+ℕ-assoc c x y)))
      (trans
        (cong (λ t → b +ℕ (t +ℕ y)) (+ℕ-comm c x))
        (trans
          (cong (λ t → b +ℕ t) (+ℕ-assoc x c y))
          (sym (+ℕ-assoc b x (c +ℕ y))))))

*ℕ-distrib-right-+ℕ : (a b c : ℕ) → a *ℕ (b +ℕ c) ≡ (a *ℕ b) +ℕ (a *ℕ c)
*ℕ-distrib-right-+ℕ zero b c = refl
*ℕ-distrib-right-+ℕ (suc a) b c =
  trans
    refl
    (trans
      (cong (λ t → (b +ℕ c) +ℕ t) (*ℕ-distrib-right-+ℕ a b c))
      (trans
        (shuffleℕ b c (a *ℕ b) (a *ℕ c))
        refl))

-- Associativity of *ℕ.

*ℕ-assoc : (a b c : ℕ) → (a *ℕ b) *ℕ c ≡ a *ℕ (b *ℕ c)
*ℕ-assoc zero b c = refl
*ℕ-assoc (suc a) b c =
  trans
    (*ℕ-distrib-left-+ℕ b (a *ℕ b) c)
    (trans
      (cong (λ t → (b *ℕ c) +ℕ t) (*ℕ-assoc a b c))
      refl)

-- Zero-cancellation for positive left factors.

*ℕ-pos-zero→zero : (a n : ℕ) → suc a *ℕ n ≡ zero → n ≡ zero
*ℕ-pos-zero→zero a zero _ = refl
*ℕ-pos-zero→zero a (suc n) ()

-- Multiplication by a successor on the right.

*ℕ-suc-right-+ℕ : (n m : ℕ) → n *ℕ (suc m) ≡ n +ℕ (n *ℕ m)
*ℕ-suc-right-+ℕ zero m = refl
*ℕ-suc-right-+ℕ (suc n) m =
  trans
    refl
    (trans
      (cong (λ t → (suc m) +ℕ t) (*ℕ-suc-right-+ℕ n m))
      (cong suc (swapHeadℕ m n (n *ℕ m))))

-- Commutativity of *ℕ forced by the successor-right law.

*ℕ-comm : (m n : ℕ) → m *ℕ n ≡ n *ℕ m
*ℕ-comm zero n = sym (*ℕ-zero-right n)
*ℕ-comm (suc m) n =
  trans
    refl
    (trans
      (cong (λ t → n +ℕ t) (*ℕ-comm m n))
      (sym (*ℕ-suc-right-+ℕ n m)))

-- Monotonicity of +ℕ in the right argument (adding the same left prefix).

≤-+ℕ-monoˡ : {a b : ℕ} → a ≤ b → (c : ℕ) → (c +ℕ a) ≤ (c +ℕ b)
≤-+ℕ-monoˡ p zero = p
≤-+ℕ-monoˡ p (suc c) = s≤s (≤-+ℕ-monoˡ p c)

-- Left-cancellation for +ℕ (forced by the inductive shape of ≤).

≤-+ℕ-cancelˡ : (c a b : ℕ) → (c +ℕ a) ≤ (c +ℕ b) → a ≤ b
≤-+ℕ-cancelˡ zero a b p = p
≤-+ℕ-cancelˡ (suc c) a b (s≤s p) = ≤-+ℕ-cancelˡ c a b p

-- Monotonicity of *ℕ in the left argument for a fixed right factor.

≤-*ℕ-monoʳ : {m n : ℕ} → m ≤ n → (t : ℕ) → (m *ℕ t) ≤ (n *ℕ t)
≤-*ℕ-monoʳ z≤n t = z≤n
≤-*ℕ-monoʳ (s≤s p) t = ≤-+ℕ-monoˡ (≤-*ℕ-monoʳ p t) t

-- Right-cancellation for *ℕ by a positive (successor) factor.

≤-*ℕ-cancelʳ-suc : {m n : ℕ} → (k : ℕ) → (m *ℕ suc k) ≤ (n *ℕ suc k) → m ≤ n
≤-*ℕ-cancelʳ-suc {zero} {zero} k _ = z≤n
≤-*ℕ-cancelʳ-suc {suc m'} {zero} k ()
≤-*ℕ-cancelʳ-suc {zero} {suc n} k _ = z≤n
≤-*ℕ-cancelʳ-suc {suc m} {suc n} k p =
  let
    step : (suc k +ℕ (m *ℕ suc k)) ≤ (suc k +ℕ (n *ℕ suc k))
    step = p

    tail : (m *ℕ suc k) ≤ (n *ℕ suc k)
    tail = ≤-+ℕ-cancelˡ (suc k) (m *ℕ suc k) (n *ℕ suc k) step

    ih : m ≤ n
    ih = ≤-*ℕ-cancelʳ-suc k tail
  in
  s≤s ih
