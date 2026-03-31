{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.NatOrderLaws where

open import FirstDistinction

suc-injective : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} z≤n z≤n = refl
≤-antisym {zero} {suc n} z≤n ()
≤-antisym {suc m} {zero} () _
≤-antisym {suc m} {suc n} (s≤s p) (s≤s q) = cong suc (≤-antisym p q)
