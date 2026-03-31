{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.NatBuiltins where

open import FirstDistinction

{-
CHAPTER 14X: Native Evaluation Layer (Bool/ℕ BUILTIN Chain)

ONTOLOGICAL STATUS: Derived (presentation-only)
DEPENDENCIES: FirstDistinction (⊥, equality, ℕ)
AGDA MODULES: Disciplines.Math.NatBuiltins
DEGREES OF FREEDOM ELIMINATED: non-terminating definitional evaluation of large Peano numerals

This module registers Agda BUILTIN pragmas for Bool/ℕ operations.
It changes evaluation strategy, not logical content.
-}

-- Bool (for computable comparison witnesses)

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

-- ℕ is imported from FirstDistinction.

{-# BUILTIN NATURAL ℕ #-}

-- Arithmetic on ℕ

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero  ∸ n     = zero
suc m ∸ zero  = suc m
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- Decidable comparisons on ℕ (boolean-valued)

_<ℕ-bool_ : ℕ → ℕ → Bool
m <ℕ-bool zero   = false
zero <ℕ-bool suc _ = true
suc m <ℕ-bool suc n = m <ℕ-bool n

{-# BUILTIN NATLESS _<ℕ-bool_ #-}

_==ℕ-bool_ : ℕ → ℕ → Bool
zero  ==ℕ-bool zero    = true
zero  ==ℕ-bool (suc _) = false
suc _ ==ℕ-bool zero    = false
suc m ==ℕ-bool suc n   = m ==ℕ-bool n

{-# BUILTIN NATEQUALS _==ℕ-bool_ #-}
