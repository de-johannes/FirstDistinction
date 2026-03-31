{-# OPTIONS --safe --without-K #-}

module Disciplines.Phenomena.K4Alpha137 where

open import FirstDistinction
open import Disciplines.Math.NatBuiltins
open import Disciplines.Graph.K4SimplexInvariants

{-
CHAPTER 15A: Forced Integer Evaluation From K₄ Simplex Invariants

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (simplex invariants)
AGDA MODULES: Disciplines.Phenomena.K4Alpha137
DEGREES OF FREEDOM ELIMINATED: ad hoc external naming of a dimensionless integer
-}

alpha-inverse : ℕ
_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
x ^ suc n = x * (x ^ n)

alpha-inverse = (simplex-vertices ^ simplex-degree) * simplex-chi + (simplex-degree * simplex-degree)

{-
### Law 15A.0: The Integer Named α⁻¹ Is Forced To Be 137
**Necessity Proof:** Expand the definition using the forced invariant values from Chapter 14C.
  **Formal Reference:** K4SimplexInvariants.agda.law14C-0-vertices
  **Formal Reference:** K4SimplexInvariants.agda.law14C-1-degree
  **Formal Reference:** K4SimplexInvariants.agda.law14C-3-chi
**Consequence:** Eliminates freedom in the numeric value of the named integer.
-}

law15A-0-alpha-inverse-137 : alpha-inverse ≡ 137
law15A-0-alpha-inverse-137 = refl
