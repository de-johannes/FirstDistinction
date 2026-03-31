{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.Endomorphisms.Iteration where

open import FirstDistinction

{-
CHAPTER 14I: Operator Iteration (Recursion Without Interpretation)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 8 (ℕ), Chapter 0–1 (equality infrastructure)
AGDA MODULES: Disciplines.Math.Endomorphisms.Iteration
DEGREES OF FREEDOM ELIMINATED: ad hoc “iteration” operations not fixed by ℕ-recursion
-}

Endo : Set → Set
Endo A = A → A

infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

idEndo : {A : Set} → Endo A
idEndo x = x

powEndo : {A : Set} → ℕ → Endo A → Endo A
powEndo zero    f = idEndo
powEndo (suc n) f = f ∘ powEndo n f

{-
## Recursion Laws (Forced)

### Law 14I.0: Zero-Iteration Is Identity
**Necessity Proof:** `powEndo` is forced by primitive recursion on ℕ. The `zero` branch fixes the base case.
**Formal Reference:** Iteration.agda.law14I-0-powEndo-zero (lines 39-40)
**Consequence:** Eliminates non-identity “zero step” ambiguity.
-}

law14I-0-powEndo-zero : {A : Set} → (f : Endo A) → powEndo zero f ≗ idEndo
law14I-0-powEndo-zero f x = refl

{-
### Law 14I.1: Successor-Iteration Is Composition
**Necessity Proof:** The `suc` branch of ℕ-recursion forces iteration to compose once more with the operator.
**Formal Reference:** Iteration.agda.law14I-1-powEndo-suc (lines 49-50)
**Consequence:** Eliminates arbitrary step-ordering in iteration.
-}

law14I-1-powEndo-suc : {A : Set} → (n : ℕ) → (f : Endo A) → powEndo (suc n) f ≗ (f ∘ powEndo n f)
law14I-1-powEndo-suc n f x = refl
