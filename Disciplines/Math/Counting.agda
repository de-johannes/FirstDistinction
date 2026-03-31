{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.Counting where

open import FirstDistinction

{-
CHAPTER 14A: Counting (Finite Indices)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: FirstDistinction (equality, sum/product types)
AGDA MODULES: Disciplines.Math.Counting
DEGREES OF FREEDOM ELIMINATED: ad hoc “three-ness” without an index type
-}

data Fin3 : Set where
  f0 f1 f2 : Fin3

Fin3≠ : (i j : Fin3) → Set
Fin3≠ i j = i ≡ j → ⊥

f0≠f1 : Fin3≠ f0 f1
f0≠f1 ()

f0≠f2 : Fin3≠ f0 f2
f0≠f2 ()

f1≠f2 : Fin3≠ f1 f2
f1≠f2 ()

Fin3-decEq : (i j : Fin3) → (i ≡ j) ⊎ (Fin3≠ i j)
Fin3-decEq f0 f0 = inj₁ refl
Fin3-decEq f1 f1 = inj₁ refl
Fin3-decEq f2 f2 = inj₁ refl
Fin3-decEq f0 f1 = inj₂ f0≠f1
Fin3-decEq f1 f0 = inj₂ (λ e → f0≠f1 (sym e))
Fin3-decEq f0 f2 = inj₂ f0≠f2
Fin3-decEq f2 f0 = inj₂ (λ e → f0≠f2 (sym e))
Fin3-decEq f1 f2 = inj₂ f1≠f2
Fin3-decEq f2 f1 = inj₂ (λ e → f1≠f2 (sym e))

data Fin4 : Set where
  g0 g1 g2 g3 : Fin4

Fin4≠ : (i j : Fin4) → Set
Fin4≠ i j = i ≡ j → ⊥

g0≠g1 : Fin4≠ g0 g1
g0≠g1 ()

g0≠g2 : Fin4≠ g0 g2
g0≠g2 ()

g0≠g3 : Fin4≠ g0 g3
g0≠g3 ()

g1≠g2 : Fin4≠ g1 g2
g1≠g2 ()

g1≠g3 : Fin4≠ g1 g3
g1≠g3 ()

g2≠g3 : Fin4≠ g2 g3
g2≠g3 ()

Fin4-decEq : (i j : Fin4) → (i ≡ j) ⊎ (Fin4≠ i j)
Fin4-decEq g0 g0 = inj₁ refl
Fin4-decEq g1 g1 = inj₁ refl
Fin4-decEq g2 g2 = inj₁ refl
Fin4-decEq g3 g3 = inj₁ refl
Fin4-decEq g0 g1 = inj₂ g0≠g1
Fin4-decEq g1 g0 = inj₂ (λ e → g0≠g1 (sym e))
Fin4-decEq g0 g2 = inj₂ g0≠g2
Fin4-decEq g2 g0 = inj₂ (λ e → g0≠g2 (sym e))
Fin4-decEq g0 g3 = inj₂ g0≠g3
Fin4-decEq g3 g0 = inj₂ (λ e → g0≠g3 (sym e))
Fin4-decEq g1 g2 = inj₂ g1≠g2
Fin4-decEq g2 g1 = inj₂ (λ e → g1≠g2 (sym e))
Fin4-decEq g1 g3 = inj₂ g1≠g3
Fin4-decEq g3 g1 = inj₂ (λ e → g1≠g3 (sym e))
Fin4-decEq g2 g3 = inj₂ g2≠g3
Fin4-decEq g3 g2 = inj₂ (λ e → g2≠g3 (sym e))
