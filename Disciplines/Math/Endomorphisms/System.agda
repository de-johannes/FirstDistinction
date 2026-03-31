{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.Endomorphisms.System where

open import FirstDistinction
open import Disciplines.Math.Endomorphisms.Iteration

{-
CHAPTER 14J: Endomorphism Systems (Universal Property Without Limits)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14I (powEndo)
AGDA MODULES: Disciplines.Math.Endomorphisms.System
DEGREES OF FREEDOM ELIMINATED: “continuity” assumptions not forced by morphism commutation
-}

record Setoid : Set1 where
  field
    Obj    : Set
    Rel    : Obj → Obj → Set
    refl≈  : (x : Obj) → Rel x x
    sym≈   : {x y : Obj} → Rel x y → Rel y x
    trans≈ : {x y z : Obj} → Rel x y → Rel y z → Rel x z

open Setoid public

record EndoSystem : Set1 where
  field
    S    : Setoid
    step : Obj S → Obj S
    step-cong : {x y : Obj S} → Rel S x y → Rel S (step x) (step y)

open EndoSystem public

record Hom (X Y : EndoSystem) : Set1 where
  field
    map  : Obj (S X) → Obj (S Y)
    map-cong : {x y : Obj (S X)} → Rel (S X) x y → Rel (S Y) (map x) (map y)
    comm : (x : Obj (S X)) → Rel (S Y) (map (step X x)) (step Y (map x))

open Hom public

{-
## Universal Property Interfaces (Forced)

A “limit object” for iteration is admitted only via initial/terminal universal property,
not via an analytic Limes.
-}

record IsTerminal (T : EndoSystem) : Set1 where
  field
    !    : (X : EndoSystem) → Hom X T
    uniq : (X : EndoSystem) → (f g : Hom X T) → (x : Obj (S X)) → Rel (S T) (map f x) (map g x)

record IsInitial (I : EndoSystem) : Set1 where
  field
    !    : (X : EndoSystem) → Hom I X
    uniq : (X : EndoSystem) → (f g : Hom I X) → (x : Obj (S I)) → Rel (S X) (map f x) (map g x)

{-
## Continuity From Iteration (Forced)

### Law 14J.0: Morphisms Commute With All Iterates
**Necessity Proof:** A morphism commutes with one step. ℕ-recursion forces commutation with every iterated step.
**Formal Reference:** System.agda.law14J-0-hom-iter (lines 69-79)
**Consequence:** Eliminates any extra “continuity axiom”: continuity is forced by iteration.
-}

law14J-0-hom-iter :
  {X Y : EndoSystem} →
  (h : Hom X Y) →
  (n : ℕ) →
  (x : Obj (S X)) →
  Rel (S Y) (map h (powEndo n (step X) x)) (powEndo n (step Y) (map h x))
law14J-0-hom-iter {X} {Y} h zero x = refl≈ (S Y) (map h x)
law14J-0-hom-iter {X} {Y} h (suc n) x =
  trans≈ (S Y)
    (comm h (powEndo n (step X) x))
    (step-cong Y (law14J-0-hom-iter h n x))
