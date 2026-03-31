{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4Graph where

open import Agda.Primitive using (Level; lsuc; _⊔_; Setω)
open import FirstDistinction

{-
CHAPTER 13: Graph Presentation (K₄)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: FirstDistinction (K₄ classification provides `EndoCase`)
AGDA MODULES: Disciplines.Graph.K4Graph
DEGREES OF FREEDOM ELIMINATED: representational freedom in presenting the complete graph on `EndoCase`
-}

record Graph : Set1 where
  field
    V    : Set
    Edge : V → V → Set
    edge-sym : {a b : V} → Edge a b → Edge b a
    edge-irr : (a : V) → Edge a a → ⊥

open Graph public

record GraphIso (G H : Graph) : Set1 where
  field
    to       : V G → V H
    from     : V H → V G
    to-from  : (y : V H) → to (from y) ≡ y
    from-to  : (x : V G) → from (to x) ≡ x
    edge-to  : {a b : V G} → Edge G a b → Edge H (to a) (to b)
    edge-from : {a b : V H} → Edge H a b → Edge G (from a) (from b)

open GraphIso public

transport≠ :
  {A : Set} →
  {a a' b b' : A} →
  a ≡ a' →
  b ≡ b' →
  (a ≠ b) →
  (a' ≠ b')
transport≠ ea eb neq eq' = neq (trans ea (trans eq' (sym eb)))

{-
## Canonical K₄ Graph

### Law 13.0: The Canonical K₄ Graph Has Edge = Inequality
**Necessity Proof:** `EndoCase` classifies into exactly four forced cases in the kernel.
The complete graph on this carrier is forced to have an edge between two vertices
exactly when they are distinct; otherwise a self-loop degree of freedom survives.
  **Formal Reference:** K4Graph.agda.K4GraphCanonical (lines 57-63)
**Consequence:** Fixes the canonical carrier and edge predicate for the K₄ graph layer.
-}

K4GraphCanonical : Graph
K4GraphCanonical = record
  { V = EndoCase
  ; Edge = λ a b → a ≠ b
  ; edge-sym = λ {a} {b} neq eq → neq (sym eq)
  ; edge-irr = λ a loop → loop refl
  }

{-
## Presentation Interface

A presentation is admissible precisely when it is an isomorphism of carriers to
`EndoCase`; all further structure is eliminable.
-}

record K4GraphPresentation : Set1 where
  field
    Vp      : Set
    toV     : Vp → EndoCase
    fromV   : EndoCase → Vp
    to-from : (c : EndoCase) → toV (fromV c) ≡ c
    from-to : (v : Vp) → fromV (toV v) ≡ v

open K4GraphPresentation public

presentedGraph : K4GraphPresentation → Graph
presentedGraph p = record
  { V = Vp p
  ; Edge = λ v w → toV p v ≠ toV p w
  ; edge-sym = λ {a} {b} neq eq → neq (sym eq)
  ; edge-irr = λ a loop → loop refl
  }

{-
## Elimination of Presentation Freedom

### Law 13.1: Any K₄ Graph Presentation Collapses To The Canonical Graph Up To Iso
**Necessity Proof:** `law9-10-canonObs-sound`-style reasoning becomes definitional here:
`presentedGraph` only depends on the image in `EndoCase`. Since `toV` and `fromV` are
mutual inverses by the presentation laws, no additional edge structure survives.
  **Formal Reference:** K4Graph.agda.law13-1-presentation-iso (lines 102-111)
**Consequence:** Eliminates representational freedom: all admissible K₄ graph presentations
are isomorphic to the canonical graph.
-}

law13-1-presentation-iso : (p : K4GraphPresentation) → GraphIso (presentedGraph p) K4GraphCanonical
law13-1-presentation-iso p = record
  { to = toV p
  ; from = fromV p
  ; to-from = to-from p
  ; from-to = from-to p
  ; edge-to = λ {a} {b} e → e
  ; edge-from = λ {a} {b} e →
      transport≠ (sym (to-from p a)) (sym (to-from p b)) e
  }
