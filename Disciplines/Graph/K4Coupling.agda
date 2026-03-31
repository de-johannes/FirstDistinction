{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4Coupling where

open import FirstDistinction
open import Disciplines.Graph.K4Graph

{-
CHAPTER 14F: Coupling Two K₄ Instances (Elimination)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 13 (K₄ as Graph with Edge = ≠), Law 1.6 (finite case carriers)
AGDA MODULES: Disciplines.Graph.K4Coupling
DEGREES OF FREEDOM ELIMINATED: vertex-labeled coupling data between two copies of K₄
-}

-- Minimal truth type (not imported elsewhere).

data ⊤ : Set where
  tt : ⊤

-- Decidable equality for EndoCase (forced by exhaustive case classification).

EndoCase≠ : (a b : EndoCase) → Set
EndoCase≠ a b = a ≡ b → ⊥

case-constL≠case-constR : EndoCase≠ case-constL case-constR
case-constL≠case-constR ()

case-constL≠case-id : EndoCase≠ case-constL case-id
case-constL≠case-id ()

case-constL≠case-dual : EndoCase≠ case-constL case-dual
case-constL≠case-dual ()

case-constR≠case-id : EndoCase≠ case-constR case-id
case-constR≠case-id ()

case-constR≠case-dual : EndoCase≠ case-constR case-dual
case-constR≠case-dual ()

case-id≠case-dual : EndoCase≠ case-id case-dual
case-id≠case-dual ()

EndoCase-decEq : (a b : EndoCase) → (a ≡ b) ⊎ (EndoCase≠ a b)
EndoCase-decEq case-constL case-constL = inj₁ refl
EndoCase-decEq case-constR case-constR = inj₁ refl
EndoCase-decEq case-id     case-id     = inj₁ refl
EndoCase-decEq case-dual   case-dual   = inj₁ refl
EndoCase-decEq case-constL case-constR = inj₂ case-constL≠case-constR
EndoCase-decEq case-constR case-constL = inj₂ (λ e → case-constL≠case-constR (sym e))
EndoCase-decEq case-constL case-id     = inj₂ case-constL≠case-id
EndoCase-decEq case-id     case-constL = inj₂ (λ e → case-constL≠case-id (sym e))
EndoCase-decEq case-constL case-dual   = inj₂ case-constL≠case-dual
EndoCase-decEq case-dual   case-constL = inj₂ (λ e → case-constL≠case-dual (sym e))
EndoCase-decEq case-constR case-id     = inj₂ case-constR≠case-id
EndoCase-decEq case-id     case-constR = inj₂ (λ e → case-constR≠case-id (sym e))
EndoCase-decEq case-constR case-dual   = inj₂ case-constR≠case-dual
EndoCase-decEq case-dual   case-constR = inj₂ (λ e → case-constR≠case-dual (sym e))
EndoCase-decEq case-id     case-dual   = inj₂ case-id≠case-dual
EndoCase-decEq case-dual   case-id     = inj₂ (λ e → case-id≠case-dual (sym e))

-- A forced swap-permutation on EndoCase (explicit table; no equality elimination).

swapEndo : EndoCase → EndoCase → EndoCase → EndoCase
swapEndo case-constL case-constL z = z
swapEndo case-constL case-constR case-constL = case-constR
swapEndo case-constL case-constR case-constR = case-constL
swapEndo case-constL case-constR case-id     = case-id
swapEndo case-constL case-constR case-dual   = case-dual
swapEndo case-constL case-id     case-constL = case-id
swapEndo case-constL case-id     case-constR = case-constR
swapEndo case-constL case-id     case-id     = case-constL
swapEndo case-constL case-id     case-dual   = case-dual
swapEndo case-constL case-dual   case-constL = case-dual
swapEndo case-constL case-dual   case-constR = case-constR
swapEndo case-constL case-dual   case-id     = case-id
swapEndo case-constL case-dual   case-dual   = case-constL

swapEndo case-constR case-constL case-constL = case-constR
swapEndo case-constR case-constL case-constR = case-constL
swapEndo case-constR case-constL case-id     = case-id
swapEndo case-constR case-constL case-dual   = case-dual
swapEndo case-constR case-constR z = z
swapEndo case-constR case-id     case-constL = case-constL
swapEndo case-constR case-id     case-constR = case-id
swapEndo case-constR case-id     case-id     = case-constR
swapEndo case-constR case-id     case-dual   = case-dual
swapEndo case-constR case-dual   case-constL = case-constL
swapEndo case-constR case-dual   case-constR = case-dual
swapEndo case-constR case-dual   case-id     = case-id
swapEndo case-constR case-dual   case-dual   = case-constR

swapEndo case-id case-constL case-constL = case-id
swapEndo case-id case-constL case-constR = case-constR
swapEndo case-id case-constL case-id     = case-constL
swapEndo case-id case-constL case-dual   = case-dual
swapEndo case-id case-constR case-constL = case-constL
swapEndo case-id case-constR case-constR = case-id
swapEndo case-id case-constR case-id     = case-constR
swapEndo case-id case-constR case-dual   = case-dual
swapEndo case-id case-id z = z
swapEndo case-id case-dual case-constL = case-constL
swapEndo case-id case-dual case-constR = case-constR
swapEndo case-id case-dual case-id     = case-dual
swapEndo case-id case-dual case-dual   = case-id

swapEndo case-dual case-constL case-constL = case-dual
swapEndo case-dual case-constL case-constR = case-constR
swapEndo case-dual case-constL case-id     = case-id
swapEndo case-dual case-constL case-dual   = case-constL
swapEndo case-dual case-constR case-constL = case-constL
swapEndo case-dual case-constR case-constR = case-dual
swapEndo case-dual case-constR case-id     = case-id
swapEndo case-dual case-constR case-dual   = case-constR
swapEndo case-dual case-id     case-constL = case-constL
swapEndo case-dual case-id     case-constR = case-constR
swapEndo case-dual case-id     case-id     = case-dual
swapEndo case-dual case-id     case-dual   = case-id
swapEndo case-dual case-dual z = z

swapEndo-involutive : (x y z : EndoCase) → swapEndo x y (swapEndo x y z) ≡ z
swapEndo-involutive case-constL case-constL z = refl
swapEndo-involutive case-constL case-constR case-constL = refl
swapEndo-involutive case-constL case-constR case-constR = refl
swapEndo-involutive case-constL case-constR case-id     = refl
swapEndo-involutive case-constL case-constR case-dual   = refl
swapEndo-involutive case-constL case-id     case-constL = refl
swapEndo-involutive case-constL case-id     case-constR = refl
swapEndo-involutive case-constL case-id     case-id     = refl
swapEndo-involutive case-constL case-id     case-dual   = refl
swapEndo-involutive case-constL case-dual   case-constL = refl
swapEndo-involutive case-constL case-dual   case-constR = refl
swapEndo-involutive case-constL case-dual   case-id     = refl
swapEndo-involutive case-constL case-dual   case-dual   = refl

swapEndo-involutive case-constR case-constL case-constL = refl
swapEndo-involutive case-constR case-constL case-constR = refl
swapEndo-involutive case-constR case-constL case-id     = refl
swapEndo-involutive case-constR case-constL case-dual   = refl
swapEndo-involutive case-constR case-constR z = refl
swapEndo-involutive case-constR case-id     case-constL = refl
swapEndo-involutive case-constR case-id     case-constR = refl
swapEndo-involutive case-constR case-id     case-id     = refl
swapEndo-involutive case-constR case-id     case-dual   = refl
swapEndo-involutive case-constR case-dual   case-constL = refl
swapEndo-involutive case-constR case-dual   case-constR = refl
swapEndo-involutive case-constR case-dual   case-id     = refl
swapEndo-involutive case-constR case-dual   case-dual   = refl

swapEndo-involutive case-id case-constL case-constL = refl
swapEndo-involutive case-id case-constL case-constR = refl
swapEndo-involutive case-id case-constL case-id     = refl
swapEndo-involutive case-id case-constL case-dual   = refl
swapEndo-involutive case-id case-constR case-constL = refl
swapEndo-involutive case-id case-constR case-constR = refl
swapEndo-involutive case-id case-constR case-id     = refl
swapEndo-involutive case-id case-constR case-dual   = refl
swapEndo-involutive case-id case-id z = refl
swapEndo-involutive case-id case-dual case-constL = refl
swapEndo-involutive case-id case-dual case-constR = refl
swapEndo-involutive case-id case-dual case-id     = refl
swapEndo-involutive case-id case-dual case-dual   = refl

swapEndo-involutive case-dual case-constL case-constL = refl
swapEndo-involutive case-dual case-constL case-constR = refl
swapEndo-involutive case-dual case-constL case-id     = refl
swapEndo-involutive case-dual case-constL case-dual   = refl
swapEndo-involutive case-dual case-constR case-constL = refl
swapEndo-involutive case-dual case-constR case-constR = refl
swapEndo-involutive case-dual case-constR case-id     = refl
swapEndo-involutive case-dual case-constR case-dual   = refl
swapEndo-involutive case-dual case-id     case-constL = refl
swapEndo-involutive case-dual case-id     case-constR = refl
swapEndo-involutive case-dual case-id     case-id     = refl
swapEndo-involutive case-dual case-id     case-dual   = refl
swapEndo-involutive case-dual case-dual z = refl

swapEndo-sends : (x y : EndoCase) → swapEndo x y x ≡ y
swapEndo-sends case-constL case-constL = refl
swapEndo-sends case-constL case-constR = refl
swapEndo-sends case-constL case-id     = refl
swapEndo-sends case-constL case-dual   = refl
swapEndo-sends case-constR case-constL = refl
swapEndo-sends case-constR case-constR = refl
swapEndo-sends case-constR case-id     = refl
swapEndo-sends case-constR case-dual   = refl
swapEndo-sends case-id     case-constL = refl
swapEndo-sends case-id     case-constR = refl
swapEndo-sends case-id     case-id     = refl
swapEndo-sends case-id     case-dual   = refl
swapEndo-sends case-dual   case-constL = refl
swapEndo-sends case-dual   case-constR = refl
swapEndo-sends case-dual   case-id     = refl
swapEndo-sends case-dual   case-dual   = refl

-- Automorphisms needed for coupling elimination: carrier permutations in Set.

record EndoPerm : Set where
  field
    to       : EndoCase → EndoCase
    from     : EndoCase → EndoCase
    to-from  : (y : EndoCase) → to (from y) ≡ y
    from-to  : (x : EndoCase) → from (to x) ≡ x

open EndoPerm public

permSwap : (x y : EndoCase) → EndoPerm
permSwap x y = record
  { to = swapEndo x y
  ; from = swapEndo x y
  ; to-from = swapEndo-involutive x y
  ; from-to = swapEndo-involutive x y
  }

-- Transitivity witness: any endpoint can be moved to any other.

endoPerm-send : (a a' : EndoCase) → Σ EndoPerm (λ σ → to σ a ≡ a')
endoPerm-send a a' = permSwap a a' , swapEndo-sends a a'

-- A coupling predicate between the two copies (left EndoCase to right EndoCase).

Coupling : Set1
Coupling = EndoCase → EndoCase → Set

CrossInv : Coupling → Set
CrossInv C = (σ τ : EndoPerm) → (a b : EndoCase) → C a b → C (to σ a) (to τ b)

transport2 : {A B : Set} {P : A → B → Set} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → P a b → P a' b'
transport2 {P = P} {a = a} {a' = a'} {b = b} {b' = b'} ea eb pab =
  subst (λ a0 → P a0 b') ea (subst (λ b0 → P a b0) eb pab)

{-
## Elimination of Vertex-Labeled Coupling

### Law 14F.0: An Iso-Invariant Coupling With One Edge Forces The Complete Join
**Necessity Proof:** Under `CrossInv`, a witness `C a₀ b₀` propagates along automorphisms.
Since every endpoint can be swapped into any other endpoint, the coupling cannot retain
vertex labels; otherwise a degree of freedom survives. Therefore one edge forces all edges.
  **Formal Reference:** K4Coupling.agda.law14F-0-edge-forces-all (lines 244-252)
**Consequence:** Eliminates all intermediate cross-couplings between two unlabeled K₄ copies.
-}

law14F-0-edge-forces-all : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → C a0 b0)) →
  (a b : EndoCase) → C a b
law14F-0-edge-forces-all C inv (a0 , (b0 , c0)) a b =
  let sa = endoPerm-send a0 a in
  let sb = endoPerm-send b0 b in
  let σ = fst sa in
  let τ = fst sb in
  transport2 {P = C} (snd sa) (snd sb) (inv σ τ a0 b0 c0)

{-
### Law 14F.1: An Iso-Invariant Coupling With One Non-Edge Forces The Disjoint Union
**Necessity Proof:** Under `CrossInv`, any alleged edge `C a b` can be transported back to
any chosen pair `(a₀,b₀)` by swapping endpoints. If `¬ C a₀ b₀`, then every transported edge
contradicts. Therefore one non-edge forces no edges.
  **Formal Reference:** K4Coupling.agda.law14F-1-nonedge-forces-none (lines 263-271)
**Consequence:** Eliminates all intermediate cross-couplings between two unlabeled K₄ copies.
-}

law14F-1-nonedge-forces-none : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → ¬ (C a0 b0))) →
  (a b : EndoCase) → ¬ (C a b)
law14F-1-nonedge-forces-none C inv (a0 , (b0 , n0)) a b cab =
  let sa = endoPerm-send a a0 in
  let sb = endoPerm-send b b0 in
  let σ = fst sa in
  let τ = fst sb in
  n0 (transport2 {P = C} (snd sa) (snd sb) (inv σ τ a b cab))

-- Two canonical survivors as actual graphs on Two × EndoCase.

Two≠ : (i j : Two) → Set
Two≠ i j = i ≡ j → ⊥

L≠R : Two≠ L R
L≠R ()

Two-decEq : (i j : Two) → (i ≡ j) ⊎ (Two≠ i j)
Two-decEq L L = inj₁ refl
Two-decEq R R = inj₁ refl
Two-decEq L R = inj₂ L≠R
Two-decEq R L = inj₂ (λ e → L≠R (sym e))

Edge2 : Coupling → (Two × EndoCase) → (Two × EndoCase) → Set
Edge2 C (L , a) (L , b) = a ≠ b
Edge2 C (R , a) (R , b) = a ≠ b
Edge2 C (L , a) (R , b) = C a b
Edge2 C (R , a) (L , b) = C b a

edge2-sym : (C : Coupling) → {x y : Two × EndoCase} → Edge2 C x y → Edge2 C y x
edge2-sym C {x = (L , a)} {y = (L , b)} e = λ eq → e (sym eq)
edge2-sym C {x = (R , a)} {y = (R , b)} e = λ eq → e (sym eq)
edge2-sym C {x = (L , a)} {y = (R , b)} e = e
edge2-sym C {x = (R , a)} {y = (L , b)} e = e

edge2-irr : (C : Coupling) → (x : Two × EndoCase) → Edge2 C x x → ⊥
edge2-irr C (L , a) e = e refl
edge2-irr C (R , a) e = e refl

K4×2 : Coupling → Graph
K4×2 C = record
  { V = Two × EndoCase
  ; Edge = Edge2 C
  ; edge-sym = λ {a} {b} e → edge2-sym C {x = a} {y = b} e
  ; edge-irr = edge2-irr C
  }

CrossEmpty : Coupling
CrossEmpty _ _ = ⊥

CrossFull : Coupling
CrossFull _ _ = ⊤
