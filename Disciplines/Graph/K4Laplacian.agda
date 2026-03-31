{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4Laplacian where

open import FirstDistinction
open import Disciplines.Graph.K4Graph
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers

{-
CHAPTER 14: Neighborhood and Laplacian Presentation (K₄)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 13
AGDA MODULES: Disciplines.Graph.K4Laplacian
DEGREES OF FREEDOM ELIMINATED: ambiguity in neighborhood structure of the canonical K₄ graph
-}

Adj : EndoCase → EndoCase → Set
Adj a b = Edge K4GraphCanonical a b

record NeighborTriple (v : EndoCase) : Set where
  field
    n₁ n₂ n₃ : EndoCase
    adj₁     : Adj v n₁
    adj₂     : Adj v n₂
    adj₃     : Adj v n₃
    n₁≠n₂     : n₁ ≠ n₂
    n₁≠n₃     : n₁ ≠ n₃
    n₂≠n₃     : n₂ ≠ n₃
    complete : (u : EndoCase) → Adj v u → (u ≡ n₁) ⊎ ((u ≡ n₂) ⊎ (u ≡ n₃))

open NeighborTriple public

case-constL≠case-constR : case-constL ≠ case-constR
case-constL≠case-constR = fst EndoCase-distinct

case-constL≠case-id : case-constL ≠ case-id
case-constL≠case-id = fst (snd EndoCase-distinct)

case-constL≠case-dual : case-constL ≠ case-dual
case-constL≠case-dual = fst (snd (snd EndoCase-distinct))

case-constR≠case-id : case-constR ≠ case-id
case-constR≠case-id = fst (snd (snd (snd EndoCase-distinct)))

case-constR≠case-dual : case-constR ≠ case-dual
case-constR≠case-dual = fst (snd (snd (snd (snd EndoCase-distinct))))

case-id≠case-dual : case-id ≠ case-dual
case-id≠case-dual = snd (snd (snd (snd (snd EndoCase-distinct))))

case-constR≠case-constL : case-constR ≠ case-constL
case-constR≠case-constL eq = case-constL≠case-constR (sym eq)

case-id≠case-constL : case-id ≠ case-constL
case-id≠case-constL eq = case-constL≠case-id (sym eq)

case-dual≠case-constL : case-dual ≠ case-constL
case-dual≠case-constL eq = case-constL≠case-dual (sym eq)

case-id≠case-constR : case-id ≠ case-constR
case-id≠case-constR eq = case-constR≠case-id (sym eq)

case-dual≠case-constR : case-dual ≠ case-constR
case-dual≠case-constR eq = case-constR≠case-dual (sym eq)

case-dual≠case-id : case-dual ≠ case-id
case-dual≠case-id eq = case-id≠case-dual (sym eq)

{-
## Neighborhood Exhaustion

### Law 14.0: Every Vertex Has Exactly Three Neighbors (Exhaustive Classification)
**Necessity Proof:** `EndoCase` has exactly four constructor cases. For a fixed vertex `v`,
`Adj v u` is definitional inequality. Therefore the only possible neighbors are the
three remaining constructor cases, and any other neighbor claim collapses by elimination.
  **Formal Reference:** K4Laplacian.agda.law14-0-neighbor-triple (lines 82-150)
**Consequence:** Eliminates any non-canonical neighborhood structure in the K₄ graph layer.
-}

law14-0-neighbor-triple : (v : EndoCase) → NeighborTriple v
law14-0-neighbor-triple case-constL = record
  { n₁ = case-constR
  ; n₂ = case-id
  ; n₃ = case-dual
  ; adj₁ = case-constL≠case-constR
  ; adj₂ = case-constL≠case-id
  ; adj₃ = case-constL≠case-dual
  ; n₁≠n₂ = case-constR≠case-id
  ; n₁≠n₃ = case-constR≠case-dual
  ; n₂≠n₃ = case-id≠case-dual
  ; complete = λ
      { case-constL adj → ⊥-elim (adj refl)
      ; case-constR adj → inj₁ refl
      ; case-id     adj → inj₂ (inj₁ refl)
      ; case-dual   adj → inj₂ (inj₂ refl)
      }
  }
law14-0-neighbor-triple case-constR = record
  { n₁ = case-constL
  ; n₂ = case-id
  ; n₃ = case-dual
  ; adj₁ = case-constR≠case-constL
  ; adj₂ = case-constR≠case-id
  ; adj₃ = case-constR≠case-dual
  ; n₁≠n₂ = case-constL≠case-id
  ; n₁≠n₃ = case-constL≠case-dual
  ; n₂≠n₃ = case-id≠case-dual
  ; complete = λ
      { case-constL adj → inj₁ refl
      ; case-constR adj → ⊥-elim (adj refl)
      ; case-id     adj → inj₂ (inj₁ refl)
      ; case-dual   adj → inj₂ (inj₂ refl)
      }
  }
law14-0-neighbor-triple case-id = record
  { n₁ = case-constL
  ; n₂ = case-constR
  ; n₃ = case-dual
  ; adj₁ = case-id≠case-constL
  ; adj₂ = case-id≠case-constR
  ; adj₃ = case-id≠case-dual
  ; n₁≠n₂ = case-constL≠case-constR
  ; n₁≠n₃ = case-constL≠case-dual
  ; n₂≠n₃ = case-constR≠case-dual
  ; complete = λ
      { case-constL adj → inj₁ refl
      ; case-constR adj → inj₂ (inj₁ refl)
      ; case-id     adj → ⊥-elim (adj refl)
      ; case-dual   adj → inj₂ (inj₂ refl)
      }
  }
law14-0-neighbor-triple case-dual = record
  { n₁ = case-constL
  ; n₂ = case-constR
  ; n₃ = case-id
  ; adj₁ = case-dual≠case-constL
  ; adj₂ = case-dual≠case-constR
  ; adj₃ = case-dual≠case-id
  ; n₁≠n₂ = case-constL≠case-constR
  ; n₁≠n₃ = case-constL≠case-id
  ; n₂≠n₃ = case-constR≠case-id
  ; complete = λ
      { case-constL adj → inj₁ refl
      ; case-constR adj → inj₂ (inj₁ refl)
      ; case-id     adj → inj₂ (inj₂ refl)
      ; case-dual   adj → ⊥-elim (adj refl)
      }
  }

neighborAt : (v : EndoCase) → Fin3 → EndoCase
neighborAt v f0 = n₁ (law14-0-neighbor-triple v)
neighborAt v f1 = n₂ (law14-0-neighbor-triple v)
neighborAt v f2 = n₃ (law14-0-neighbor-triple v)

neighborAt-adj : (v : EndoCase) → (i : Fin3) → Adj v (neighborAt v i)
neighborAt-adj v f0 = adj₁ (law14-0-neighbor-triple v)
neighborAt-adj v f1 = adj₂ (law14-0-neighbor-triple v)
neighborAt-adj v f2 = adj₃ (law14-0-neighbor-triple v)

neighborAt-injective : (v : EndoCase) → {i j : Fin3} → neighborAt v i ≡ neighborAt v j → i ≡ j
neighborAt-injective v {f0} {f0} _ = refl
neighborAt-injective v {f1} {f1} _ = refl
neighborAt-injective v {f2} {f2} _ = refl
neighborAt-injective v {f0} {f1} eq = ⊥-elim (n₁≠n₂ (law14-0-neighbor-triple v) eq)
neighborAt-injective v {f1} {f0} eq = ⊥-elim (n₁≠n₂ (law14-0-neighbor-triple v) (sym eq))
neighborAt-injective v {f0} {f2} eq = ⊥-elim (n₁≠n₃ (law14-0-neighbor-triple v) eq)
neighborAt-injective v {f2} {f0} eq = ⊥-elim (n₁≠n₃ (law14-0-neighbor-triple v) (sym eq))
neighborAt-injective v {f1} {f2} eq = ⊥-elim (n₂≠n₃ (law14-0-neighbor-triple v) eq)
neighborAt-injective v {f2} {f1} eq = ⊥-elim (n₂≠n₃ (law14-0-neighbor-triple v) (sym eq))

sum3ℤ : ℤ → ℤ → ℤ → ℤ
sum3ℤ a b c = a +ℤ (b +ℤ c)

sumFin3ℤ : (Fin3 → ℤ) → ℤ
sumFin3ℤ f = sum3ℤ (f f0) (f f1) (f f2)

adjSumℤ : (EndoCase → ℤ) → EndoCase → ℤ
adjSumℤ f v = sumFin3ℤ (λ i → f (neighborAt v i))

deg3ℤ : (EndoCase → ℤ) → EndoCase → ℤ
deg3ℤ f v = sum3ℤ (f v) (f v) (f v)

laplacianℤ : (EndoCase → ℤ) → EndoCase → ℤ
laplacianℤ f v = deg3ℤ f v +ℤ negℤ (adjSumℤ f v)
