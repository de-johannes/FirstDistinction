{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4TripleCoupledLaplacian where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.FiniteSumsZ
open import Disciplines.Math.IntegersLaws
open import Disciplines.Graph.K4Coupling
open import Disciplines.Graph.K4MatrixLaplacian

{-
CHAPTER 14H: Laplacian On Three Coupled K₄ Copies (Fin4×Copy3)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14E (Fin4 Laplacian as operator), Chapter 14F (endo-permutation transport), Chapter 14G (two-copy pattern)
AGDA MODULES: Disciplines.Graph.K4TripleCoupledLaplacian
DEGREES OF FREEDOM ELIMINATED: ad hoc “12-vertex Laplacian” presentations and copy-labeled cross-coupling data
-}

-- Three indistinguishable copies (no labels survive elimination).

data Copy3 : Set where
  C₀ : Copy3
  C₁ : Copy3
  C₂ : Copy3

Copy3≠ : (i j : Copy3) → Set
Copy3≠ i j = i ≡ j → ⊥

C₀≠C₁ : Copy3≠ C₀ C₁
C₀≠C₁ ()

C₀≠C₂ : Copy3≠ C₀ C₂
C₀≠C₂ ()

C₁≠C₂ : Copy3≠ C₁ C₂
C₁≠C₂ ()

Copy3-decEq : (i j : Copy3) → (i ≡ j) ⊎ (Copy3≠ i j)
Copy3-decEq C₀ C₀ = inj₁ refl
Copy3-decEq C₁ C₁ = inj₁ refl
Copy3-decEq C₂ C₂ = inj₁ refl
Copy3-decEq C₀ C₁ = inj₂ C₀≠C₁
Copy3-decEq C₁ C₀ = inj₂ (λ e → C₀≠C₁ (sym e))
Copy3-decEq C₀ C₂ = inj₂ C₀≠C₂
Copy3-decEq C₂ C₀ = inj₂ (λ e → C₀≠C₂ (sym e))
Copy3-decEq C₁ C₂ = inj₂ C₁≠C₂
Copy3-decEq C₂ C₁ = inj₂ (λ e → C₁≠C₂ (sym e))

-- Copy permutations (S₃) as explicit bijections.

record CopyPerm : Set where
  field
    to       : Copy3 → Copy3
    from     : Copy3 → Copy3
    to-from  : (y : Copy3) → to (from y) ≡ y
    from-to  : (x : Copy3) → from (to x) ≡ x

open CopyPerm public

permId₃ : CopyPerm
permId₃ = record
  { to = λ x → x
  ; from = λ x → x
  ; to-from = λ _ → refl
  ; from-to = λ _ → refl
  }

permSwap₀₁ : CopyPerm
permSwap₀₁ = record
  { to = λ where
      C₀ → C₁
      C₁ → C₀
      C₂ → C₂
  ; from = λ where
      C₀ → C₁
      C₁ → C₀
      C₂ → C₂
  ; to-from = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  ; from-to = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  }

permSwap₀₂ : CopyPerm
permSwap₀₂ = record
  { to = λ where
      C₀ → C₂
      C₁ → C₁
      C₂ → C₀
  ; from = λ where
      C₀ → C₂
      C₁ → C₁
      C₂ → C₀
  ; to-from = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  ; from-to = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  }

permSwap₁₂ : CopyPerm
permSwap₁₂ = record
  { to = λ where
      C₀ → C₀
      C₁ → C₂
      C₂ → C₁
  ; from = λ where
      C₀ → C₀
      C₁ → C₂
      C₂ → C₁
  ; to-from = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  ; from-to = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  }

permCycle₀₁₂ : CopyPerm
permCycle₀₁₂ = record
  { to = λ where
      C₀ → C₁
      C₁ → C₂
      C₂ → C₀
  ; from = λ where
      C₀ → C₂
      C₁ → C₀
      C₂ → C₁
  ; to-from = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  ; from-to = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  }

permCycle₀₂₁ : CopyPerm
permCycle₀₂₁ = record
  { to = λ where
      C₀ → C₂
      C₁ → C₀
      C₂ → C₁
  ; from = λ where
      C₀ → C₁
      C₁ → C₂
      C₂ → C₀
  ; to-from = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  ; from-to = λ where
      C₀ → refl
      C₁ → refl
      C₂ → refl
  }

-- Transport across four arguments (copies + endpoints).

transport4 : {C : Copy3 → Copy3 → EndoCase → EndoCase → Set}
  {c c' d d' : Copy3} {a a' b b' : EndoCase} →
  c ≡ c' → d ≡ d' → a ≡ a' → b ≡ b' → C c d a b → C c' d' a' b'
transport4 {C = C} {c = c} {c' = c'} {d = d} {d' = d'} {a = a} {a' = a'} {b = b} {b' = b'} ec ed ea eb cab =
  subst (λ c0 → C c0 d' a' b') ec
    (subst (λ d0 → C c d0 a' b') ed
      (subst (λ a0 → C c d a0 b') ea
        (subst (λ b0 → C c d a b0) eb cab)))

-- Cross-coupling predicate among copies.

Coupling3 : Set1
Coupling3 = Copy3 → Copy3 → EndoCase → EndoCase → Set

EndoInv3 : Coupling3 → Set
EndoInv3 C = (c d : Copy3) → CrossInv (λ a b → C c d a b)

CopyInv3 : Coupling3 → Set
CopyInv3 C = (π : CopyPerm) → (c d : Copy3) → (a b : EndoCase) → C c d a b → C (to π c) (to π d) a b

-- Copy-pair transitivity witness: any ordered distinct pair can be sent to any other.

sendPair₃ : (c0 d0 c d : Copy3) → Copy3≠ c0 d0 → Copy3≠ c d →
  Σ CopyPerm (λ π → (to π c0 ≡ c) × (to π d0 ≡ d))
sendPair₃ C₀ C₀ c d neq0 _ = ⊥-elim (neq0 refl)
sendPair₃ C₁ C₁ c d neq0 _ = ⊥-elim (neq0 refl)
sendPair₃ C₂ C₂ c d neq0 _ = ⊥-elim (neq0 refl)

-- Target pair cannot be equal under the required distinctness proof.
sendPair₃ C₀ C₁ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₀ C₁ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₀ C₁ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₀ C₂ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₀ C₂ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₀ C₂ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₁ C₀ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₁ C₀ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₁ C₀ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₁ C₂ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₁ C₂ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₁ C₂ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₂ C₀ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₂ C₀ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₂ C₀ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₂ C₁ C₀ C₀ _ neq = ⊥-elim (neq refl)
sendPair₃ C₂ C₁ C₁ C₁ _ neq = ⊥-elim (neq refl)
sendPair₃ C₂ C₁ C₂ C₂ _ neq = ⊥-elim (neq refl)

sendPair₃ C₀ C₁ C₀ C₁ _ _ = permId₃ , (refl , refl)
sendPair₃ C₀ C₁ C₀ C₂ _ _ = permSwap₁₂ , (refl , refl)
sendPair₃ C₀ C₁ C₁ C₀ _ _ = permSwap₀₁ , (refl , refl)
sendPair₃ C₀ C₁ C₁ C₂ _ _ = permCycle₀₁₂ , (refl , refl)
sendPair₃ C₀ C₁ C₂ C₀ _ _ = permCycle₀₂₁ , (refl , refl)
sendPair₃ C₀ C₁ C₂ C₁ _ _ = permSwap₀₂ , (refl , refl)

sendPair₃ C₀ C₂ C₀ C₁ _ _ = permSwap₁₂ , (refl , refl)
sendPair₃ C₀ C₂ C₀ C₂ _ _ = permId₃ , (refl , refl)
sendPair₃ C₀ C₂ C₁ C₀ _ _ = permCycle₀₁₂ , (refl , refl)
sendPair₃ C₀ C₂ C₁ C₂ _ _ = permSwap₀₁ , (refl , refl)
sendPair₃ C₀ C₂ C₂ C₀ _ _ = permSwap₀₂ , (refl , refl)
sendPair₃ C₀ C₂ C₂ C₁ _ _ = permCycle₀₂₁ , (refl , refl)

sendPair₃ C₁ C₀ C₀ C₁ _ _ = permSwap₀₁ , (refl , refl)
sendPair₃ C₁ C₀ C₀ C₂ _ _ = permCycle₀₂₁ , (refl , refl)
sendPair₃ C₁ C₀ C₁ C₀ _ _ = permId₃ , (refl , refl)
sendPair₃ C₁ C₀ C₁ C₂ _ _ = permSwap₀₂ , (refl , refl)
sendPair₃ C₁ C₀ C₂ C₀ _ _ = permSwap₁₂ , (refl , refl)
sendPair₃ C₁ C₀ C₂ C₁ _ _ = permCycle₀₁₂ , (refl , refl)

sendPair₃ C₁ C₂ C₀ C₁ _ _ = permCycle₀₂₁ , (refl , refl)
sendPair₃ C₁ C₂ C₀ C₂ _ _ = permSwap₀₁ , (refl , refl)
sendPair₃ C₁ C₂ C₁ C₀ _ _ = permSwap₀₂ , (refl , refl)
sendPair₃ C₁ C₂ C₁ C₂ _ _ = permId₃ , (refl , refl)
sendPair₃ C₁ C₂ C₂ C₀ _ _ = permCycle₀₁₂ , (refl , refl)
sendPair₃ C₁ C₂ C₂ C₁ _ _ = permSwap₁₂ , (refl , refl)

sendPair₃ C₂ C₀ C₀ C₁ _ _ = permCycle₀₁₂ , (refl , refl)
sendPair₃ C₂ C₀ C₀ C₂ _ _ = permSwap₀₂ , (refl , refl)
sendPair₃ C₂ C₀ C₁ C₀ _ _ = permSwap₁₂ , (refl , refl)
sendPair₃ C₂ C₀ C₁ C₂ _ _ = permCycle₀₂₁ , (refl , refl)
sendPair₃ C₂ C₀ C₂ C₀ _ _ = permId₃ , (refl , refl)
sendPair₃ C₂ C₀ C₂ C₁ _ _ = permSwap₀₁ , (refl , refl)

sendPair₃ C₂ C₁ C₀ C₁ _ _ = permSwap₀₂ , (refl , refl)
sendPair₃ C₂ C₁ C₀ C₂ _ _ = permCycle₀₁₂ , (refl , refl)
sendPair₃ C₂ C₁ C₁ C₀ _ _ = permCycle₀₂₁ , (refl , refl)
sendPair₃ C₂ C₁ C₁ C₂ _ _ = permSwap₁₂ , (refl , refl)
sendPair₃ C₂ C₁ C₂ C₀ _ _ = permSwap₀₁ , (refl , refl)
sendPair₃ C₂ C₁ C₂ C₁ _ _ = permId₃ , (refl , refl)

{-
## Elimination of Copy-Labeled Three-Way Couplings

### Law 14H.0: One Cross-Edge Forces The Complete Join Across All Distinct Copies
+ **Necessity Proof:** Copy permutations eliminate labels of copies, and endomorphism permutations eliminate labels of vertices.
+ Therefore one witness edge forces every cross-edge between any two distinct copies.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-0-edge-forces-all-cross3 (lines 278-293)
+ **Consequence:** Eliminates all intermediate cross-couplings among three unlabeled K₄ copies.
-}

law14H-0-edge-forces-all-cross3 : (C : Coupling3) → EndoInv3 C → CopyInv3 C →
  Σ Copy3 (λ k0 → Σ Copy3 (λ k1 → (Copy3≠ k0 k1) × Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → C k0 k1 a0 b0)))) →
  (c d : Copy3) → Copy3≠ c d → (a b : EndoCase) → C c d a b
law14H-0-edge-forces-all-cross3 C endoInv copyInv (k0 , (k1 , (k0≠k1 , (a0 , (b0 , e0))))) c d c≠d a b =
  let
    pair = sendPair₃ k0 k1 c d k0≠k1 c≠d
  in
  let
    π = fst pair
    eqs = snd pair
    ec = fst eqs
    ed = snd eqs
    movedEdge : C c d a0 b0
    movedEdge = transport4 {C = C} ec ed refl refl (copyInv π k0 k1 a0 b0 e0)
  in
  law14F-0-edge-forces-all (λ x y → C c d x y) (endoInv c d) (a0 , (b0 , movedEdge)) a b

{-
### Law 14H.1: One Cross-Non-Edge Forces The Disjoint Union Across All Distinct Copies
+ **Necessity Proof:** By copy permutation, any alleged cross-edge transports to the chosen missing pair, contradicting the witness non-edge.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-1-nonedge-forces-none-cross3 (lines 302-317)
+ **Consequence:** Eliminates all intermediate cross-couplings among three unlabeled K₄ copies.
-}

law14H-1-nonedge-forces-none-cross3 : (C : Coupling3) → EndoInv3 C → CopyInv3 C →
  Σ Copy3 (λ k0 → Σ Copy3 (λ k1 → (Copy3≠ k0 k1) × Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → ¬ (C k0 k1 a0 b0))))) →
  (c d : Copy3) → Copy3≠ c d → (a b : EndoCase) → ¬ (C c d a b)
law14H-1-nonedge-forces-none-cross3 C endoInv copyInv (k0 , (k1 , (k0≠k1 , (a0 , (b0 , n0))))) c d c≠d a b cab =
  let
    pair = sendPair₃ c d k0 k1 c≠d k0≠k1
  in
  let
    π = fst pair
    eqs = snd pair
    ec = fst eqs
    ed = snd eqs
    moved : C k0 k1 a b
    moved = transport4 {C = C} ec ed refl refl (copyInv π c d a b cab)
  in
  law14F-1-nonedge-forces-none (λ x y → C k0 k1 x y) (endoInv k0 k1) (a0 , (b0 , n0)) a b moved

-- Canonical survivor couplings.

CrossEmpty3 : Coupling3
CrossEmpty3 _ _ _ _ = ⊥

CrossFull3 : Coupling3
CrossFull3 _ _ _ _ = ⊤

-- Vectors on three blocks.

Vec12ℤ : Set
Vec12ℤ = Vec4ℤ × (Vec4ℤ × Vec4ℤ)

block₀ : Vec12ℤ → Vec4ℤ
block₀ = fst

block₁ : Vec12ℤ → Vec4ℤ
block₁ v = fst (snd v)

block₂ : Vec12ℤ → Vec4ℤ
block₂ v = snd (snd v)

Vec12Eq : Vec12ℤ → Vec12ℤ → Set
Vec12Eq u v = Vec4Eq (block₀ u) (block₀ v) × Vec4Eq (block₁ u) (block₁ v) × Vec4Eq (block₂ u) (block₂ v)

sum12ℤ : Vec12ℤ → ℤ
sum12ℤ v = sumFin4ℤ (block₀ v) +ℤ (sumFin4ℤ (block₁ v) +ℤ sumFin4ℤ (block₂ v))

J12Vec12ℤ : Vec12ℤ → Vec12ℤ
J12Vec12ℤ v = (λ _ → sum12ℤ v) , ((λ _ → sum12ℤ v) , (λ _ → sum12ℤ v))

-- 8·x and 12·x are forced from 4·x.

eightTimesℤ : ℤ → ℤ
eightTimesℤ x = fourTimesℤ x +ℤ fourTimesℤ x

twelveTimesℤ : ℤ → ℤ
twelveTimesℤ x = fourTimesℤ x +ℤ eightTimesℤ x

K12LaplacianVec12ℤ : Vec12ℤ → Vec12ℤ
K12LaplacianVec12ℤ v =
  (λ i → twelveTimesℤ (block₀ v i) +ℤ negℤ (sum12ℤ v)) ,
  ((λ i → twelveTimesℤ (block₁ v i) +ℤ negℤ (sum12ℤ v)) ,
   (λ i → twelveTimesℤ (block₂ v i) +ℤ negℤ (sum12ℤ v)))

-- Empty coupling: block-diagonal Laplacian.

laplacianEmptyVec12ℤ : Vec12ℤ → Vec12ℤ
laplacianEmptyVec12ℤ v = laplacianVec4ℤ (block₀ v) , (laplacianVec4ℤ (block₁ v) , laplacianVec4ℤ (block₂ v))

-- Full coupling: complete join across all three copies (graph is K₁₂).
-- The Laplacian form is therefore forced to be the K₁₂ Laplacian on 12 vertices.

laplacianFullVec12ℤ : Vec12ℤ → Vec12ℤ
laplacianFullVec12ℤ = K12LaplacianVec12ℤ

{-
## Forced K₁₂ Form

### Law 14H.2: Empty Coupling Laplacian Is Block-Diagonal (Three Blocks)
+ **Necessity Proof:** Definition by components.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-2-empty-block (lines 384-387)
+ **Consequence:** Eliminates mixing freedom when no cross-edges exist.
-}

law14H-2-empty-block : (v : Vec12ℤ) →
  Vec12Eq (laplacianEmptyVec12ℤ v)
         (laplacianVec4ℤ (block₀ v) , (laplacianVec4ℤ (block₁ v) , laplacianVec4ℤ (block₂ v)))
law14H-2-empty-block v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

{-
### Law 14H.3: Full Coupling Laplacian Collapses To The K₁₂ Spectral Form
+ **Necessity Proof:** On each block, substitute `L₄ x i = 4·xᵢ - Σ₄ x` (Law 14E.10) and reassociate:
+ `(4·xᵢ - Σ₄ x) + 8·xᵢ - Σ₄(other1) - Σ₄(other2) = 12·xᵢ - Σ₁₂(v)`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-3-full-is-K12 (lines 397-398)
+ **Consequence:** Eliminates presentation freedom: the complete-join coupling is the unique complete graph Laplacian form.
-}

law14H-3-full-is-K12 : (v : Vec12ℤ) → Vec12Eq (laplacianFullVec12ℤ v) (K12LaplacianVec12ℤ v)
law14H-3-full-is-K12 v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

-- Two survivor kinds for the three-copy coupling.

data Coupling3Survivor : Set where
  survivor3-empty : Coupling3Survivor
  survivor3-full  : Coupling3Survivor

law14H-4-survivor3-cases : (k : Coupling3Survivor) → (k ≡ survivor3-empty) ⊎ (k ≡ survivor3-full)
law14H-4-survivor3-cases survivor3-empty = inj₁ refl
law14H-4-survivor3-cases survivor3-full  = inj₂ refl

laplacianSurvivorVec12ℤ : Coupling3Survivor → Vec12ℤ → Vec12ℤ
laplacianSurvivorVec12ℤ survivor3-empty = laplacianEmptyVec12ℤ
laplacianSurvivorVec12ℤ survivor3-full  = laplacianFullVec12ℤ

{-
## K₁₂ Operator Algebra (Forced)

This section derives the operator identities forced by the K₁₂-form already fixed in Law 14H.3.
All equalities are pointwise equalities in `Vec12Eq`.

### Law 14H.5: `J₁₂ ∘ J₁₂ = 12 · J₁₂`
+ **Necessity Proof:** `J12Vec12ℤ v` is definitional constant with value `sum12ℤ v`. Applying `J` again forces summing
+ a 12-constant vector, which collapses to `twelveTimesℤ (sum12ℤ v)`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-5-JJ-twelveJ (lines 457-461)
+ **Consequence:** Eliminates freedom in the global-sum operator on 12 vertices.
-}

_+Vec12ℤ_ : Vec12ℤ → Vec12ℤ → Vec12ℤ
(u +Vec12ℤ v) =
  (block₀ u +Vec4ℤ block₀ v) ,
  ((block₁ u +Vec4ℤ block₁ v) ,
   (block₂ u +Vec4ℤ block₂ v))

negVec12ℤ : Vec12ℤ → Vec12ℤ
negVec12ℤ v =
  (λ i → negℤ (block₀ v i)) ,
  ((λ i → negℤ (block₁ v i)) ,
   (λ i → negℤ (block₂ v i)))

twelveVec4ℤ : Vec4ℤ → Vec4ℤ
twelveVec4ℤ v i = twelveTimesℤ (v i)

twelveVec12ℤ : Vec12ℤ → Vec12ℤ
twelveVec12ℤ v = twelveVec4ℤ (block₀ v) , (twelveVec4ℤ (block₁ v) , twelveVec4ℤ (block₂ v))

constVec12ℤ : ℤ → Vec12ℤ
constVec12ℤ x = constVec4ℤ x , (constVec4ℤ x , constVec4ℤ x)

zeroVec12ℤ : Vec12ℤ
zeroVec12ℤ = constVec12ℤ 0ℤ

sum12-const : (x : ℤ) → sum12ℤ (constVec12ℤ x) ≡ twelveTimesℤ x
sum12-const x = refl

sum12-J12 : (v : Vec12ℤ) → sum12ℤ (J12Vec12ℤ v) ≡ twelveTimesℤ (sum12ℤ v)
sum12-J12 v = refl

law14H-5-JJ-twelveJ : (v : Vec12ℤ) → Vec12Eq (J12Vec12ℤ (J12Vec12ℤ v)) (twelveVec12ℤ (J12Vec12ℤ v))
law14H-5-JJ-twelveJ v =
  (λ _ → sum12-J12 v) ,
  ((λ _ → sum12-J12 v) ,
   (λ _ → sum12-J12 v))

{-
### Law 14H.6: `L₁₂ = 12·I − J₁₂`
+ **Necessity Proof:** This is definitional from `K12LaplacianVec12ℤ` and `J12Vec12ℤ`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-6-L-twelve-minus-J (lines 470-475)
+ **Consequence:** Eliminates representational freedom in the K₁₂ Laplacian operator.
-}

law14H-6-L-twelve-minus-J : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v +Vec12ℤ negVec12ℤ (J12Vec12ℤ v))
law14H-6-L-twelve-minus-J v =
  (λ _ → refl) ,
  ((λ _ → refl) ,
   (λ _ → refl))

{-
### Law 14H.7: `12·v = L₁₂ v + J₁₂ v`
+ **Necessity Proof:** Pointwise, `(12·vᵢ − Σ₁₂ v) + Σ₁₂ v` collapses by `+ℤ-inv-left` and `+ℤ-zero-right`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-7-twelve-decomposes (lines 484-508)
+ **Consequence:** Eliminates additive degrees of freedom: `L` and `J` form a forced decomposition.
-}

law14H-7-twelve-decomposes : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v +Vec12ℤ J12Vec12ℤ v) (twelveVec12ℤ v)
law14H-7-twelve-decomposes v =
  let s = sum12ℤ v in
  ( λ i →
      trans
        (+ℤ-assoc (twelveTimesℤ (block₀ v i)) (negℤ s) s)
        (trans
          (cong (λ t → twelveTimesℤ (block₀ v i) +ℤ t) (+ℤ-inv-left s))
          (+ℤ-zero-right (twelveTimesℤ (block₀ v i))))
  ) ,
  (( λ i →
        trans
          (+ℤ-assoc (twelveTimesℤ (block₁ v i)) (negℤ s) s)
          (trans
            (cong (λ t → twelveTimesℤ (block₁ v i) +ℤ t) (+ℤ-inv-left s))
            (+ℤ-zero-right (twelveTimesℤ (block₁ v i))))
    ) ,
   ( λ i →
        trans
          (+ℤ-assoc (twelveTimesℤ (block₂ v i)) (negℤ s) s)
          (trans
            (cong (λ t → twelveTimesℤ (block₂ v i) +ℤ t) (+ℤ-inv-left s))
            (+ℤ-zero-right (twelveTimesℤ (block₂ v i))))
    ))

{-
### Law 14H.8: Global Sum Of The K₁₂ Laplacian Is Forced To Be Zero
+ **Necessity Proof:** Summing `12·vᵢ − Σ₁₂ v` over 12 vertices forces `12·Σ₁₂ v − 12·Σ₁₂ v`, which collapses by `+ℤ-inv-right`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-8-sumL12-0 (lines 648-753)
+ **Consequence:** Forces `J₁₂ (L₁₂ v) = 0` and eliminates any leftover drift term.
-}

eightTimes-+ℤ : (x y : ℤ) → eightTimesℤ (x +ℤ y) ≡ eightTimesℤ x +ℤ eightTimesℤ y
eightTimes-+ℤ x y =
  let fx = fourTimesℤ x in
  let fy = fourTimesℤ y in
  trans
    (cong (λ t → t +ℤ t) (fourTimes-+ℤ x y))
    (trans
      (+ℤ-assoc fx fy (fx +ℤ fy))
      (trans
        (cong (λ t → fx +ℤ t) (swapHeadℤ fy fx fy))
        (trans
          (sym (+ℤ-assoc fx fx (fy +ℤ fy)))
          refl)))

eightTimes-neg : (x : ℤ) → eightTimesℤ (negℤ x) ≡ negℤ (eightTimesℤ x)
eightTimes-neg x =
  trans
    (cong (λ t → t +ℤ t) (sym (neg-fourTimesℤ x)))
    (trans
      (sym (neg-+ℤ (fourTimesℤ x) (fourTimesℤ x)))
      refl)

twelveTimes-+ℤ : (x y : ℤ) → twelveTimesℤ (x +ℤ y) ≡ twelveTimesℤ x +ℤ twelveTimesℤ y
twelveTimes-+ℤ x y =
  let fx = fourTimesℤ x in
  let fy = fourTimesℤ y in
  let ex = eightTimesℤ x in
  let ey = eightTimesℤ y in
  trans
    refl
    (trans
      (cong (λ t → t +ℤ eightTimesℤ (x +ℤ y)) (fourTimes-+ℤ x y))
      (trans
        (cong (λ t → (fx +ℤ fy) +ℤ t) (eightTimes-+ℤ x y))
        (trans
          (+ℤ-assoc fx fy (ex +ℤ ey))
          (trans
            (cong (λ t → fx +ℤ t) (swapHeadℤ fy ex ey))
            (trans
              (sym (+ℤ-assoc fx ex (fy +ℤ ey)))
              refl)))))

twelveTimes-neg : (x : ℤ) → twelveTimesℤ (negℤ x) ≡ negℤ (twelveTimesℤ x)
twelveTimes-neg x =
  trans
    refl
    (trans
      (cong (λ t → t +ℤ eightTimesℤ (negℤ x)) (sym (neg-fourTimesℤ x)))
      (trans
        (cong (λ t → negℤ (fourTimesℤ x) +ℤ t) (eightTimes-neg x))
        (trans
          (sym (neg-+ℤ (fourTimesℤ x) (eightTimesℤ x)))
          refl)))

sumFin4-eightTimes : (v : Vec4ℤ) →
  sumFin4ℤ (λ i → eightTimesℤ (v i)) ≡ eightTimesℤ (sumFin4ℤ v)
sumFin4-eightTimes v =
  let vt : Vec4ℤ
      vt i = fourTimesℤ (v i)
  in
  trans
    (sumFin4-+Vec4ℤ vt vt)
    (trans
      (cong (λ t → t +ℤ t) (sumFin4-fourTimes v))
      refl)

sumFin4-twelveTimes : (v : Vec4ℤ) →
  sumFin4ℤ (λ i → twelveTimesℤ (v i)) ≡ twelveTimesℤ (sumFin4ℤ v)
sumFin4-twelveTimes v =
  let fv : Vec4ℤ
      fv i = fourTimesℤ (v i)
  in
  let ev : Vec4ℤ
      ev i = eightTimesℤ (v i)
  in
  trans
    (sumFin4-+Vec4ℤ fv ev)
    (trans
      (cong (λ t → t +ℤ sumFin4ℤ ev) (sumFin4-fourTimes v))
      (trans
        (cong (λ t → fourTimesℤ (sumFin4ℤ v) +ℤ t) (sumFin4-eightTimes v))
        refl))

reassoc3-addConst : (A B C k : ℤ) →
  (A +ℤ k) +ℤ ((B +ℤ k) +ℤ (C +ℤ k)) ≡ (A +ℤ (B +ℤ C)) +ℤ (k +ℤ (k +ℤ k))
reassoc3-addConst A B C k =
  let
    x = A +ℤ k
    y = B +ℤ k
    z = C +ℤ k

    step1 : x +ℤ (y +ℤ z) ≡ (x +ℤ y) +ℤ z
    step1 = sym (+ℤ-assoc x y z)

    step2 : x +ℤ y ≡ (A +ℤ B) +ℤ (k +ℤ k)
    step2 =
      trans
        (+ℤ-assoc A k (B +ℤ k))
        (trans
          (cong (λ t → A +ℤ t) (swapHeadℤ k B k))
          (sym (+ℤ-assoc A B (k +ℤ k))))

    step3 : (x +ℤ y) +ℤ z ≡ ((A +ℤ B) +ℤ (k +ℤ k)) +ℤ (C +ℤ k)
    step3 = cong (λ t → t +ℤ z) step2

    step4 : ((A +ℤ B) +ℤ (k +ℤ k)) +ℤ (C +ℤ k) ≡ (A +ℤ B) +ℤ ((k +ℤ k) +ℤ (C +ℤ k))
    step4 = +ℤ-assoc (A +ℤ B) (k +ℤ k) (C +ℤ k)

    step5 : (k +ℤ k) +ℤ (C +ℤ k) ≡ C +ℤ ((k +ℤ k) +ℤ k)
    step5 = swapHeadℤ (k +ℤ k) C k

    step6 : ((A +ℤ B) +ℤ C) ≡ A +ℤ (B +ℤ C)
    step6 = +ℤ-assoc A B C

    step7 : ((k +ℤ k) +ℤ k) ≡ k +ℤ (k +ℤ k)
    step7 = +ℤ-assoc k k k
  in
    trans
      step1
      (trans
        step3
        (trans
          step4
          (trans
            (cong (λ t → (A +ℤ B) +ℤ t) step5)
            (trans
              (sym (+ℤ-assoc (A +ℤ B) C ((k +ℤ k) +ℤ k)))
              (trans
                (cong (λ t → t +ℤ ((k +ℤ k) +ℤ k)) step6)
                (cong (λ t → (A +ℤ (B +ℤ C)) +ℤ t) step7))))))

law14H-8-sumL12-0 : (v : Vec12ℤ) → sum12ℤ (K12LaplacianVec12ℤ v) ≡ 0ℤ
law14H-8-sumL12-0 v =
  let
    s  = sum12ℤ v
    s0 = sumFin4ℤ (block₀ v)
    s1 = sumFin4ℤ (block₁ v)
    s2 = sumFin4ℤ (block₂ v)

    part0 = λ i → twelveTimesℤ (block₀ v i) +ℤ negℤ s
    part1 = λ i → twelveTimesℤ (block₁ v i) +ℤ negℤ s
    part2 = λ i → twelveTimesℤ (block₂ v i) +ℤ negℤ s

    step0 :
      sum12ℤ (K12LaplacianVec12ℤ v) ≡ sumFin4ℤ part0 +ℤ (sumFin4ℤ part1 +ℤ sumFin4ℤ part2)
    step0 = refl

    step1 :
      sumFin4ℤ part0 ≡ sumFin4ℤ (λ i → twelveTimesℤ (block₀ v i)) +ℤ fourTimesℤ (negℤ s)
    step1 = sumFin4-addConst (λ i → twelveTimesℤ (block₀ v i)) (negℤ s)

    step2 :
      sumFin4ℤ part1 ≡ sumFin4ℤ (λ i → twelveTimesℤ (block₁ v i)) +ℤ fourTimesℤ (negℤ s)
    step2 = sumFin4-addConst (λ i → twelveTimesℤ (block₁ v i)) (negℤ s)

    step3 :
      sumFin4ℤ part2 ≡ sumFin4ℤ (λ i → twelveTimesℤ (block₂ v i)) +ℤ fourTimesℤ (negℤ s)
    step3 = sumFin4-addConst (λ i → twelveTimesℤ (block₂ v i)) (negℤ s)

    step4 :
      sum12ℤ (K12LaplacianVec12ℤ v) ≡
        (sumFin4ℤ (λ i → twelveTimesℤ (block₀ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
        ((sumFin4ℤ (λ i → twelveTimesℤ (block₁ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
         (sumFin4ℤ (λ i → twelveTimesℤ (block₂ v i)) +ℤ fourTimesℤ (negℤ s)))
    step4 =
      trans
        step0
        (trans
          (cong (λ t → t +ℤ (sumFin4ℤ part1 +ℤ sumFin4ℤ part2)) step1)
          (trans
            (cong
              (λ t → (sumFin4ℤ (λ i → twelveTimesℤ (block₀ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ t)
              (cong (λ t → t +ℤ sumFin4ℤ part2) step2))
            (cong
              (λ t →
                (sumFin4ℤ (λ i → twelveTimesℤ (block₀ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
                ((sumFin4ℤ (λ i → twelveTimesℤ (block₁ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ t))
              step3)))

    step5 :
      sumFin4ℤ (λ i → twelveTimesℤ (block₀ v i)) ≡ twelveTimesℤ s0
    step5 = sumFin4-twelveTimes (block₀ v)

    step6 :
      sumFin4ℤ (λ i → twelveTimesℤ (block₁ v i)) ≡ twelveTimesℤ s1
    step6 = sumFin4-twelveTimes (block₁ v)

    step7 :
      sumFin4ℤ (λ i → twelveTimesℤ (block₂ v i)) ≡ twelveTimesℤ s2
    step7 = sumFin4-twelveTimes (block₂ v)

    step8 :
      sum12ℤ (K12LaplacianVec12ℤ v) ≡
        (twelveTimesℤ s0 +ℤ fourTimesℤ (negℤ s)) +ℤ
        ((twelveTimesℤ s1 +ℤ fourTimesℤ (negℤ s)) +ℤ (twelveTimesℤ s2 +ℤ fourTimesℤ (negℤ s)))
    step8 =
      trans
        step4
        (trans
          (cong
            (λ t → (t +ℤ fourTimesℤ (negℤ s)) +ℤ ((sumFin4ℤ (λ i → twelveTimesℤ (block₁ v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ (sumFin4ℤ (λ i → twelveTimesℤ (block₂ v i)) +ℤ fourTimesℤ (negℤ s))))
            step5)
          (trans
            (cong
              (λ t → (twelveTimesℤ s0 +ℤ fourTimesℤ (negℤ s)) +ℤ ((t +ℤ fourTimesℤ (negℤ s)) +ℤ (sumFin4ℤ (λ i → twelveTimesℤ (block₂ v i)) +ℤ fourTimesℤ (negℤ s))))
              step6)
            (cong
              (λ t → (twelveTimesℤ s0 +ℤ fourTimesℤ (negℤ s)) +ℤ ((twelveTimesℤ s1 +ℤ fourTimesℤ (negℤ s)) +ℤ (t +ℤ fourTimesℤ (negℤ s))))
              step7)))

    step9 :
      (twelveTimesℤ s0 +ℤ fourTimesℤ (negℤ s)) +ℤ
      ((twelveTimesℤ s1 +ℤ fourTimesℤ (negℤ s)) +ℤ (twelveTimesℤ s2 +ℤ fourTimesℤ (negℤ s))) ≡
        (twelveTimesℤ s0 +ℤ (twelveTimesℤ s1 +ℤ twelveTimesℤ s2)) +ℤ
        (fourTimesℤ (negℤ s) +ℤ (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)))
    step9 = reassoc3-addConst (twelveTimesℤ s0) (twelveTimesℤ s1) (twelveTimesℤ s2) (fourTimesℤ (negℤ s))

    step10 : twelveTimesℤ s0 +ℤ (twelveTimesℤ s1 +ℤ twelveTimesℤ s2) ≡ twelveTimesℤ s
    step10 =
      trans
        (cong (λ t → twelveTimesℤ s0 +ℤ t) (sym (twelveTimes-+ℤ s1 s2)))
        (sym (twelveTimes-+ℤ s0 (s1 +ℤ s2)))

    step11 : fourTimesℤ (negℤ s) +ℤ (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)) ≡ negℤ (twelveTimesℤ s)
    step11 = trans refl (twelveTimes-neg s)
  in
  trans
    step8
    (trans
      step9
      (trans
        (cong
          (λ t → t +ℤ (fourTimesℤ (negℤ s) +ℤ (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s))))
          step10)
        (trans
          (cong (λ t → twelveTimesℤ s +ℤ t) step11)
          (+ℤ-inv-right (twelveTimesℤ s)))))

{-
### Law 14H.9: `J₁₂ (L₁₂ v) = 0`
+ **Necessity Proof:** `J12Vec12ℤ (K12LaplacianVec12ℤ v)` is constant with value `sum12ℤ (K12LaplacianVec12ℤ v)`, which is
+ forced to be `0` by Law 14H.8.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-9-JL-zero (lines 763-768)
+ **Consequence:** Forces the image of `L₁₂` into the sum-zero subspace.
-}

law14H-9-JL-zero : (v : Vec12ℤ) → Vec12Eq (J12Vec12ℤ (K12LaplacianVec12ℤ v)) zeroVec12ℤ
law14H-9-JL-zero v =
  let sum0 = law14H-8-sumL12-0 v in
  (λ _ → sum0) ,
  ((λ _ → sum0) ,
   (λ _ → sum0))

{-
### Law 14H.10: `L₁₂ (J₁₂ v) = 0`
+ **Necessity Proof:** Pointwise, `L₁₂ (J₁₂ v) = 12·Σ − Σ(J₁₂ v)`. By `sum12-J12`, the two terms coincide and cancel.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-10-LJ-zero (lines 777-795)
+ **Consequence:** Eliminates mixed operator freedom: `L` and `J` annihilate each other.
-}

law14H-10-LJ-zero : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ (J12Vec12ℤ v)) zeroVec12ℤ
law14H-10-LJ-zero v =
  let s = sum12ℤ v in
  let sj = sum12-J12 v in
  ( λ _ →
      trans
        (cong (λ t → twelveTimesℤ s +ℤ negℤ t) sj)
        (+ℤ-inv-right (twelveTimesℤ s))
  ) ,
  (( λ _ →
        trans
          (cong (λ t → twelveTimesℤ s +ℤ negℤ t) sj)
          (+ℤ-inv-right (twelveTimesℤ s))
    ) ,
   ( λ _ →
        trans
          (cong (λ t → twelveTimesℤ s +ℤ negℤ t) sj)
          (+ℤ-inv-right (twelveTimesℤ s))
    ))

{-
### Law 14H.11: `L₁₂ ∘ L₁₂ = 12 · L₁₂`
+ **Necessity Proof:** Pointwise, `L₁₂ (L₁₂ v) = 12·(L₁₂ v) − Σ(L₁₂ v)`. The sum term vanishes by Law 14H.8.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-11-LL-twelveL (lines 804-821)
+ **Consequence:** Eliminates remaining operator algebra freedom on K₁₂.
-}

law14H-11-LL-twelveL : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (twelveVec12ℤ (K12LaplacianVec12ℤ v))
law14H-11-LL-twelveL v =
  let sum0 = law14H-8-sumL12-0 v in
  ( λ i →
      trans
        (cong (λ t → twelveTimesℤ (block₀ (K12LaplacianVec12ℤ v) i) +ℤ negℤ t) sum0)
        (+ℤ-zero-right (twelveTimesℤ (block₀ (K12LaplacianVec12ℤ v) i)))
  ) ,
  (( λ i →
        trans
          (cong (λ t → twelveTimesℤ (block₁ (K12LaplacianVec12ℤ v) i) +ℤ negℤ t) sum0)
          (+ℤ-zero-right (twelveTimesℤ (block₁ (K12LaplacianVec12ℤ v) i)))
    ) ,
   ( λ i →
        trans
          (cong (λ t → twelveTimesℤ (block₂ (K12LaplacianVec12ℤ v) i) +ℤ negℤ t) sum0)
          (+ℤ-zero-right (twelveTimesℤ (block₂ (K12LaplacianVec12ℤ v) i)))
    ))

{-
## K₁₂ Spectral Corollaries (Forced)

### Law 14H.12: Sum-Zero Vectors Are Forced 12-Eigenvectors
+ **Necessity Proof:** Pointwise, `L₁₂ v = 12·vᵢ - Σ₁₂ v`. If `Σ₁₂ v = 0`, the second term vanishes by `+ℤ-zero-right`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-12-sum0-eigen12 (lines 832-848)
+ **Consequence:** Eliminates spectral freedom: sum-zero forces eigenvalue 12.
-}

law14H-12-sum0-eigen12 : (v : Vec12ℤ) → sum12ℤ v ≡ 0ℤ → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v)
law14H-12-sum0-eigen12 v sum0 =
  ( λ i →
      trans
        (cong (λ s → twelveTimesℤ (block₀ v i) +ℤ negℤ s) sum0)
        (+ℤ-zero-right (twelveTimesℤ (block₀ v i)))
  ) ,
  (( λ i →
        trans
          (cong (λ s → twelveTimesℤ (block₁ v i) +ℤ negℤ s) sum0)
          (+ℤ-zero-right (twelveTimesℤ (block₁ v i)))
    ) ,
   ( λ i →
        trans
          (cong (λ s → twelveTimesℤ (block₂ v i) +ℤ negℤ s) sum0)
          (+ℤ-zero-right (twelveTimesℤ (block₂ v i)))
    ))

{-
### Law 14H.13: Pointwise 12-Eigenvectors Force Sum-Zero
+ **Necessity Proof:** Evaluating the eigen-equation at one index forces cancellation of the `12·vᵢ` term,
+ leaving `negℤ (Σ₁₂ v) = 0`, hence `Σ₁₂ v = 0` by `negℤ-zero→zero`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-13-eigen12→sum0 (lines 858-865)
+ **Consequence:** Eliminates the remaining direction: pointwise eigenvalue 12 forces the sum-zero predicate.
-}

law14H-13-eigen12→sum0 : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ
law14H-13-eigen12→sum0 v eigen12 =
  let a = twelveTimesℤ (block₀ v g0) in
  let s = sum12ℤ v in
  let eq₀ : a +ℤ negℤ s ≡ a
      eq₀ = fst eigen12 g0
  in
  negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)

{-
### Law 14H.14: Constant Vectors Are Forced 0-Eigenvectors
+ **Necessity Proof:** For `v = constVec12ℤ x`, `Σ₁₂ v` is forced to be `12·x`, so `L₁₂ (const x) = 12·x - 12·x`,
+ which collapses by `+ℤ-inv-right`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-14-const-eigen0 (lines 875-891)
+ **Consequence:** Eliminates the 0-eigenspace degree of freedom: constants are forced into the kernel.
-}

law14H-14-const-eigen0 : (x : ℤ) → Vec12Eq (K12LaplacianVec12ℤ (constVec12ℤ x)) zeroVec12ℤ
law14H-14-const-eigen0 x =
  ( λ _ →
      trans
        (cong (λ s → twelveTimesℤ x +ℤ negℤ s) (sum12-const x))
        (+ℤ-inv-right (twelveTimesℤ x))
  ) ,
  (( λ _ →
        trans
          (cong (λ s → twelveTimesℤ x +ℤ negℤ s) (sum12-const x))
          (+ℤ-inv-right (twelveTimesℤ x))
    ) ,
   ( λ _ →
        trans
          (cong (λ s → twelveTimesℤ x +ℤ negℤ s) (sum12-const x))
          (+ℤ-inv-right (twelveTimesℤ x))
    ))

{-
### Law 14H.15: Kernel Condition As Pointwise Constraint `L₁₂ v = 0 ⇔ 12·v = J₁₂ v`
+ **Necessity Proof:** Pointwise, `L₁₂ v i = 12·vᵢ - Σ₁₂ v`. If this vanishes, adding `Σ₁₂ v` forces cancellation
+ of `(-Σ₁₂ v) + Σ₁₂ v` by `+ℤ-inv-left`, yielding `12·vᵢ = Σ₁₂ v`. Conversely, substituting `12·vᵢ = Σ₁₂ v` yields
+ `Σ₁₂ v - Σ₁₂ v`, eliminated by `+ℤ-inv-right`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-15-L0→twelveEqJ (lines 903-953)
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-15-twelveEqJ→L0 (lines 955-972)
+ **Consequence:** Eliminates freedom in kernel/image predicates for K₁₂ without importing function extensionality.
-}

law14H-15-L0→twelveEqJ : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ v) zeroVec12ℤ → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v)
law14H-15-L0→twelveEqJ v L0 =
  let s = sum12ℤ v in
  ( λ i →
      let a = twelveTimesℤ (block₀ v i) in
      let eq₀ : a +ℤ negℤ s ≡ 0ℤ
          eq₀ = fst L0 i
      in
      let step₁ : (a +ℤ negℤ s) +ℤ s ≡ 0ℤ +ℤ s
          step₁ = cong (λ t → t +ℤ s) eq₀
          step₂ : a +ℤ (negℤ s +ℤ s) ≡ 0ℤ +ℤ s
          step₂ = trans (sym (+ℤ-assoc a (negℤ s) s)) step₁
          step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ s
          step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left s))) step₂
      in
      trans
        (trans (sym (+ℤ-zero-right a)) step₃)
        (+ℤ-zero-left s)
  ) ,
  (( λ i →
        let a = twelveTimesℤ (block₁ v i) in
        let eq₀ : a +ℤ negℤ s ≡ 0ℤ
            eq₀ = fst (snd L0) i
        in
        let step₁ : (a +ℤ negℤ s) +ℤ s ≡ 0ℤ +ℤ s
            step₁ = cong (λ t → t +ℤ s) eq₀
            step₂ : a +ℤ (negℤ s +ℤ s) ≡ 0ℤ +ℤ s
            step₂ = trans (sym (+ℤ-assoc a (negℤ s) s)) step₁
            step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ s
            step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left s))) step₂
        in
        trans
          (trans (sym (+ℤ-zero-right a)) step₃)
          (+ℤ-zero-left s)
    ) ,
   ( λ i →
        let a = twelveTimesℤ (block₂ v i) in
        let eq₀ : a +ℤ negℤ s ≡ 0ℤ
            eq₀ = snd (snd L0) i
        in
        let step₁ : (a +ℤ negℤ s) +ℤ s ≡ 0ℤ +ℤ s
            step₁ = cong (λ t → t +ℤ s) eq₀
            step₂ : a +ℤ (negℤ s +ℤ s) ≡ 0ℤ +ℤ s
            step₂ = trans (sym (+ℤ-assoc a (negℤ s) s)) step₁
            step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ s
            step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left s))) step₂
        in
        trans
          (trans (sym (+ℤ-zero-right a)) step₃)
          (+ℤ-zero-left s)
    ))

law14H-15-twelveEqJ→L0 : (v : Vec12ℤ) → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v) → Vec12Eq (K12LaplacianVec12ℤ v) zeroVec12ℤ
law14H-15-twelveEqJ→L0 v twelveEqJ =
  let s = sum12ℤ v in
  ( λ i →
      trans
        (cong (λ t → t +ℤ negℤ s) (fst twelveEqJ i))
        (+ℤ-inv-right s)
  ) ,
  (( λ i →
        trans
          (cong (λ t → t +ℤ negℤ s) (fst (snd twelveEqJ) i))
          (+ℤ-inv-right s)
    ) ,
   ( λ i →
        trans
          (cong (λ t → t +ℤ negℤ s) (snd (snd twelveEqJ) i))
          (+ℤ-inv-right s)
    ))

{-
### Law 14H.16: Image Vectors Are Forced 12-Eigenvectors
+ **Necessity Proof:** Any image vector has the form `w = L₁₂ v`. Then `L₁₂ w = L₁₂ (L₁₂ v)`, which is forced to equal
+ `12·(L₁₂ v) = 12·w` by Law 14H.11.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-16-image⊆eigen12 (lines 982-983)
+ **Consequence:** Eliminates false “image = all sum-zero” freedom over ℤ: the image satisfies the eigen-constraint.
-}

law14H-16-image⊆eigen12 : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (twelveVec12ℤ (K12LaplacianVec12ℤ v))
law14H-16-image⊆eigen12 = law14H-11-LL-twelveL

{-
### Law 14H.17: Sum-Zero Vectors Become Image Vectors After Forced 12-Scaling
+ **Necessity Proof:** If `Σ₁₂ w = 0`, then Law 14H.12 forces `L₁₂ w = 12·w`. Therefore `12·w` is in the image, witnessed
+ by choosing the preimage `v = w`.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-17-sum0→twelveInImage (lines 993-994)
+ **Consequence:** Eliminates remaining arithmetic freedom: image-membership is forced only up to the 12-scaling.
-}

law14H-17-sum0→twelveInImage : (w : Vec12ℤ) → sum12ℤ w ≡ 0ℤ → Σ Vec12ℤ (λ v → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ w))
law14H-17-sum0→twelveInImage w sum0 = w , law14H-12-sum0-eigen12 w sum0

{-
## Full Survivor Spectral Package (Forced)

This section packages the K₁₂ corollaries as a single witness bundle for the full three-copy survivor.

### Law 14H.18: Full Survivor Spectral Package (Drift / JL / Sum0⇔Eigen12 / Image⊆Eigen12)
+ **Necessity Proof:** `laplacianSurvivorVec12ℤ survivor3-full` is definitional `K12LaplacianVec12ℤ`.
+ Therefore the package is forced by Laws 14H.8, 14H.9, 14H.12, 14H.13, and 14H.16.
+ **Formal Reference:** K4TripleCoupledLaplacian.agda.law14H-18-survivor3-full-spectral-package (lines 1017-1022)
+ **Consequence:** Eliminates per-lemma bookkeeping for the full survivor.
-}

Survivor3FullSpectralPackage : Vec12ℤ → Set
Survivor3FullSpectralPackage v =
  (sum12ℤ (laplacianSurvivorVec12ℤ survivor3-full v) ≡ 0ℤ) ×
  (Vec12Eq (J12Vec12ℤ (laplacianSurvivorVec12ℤ survivor3-full v)) zeroVec12ℤ) ×
  ((sum12ℤ v ≡ 0ℤ → Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full v) (twelveVec12ℤ v)) ×
   (Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ)) ×
  (Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full (laplacianSurvivorVec12ℤ survivor3-full v))
           (twelveVec12ℤ (laplacianSurvivorVec12ℤ survivor3-full v)))

law14H-18-survivor3-full-spectral-package : (v : Vec12ℤ) → Survivor3FullSpectralPackage v
law14H-18-survivor3-full-spectral-package v =
  law14H-8-sumL12-0 v ,
  (law14H-9-JL-zero v ,
   ((law14H-12-sum0-eigen12 v , law14H-13-eigen12→sum0 v) ,
    law14H-16-image⊆eigen12 v))
