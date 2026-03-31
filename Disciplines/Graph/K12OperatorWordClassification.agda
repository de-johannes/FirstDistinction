{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K12OperatorWordClassification where

open import FirstDistinction
open import Disciplines.Math.Endomorphisms.Iteration
open import Disciplines.Graph.K4TripleCoupledLaplacian
open import Disciplines.Graph.K12IteratedOperatorAlgebra

{-
CHAPTER 14L: Word Algebra Of {L₁₂, J₁₂} (Classification Without Interpretation)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14H (JL/LJ/LL/JJ laws), Chapter 14I (powEndo recursion), Chapter 14K (congruence helpers)
AGDA MODULES: Disciplines.Graph.K12OperatorWordClassification
DEGREES OF FREEDOM ELIMINATED: ad hoc operator-algebra branches beyond the forced K₁₂ relations
-}

-- A “word” over the two generators L and J.

data Gen : Set where
  Lg : Gen
  Jg : Gen

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

Word : Set
Word = List Gen

Op : Set
Op = Endo Vec12ℤ

OpEq : Op → Op → Set
OpEq f g = (v : Vec12ℤ) → Vec12Eq (f v) (g v)

idOp : Op
idOp = idEndo

zeroOp : Op
zeroOp _ = zeroVec12ℤ

LOp : Op
LOp = K12LaplacianVec12ℤ

JOp : Op
JOp = J12Vec12ℤ

-- Word evaluation is forced by recursion.

evalGen : Gen → Op
evalGen Lg = LOp
evalGen Jg = JOp

evalWord : Word → Op
evalWord []       = idOp
evalWord (g ∷ w)  = evalGen g ∘ evalWord w

-- Classification cases: empty, pure powers, or mixed.
-- In pure cases, the index n denotes length = suc n.

data WordCase : Set where
  empty : WordCase
  Lpow  : ℕ → WordCase
  Jpow  : ℕ → WordCase
  mixed : WordCase

caseOp : WordCase → Op
caseOp empty     = idOp
caseOp (Lpow n)  = powEndo (suc n) LOp
caseOp (Jpow n)  = powEndo (suc n) JOp
caseOp mixed     = zeroOp

stepCase : Gen → WordCase → WordCase
stepCase Lg empty     = Lpow zero
stepCase Jg empty     = Jpow zero
stepCase Lg (Lpow n)  = Lpow (suc n)
stepCase Jg (Jpow n)  = Jpow (suc n)
stepCase Lg (Jpow _)  = mixed
stepCase Jg (Lpow _)  = mixed
stepCase _  mixed     = mixed

-- Congruence: J is forced constant from sum, so it respects Vec12Eq.

J12-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (JOp u) (JOp v)
J12-cong u v eq =
  let sEq = sum12-cong u v eq in
  (λ _ → sEq) , ((λ _ → sEq) , (λ _ → sEq))

-- Mixed annihilation extends from the forced one-step laws.

L∘Jpow-zero : (n : ℕ) → OpEq (LOp ∘ powEndo (suc n) JOp) zeroOp
L∘Jpow-zero n v = law14H-10-LJ-zero (powEndo n JOp v)

J∘Lpow-zero : (n : ℕ) → OpEq (JOp ∘ powEndo (suc n) LOp) zeroOp
J∘Lpow-zero n v = law14H-9-JL-zero (powEndo n LOp v)

composeGenCase : (g : Gen) → (c : WordCase) → OpEq (evalGen g ∘ caseOp c) (caseOp (stepCase g c))
composeGenCase Lg empty v = Vec12Eq-refl (LOp v)
composeGenCase Jg empty v = Vec12Eq-refl (JOp v)
composeGenCase Lg (Lpow n) v = Vec12Eq-refl (powEndo (suc (suc n)) LOp v)
composeGenCase Jg (Jpow n) v = Vec12Eq-refl (powEndo (suc (suc n)) JOp v)
composeGenCase Lg (Jpow n) v = L∘Jpow-zero n v
composeGenCase Jg (Lpow n) v = J∘Lpow-zero n v
composeGenCase Lg mixed v = Vec12Eq-refl zeroVec12ℤ
composeGenCase Jg mixed v = Vec12Eq-refl zeroVec12ℤ

congGen : (g : Gen) → (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (evalGen g u) (evalGen g v)
congGen Lg u v eq = K12Laplacian-cong u v eq
congGen Jg u v eq = J12-cong u v eq

{-
## Word Classification (Forced)

### Law 14L.0: Every Word Collapses To A Unique Case
**Necessity Proof:** Recursion on the word. Each new generator forces either extension of the current pure power,
 or forces the mixed case. In the mixed case, Law 14H.9 and Law 14H.10 force annihilation.
**Formal Reference:** K12OperatorWordClassification.agda.law14L-0-classify-word (lines 123-133)
**Consequence:** Eliminates all operator-word degrees of freedom beyond: identity, pure powers, or zero.
-}

law14L-0-classify-word : (w : Word) → Σ WordCase (λ c → OpEq (evalWord w) (caseOp c))
law14L-0-classify-word [] = empty , (λ v → Vec12Eq-refl v)
law14L-0-classify-word (g ∷ w) =
  let rec = law14L-0-classify-word w in
  let c   = fst rec in
  let eq  = snd rec in
  stepCase g c ,
  (λ v →
    Vec12Eq-trans
      (congGen g (evalWord w v) (caseOp c v) (eq v))
      (composeGenCase g c v))
