{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K12SpectralDecomposition where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.FiniteSumsZ
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Graph.K4MatrixLaplacian
open import Disciplines.Graph.K4TripleCoupledLaplacian
open import Disciplines.Graph.K12IteratedOperatorAlgebra using (sum12-cong ; K12Laplacian-cong)
open import Disciplines.Graph.K12ZSpanIJ

{-
CHAPTER 14O: Forced Spectral Action Of The (I,J)-Span On Vec12ℤ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14H (K₁₂ operator algebra), Chapter 14N ((I,J)-span normal form)
AGDA MODULES: Disciplines.Graph.K12SpectralDecomposition
DEGREES OF FREEDOM ELIMINATED: spectral ambiguity of (I,J)-endomorphisms on the forced subspaces
-}

-- Forced predicates (as Σ-witnesses) on Vec12ℤ.

ZeroSumVec12 : Vec12ℤ → Set
ZeroSumVec12 v = sum12ℤ v ≡ 0ℤ

ConstVec12 : Vec12ℤ → Set
ConstVec12 v = Σ ℤ (λ c → Vec12Eq v (constVec12ℤ c))

-- Transport lemmas for Vec12Eq (no function extensionality is imported).

Vec12Eq-refl : (v : Vec12ℤ) → Vec12Eq v v
Vec12Eq-refl v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

Vec12Eq-trans : {u v w : Vec12ℤ} → Vec12Eq u v → Vec12Eq v w → Vec12Eq u w
Vec12Eq-trans eq₁ eq₂ =
  (λ i → trans (fst eq₁ i) (fst eq₂ i)) ,
  ((λ i → trans (fst (snd eq₁) i) (fst (snd eq₂) i)) ,
   (λ i → trans (snd (snd eq₁) i) (snd (snd eq₂) i)))

Vec12Eq-sym : {u v : Vec12ℤ} → Vec12Eq u v → Vec12Eq v u
Vec12Eq-sym eq =
  (λ i → sym (fst eq i)) ,
  ((λ i → sym (fst (snd eq) i)) ,
   (λ i → sym (snd (snd eq) i)))

-- Congruence of `linIJ` and `interpIJ` under pointwise equality.

linIJ-cong : (a b : ℤ) → (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (linIJ a b u) (linIJ a b v)
linIJ-cong a b u v eq = eq0 , (eq1 , eq2)
  where
    sEq : sum12ℤ u ≡ sum12ℤ v
    sEq = sum12-cong u v eq

    eq0 : (i : Fin4) → block₀ (linIJ a b u) i ≡ block₀ (linIJ a b v) i
    eq0 i =
      let
        pA : a *ℤ block₀ u i ≡ a *ℤ block₀ v i
        pA = cong (λ t → a *ℤ t) (fst eq i)

        pB : b *ℤ sum12ℤ u ≡ b *ℤ sum12ℤ v
        pB = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₀ u i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₀ v i) +ℤ (b *ℤ sum12ℤ u)
        step₁ = cong (λ t → t +ℤ (b *ℤ sum12ℤ u)) pA

        step₂ : (a *ℤ block₀ v i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₀ v i) +ℤ (b *ℤ sum12ℤ v)
        step₂ = cong (λ t → (a *ℤ block₀ v i) +ℤ t) pB
      in
      trans
        (block₀-linIJ a b u i)
        (trans (trans step₁ step₂) (sym (block₀-linIJ a b v i)))

    eq1 : (i : Fin4) → block₁ (linIJ a b u) i ≡ block₁ (linIJ a b v) i
    eq1 i =
      let
        pA : a *ℤ block₁ u i ≡ a *ℤ block₁ v i
        pA = cong (λ t → a *ℤ t) (fst (snd eq) i)

        pB : b *ℤ sum12ℤ u ≡ b *ℤ sum12ℤ v
        pB = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₁ u i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₁ v i) +ℤ (b *ℤ sum12ℤ u)
        step₁ = cong (λ t → t +ℤ (b *ℤ sum12ℤ u)) pA

        step₂ : (a *ℤ block₁ v i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₁ v i) +ℤ (b *ℤ sum12ℤ v)
        step₂ = cong (λ t → (a *ℤ block₁ v i) +ℤ t) pB
      in
      trans
        (block₁-linIJ a b u i)
        (trans (trans step₁ step₂) (sym (block₁-linIJ a b v i)))

    eq2 : (i : Fin4) → block₂ (linIJ a b u) i ≡ block₂ (linIJ a b v) i
    eq2 i =
      let
        pA : a *ℤ block₂ u i ≡ a *ℤ block₂ v i
        pA = cong (λ t → a *ℤ t) (snd (snd eq) i)

        pB : b *ℤ sum12ℤ u ≡ b *ℤ sum12ℤ v
        pB = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₂ u i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₂ v i) +ℤ (b *ℤ sum12ℤ u)
        step₁ = cong (λ t → t +ℤ (b *ℤ sum12ℤ u)) pA

        step₂ : (a *ℤ block₂ v i) +ℤ (b *ℤ sum12ℤ u) ≡ (a *ℤ block₂ v i) +ℤ (b *ℤ sum12ℤ v)
        step₂ = cong (λ t → (a *ℤ block₂ v i) +ℤ t) pB
      in
      trans
        (block₂-linIJ a b u i)
        (trans (trans step₁ step₂) (sym (block₂-linIJ a b v i)))

interpIJ-cong : (p : SpanIJ) → (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (interpIJ p u) (interpIJ p v)
interpIJ-cong p = linIJ-cong (fst p) (snd p)

{-
## Forced J-Action

### Law 14O.0: Sum-Zero Forces J-Annihilation
**Necessity Proof:** `J12Vec12ℤ v` is definitional constant with value `sum12ℤ v`. If the sum is `0ℤ`, every coordinate is `0ℤ`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-0-J-sum0 (lines 128-130)
**Consequence:** Eliminates freedom in the J-image on the sum-zero predicate.
-}

law14O-0-J-sum0 : (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (J12Vec12ℤ v) zeroVec12ℤ
law14O-0-J-sum0 v sum0 =
  (λ _ → sum0) , ((λ _ → sum0) , (λ _ → sum0))

{-
### Law 14O.1: Constant Vectors Force J-Scaling By 12
**Necessity Proof:** `J12Vec12ℤ (constVec12ℤ c)` is definitional constant with value `sum12ℤ (constVec12ℤ c)`, and
`sum12-const` collapses that sum to `twelveTimesℤ c`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-1-J-const (lines 140-142)
**Consequence:** Eliminates freedom in the J-action on the constant predicate.
-}

law14O-1-J-const : (c : ℤ) → Vec12Eq (J12Vec12ℤ (constVec12ℤ c)) (constVec12ℤ (twelveTimesℤ c))
law14O-1-J-const c =
  (λ _ → sum12-const c) , ((λ _ → sum12-const c) , (λ _ → sum12-const c))

{-
## Forced Two-Eigenvalue Classification

### Law 14O.2: Sum-Zero Forces Eigenvalue `a` For Every `(a·I + b·J)`
**Necessity Proof:** Pointwise, `linIJ a b v` unfolds to `(a·vᵢ) + (b·sum12ℤ v)`. If `sum12ℤ v = 0ℤ`, the second term
collapses to `0ℤ` by `*ℤ-zero-right`, forcing `linIJ a b v = a·v`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-2-linIJ-sum0-eigen (lines 154-187)
**Consequence:** Eliminates spectral freedom on the sum-zero predicate: the J-parameter is forced to be invisible there.
-}

law14O-2-linIJ-sum0-eigen : (a b : ℤ) → (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (linIJ a b v) (scaleVec12ℤ a v)
law14O-2-linIJ-sum0-eigen a b v sum0 = eq0 , (eq1 , eq2)
  where
    kill : (x : ℤ) → x +ℤ (b *ℤ sum12ℤ v) ≡ x
    kill x =
      let
        p₀ : b *ℤ sum12ℤ v ≡ b *ℤ 0ℤ
        p₀ = cong (λ t → b *ℤ t) sum0

        p₁ : b *ℤ sum12ℤ v ≡ 0ℤ
        p₁ = trans p₀ (*ℤ-zero-right b)

        p₂ : x +ℤ (b *ℤ sum12ℤ v) ≡ x +ℤ 0ℤ
        p₂ = cong (λ t → x +ℤ t) p₁
      in
      trans p₂ (+ℤ-zero-right x)

    eq0 : (i : Fin4) → block₀ (linIJ a b v) i ≡ block₀ (scaleVec12ℤ a v) i
    eq0 i =
      trans
        (block₀-linIJ a b v i)
        (kill (a *ℤ block₀ v i))

    eq1 : (i : Fin4) → block₁ (linIJ a b v) i ≡ block₁ (scaleVec12ℤ a v) i
    eq1 i =
      trans
        (block₁-linIJ a b v i)
        (kill (a *ℤ block₁ v i))

    eq2 : (i : Fin4) → block₂ (linIJ a b v) i ≡ block₂ (scaleVec12ℤ a v) i
    eq2 i =
      trans
        (block₂-linIJ a b v i)
        (kill (a *ℤ block₂ v i))

{-
### Law 14O.3: Constants Force Eigenvalue `a + 12·b` For Every `(a·I + b·J)`
**Necessity Proof:** On a constant vector `constVec12ℤ c`, `sum12-const` forces `sum12ℤ v = 12·c`, so the `J`-term
becomes `b·(12·c)`. The forced shift lemma `mul-twelveShift` collapses `b·(12·c)` to `(12·b)·c`, and left distributivity
forces `(a + 12·b)·c = a·c + (12·b)·c`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-3-linIJ-const-eigen (lines 198-275)
**Consequence:** Eliminates spectral ambiguity on the constant predicate: every `(a,b)` has forced constant-mode eigenvalue.
-}

law14O-3-linIJ-const-eigen : (a b c : ℤ) →
  Vec12Eq (linIJ a b (constVec12ℤ c)) (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c))
law14O-3-linIJ-const-eigen a b c = eq0 , (eq1 , eq2)
  where
    coord : (a b c : ℤ) → (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c) ≡ (a +ℤ twelveTimesℤ b) *ℤ c
    coord a b c =
      trans
        (cong (λ t → (a *ℤ c) +ℤ t) (mul-twelveShift b c))
        (sym (*ℤ-distrib-left-+ℤ a (twelveTimesℤ b) c))

    eq0 : (i : Fin4) →
      block₀ (linIJ a b (constVec12ℤ c)) i ≡ block₀ (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c)) i
    eq0 i =
      let
        s0 : sum12ℤ (constVec12ℤ c) ≡ twelveTimesℤ c
        s0 = sum12-const c

        step₀a : (a *ℤ block₀ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
        step₀a = refl

        step₀b : (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀b = cong (λ t → (a *ℤ c) +ℤ (b *ℤ t)) s0

        step₀ : (a *ℤ block₀ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀ = trans step₀a step₀b
      in
      trans
        (block₀-linIJ a b (constVec12ℤ c) i)
        (trans step₀ (coord a b c))

    eq1 : (i : Fin4) →
      block₁ (linIJ a b (constVec12ℤ c)) i ≡ block₁ (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c)) i
    eq1 i =
      let
        s0 : sum12ℤ (constVec12ℤ c) ≡ twelveTimesℤ c
        s0 = sum12-const c

        step₀a : (a *ℤ block₁ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
        step₀a = refl

        step₀b : (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀b = cong (λ t → (a *ℤ c) +ℤ (b *ℤ t)) s0

        step₀ : (a *ℤ block₁ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀ = trans step₀a step₀b
      in
      trans
        (block₁-linIJ a b (constVec12ℤ c) i)
        (trans step₀ (coord a b c))

    eq2 : (i : Fin4) →
      block₂ (linIJ a b (constVec12ℤ c)) i ≡ block₂ (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c)) i
    eq2 i =
      let
        s0 : sum12ℤ (constVec12ℤ c) ≡ twelveTimesℤ c
        s0 = sum12-const c

        step₀a : (a *ℤ block₂ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
        step₀a = refl

        step₀b : (a *ℤ c) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀b = cong (λ t → (a *ℤ c) +ℤ (b *ℤ t)) s0

        step₀ : (a *ℤ block₂ (constVec12ℤ c) i) +ℤ (b *ℤ sum12ℤ (constVec12ℤ c))
          ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₀ = trans step₀a step₀b
      in
      trans
        (block₂-linIJ a b (constVec12ℤ c) i)
        (trans step₀ (coord a b c))

{-
## Forced Invariance Of Predicates Under The (I,J)-Span

### Law 14O.8: Sum-Zero Is Forced To Be Invariant Under Every `(a·I + b·J)`
**Necessity Proof:** `sum12-linIJ` forces a closed form for `sum12ℤ (linIJ a b v)`. If `sum12ℤ v = 0ℤ`, both summands
collapse to `0ℤ` by `*ℤ-zero-right` and the forced zero-collapse of `twelveTimesℤ`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-8-linIJ-preserves-sum0 (lines 332-355)
**Consequence:** Eliminates freedom: the sum-zero predicate is stable under the entire `(I,J)`-span.
-}

fourTimesℤ-zero : fourTimesℤ 0ℤ ≡ 0ℤ
fourTimesℤ-zero =
  let
    step₀ : fourTimesℤ 0ℤ ≡ sum4ℤ 0ℤ 0ℤ 0ℤ 0ℤ
    step₀ = refl

    step₁ : sum4ℤ 0ℤ 0ℤ 0ℤ 0ℤ ≡ 0ℤ +ℤ (0ℤ +ℤ (0ℤ +ℤ 0ℤ))
    step₁ = refl

    step₂ : 0ℤ +ℤ (0ℤ +ℤ (0ℤ +ℤ 0ℤ)) ≡ 0ℤ +ℤ (0ℤ +ℤ 0ℤ)
    step₂ = cong (λ t → 0ℤ +ℤ (0ℤ +ℤ t)) (+ℤ-zero-left 0ℤ)

    step₃ : 0ℤ +ℤ (0ℤ +ℤ 0ℤ) ≡ 0ℤ +ℤ 0ℤ
    step₃ = cong (λ t → 0ℤ +ℤ t) (+ℤ-zero-left 0ℤ)
  in
  trans step₀ (trans step₁ (trans step₂ (trans step₃ (+ℤ-zero-left 0ℤ))))

eightTimesℤ-zero : eightTimesℤ 0ℤ ≡ 0ℤ
eightTimesℤ-zero =
  let
    step₀ : eightTimesℤ 0ℤ ≡ fourTimesℤ 0ℤ +ℤ fourTimesℤ 0ℤ
    step₀ = refl

    step₁a : fourTimesℤ 0ℤ +ℤ fourTimesℤ 0ℤ ≡ 0ℤ +ℤ fourTimesℤ 0ℤ
    step₁a = cong (λ t → t +ℤ fourTimesℤ 0ℤ) fourTimesℤ-zero

    step₁b : 0ℤ +ℤ fourTimesℤ 0ℤ ≡ 0ℤ +ℤ 0ℤ
    step₁b = cong (λ t → 0ℤ +ℤ t) fourTimesℤ-zero
  in
  trans step₀ (trans step₁a (trans step₁b (+ℤ-zero-left 0ℤ)))

twelveTimesℤ-zero : twelveTimesℤ 0ℤ ≡ 0ℤ
twelveTimesℤ-zero =
  let
    step₀ : twelveTimesℤ 0ℤ ≡ fourTimesℤ 0ℤ +ℤ eightTimesℤ 0ℤ
    step₀ = refl

    step₁a : fourTimesℤ 0ℤ +ℤ eightTimesℤ 0ℤ ≡ 0ℤ +ℤ eightTimesℤ 0ℤ
    step₁a = cong (λ t → t +ℤ eightTimesℤ 0ℤ) fourTimesℤ-zero

    step₁b : 0ℤ +ℤ eightTimesℤ 0ℤ ≡ 0ℤ +ℤ 0ℤ
    step₁b = cong (λ t → 0ℤ +ℤ t) eightTimesℤ-zero
  in
  trans step₀ (trans step₁a (trans step₁b (+ℤ-zero-left 0ℤ)))

law14O-8-linIJ-preserves-sum0 : (a b : ℤ) → (v : Vec12ℤ) → ZeroSumVec12 v → ZeroSumVec12 (linIJ a b v)
law14O-8-linIJ-preserves-sum0 a b v sum0 =
  let
    step₀ : sum12ℤ (linIJ a b v)
      ≡ (a *ℤ sum12ℤ v) +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v))
    step₀ = sum12-linIJ a b v

    a0 : a *ℤ sum12ℤ v ≡ 0ℤ
    a0 = trans (cong (λ t → a *ℤ t) sum0) (*ℤ-zero-right a)

    twelve0 : twelveTimesℤ (sum12ℤ v) ≡ 0ℤ
    twelve0 = trans (cong twelveTimesℤ sum0) twelveTimesℤ-zero

    b0 : b *ℤ twelveTimesℤ (sum12ℤ v) ≡ 0ℤ
    b0 = trans (cong (λ t → b *ℤ t) twelve0) (*ℤ-zero-right b)

    step₁a : (a *ℤ sum12ℤ v) +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v))
          ≡ 0ℤ +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v))
    step₁a = cong (λ t → t +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v))) a0

    step₁b : 0ℤ +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v)) ≡ 0ℤ +ℤ 0ℤ
    step₁b = cong (λ t → 0ℤ +ℤ t) b0
  in
  trans step₀ (trans step₁a (trans step₁b (+ℤ-zero-left 0ℤ)))

{-
### Law 14O.9: Constant Vectors Are Forced To Be Invariant Under Every `(a·I + b·J)`
**Necessity Proof:** A `ConstVec12 v` witness forces pointwise equality `v = const c`, and `sum12-cong` forces
`sum12ℤ v = sum12ℤ (const c) = 12·c`. Substituting these into `blockₖ-linIJ` forces every output coordinate to be the
same constant value.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-9-linIJ-preserves-const (lines 369-448)
**Consequence:** Eliminates freedom: the constant predicate is stable under the entire `(I,J)`-span.
-}

scaleVec12ℤ-const : (a c : ℤ) → Vec12Eq (scaleVec12ℤ a (constVec12ℤ c)) (constVec12ℤ (a *ℤ c))
scaleVec12ℤ-const a c = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

law14O-9-linIJ-preserves-const : (a b : ℤ) → (v : Vec12ℤ) → ConstVec12 v → ConstVec12 (linIJ a b v)
law14O-9-linIJ-preserves-const a b v (c , vConst) = k , (eq0 , (eq1 , eq2))
  where
    sEq : sum12ℤ v ≡ twelveTimesℤ c
    sEq = trans (sum12-cong v (constVec12ℤ c) vConst) (sum12-const c)

    k : ℤ
    k = (a +ℤ twelveTimesℤ b) *ℤ c

    coord : (a b c : ℤ) → (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c) ≡ (a +ℤ twelveTimesℤ b) *ℤ c
    coord a b c =
      trans
        (cong (λ t → (a *ℤ c) +ℤ t) (mul-twelveShift b c))
        (sym (*ℤ-distrib-left-+ℤ a (twelveTimesℤ b) c))

    eq0 : (i : Fin4) → block₀ (linIJ a b v) i ≡ block₀ (constVec12ℤ k) i
    eq0 i =
      let
        v0 : block₀ v i ≡ c
        v0 = fst vConst i

        a0 : a *ℤ block₀ v i ≡ a *ℤ c
        a0 = cong (λ t → a *ℤ t) v0

        b0 : b *ℤ sum12ℤ v ≡ b *ℤ twelveTimesℤ c
        b0 = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₀ v i) +ℤ (b *ℤ sum12ℤ v) ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₁ =
          trans
            (cong (λ t → t +ℤ (b *ℤ sum12ℤ v)) a0)
            (cong (λ t → (a *ℤ c) +ℤ t) b0)
      in
      trans
        (block₀-linIJ a b v i)
        (trans step₁ (trans (coord a b c) refl))

    eq1 : (i : Fin4) → block₁ (linIJ a b v) i ≡ block₁ (constVec12ℤ k) i
    eq1 i =
      let
        v1 : block₁ v i ≡ c
        v1 = fst (snd vConst) i

        a1 : a *ℤ block₁ v i ≡ a *ℤ c
        a1 = cong (λ t → a *ℤ t) v1

        b1 : b *ℤ sum12ℤ v ≡ b *ℤ twelveTimesℤ c
        b1 = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₁ v i) +ℤ (b *ℤ sum12ℤ v) ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₁ =
          trans
            (cong (λ t → t +ℤ (b *ℤ sum12ℤ v)) a1)
            (cong (λ t → (a *ℤ c) +ℤ t) b1)
      in
      trans
        (block₁-linIJ a b v i)
        (trans step₁ (trans (coord a b c) refl))

    eq2 : (i : Fin4) → block₂ (linIJ a b v) i ≡ block₂ (constVec12ℤ k) i
    eq2 i =
      let
        v2 : block₂ v i ≡ c
        v2 = snd (snd vConst) i

        a2 : a *ℤ block₂ v i ≡ a *ℤ c
        a2 = cong (λ t → a *ℤ t) v2

        b2 : b *ℤ sum12ℤ v ≡ b *ℤ twelveTimesℤ c
        b2 = cong (λ t → b *ℤ t) sEq

        step₁ : (a *ℤ block₂ v i) +ℤ (b *ℤ sum12ℤ v) ≡ (a *ℤ c) +ℤ (b *ℤ twelveTimesℤ c)
        step₁ =
          trans
            (cong (λ t → t +ℤ (b *ℤ sum12ℤ v)) a2)
            (cong (λ t → (a *ℤ c) +ℤ t) b2)
      in
      trans
        (block₂-linIJ a b v i)
        (trans step₁ (trans (coord a b c) refl))

{-
### Law 14O.10: `(I,J)`-Span Predicate / Eigen Package For `linIJ a b`
**Necessity Proof:** Each component is already forced (Laws 14O.2, 14O.3, 14O.8, 14O.9).
**Formal Reference:** K12SpectralDecomposition.agda.law14O-10-linIJ-spectral-package (lines 467-472)
**Consequence:** Eliminates downstream boilerplate: later chapters consume a single witness for predicate invariance and the
two forced eigen-actions of `linIJ a b`.
-}

LinIJSpectralPackage : (a b : ℤ) → Set
LinIJSpectralPackage a b =
  (v : Vec12ℤ) →
    (ZeroSumVec12 v → ZeroSumVec12 (linIJ a b v)) ×
    (ConstVec12 v → ConstVec12 (linIJ a b v)) ×
    (ZeroSumVec12 v → Vec12Eq (linIJ a b v) (scaleVec12ℤ a v)) ×
    ((c : ℤ) → Vec12Eq (linIJ a b (constVec12ℤ c))
                      (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c)))

law14O-10-linIJ-spectral-package : (a b : ℤ) → LinIJSpectralPackage a b
law14O-10-linIJ-spectral-package a b v =
  law14O-8-linIJ-preserves-sum0 a b v ,
  (law14O-9-linIJ-preserves-const a b v ,
   (law14O-2-linIJ-sum0-eigen a b v ,
    law14O-3-linIJ-const-eigen a b))

-- Helper projections: consume `LinIJSpectralPackage` without re-associating products.

LinIJPkg-sum0-inv : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ZeroSumVec12 v → ZeroSumVec12 (linIJ a b v)
LinIJPkg-sum0-inv pkg v = fst (pkg v)

LinIJPkg-const-inv : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ConstVec12 v → ConstVec12 (linIJ a b v)
LinIJPkg-const-inv pkg v = fst (snd (pkg v))

LinIJPkg-sum0-eigen : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (linIJ a b v) (scaleVec12ℤ a v)
LinIJPkg-sum0-eigen pkg v = fst (snd (snd (pkg v)))

LinIJPkg-const-eigen : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → (c : ℤ) →
  Vec12Eq (linIJ a b (constVec12ℤ c)) (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c))
LinIJPkg-const-eigen pkg v = snd (snd (snd (pkg v)))

{-
## Forced Transport From Normal Form To Spectral Facts

### Law 14O.11: Any `f` With A Witness `f = (a·I + b·J)` Inherits The Forced Two-Mode Spectral Facts
**Necessity Proof:** The witness `OpEq f (linIJ a b)` forces `f v = linIJ a b v` pointwise. Every conclusion is then
forced by composing this equality with the corresponding forced law for `linIJ a b` (Laws 14O.2, 14O.3, 14O.8, 14O.9).
**Formal Reference:** K12SpectralDecomposition.agda.law14O-11-spanIJ-transport (lines 508-540)
**Consequence:** Eliminates representational freedom: spectral facts are properties of the operator, not of the chosen normal-form witness.
-}

SpanOpSpectralFacts : (f : Op) → (a b : ℤ) → Set
SpanOpSpectralFacts f a b =
  (v : Vec12ℤ) →
    (ZeroSumVec12 v → ZeroSumVec12 (f v)) ×
    (ConstVec12 v → ConstVec12 (f v)) ×
    (ZeroSumVec12 v → Vec12Eq (f v) (scaleVec12ℤ a v)) ×
    ((c : ℤ) → Vec12Eq (f (constVec12ℤ c))
                      (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c)))

law14O-11-spanIJ-transport : (f : Op) → (a b : ℤ) → OpEq f (linIJ a b) → SpanOpSpectralFacts f a b
law14O-11-spanIJ-transport f a b fEq v =
  sum0Inv ,
  (constInv ,
   (sum0Eigen ,
    constEigen))
  where
    sum0Inv : ZeroSumVec12 v → ZeroSumVec12 (f v)
    sum0Inv sum0 =
      trans
        (sum12-cong (f v) (linIJ a b v) (fEq v))
        (law14O-8-linIJ-preserves-sum0 a b v sum0)

    constInv : ConstVec12 v → ConstVec12 (f v)
    constInv (c , vConst) =
      let
        kLin : ConstVec12 (linIJ a b v)
        kLin = law14O-9-linIJ-preserves-const a b v (c , vConst)
      in
      fst kLin , Vec12Eq-trans (fEq v) (snd kLin)

    sum0Eigen : ZeroSumVec12 v → Vec12Eq (f v) (scaleVec12ℤ a v)
    sum0Eigen sum0 =
      Vec12Eq-trans
        (fEq v)
        (law14O-2-linIJ-sum0-eigen a b v sum0)

    constEigen : (c : ℤ) → Vec12Eq (f (constVec12ℤ c))
                           (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c))
    constEigen c =
      Vec12Eq-trans
        (fEq (constVec12ℤ c))
        (law14O-3-linIJ-const-eigen a b c)

{-
### Law 14O.12: The IJ-Coefficient Witness For `f` Is Forced Unique
**Necessity Proof:** This is Law 14N.2 specialized to the witness space `Σ SpanIJ (λ p → OpEq f (interpIJ p))`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-12-spanIJ-witness-unique (lines 552-553)
**Consequence:** Eliminates freedom in transporting spectral facts: the coefficients `(a,b)` are not a choice.
-}

SpanIJSpectralPackage : Op → Set
SpanIJSpectralPackage f = Σ SpanIJ (λ p → OpEq f (interpIJ p))

law14O-12-spanIJ-witness-unique : (f : Op) → (w₁ w₂ : SpanIJSpectralPackage f) → fst w₁ ≡ fst w₂
law14O-12-spanIJ-witness-unique f = law14N-2-image-witness-unique f

{-
### Law 14O.13: Spectral Facts Are Forced To Be Read Directly From A Span Witness
**Necessity Proof:** A package `w : Σ SpanIJ (λ p → OpEq f (interpIJ p))` forces concrete coefficients `p=(a,b)` and a
pointwise equality `f = linIJ a b`. Law 14O.11 then forces the complete two-mode spectral facts for that same `f`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-13-spanIJ-package-projections (lines 578-579)
**Consequence:** Eliminates downstream degrees of freedom: no consumer may “choose” coefficients or re-prove transport steps.
-}
SpanIJPkg-coeffs : {f : Op} → SpanIJSpectralPackage f → SpanIJ
SpanIJPkg-coeffs pkg = fst pkg

SpanIJPkg-opEq : {f : Op} → (pkg : SpanIJSpectralPackage f) → OpEq f (interpIJ (SpanIJPkg-coeffs pkg))
SpanIJPkg-opEq pkg = snd pkg

SpanIJPkg-a : {f : Op} → SpanIJSpectralPackage f → ℤ
SpanIJPkg-a pkg = fst (SpanIJPkg-coeffs pkg)

SpanIJPkg-b : {f : Op} → SpanIJSpectralPackage f → ℤ
SpanIJPkg-b pkg = snd (SpanIJPkg-coeffs pkg)

SpanIJPkg-spectral : {f : Op} → (pkg : SpanIJSpectralPackage f) → SpanOpSpectralFacts f (SpanIJPkg-a pkg) (SpanIJPkg-b pkg)
SpanIJPkg-spectral {f} pkg =
  law14O-11-spanIJ-transport f (SpanIJPkg-a pkg) (SpanIJPkg-b pkg) (SpanIJPkg-opEq pkg)

law14O-13-spanIJ-package-projections : {f : Op} → (pkg : SpanIJSpectralPackage f) → SpanOpSpectralFacts f (SpanIJPkg-a pkg) (SpanIJPkg-b pkg)
law14O-13-spanIJ-package-projections pkg = SpanIJPkg-spectral pkg

-- Consumer projections: use `SpanIJSpectralPackage` without unpacking Σ-witnesses.

SpanIJPkg-sum0-inv : {f : Op} → (pkg : SpanIJSpectralPackage f) → (v : Vec12ℤ) → ZeroSumVec12 v → ZeroSumVec12 (f v)
SpanIJPkg-sum0-inv pkg v = fst (SpanIJPkg-spectral pkg v)

SpanIJPkg-const-inv : {f : Op} → (pkg : SpanIJSpectralPackage f) → (v : Vec12ℤ) → ConstVec12 v → ConstVec12 (f v)
SpanIJPkg-const-inv pkg v = fst (snd (SpanIJPkg-spectral pkg v))

SpanIJPkg-sum0-eigen : {f : Op} → (pkg : SpanIJSpectralPackage f) → (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (f v) (scaleVec12ℤ (SpanIJPkg-a pkg) v)
SpanIJPkg-sum0-eigen pkg v = fst (snd (snd (SpanIJPkg-spectral pkg v)))

SpanIJPkg-const-eigen : {f : Op} → (pkg : SpanIJSpectralPackage f) → (c : ℤ) →
  Vec12Eq (f (constVec12ℤ c))
         (scaleVec12ℤ ((SpanIJPkg-a pkg) +ℤ twelveTimesℤ (SpanIJPkg-b pkg)) (constVec12ℤ c))
SpanIJPkg-const-eigen pkg c = snd (snd (snd (SpanIJPkg-spectral pkg (constVec12ℤ c)))) c

{-
### Law 14O.14: Unified Span Transport Package (Coefficients / Normal Form / Spectral Facts)
**Necessity Proof:** The witness `pkg : Σ SpanIJ (λ p → OpEq f (interpIJ p))` forces a unique coefficient pair `p=(a,b)`.
The forced equality `OpEq f (linIJ a b)` is definitional from `interpIJ`. Law 14O.11 forces the spectral facts for `f`.
Law 14O.10 forces the corresponding `linIJ`-package for the same `(a,b)`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-14-spanIJ-unified-package (lines 613-634)
**Consequence:** Eliminates remaining consumer freedom: one witness contains everything needed to use the span and spectral layer.
-}

SpanIJUnifiedPackage : Op → Set
SpanIJUnifiedPackage f =
  Σ SpanIJ (λ p →
    OpEq f (interpIJ p) ×
    SpanOpSpectralFacts f (fst p) (snd p) ×
    LinIJSpectralPackage (fst p) (snd p))

law14O-14-spanIJ-unified-package : (f : Op) → SpanIJSpectralPackage f → SpanIJUnifiedPackage f
law14O-14-spanIJ-unified-package f pkg =
  let
    p : SpanIJ
    p = SpanIJPkg-coeffs pkg

    a : ℤ
    a = fst p

    b : ℤ
    b = snd p

    eq : OpEq f (interpIJ p)
    eq = SpanIJPkg-opEq pkg

    facts : SpanOpSpectralFacts f a b
    facts = law14O-11-spanIJ-transport f a b eq

    linPkg : LinIJSpectralPackage a b
    linPkg = law14O-10-linIJ-spectral-package a b
  in
  p , (eq , (facts , linPkg))

-- Helper projections: consume `SpanIJUnifiedPackage` without re-associating products.

SpanIJUpkg-coeffs : {f : Op} → SpanIJUnifiedPackage f → SpanIJ
SpanIJUpkg-coeffs upkg = fst upkg

SpanIJUpkg-a : {f : Op} → SpanIJUnifiedPackage f → ℤ
SpanIJUpkg-a upkg = fst (SpanIJUpkg-coeffs upkg)

SpanIJUpkg-b : {f : Op} → SpanIJUnifiedPackage f → ℤ
SpanIJUpkg-b upkg = snd (SpanIJUpkg-coeffs upkg)

SpanIJUpkg-opEq : {f : Op} → (upkg : SpanIJUnifiedPackage f) → OpEq f (interpIJ (SpanIJUpkg-coeffs upkg))
SpanIJUpkg-opEq upkg = fst (snd upkg)

SpanIJUpkg-spectral : {f : Op} → (upkg : SpanIJUnifiedPackage f) → SpanOpSpectralFacts f (SpanIJUpkg-a upkg) (SpanIJUpkg-b upkg)
SpanIJUpkg-spectral upkg = fst (snd (snd upkg))

SpanIJUpkg-linIJ : {f : Op} → (upkg : SpanIJUnifiedPackage f) → LinIJSpectralPackage (SpanIJUpkg-a upkg) (SpanIJUpkg-b upkg)
SpanIJUpkg-linIJ upkg = snd (snd (snd upkg))

{-
### Law 14O.15: Unified Span Coefficients Are Forced Unique
**Necessity Proof:** Each `SpanIJUnifiedPackage f` contains a witness in `Σ SpanIJ (λ p → OpEq f (interpIJ p))`. Law 14N.2
forces uniqueness of the coefficient pair for that witness space; projecting the unified packages into this space eliminates
all remaining coefficient freedom.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-15-unified-coeffs-unique (lines 668-670)
**Consequence:** Eliminates any possibility of divergent coefficient extraction at the unified layer.
-}

SpanIJUpkg-witness : {f : Op} → SpanIJUnifiedPackage f → Σ SpanIJ (λ p → OpEq f (interpIJ p))
SpanIJUpkg-witness upkg = SpanIJUpkg-coeffs upkg , SpanIJUpkg-opEq upkg

law14O-15-unified-coeffs-unique : (f : Op) → (u₁ u₂ : SpanIJUnifiedPackage f) → SpanIJUpkg-coeffs u₁ ≡ SpanIJUpkg-coeffs u₂
law14O-15-unified-coeffs-unique f u₁ u₂ =
  law14N-2-image-witness-unique f (SpanIJUpkg-witness u₁) (SpanIJUpkg-witness u₂)

-- Forced helper coefficients.

twelveℤ : ℤ
twelveℤ = twelveTimesℤ oneℤ

-- Forced positivity witness for twelveℤ.

twelveℤ-pos : Σ ℕ (λ n → twelveℤ ≡ +suc n)
twelveℤ-pos = (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) , refl

-- 12-as-multiplication on the left collapses to twelveTimes.

twelveℤ-*ℤ-left : (x : ℤ) → twelveℤ *ℤ x ≡ twelveTimesℤ x
twelveℤ-*ℤ-left x =
  trans
    (*ℤ-twelveTimes-left oneℤ x)
    (cong twelveTimesℤ (*ℤ-one-left x))

-- Multiplication by (-1) on the left collapses to additive negation.

negOne-*ℤ-left : (x : ℤ) → (negℤ oneℤ) *ℤ x ≡ negℤ x
negOne-*ℤ-left x =
  let
    neg1 = negℤ oneℤ

    -- Distribute (neg1 + 1) across x.
    dist : (neg1 +ℤ oneℤ) *ℤ x ≡ (neg1 *ℤ x) +ℤ (oneℤ *ℤ x)
    dist = *ℤ-distrib-left-+ℤ neg1 oneℤ x

    -- (neg1 + 1) is forced to be 0.
    sum0 : (neg1 +ℤ oneℤ) ≡ 0ℤ
    sum0 = +ℤ-inv-left oneℤ

    zeroMul : (neg1 +ℤ oneℤ) *ℤ x ≡ 0ℤ
    zeroMul = trans (cong (λ t → t *ℤ x) sum0) (*ℤ-zero-left x)

    eq0 : (neg1 *ℤ x) +ℤ (oneℤ *ℤ x) ≡ 0ℤ
    eq0 = trans (sym dist) zeroMul

    eq1 : (neg1 *ℤ x) +ℤ x ≡ 0ℤ
    eq1 = trans (sym (cong (λ t → (neg1 *ℤ x) +ℤ t) (*ℤ-one-left x))) eq0

    eq2 : (neg1 *ℤ x) +ℤ x ≡ (negℤ x) +ℤ x
    eq2 = trans eq1 (sym (+ℤ-inv-left x))
  in
  +ℤ-cancel-right (neg1 *ℤ x) (negℤ x) x eq2

{-
## Laplacian As A Forced (I,J)-Span Element

### Law 14O.4: `L₁₂` Is Forced To Equal `(12·I) + (-1)·J`
**Necessity Proof:** Pointwise, `K12LaplacianVec12ℤ v` is definitional `12·vᵢ - Σ₁₂ v`.
The span form `linIJ twelveℤ (negℤ oneℤ)` evaluates to `(twelveℤ *ℤ vᵢ) + (neg1 *ℤ Σ₁₂ v)`.
The two multiplications collapse to `twelveTimesℤ vᵢ` and `negℤ (Σ₁₂ v)` by the forced lemmas above.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-4-L-in-span (lines 730-787)
**Consequence:** Eliminates representational freedom: the K₁₂ Laplacian is an element of the forced `(I,J)`-span.
-}

law14O-4-L-in-span : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ v) (linIJ twelveℤ (negℤ oneℤ) v)
law14O-4-L-in-span v = eq0 , (eq1 , eq2)
  where
    s : ℤ
    s = sum12ℤ v

    neg1 = negℤ oneℤ

    rhs0 : (i : Fin4) →
      block₀ (linIJ twelveℤ neg1 v) i ≡ twelveTimesℤ (block₀ v i) +ℤ negℤ s
    rhs0 i =
      let
        pA : (twelveℤ *ℤ block₀ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₀ v i) +ℤ (neg1 *ℤ s)
        pA = cong (λ t → t +ℤ (neg1 *ℤ s)) (twelveℤ-*ℤ-left (block₀ v i))

        pB : twelveTimesℤ (block₀ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₀ v i) +ℤ negℤ s
        pB = cong (λ t → twelveTimesℤ (block₀ v i) +ℤ t) (negOne-*ℤ-left s)
      in
      trans
        (block₀-linIJ twelveℤ neg1 v i)
        (trans pA pB)

    rhs1 : (i : Fin4) →
      block₁ (linIJ twelveℤ neg1 v) i ≡ twelveTimesℤ (block₁ v i) +ℤ negℤ s
    rhs1 i =
      let
        pA : (twelveℤ *ℤ block₁ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₁ v i) +ℤ (neg1 *ℤ s)
        pA = cong (λ t → t +ℤ (neg1 *ℤ s)) (twelveℤ-*ℤ-left (block₁ v i))

        pB : twelveTimesℤ (block₁ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₁ v i) +ℤ negℤ s
        pB = cong (λ t → twelveTimesℤ (block₁ v i) +ℤ t) (negOne-*ℤ-left s)
      in
      trans
        (block₁-linIJ twelveℤ neg1 v i)
        (trans pA pB)

    rhs2 : (i : Fin4) →
      block₂ (linIJ twelveℤ neg1 v) i ≡ twelveTimesℤ (block₂ v i) +ℤ negℤ s
    rhs2 i =
      let
        pA : (twelveℤ *ℤ block₂ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₂ v i) +ℤ (neg1 *ℤ s)
        pA = cong (λ t → t +ℤ (neg1 *ℤ s)) (twelveℤ-*ℤ-left (block₂ v i))

        pB : twelveTimesℤ (block₂ v i) +ℤ (neg1 *ℤ s) ≡ twelveTimesℤ (block₂ v i) +ℤ negℤ s
        pB = cong (λ t → twelveTimesℤ (block₂ v i) +ℤ t) (negOne-*ℤ-left s)
      in
      trans
        (block₂-linIJ twelveℤ neg1 v i)
        (trans pA pB)

    eq0 : (i : Fin4) → block₀ (K12LaplacianVec12ℤ v) i ≡ block₀ (linIJ twelveℤ neg1 v) i
    eq0 i = trans refl (sym (rhs0 i))

    eq1 : (i : Fin4) → block₁ (K12LaplacianVec12ℤ v) i ≡ block₁ (linIJ twelveℤ neg1 v) i
    eq1 i = trans refl (sym (rhs1 i))

    eq2 : (i : Fin4) → block₂ (K12LaplacianVec12ℤ v) i ≡ block₂ (linIJ twelveℤ neg1 v) i
    eq2 i = trans refl (sym (rhs2 i))

{-
## Forced Laplacian Composition Closure (No Coordinates)

### Law 14O.16: The K₁₂ Laplacian Has A Forced Span Witness `(12, -1)`
**Necessity Proof:** Law 14O.4 is pointwise `Vec12Eq`; this is exactly an `OpEq` witness of `K12LaplacianVec12ℤ = interpIJ (12,-1)`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-16-L-span-witness (lines 801-802)
**Consequence:** Eliminates freedom in treating the Laplacian as a span element: composition may be handled purely by 14N.3.
-}

LSpanIJ : SpanIJ
LSpanIJ = twelveℤ , (negℤ oneℤ)

law14O-16-L-span-witness : SpanIJSpectralPackage K12LaplacianVec12ℤ
law14O-16-L-span-witness = LSpanIJ , (λ v → law14O-4-L-in-span v)

{-
### Law 14O.17: Left Composition By The Laplacian Preserves Span Membership
**Necessity Proof:** If `f = interpIJ p`, then `L₁₂ ∘ f = interpIJ LSpanIJ ∘ interpIJ p`. Law 14N.3 forces this to
equal `interpIJ (mulSpanIJ LSpanIJ p)`. The only transport step uses the forced congruence of `K12LaplacianVec12ℤ`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-17-L-compose-left-span (lines 812-836)
**Consequence:** Eliminates freedom in composing span witnesses with `L₁₂` on the left.
-}

law14O-17-L-compose-left-span : (f : Op) → SpanIJSpectralPackage f → SpanIJSpectralPackage (λ v → K12LaplacianVec12ℤ (f v))
law14O-17-L-compose-left-span f pkg = p' , eq'
  where
    p : SpanIJ
    p = SpanIJPkg-coeffs pkg

    p' : SpanIJ
    p' = mulSpanIJ LSpanIJ p

    fEq : OpEq f (interpIJ p)
    fEq = SpanIJPkg-opEq pkg

    eq' : OpEq (λ v → K12LaplacianVec12ℤ (f v)) (interpIJ p')
    eq' v =
      let
        step₁ : Vec12Eq (K12LaplacianVec12ℤ (f v)) (K12LaplacianVec12ℤ (interpIJ p v))
        step₁ = K12Laplacian-cong (f v) (interpIJ p v) (fEq v)

        step₂ : Vec12Eq (K12LaplacianVec12ℤ (interpIJ p v)) (interpIJ LSpanIJ (interpIJ p v))
        step₂ = law14O-4-L-in-span (interpIJ p v)

        step₃ : Vec12Eq (interpIJ LSpanIJ (interpIJ p v)) (interpIJ p' v)
        step₃ = law14N-3-IJ-compose-closed LSpanIJ p v
      in
      Vec12Eq-trans step₁ (Vec12Eq-trans step₂ step₃)

{-
### Law 14O.18: Right Composition By The Laplacian Preserves Span Membership
**Necessity Proof:** If `f = interpIJ p`, then `f ∘ L₁₂ = interpIJ p ∘ interpIJ LSpanIJ`. Law 14N.3 forces this to
equal `interpIJ (mulSpanIJ p LSpanIJ)`. The only non-14N step is the forced congruence of `interpIJ p` under `Vec12Eq`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-18-L-compose-right-span (lines 846-870)
**Consequence:** Eliminates freedom in composing span witnesses with `L₁₂` on the right.
-}

law14O-18-L-compose-right-span : (f : Op) → SpanIJSpectralPackage f → SpanIJSpectralPackage (λ v → f (K12LaplacianVec12ℤ v))
law14O-18-L-compose-right-span f pkg = p' , eq'
  where
    p : SpanIJ
    p = SpanIJPkg-coeffs pkg

    p' : SpanIJ
    p' = mulSpanIJ p LSpanIJ

    fEq : OpEq f (interpIJ p)
    fEq = SpanIJPkg-opEq pkg

    eq' : OpEq (λ v → f (K12LaplacianVec12ℤ v)) (interpIJ p')
    eq' v =
      let
        step₁ : Vec12Eq (f (K12LaplacianVec12ℤ v)) (interpIJ p (K12LaplacianVec12ℤ v))
        step₁ = fEq (K12LaplacianVec12ℤ v)

        step₂ : Vec12Eq (interpIJ p (K12LaplacianVec12ℤ v)) (interpIJ p (interpIJ LSpanIJ v))
        step₂ = interpIJ-cong p (K12LaplacianVec12ℤ v) (interpIJ LSpanIJ v) (law14O-4-L-in-span v)

        step₃ : Vec12Eq (interpIJ p (interpIJ LSpanIJ v)) (interpIJ p' v)
        step₃ = law14N-3-IJ-compose-closed p LSpanIJ v
      in
      Vec12Eq-trans step₁ (Vec12Eq-trans step₂ step₃)

{-
### Law 14O.19: Left Composition By The Laplacian Preserves Unified Span Packages
**Necessity Proof:** A `SpanIJUnifiedPackage f` forces a span witness `Σ SpanIJ (λ p → OpEq f (interpIJ p))`.
Law 14O.17 forces a span witness for `L₁₂ ∘ f`. Law 14O.14 then forces the unified package for `L₁₂ ∘ f`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-19-L-compose-left-unified (lines 883-887)
**Consequence:** Eliminates all remaining consumer work: unified packages are closed under left composition by `L₁₂`.
-}

SpanIJUpkg-to-span : {f : Op} → SpanIJUnifiedPackage f → SpanIJSpectralPackage f
SpanIJUpkg-to-span upkg = SpanIJUpkg-coeffs upkg , SpanIJUpkg-opEq upkg

law14O-19-L-compose-left-unified : (f : Op) → SpanIJUnifiedPackage f → SpanIJUnifiedPackage (λ v → K12LaplacianVec12ℤ (f v))
law14O-19-L-compose-left-unified f upkg =
  law14O-14-spanIJ-unified-package
    (λ v → K12LaplacianVec12ℤ (f v))
    (law14O-17-L-compose-left-span f (SpanIJUpkg-to-span upkg))

{-
### Law 14O.20: Right Composition By The Laplacian Preserves Unified Span Packages
**Necessity Proof:** A `SpanIJUnifiedPackage f` forces a span witness `Σ SpanIJ (λ p → OpEq f (interpIJ p))`.
Law 14O.18 forces a span witness for `f ∘ L₁₂`. Law 14O.14 then forces the unified package for `f ∘ L₁₂`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-20-L-compose-right-unified (lines 897-901)
**Consequence:** Eliminates all remaining consumer work: unified packages are closed under right composition by `L₁₂`.
-}

law14O-20-L-compose-right-unified : (f : Op) → SpanIJUnifiedPackage f → SpanIJUnifiedPackage (λ v → f (K12LaplacianVec12ℤ v))
law14O-20-L-compose-right-unified f upkg =
  law14O-14-spanIJ-unified-package
    (λ v → f (K12LaplacianVec12ℤ v))
    (law14O-18-L-compose-right-span f (SpanIJUpkg-to-span upkg))

{-
### Law 14O.5: Sum-Zero Forces Laplacian Eigenvalue `12`
**Necessity Proof:** Combine Law 14O.4 with Law 14O.2 instantiated at `(a,b) = (12, -1)`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-5-L-sum0-eigen12 (lines 910-914)
**Consequence:** Eliminates freedom in the Laplacian action on the sum-zero predicate.
-}

law14O-5-L-sum0-eigen12 : (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ twelveℤ v)
law14O-5-L-sum0-eigen12 v sum0 =
  Vec12Eq-trans
    (law14O-4-L-in-span v)
    (law14O-2-linIJ-sum0-eigen twelveℤ (negℤ oneℤ) v sum0)

{-
### Law 14O.6: Constant Vectors Force Laplacian Eigenvalue `0`
**Necessity Proof:** Combine Law 14O.4 with Law 14O.3 instantiated at `(a,b) = (12, -1)`.
The forced coefficient collapse is `12 + 12·(-1) = 0`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-6-L-const-eigen0 (lines 924-925)
**Consequence:** Eliminates freedom in the Laplacian action on the constant predicate.
-}

law14O-6-L-const-eigen0 : (c : ℤ) → Vec12Eq (K12LaplacianVec12ℤ (constVec12ℤ c)) zeroVec12ℤ
law14O-6-L-const-eigen0 = law14H-14-const-eigen0

{-
## Laplacian Spectral Package (Forced)

### Law 14O.7: K₁₂ Laplacian Spectral Package (Span / Drift / JL / Sum0⇔Eigen12 / Image⊆Eigen12 / ConstKer)
**Necessity Proof:** Each component is already forced (Laws 14O.4–14O.6 and Laws 14H.8–14H.16).
**Formal Reference:** K12SpectralDecomposition.agda.law14O-7-L-spectral-package (lines 950-957)
**Consequence:** Eliminates downstream proof boilerplate: later chapters consume a single witness of all forced spectral behavior.
-}

L12ConstKernel : Set
L12ConstKernel = (x : ℤ) → Vec12Eq (K12LaplacianVec12ℤ (constVec12ℤ x)) zeroVec12ℤ

L12SpectralPackage : Vec12ℤ → Set
L12SpectralPackage v =
  (Vec12Eq (K12LaplacianVec12ℤ v) (linIJ twelveℤ (negℤ oneℤ) v)) ×
  (sum12ℤ (K12LaplacianVec12ℤ v) ≡ 0ℤ) ×
  (Vec12Eq (J12Vec12ℤ (K12LaplacianVec12ℤ v)) zeroVec12ℤ) ×
  ((sum12ℤ v ≡ 0ℤ → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v)) ×
   (Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ)) ×
  (Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v))
          (twelveVec12ℤ (K12LaplacianVec12ℤ v))) ×
  L12ConstKernel

law14O-7-L-spectral-package : (v : Vec12ℤ) → L12SpectralPackage v
law14O-7-L-spectral-package v =
  law14O-4-L-in-span v ,
  (law14H-8-sumL12-0 v ,
   (law14H-9-JL-zero v ,
    ((law14H-12-sum0-eigen12 v , law14H-13-eigen12→sum0 v) ,
     (law14H-16-image⊆eigen12 v ,
      law14O-6-L-const-eigen0))))

-- Helper projections: downstream chapters consume `L12SpectralPackage` without re-associating products.

L12Pkg-span : {v : Vec12ℤ} → L12SpectralPackage v → Vec12Eq (K12LaplacianVec12ℤ v) (linIJ twelveℤ (negℤ oneℤ) v)
L12Pkg-span pkg = fst pkg

L12Pkg-sumL0 : {v : Vec12ℤ} → L12SpectralPackage v → sum12ℤ (K12LaplacianVec12ℤ v) ≡ 0ℤ
L12Pkg-sumL0 pkg = fst (snd pkg)

L12Pkg-JL0 : {v : Vec12ℤ} → L12SpectralPackage v → Vec12Eq (J12Vec12ℤ (K12LaplacianVec12ℤ v)) zeroVec12ℤ
L12Pkg-JL0 pkg = fst (snd (snd pkg))

L12Pkg-sum0→eigen12 : {v : Vec12ℤ} → L12SpectralPackage v → sum12ℤ v ≡ 0ℤ → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v)
L12Pkg-sum0→eigen12 pkg = fst (fst (snd (snd (snd pkg))))

L12Pkg-eigen12→sum0 : {v : Vec12ℤ} → L12SpectralPackage v → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ
L12Pkg-eigen12→sum0 pkg = snd (fst (snd (snd (snd pkg))))

L12Pkg-image⊆eigen12 : {v : Vec12ℤ} → L12SpectralPackage v →
  Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (twelveVec12ℤ (K12LaplacianVec12ℤ v))
L12Pkg-image⊆eigen12 pkg = fst (snd (snd (snd (snd pkg))))

L12Pkg-constKer : {v : Vec12ℤ} → L12SpectralPackage v → L12ConstKernel
L12Pkg-constKer pkg = snd (snd (snd (snd (snd pkg))))

{-
## Forced Eigen-Constraint Refinements (No Torsion Assumptions)

This section adds the missing “reverse direction” facts that are already forced by Chapter 14H,
but phrased in the `scaleVec12ℤ` language used by the `(I,J)`-span.

### Law 14O.21: 12-Scaling In `scaleVec12ℤ` Agrees With `twelveVec12ℤ`
**Necessity Proof:** `twelveℤ-*ℤ-left` forces `twelveℤ *ℤ x ≡ twelveTimesℤ x` for every coordinate.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-21-scale12≡twelveVec12 (lines 996-1000)
**Consequence:** Eliminates representation mismatch: eigen-laws stated with `scaleVec12ℤ twelveℤ` may be consumed by
Chapter-14H laws stated with `twelveVec12ℤ`.
-}

law14O-21-scale12≡twelveVec12 : (v : Vec12ℤ) → Vec12Eq (scaleVec12ℤ twelveℤ v) (twelveVec12ℤ v)
law14O-21-scale12≡twelveVec12 v =
  (λ i → twelveℤ-*ℤ-left (block₀ v i)) ,
  ((λ i → twelveℤ-*ℤ-left (block₁ v i)) ,
   (λ i → twelveℤ-*ℤ-left (block₂ v i)))

{-
### Law 14O.22: 0-Scaling In `scaleVec12ℤ` Collapses To `zeroVec12ℤ`
**Necessity Proof:** `scaleVec12ℤ 0ℤ v` is pointwise `0ℤ *ℤ vᵢ`, which collapses to `0ℤ` by `*ℤ-zero-left`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-22-scale0≡zeroVec12 (lines 1009-1013)
**Consequence:** Eliminates representational freedom in the λ=0 eigen-equation: it is forced to be the kernel equation.
-}

law14O-22-scale0≡zeroVec12 : (v : Vec12ℤ) → Vec12Eq (scaleVec12ℤ 0ℤ v) zeroVec12ℤ
law14O-22-scale0≡zeroVec12 v =
  (λ i → *ℤ-zero-left (block₀ v i)) ,
  ((λ i → *ℤ-zero-left (block₁ v i)) ,
   (λ i → *ℤ-zero-left (block₂ v i)))

{-
### Law 14O.23: `scaleVec12ℤ`-Form 12-Eigenvectors Force Sum-Zero
**Necessity Proof:** If `L v = scale12 v`, Law 14O.21 forces `L v = twelveVec12ℤ v`, and Law 14H.13 forces `Σ₁₂ v = 0`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-23-eigen12Scale→sum0 (lines 1022-1032)
**Consequence:** Eliminates ambiguity between the two 12-scaling presentations.
-}

law14O-23-eigen12Scale→sum0 : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ twelveℤ v) → ZeroSumVec12 v
law14O-23-eigen12Scale→sum0 v eigen12Scale =
  let
    pkg : L12SpectralPackage v
    pkg = law14O-7-L-spectral-package v

    eigen12 : Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v)
    eigen12 = Vec12Eq-trans eigen12Scale (law14O-21-scale12≡twelveVec12 v)
  in
  L12Pkg-eigen12→sum0 {v = v} pkg eigen12

{-
### Law 14O.24: `scaleVec12ℤ`-Form 0-Eigenvectors Force The Kernel Constraint `12·v = J v`
**Necessity Proof:** If `L v = scale0 v`, Law 14O.22 forces `L v = 0`. Law 14H.15 then forces `12·v = J v`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-24-eigen0Scale→twelveEqJ (lines 1041-1048)
**Consequence:** Eliminates false “eigenvalue 0 is unconstrained” freedom without importing any torsion-freeness.
-}

law14O-24-eigen0Scale→twelveEqJ : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v)
law14O-24-eigen0Scale→twelveEqJ v eigen0Scale =
  let
    L0 : Vec12Eq (K12LaplacianVec12ℤ v) zeroVec12ℤ
    L0 = Vec12Eq-trans eigen0Scale (law14O-22-scale0≡zeroVec12 v)
  in
  law14H-15-L0→twelveEqJ v L0

{-
### Law 14O.25: Eigen-Equation Forces The Corresponding Constraint For λ = 12 Or λ = 0
**Necessity Proof:** Rewriting `λ` to `twelveℤ` or `0ℤ` in the eigen-equation reduces to Laws 14O.23 and 14O.24.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-25-eigen-constraints (lines 1058-1071)
**Consequence:** Eliminates the spurious “missing reverse direction” claim: the forced reverse directions exist at the
level of constraints that do not require division.
-}

law14O-25-eigen-constraints : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) → ZeroSumVec12 v) ×
  ((lam ≡ 0ℤ) → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v))
law14O-25-eigen-constraints v lam eigen = sumPart , kernelPart
  where
    P : ℤ → Set
    P t = Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ t v)

    sumPart : (lam ≡ twelveℤ) → ZeroSumVec12 v
    sumPart eqλ = law14O-23-eigen12Scale→sum0 v (subst P eqλ eigen)

    kernelPart : (lam ≡ 0ℤ) → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v)
    kernelPart eqλ = law14O-24-eigen0Scale→twelveEqJ v (subst P eqλ eigen)

{-
### Law 14O.26: J-Images Are Forced To Be Constant Vectors
**Necessity Proof:** `J12Vec12ℤ v` is definitional constant with value `sum12ℤ v`, hence it equals `constVec12ℤ (sum12ℤ v)`.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-26-J-constVec (lines 1080-1081)
**Consequence:** Eliminates any residual freedom about the structure of `J v` independent of `v`.
-}

law14O-26-J-constVec : (v : Vec12ℤ) → ConstVec12 (J12Vec12ℤ v)
law14O-26-J-constVec v = (sum12ℤ v) , ((λ _ → refl) , ((λ _ → refl) , (λ _ → refl)))

{-
### Law 14O.27: The Kernel Constraint Forces `12·v` To Be Constant
**Necessity Proof:** If `12·v = J v`, Law 14O.26 forces `J v` to be constant, hence `12·v` is constant by transport.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-27-twelveEqJ→twelveConst (lines 1090-1100)
**Consequence:** Eliminates the false degree of freedom that the λ=0 constraint leaves `12·v` structurally arbitrary.
-}

law14O-27-twelveEqJ→twelveConst : (v : Vec12ℤ) →
  Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v) → ConstVec12 (twelveVec12ℤ v)
law14O-27-twelveEqJ→twelveConst v twelveEqJ =
  let
    c : ℤ
    c = sum12ℤ v

    Jconst : Vec12Eq (J12Vec12ℤ v) (constVec12ℤ c)
    Jconst = snd (law14O-26-J-constVec v)
  in
  c , (Vec12Eq-trans twelveEqJ Jconst)

{-
### Law 14O.28: `scaleVec12ℤ`-Form 0-Eigenvectors Force `12·v` To Be Constant
**Necessity Proof:** Law 14O.24 forces `12·v = J v`, and Law 14O.27 transports constantness.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-28-eigen0Scale→twelveConst (lines 1109-1112)
**Consequence:** Adds the strongest λ=0 consequence forced over ℤ without division.
-}

law14O-28-eigen0Scale→twelveConst : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) → ConstVec12 (twelveVec12ℤ v)
law14O-28-eigen0Scale→twelveConst v eigen0Scale =
  law14O-27-twelveEqJ→twelveConst v (law14O-24-eigen0Scale→twelveEqJ v eigen0Scale)

{-
### Law 14O.29: Eigen-Equation Forces Sum-Zero (λ=12) And `12·v` Constant (λ=0)
**Necessity Proof:** The λ=12 branch is forced by Law 14O.23. The λ=0 branch is forced by Law 14O.28.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-29-eigen-constraints-strong (lines 1122-1135)
**Consequence:** Eliminates the remaining ambiguity in the external “Ausschlussgesetz” proposal: over ℤ, the forced
reverse direction for λ=0 is `ConstVec12 (12·v)`; the upgrade to `ConstVec12 v` requires an additional torsion-free law.
-}

law14O-29-eigen-constraints-strong : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) → ZeroSumVec12 v) ×
  ((lam ≡ 0ℤ) → ConstVec12 (twelveVec12ℤ v))
law14O-29-eigen-constraints-strong v lam eigen = sumPart , twelveConstPart
  where
    P : ℤ → Set
    P t = Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ t v)

    sumPart : (lam ≡ twelveℤ) → ZeroSumVec12 v
    sumPart eqλ = law14O-23-eigen12Scale→sum0 v (subst P eqλ eigen)

    twelveConstPart : (lam ≡ 0ℤ) → ConstVec12 (twelveVec12ℤ v)
    twelveConstPart eqλ = law14O-28-eigen0Scale→twelveConst v (subst P eqλ eigen)

{-
### Law 14O.30: 0-Eigenvectors Are Forced Constant Under A Positivity Witness For `twelveℤ`
**Necessity Proof:** Law 14O.24 forces `12·v = J v`, hence every coordinate has the same 12-multiple.
If `twelveℤ ≡ +suc n`, Law `*ℤ-pos-left-zero→zero` forces torsion-freeness for that multiplier, eliminating all
coordinate freedom and forcing constancy.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-30-eigen0Scale→const-assuming-twelvePos (lines 1146-1272)
**Consequence:** Reduces `λ=0` eigenvectors to constant vectors once the sign of `twelveℤ` is forced.
-}

law14O-30-eigen0Scale→const-assuming-twelvePos : (v : Vec12ℤ) →
  Σ ℕ (λ n → twelveℤ ≡ +suc n) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) →
  ConstVec12 v
law14O-30-eigen0Scale→const-assuming-twelvePos v (n , twelvePos) eigen0Scale =
  c , (eq0 , (eq1 , eq2))
  where
    c : ℤ
    c = block₀ v g0

    twelveEqJ : Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v)
    twelveEqJ = law14O-24-eigen0Scale→twelveEqJ v eigen0Scale

    -- Convert a coordinate equation `12·x = Σ` into `twelveℤ*x = Σ`.
    toMul12 : (x s : ℤ) → twelveTimesℤ x ≡ s → twelveℤ *ℤ x ≡ s
    toMul12 x s eq = trans (twelveℤ-*ℤ-left x) eq

    -- From `twelveℤ*x = twelveℤ*y`, force `x = y` using torsion-freeness of (+suc n).
    cancel12 : (x y : ℤ) → twelveℤ *ℤ x ≡ twelveℤ *ℤ y → x ≡ y
    cancel12 x y mulEq =
      let
        -- Rewrite multiplier to (+suc n).
        Q : ℤ → Set
        Q t = t *ℤ x ≡ t *ℤ y
        mulEq' : (+suc n) *ℤ x ≡ (+suc n) *ℤ y
        mulEq' = subst Q twelvePos mulEq

        -- Force (+suc n) * (x + (-y)) = 0.
        diff : ℤ
        diff = x +ℤ negℤ y

        step₀ : (+suc n) *ℤ diff +ℤ ((+suc n) *ℤ y) ≡ ((+suc n) *ℤ y)
        step₀ =
          trans
            (cong (λ t → t +ℤ ((+suc n) *ℤ y)) (*ℤ-distrib-right-+ℤ (+suc n) x (negℤ y)))
            (trans
              (+ℤ-assoc ((+suc n) *ℤ x) ((+suc n) *ℤ (negℤ y)) ((+suc n) *ℤ y))
              (trans
                (cong (λ t → ((+suc n) *ℤ x) +ℤ t)
                      (trans
                        (sym (*ℤ-distrib-right-+ℤ (+suc n) (negℤ y) y))
                        (trans
                          (cong (λ t → (+suc n) *ℤ t) (+ℤ-inv-left y))
                          (*ℤ-zero-right (+suc n)))))
                (trans
                  (cong (λ t → t +ℤ 0ℤ) mulEq')
                  (+ℤ-zero-right ((+suc n) *ℤ y)))))

        step₁ : ((+suc n) *ℤ y) +ℤ ((+suc n) *ℤ diff) ≡ ((+suc n) *ℤ y)
        step₁ =
          trans
            (sym (+ℤ-comm ((+suc n) *ℤ diff) ((+suc n) *ℤ y)))
            step₀

        mulDiff0 : (+suc n) *ℤ diff ≡ 0ℤ
        mulDiff0 = +ℤ-cancel-left ((+suc n) *ℤ y) ((+suc n) *ℤ diff) step₁

        diff0 : diff ≡ 0ℤ
        diff0 = *ℤ-pos-left-zero→zero n diff mulDiff0

        -- x + (-y) = 0 ⇒ x = y
        xy : x ≡ y
        xy =
          let
            addY : (x +ℤ negℤ y) +ℤ y ≡ 0ℤ +ℤ y
            addY = cong (λ t → t +ℤ y) diff0

            stepA : (x +ℤ negℤ y) +ℤ y ≡ x
            stepA =
              trans
                (+ℤ-assoc x (negℤ y) y)
                (trans
                  (cong (λ t → x +ℤ t) (+ℤ-inv-left y))
                  (+ℤ-zero-right x))

            stepB : (x +ℤ negℤ y) +ℤ y ≡ y
            stepB = trans addY (+ℤ-zero-left y)
          in
          trans (sym stepA) stepB
      in
      xy

    sumVal : ℤ
    sumVal = sum12ℤ v

    -- Coordinate-wise equality proofs for each block.
    eq0 : (i : Fin4) → block₀ v i ≡ c
    eq0 i =
      let
        sx : twelveTimesℤ (block₀ v i) ≡ sumVal
        sx = fst twelveEqJ i

        sc : twelveTimesℤ c ≡ sumVal
        sc = fst twelveEqJ g0

        mulEq : twelveℤ *ℤ (block₀ v i) ≡ twelveℤ *ℤ c
        mulEq = trans (toMul12 (block₀ v i) sumVal sx) (sym (toMul12 c sumVal sc))
      in
      cancel12 (block₀ v i) c mulEq

    eq1 : (i : Fin4) → block₁ v i ≡ c
    eq1 i =
      let
        sx : twelveTimesℤ (block₁ v i) ≡ sumVal
        sx = fst (snd twelveEqJ) i

        sc : twelveTimesℤ c ≡ sumVal
        sc = fst twelveEqJ g0

        mulEq : twelveℤ *ℤ (block₁ v i) ≡ twelveℤ *ℤ c
        mulEq = trans (toMul12 (block₁ v i) sumVal sx) (sym (toMul12 c sumVal sc))
      in
      cancel12 (block₁ v i) c mulEq

    eq2 : (i : Fin4) → block₂ v i ≡ c
    eq2 i =
      let
        sx : twelveTimesℤ (block₂ v i) ≡ sumVal
        sx = snd (snd twelveEqJ) i

        sc : twelveTimesℤ c ≡ sumVal
        sc = fst twelveEqJ g0

        mulEq : twelveℤ *ℤ (block₂ v i) ≡ twelveℤ *ℤ c
        mulEq = trans (toMul12 (block₂ v i) sumVal sx) (sym (toMul12 c sumVal sc))
      in
      cancel12 (block₂ v i) c mulEq

{-
### Law 14O.31: 0-Eigenvectors Are Forced Constant (No Extra Witness)
**Necessity Proof:** `twelveℤ` is definitional `twelveTimesℤ oneℤ` and reduces to a positive constructor `+suc n`.
Law 14O.30 eliminates all remaining freedom once this forced positivity witness is supplied.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-31-eigen0Scale→const (lines 1282-1286)
**Consequence:** Eliminates the remaining assumption in the kernel-to-const upgrade: `λ=0` eigenvectors are forced constant.
-}

law14O-31-eigen0Scale→const : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) →
  ConstVec12 v
law14O-31-eigen0Scale→const v eigen0Scale =
  law14O-30-eigen0Scale→const-assuming-twelvePos v twelveℤ-pos eigen0Scale

{-
### Law 14O.32: Eigen-Equation Forces Sum-Zero (λ=12) And Const (λ=0)
**Necessity Proof:** The λ=12 branch is Law 14O.23 after rewriting. The λ=0 branch is Law 14O.31 after rewriting.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-32-eigen-constraints-final (lines 1295-1308)
**Consequence:** Eliminates the final remaining gap to the corrected “Ausschlussgesetz” constraint form over ℤ.
-}

law14O-32-eigen-constraints-final : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) → ZeroSumVec12 v) ×
  ((lam ≡ 0ℤ) → ConstVec12 v)
law14O-32-eigen-constraints-final v lam eigen = sumPart , constPart
  where
    P : ℤ → Set
    P t = Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ t v)

    sumPart : (lam ≡ twelveℤ) → ZeroSumVec12 v
    sumPart eqλ = law14O-23-eigen12Scale→sum0 v (subst P eqλ eigen)

    constPart : (lam ≡ 0ℤ) → ConstVec12 v
    constPart eqλ = law14O-31-eigen0Scale→const v (subst P eqλ eigen)

{-
## Eigenvalue Exhaustion (Forced)

This section eliminates the remaining λ-freedom. The earlier laws force the constraints for λ = 12 and λ = 0;
here we force that any eigen-equation can only occur with λ = 12, λ = 0, or with the zero vector.

### Law 14O.33: Laplacian Commutes With `scaleVec12ℤ`
**Necessity Proof:** Expand both sides by the definitional K₁₂ Laplacian form.
Right-distributivity forces scaling of the 12-times term (`*ℤ-twelveTimes-right`) and of the negated sum (`*ℤ-neg-right`).
**Formal Reference:** K12SpectralDecomposition.agda.law14O-33-L-scale (lines 1336-1389)
**Consequence:** Eliminates the missing linearity degree of freedom needed to collapse the eigen-equation into a scalar constraint.
-}

scaleVec12-cong : (a : ℤ) → {u v : Vec12ℤ} → Vec12Eq u v → Vec12Eq (scaleVec12ℤ a u) (scaleVec12ℤ a v)
scaleVec12-cong a eq =
  (λ i → cong (λ t → a *ℤ t) (fst eq i)) ,
  ((λ i → cong (λ t → a *ℤ t) (fst (snd eq) i)) ,
   (λ i → cong (λ t → a *ℤ t) (snd (snd eq) i)))

scaleVec12-assoc : (a b : ℤ) → (v : Vec12ℤ) → Vec12Eq (scaleVec12ℤ a (scaleVec12ℤ b v)) (scaleVec12ℤ (a *ℤ b) v)
scaleVec12-assoc a b v =
  (λ i → sym (*ℤ-assoc a b (block₀ v i))) ,
  ((λ i → sym (*ℤ-assoc a b (block₁ v i))) ,
   (λ i → sym (*ℤ-assoc a b (block₂ v i)))
  )

law14O-33-L-scale : (lam : ℤ) → (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) (scaleVec12ℤ lam (K12LaplacianVec12ℤ v))
law14O-33-L-scale lam v = eq0 , (eq1 , eq2)
  where
    s : ℤ
    s = sum12ℤ v

    sScale : sum12ℤ (scaleVec12ℤ lam v) ≡ lam *ℤ s
    sScale = sum12-scaleVec12ℤ lam v

    sNegScale : negℤ (sum12ℤ (scaleVec12ℤ lam v)) ≡ negℤ (lam *ℤ s)
    sNegScale = cong negℤ sScale

    rhsBlock : (x : ℤ) →
      lam *ℤ (twelveTimesℤ x +ℤ negℤ s) ≡ twelveTimesℤ (lam *ℤ x) +ℤ negℤ (lam *ℤ s)
    rhsBlock x =
      trans
        (*ℤ-distrib-right-+ℤ lam (twelveTimesℤ x) (negℤ s))
        (trans
          (cong (λ t → t +ℤ (lam *ℤ negℤ s)) (*ℤ-twelveTimes-right lam x))
          (cong (λ t → twelveTimesℤ (lam *ℤ x) +ℤ t) (*ℤ-neg-right lam s)))

    eq0 : (i : Fin4) → block₀ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡ block₀ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i
    eq0 i =
      let
        step₁ :
          twelveTimesℤ (lam *ℤ block₀ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₀ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₀ v i) +ℤ t) sNegScale
      in
      trans step₁ (sym (rhsBlock (block₀ v i)))

    eq1 : (i : Fin4) → block₁ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡ block₁ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i
    eq1 i =
      let
        step₁ :
          twelveTimesℤ (lam *ℤ block₁ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₁ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₁ v i) +ℤ t) sNegScale
      in
      trans step₁ (sym (rhsBlock (block₁ v i)))

    eq2 : (i : Fin4) → block₂ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡ block₂ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i
    eq2 i =
      let
        step₁ :
          twelveTimesℤ (lam *ℤ block₂ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₂ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₂ v i) +ℤ t) sNegScale
      in
      trans step₁ (sym (rhsBlock (block₂ v i)))

{-
### Law 14O.34: Nonzero Scalar Multiplication On Vec12ℤ Has No Torsion
**Necessity Proof:** Each coordinate equation is a ℤ equation. Torsion-freeness for `+suc n` and `-suc n` forces every coordinate to be zero.
**Formal Reference:** K12SpectralDecomposition.agda.scaleVec12_nonzero_left_zero_to_zeroVec (lines 1575-1580)
**Consequence:** Eliminates the possibility that a nonzero scalar annihilates a nonzero vector.
-}

scaleVec12-pos-left-zero→zeroVec : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (scaleVec12ℤ (+suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ
scaleVec12-pos-left-zero→zeroVec n v eq =
  (λ i → *ℤ-pos-left-zero→zero n (block₀ v i) (fst eq i)) ,
  ((λ i → *ℤ-pos-left-zero→zero n (block₁ v i) (fst (snd eq) i)) ,
   (λ i → *ℤ-pos-left-zero→zero n (block₂ v i) (snd (snd eq) i)))

scaleVec12-neg-left-zero→zeroVec : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (scaleVec12ℤ (-suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ
scaleVec12-neg-left-zero→zeroVec n v eq =
  (λ i → *ℤ-neg-left-zero→zero n (block₀ v i) (fst eq i)) ,
  ((λ i → *ℤ-neg-left-zero→zero n (block₁ v i) (fst (snd eq) i)) ,
   (λ i → *ℤ-neg-left-zero→zero n (block₂ v i) (snd (snd eq) i)))

lamMinusTwelve0→lamEqTwelve : (lam : ℤ) → lam +ℤ negℤ twelveℤ ≡ 0ℤ → lam ≡ twelveℤ
lamMinusTwelve0→lamEqTwelve lam eq =
  let
    eq' : (lam +ℤ negℤ twelveℤ) +ℤ twelveℤ ≡ 0ℤ +ℤ twelveℤ
    eq' = cong (λ t → t +ℤ twelveℤ) eq

    lhsReduce : (lam +ℤ negℤ twelveℤ) +ℤ twelveℤ ≡ lam
    lhsReduce =
      trans
        (+ℤ-assoc lam (negℤ twelveℤ) twelveℤ)
        (trans
          (cong (λ t → lam +ℤ t) (+ℤ-inv-left twelveℤ))
          (+ℤ-zero-right lam))
  in
  trans (sym lhsReduce) (trans eq' (+ℤ-zero-left twelveℤ))

scaleEq→scaleDiff0 : (lam : ℤ) → (w : Vec12ℤ) →
  Vec12Eq (scaleVec12ℤ lam w) (scaleVec12ℤ twelveℤ w) →
  Vec12Eq (scaleVec12ℤ (lam +ℤ negℤ twelveℤ) w) zeroVec12ℤ
scaleEq→scaleDiff0 lam w eq = eq0 , (eq1 , eq2)
  where
    mk : (x : ℤ) → lam *ℤ x ≡ twelveℤ *ℤ x → (lam +ℤ negℤ twelveℤ) *ℤ x ≡ 0ℤ
    mk x e =
      let
        inv : lam *ℤ x +ℤ negℤ (twelveℤ *ℤ x) ≡ 0ℤ
        inv = trans (cong (λ t → t +ℤ negℤ (twelveℤ *ℤ x)) e) (+ℤ-inv-right (twelveℤ *ℤ x))
      in
      trans
        (*ℤ-distrib-left-+ℤ lam (negℤ twelveℤ) x)
        (trans
          (cong (λ t → (lam *ℤ x) +ℤ t) (*ℤ-neg-left twelveℤ x))
          inv)

    eq0 : (i : Fin4) → block₀ (scaleVec12ℤ (lam +ℤ negℤ twelveℤ) w) i ≡ block₀ zeroVec12ℤ i
    eq0 i = mk (block₀ w i) (fst eq i)

    eq1 : (i : Fin4) → block₁ (scaleVec12ℤ (lam +ℤ negℤ twelveℤ) w) i ≡ block₁ zeroVec12ℤ i
    eq1 i = mk (block₁ w i) (fst (snd eq) i)

    eq2 : (i : Fin4) → block₂ (scaleVec12ℤ (lam +ℤ negℤ twelveℤ) w) i ≡ block₂ zeroVec12ℤ i
    eq2 i = mk (block₂ w i) (snd (snd eq) i)

{-
### Law 14O.35: Eigen-Equation Forces λ ∈ {0,12} Or The Zero Vector
**Necessity Proof:** Apply `L` to the eigen-equation, use Law 14O.33 and the forced identity `L∘L = 12·L`.
This forces a scalar annihilator on `w = λ·v`. Case-split on `λ-12` and on `λ` using torsion-freeness.
**Formal Reference:** K12SpectralDecomposition.agda.law14O-35-eigenvalue-exhaustion (lines 1468-1470)
**Consequence:** Eliminates the last spurious freedom in the external “Ausschlussgesetz”: λ cannot be arbitrary unless v is zero.
-}

data Inspect {A : Set} (x : A) : Set where
  reveal : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect x = reveal x refl

law14O-35-eigenvalue-exhaustion : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) ⊎ (lam ≡ 0ℤ)) ⊎ (Vec12Eq v zeroVec12ℤ)
-- Drive the case split by matching on the computed difference.
law14O-35-eigenvalue-exhaustion v lam eigen with inspect (lam +ℤ negℤ twelveℤ)
... | reveal 0ℤ eq = inj₁ (inj₁ (lamMinusTwelve0→lamEqTwelve lam eq))
... | reveal (+suc n) eq =
  let
    w : Vec12ℤ
    w = scaleVec12ℤ lam v

    LL : Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (K12LaplacianVec12ℤ (scaleVec12ℤ lam v))
    LL = K12Laplacian-cong (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) eigen

    eqLamW : Vec12Eq (scaleVec12ℤ lam w) (scaleVec12ℤ twelveℤ w)
    eqLamW =
      let
        left : Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (scaleVec12ℤ twelveℤ w)
        left =
          Vec12Eq-trans
            (law14H-11-LL-twelveL v)
            (Vec12Eq-trans
              (Vec12Eq-sym (law14O-21-scale12≡twelveVec12 (K12LaplacianVec12ℤ v)))
              (scaleVec12-cong twelveℤ eigen))

        right : Vec12Eq (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) (scaleVec12ℤ lam w)
        right = Vec12Eq-trans (law14O-33-L-scale lam v) (scaleVec12-cong lam eigen)

        both : Vec12Eq (scaleVec12ℤ twelveℤ w) (scaleVec12ℤ lam w)
        both = Vec12Eq-trans (Vec12Eq-sym left) (Vec12Eq-trans LL right)
      in
      Vec12Eq-sym both

    diff0 : Vec12Eq (scaleVec12ℤ (+suc n) w) zeroVec12ℤ
    diff0 = subst (λ t → Vec12Eq (scaleVec12ℤ t w) zeroVec12ℤ) eq (scaleEq→scaleDiff0 lam w eqLamW)

    w0 : Vec12Eq w zeroVec12ℤ
    w0 = scaleVec12-pos-left-zero→zeroVec n w diff0
  in
  caseLam lam w0
  where
    caseLam : (lam : ℤ) → Vec12Eq (scaleVec12ℤ lam v) zeroVec12ℤ → ((lam ≡ twelveℤ) ⊎ (lam ≡ 0ℤ)) ⊎ (Vec12Eq v zeroVec12ℤ)
    caseLam lam w0 with lam
    ... | 0ℤ = inj₁ (inj₂ refl)
    ... | +suc m = inj₂ (scaleVec12-pos-left-zero→zeroVec m v w0)
    ... | -suc m = inj₂ (scaleVec12-neg-left-zero→zeroVec m v w0)

... | reveal (-suc n) eq =
  let
    w : Vec12ℤ
    w = scaleVec12ℤ lam v

    LL : Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (K12LaplacianVec12ℤ (scaleVec12ℤ lam v))
    LL = K12Laplacian-cong (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) eigen

    eqLamW : Vec12Eq (scaleVec12ℤ lam w) (scaleVec12ℤ twelveℤ w)
    eqLamW =
      let
        left : Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (scaleVec12ℤ twelveℤ w)
        left =
          Vec12Eq-trans
            (law14H-11-LL-twelveL v)
            (Vec12Eq-trans
              (Vec12Eq-sym (law14O-21-scale12≡twelveVec12 (K12LaplacianVec12ℤ v)))
              (scaleVec12-cong twelveℤ eigen))

        right : Vec12Eq (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) (scaleVec12ℤ lam w)
        right = Vec12Eq-trans (law14O-33-L-scale lam v) (scaleVec12-cong lam eigen)

        both : Vec12Eq (scaleVec12ℤ twelveℤ w) (scaleVec12ℤ lam w)
        both = Vec12Eq-trans (Vec12Eq-sym left) (Vec12Eq-trans LL right)
      in
      Vec12Eq-sym both

    diff0 : Vec12Eq (scaleVec12ℤ (-suc n) w) zeroVec12ℤ
    diff0 = subst (λ t → Vec12Eq (scaleVec12ℤ t w) zeroVec12ℤ) eq (scaleEq→scaleDiff0 lam w eqLamW)

    w0 : Vec12Eq w zeroVec12ℤ
    w0 = scaleVec12-neg-left-zero→zeroVec n w diff0
  in
  caseLam lam w0
  where
    caseLam : (lam : ℤ) → Vec12Eq (scaleVec12ℤ lam v) zeroVec12ℤ → ((lam ≡ twelveℤ) ⊎ (lam ≡ 0ℤ)) ⊎ (Vec12Eq v zeroVec12ℤ)
    caseLam lam w0 with lam
    ... | 0ℤ = inj₁ (inj₂ refl)
    ... | +suc m = inj₂ (scaleVec12-pos-left-zero→zeroVec m v w0)
    ... | -suc m = inj₂ (scaleVec12-neg-left-zero→zeroVec m v w0)

{-
### Law 14O.36: Corrected Ausschlussgesetz (Constraint + Exhaustion)
**Necessity Proof:** Combine Law 14O.35 (exhaustion) with Law 14O.32 (forced constraints for λ=12 and λ=0).
**Formal Reference:** K12SpectralDecomposition.agda.law14O-36-eigen-classification (lines 1564-1567)
**Consequence:** Produces the unique coherent classification statement: eigenvectors are forced into the λ=12 sum-zero case,
the λ=0 constant case, or the zero-vector case.
-}

law14O-36-eigen-classification : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) × ZeroSumVec12 v) ⊎ (((lam ≡ 0ℤ) × ConstVec12 v) ⊎ (Vec12Eq v zeroVec12ℤ))
law14O-36-eigen-classification v lam eigen with law14O-35-eigenvalue-exhaustion v lam eigen
... | inj₁ (inj₁ lam12) =
  inj₁ (lam12 , fst (law14O-32-eigen-constraints-final v lam eigen) lam12)
... | inj₁ (inj₂ lam0) =
  inj₂ (inj₁ (lam0 , snd (law14O-32-eigen-constraints-final v lam eigen) lam0))
... | inj₂ v0 =
  inj₂ (inj₂ v0)

scaleVec12_nonzero_left_zero_to_zeroVec :
  (n : ℕ) → (v : Vec12ℤ) →
  (Vec12Eq (scaleVec12ℤ (+suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ)
  × (Vec12Eq (scaleVec12ℤ (-suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ)
scaleVec12_nonzero_left_zero_to_zeroVec n v =
  scaleVec12-pos-left-zero→zeroVec n v , scaleVec12-neg-left-zero→zeroVec n v
