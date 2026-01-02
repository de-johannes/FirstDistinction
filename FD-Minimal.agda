{-# OPTIONS --safe --without-K #-}

-- ============================================================
-- WhyTypeTheory: Minmal Core of the First Distinction
-- ============================================================
--
-- Constructive type theory replaces postulation with construction.
-- The first distinction is not a value but an act.
-- This file does not report the act; it instantiates it.
--
-- ============================================================

module FD-Minimal where

open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)

-- ============================================================
-- § 1. The Act of Distinction
-- ============================================================
--
-- Writing this is the act.
-- Before the code: the unmarked space (not formalizable).
-- After the code: structure.

-- ============================================================
-- § 2. D₀ - The First Act
-- ============================================================
--
-- A singleton: no internal difference.
-- D₀ says only: there is.
--
-- Writing this definition is the first act (Spencer-Brown: the mark).

data D₀ : Set where
  ● : D₀

-- ============================================================
-- § 3. D₁ - The Polarity
-- ============================================================
--
-- Polarity is not assumed; it is formed from the first act.
-- Formally: there is no inhabitant of D₁ without a D₀ witness.
--
-- Writing this definition is the second act.

record D₁ : Set where
  constructor ○
  field
    from₀ : D₀

-- ============================================================
-- § 4. D₂ - The Relation
-- ============================================================
--
-- Relation is not added; it appears once polarity exists.
-- Formally: there is no inhabitant of D₂ without a D₁ witness,
-- and thus none without D₀.
--
-- Two constructors witness the minimal split (here/there).
-- Writing this definition is the third act.

data D₂ : Set where
  here  : D₁ → D₂
  there : D₁ → D₂

-- ============================================================
-- § 5. Minimal Definitions
-- ============================================================

-- Minimal primitives used below: ⊥, ⊤, ¬, ≡, Σ.

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

-- ============================================================
-- § 6. Typed Dependency
-- ============================================================
--
-- The dependence is typed, not narrated.
-- Any inhabitant of D₂ contains a D₁ witness.
-- Any inhabitant of D₁ contains a D₀ witness.
-- Therefore any inhabitant of D₂ contains D₀ implicitly.

step₀ : ⊤ → D₀
step₀ _ = ●

step₁ : D₀ → D₁
step₁ d0 = ○ d0

step₂ : D₁ → D₂
step₂ d1 = here d1

-- One canonical construction: ⊤ → D₀ → D₁ → D₂
the-path : ⊤ → D₂
the-path t = step₂ (step₁ (step₀ t))

-- ============================================================
-- § 7. Only D₂ Enables Distinguishability
-- ============================================================
--
-- Distinguishability begins at the level of relation.
-- here (○ ●) and there (○ ●) are different constructors, hence unequal.

-- Every inhabitant of D₂ carries its D₁ witness.
extract₁ : D₂ → D₁
extract₁ (here d1)  = d1
extract₁ (there d1) = d1

-- Therefore every inhabitant of D₂ carries D₀ implicitly.
extract₀ : D₂ → D₀
extract₀ (here d1)  = D₁.from₀ d1
extract₀ (there d1) = D₁.from₀ d1

-- Packaging lemma (no extra content beyond definitional equality):
-- every relation carries an origin witness.
origin-witness : (d : D₂) → Σ D₀ (λ o → extract₀ d ≡ o)
origin-witness d = extract₀ d , refl

here≢there : ¬ (here (○ ●) ≡ there (○ ●))
here≢there ()

-- ============================================================
-- § 8. ConstructiveOntology
-- ============================================================
--
-- A constructive ontology: inhabited, and not collapsed to one point.
-- D₀ alone cannot witness a split; D₂ can.

record ConstructiveOntology (ℓ : Level) : Set (lsuc ℓ) where
  field
    Dist : Set ℓ
    inhabited : Dist
    distinguishable : Σ Dist (λ a → Σ Dist (λ b → ¬ (a ≡ b)))

open ConstructiveOntology public

-- D₂ satisfies ConstructiveOntology
D₂-is-ontology : ConstructiveOntology lzero
D₂-is-ontology = record
  { Dist = D₂
  ; inhabited = here (○ ●)
  ; distinguishable = here (○ ●) , (there (○ ●) , here≢there)
  }

-- ============================================================
-- § 9. The Sequence IS Time
-- ============================================================
--
-- Reading (not a meta-theorem about the host language):
-- every term of D₂ carries a D₁ witness (extract₁),
-- and therefore carries a D₀ witness (extract₀).

record Sequence : Set where
  field
    first  : D₀
    second : D₁
    third  : D₂

the-sequence : Sequence
the-sequence = record
  { first  = ●
  ; second = ○ ●
  ; third  = here (○ ●)
  }

-- ============================================================
-- § 10. Ontological Priority
-- ============================================================
--
-- Although the split is witnessed only in D₂,
-- the chain begins with D₀.

origin : D₀
origin = ●

polarity : D₁
polarity = ○ ●

ontology : ConstructiveOntology lzero
ontology = D₂-is-ontology

-- ============================================================
-- § 11. Summary
-- ============================================================
--
-- The first distinction is not a value but an act.
--
-- Unmarked space (not formalizable)
-- D₀ = ●  (first act)
-- D₁ = ○  (polarity, carrying D₀)
-- D₂ = here | there  (relation, carrying D₁ and thus D₀)
--
-- Being begins with D₀.
-- Distinguishability begins with D₂.
--
-- "Existence is represented as a singleton;
--  the first distinction is modeled as a primitive transition
--  introducing relational structure, not as a Boolean value."
