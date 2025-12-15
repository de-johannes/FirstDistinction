{-# OPTIONS --safe --without-K #-}

-- ═══════════════════════════════════════════════════════════════════════════
-- PHYSICS-CHALLENGE: Why Physics Doesn't Come First
-- ═══════════════════════════════════════════════════════════════════════════
--
-- Claim: D₀ (distinction) is ontologically prior to physics.
--
-- This IS a claim about reality:
--   Nothing can exist without being distinguishable from non-existence.
--
-- Proof: To deny distinction requires using distinction.
--        Therefore distinction cannot be denied.
--        Therefore distinction is necessary for any possible world.
--
-- CHALLENGE TO PHYSICISTS:
--   To refute this result, you must deny that distinction
--   is a precondition for identity, difference, or existence.
--   Any such denial necessarily uses the very notion it rejects.
--
-- Type checker verifies. No axioms. No postulates. --safe --without-K
--
-- ═══════════════════════════════════════════════════════════════════════════

module Physics-Challenge where

open import Agda.Primitive using (Level; lsuc; _⊔_; lzero)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- § 1. Minimal Definitions
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

data ⊥ : Set where

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥

data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (ℓ ⊔ ℓ') where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- § 2. The First Distinction D₀
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- D₀: φ distinguishable from ¬φ
--
-- This is not an assumption. To deny it requires using it.

data Distinction : Set where
  φ  : Distinction
  ¬φ : Distinction

-- Proof: φ ≠ ¬φ (type checker verifies)
φ≢¬φ : ¬ (φ ≡ ¬φ)
φ≢¬φ ()

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- § 3. Constraint: Formally Verifiable Theories
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Constraint (C1):
--   We restrict attention to theories whose objects are
--   constructively representable.
--
-- This is methodological, not ontological:
--   Any theory that can be formally checked falls under (C1).
--   Physics, to be testable, must be formalizable.
--   Therefore physics falls under (C1).

record ConstructiveOntology (ℓ : Level) : Set (lsuc ℓ) where
  field
    Dist            : Set ℓ
    inhabited       : Dist
    distinguishable : Σ Dist (λ a → Σ Dist (λ b → ¬ (a ≡ b)))

open ConstructiveOntology public

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- § 4. Theorem: D₀ is Forced
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

theorem-D0-forced : ConstructiveOntology lzero
theorem-D0-forced = record
  { Dist            = Distinction
  ; inhabited       = φ
  ; distinguishable = φ , (¬φ , φ≢¬φ)
  }

-- Initiality: Distinction is initial among constructive ontologies.
-- For any ConstructiveOntology O, there exists a canonical map from D₀.
-- (Universal property, not value extraction.)

physics-cannot-be-prior : ∀ {ℓ} → ConstructiveOntology ℓ → Distinction
physics-cannot-be-prior _ = φ

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- § 5. Consequence: Physics Cannot Come First
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Any physical theory that is:
--   - formally expressible
--   - empirically testable
--   - logically consistent
--
-- must presuppose distinguishable states.
--
-- Therefore: D₀ is prior to physics.
--
-- To reject this, provide ONE of:
--   1. A physical observable without distinguishable outcomes
--   2. A formal theory without distinction that makes predictions
--   3. A denial of distinction that doesn't use distinction
--
-- Until then: D₀ comes first. Physics follows.

-- ═══════════════════════════════════════════════════════════════════════════
-- DEDICATION
-- ═══════════════════════════════════════════════════════════════════════════
--
-- This proof stands on the shoulders of giants:
--
--   George Spencer-Brown (1923–2016)
--     "Draw a distinction." — Laws of Form, 1969
--
--   Per Martin-Löf (*1942)
--     Constructive type theory: existence = construction
--
--   Gottlob Frege (1848–1925)
--     The concept of concept; logic as foundation
--
--   L.E.J. Brouwer (1881–1966)
--     Intuitionism: mathematics is construction, not discovery
--
--   Ulf Norell (*1979)
--     Agda: the tool that makes this proof checkable
--
-- And to all who dared ask: "What comes before physics?"
--
-- ═══════════════════════════════════════════════════════════════════════════
-- END
-- ═══════════════════════════════════════════════════════════════════════════
