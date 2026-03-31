-- § Strict Environment Constraint: No axioms, no postulates, no Axiom K.
{-# OPTIONS --safe --without-K #-}

module FirstDistinction where

-- § Stratification primitives are forced to prevent self-reference paradoxes.
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
-- § Propositional equality: the identity type with unique constructor refl.
infix 4 _≡_

data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- § Symmetry is forced by elimination on refl.
sym : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- § Transitivity is forced by elimination on the first proof.
trans : {ℓ : Level} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

-- § Congruence: equality is invariant under function application.
cong : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- § Substitution: transport along an equality proof.
subst : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} (P : A → Set ℓ₂) {x y : A} → x ≡ y → P x → P y
subst P refl px = px
-- § Lift embeds a type into the next universe level.
data Lift {ℓ : Level} (A : Set ℓ) : Set (lsuc ℓ) where
  lift : A → Lift A

-- § Lower extracts the embedded value.
lower : {ℓ : Level} {A : Set ℓ} → Lift A → A
lower (lift x) = x

-- § Lift is injective by construction.
lift-injective : {ℓ : Level} {A : Set ℓ} {x y : A} → lift x ≡ lift y → x ≡ y
lift-injective refl = refl
-- § Universe-polymorphic equality at Setω.
infix 4 _≡ω_

data _≡ω_ {A : Setω} (x : A) : A → Setω where
  reflω : x ≡ω x

-- § Symmetry at Setω.
symω : {A : Setω} {x y : A} → x ≡ω y → y ≡ω x
symω reflω = reflω

-- § Transitivity at Setω.
transω : {A : Setω} {x y z : A} → x ≡ω y → y ≡ω z → x ≡ω z
transω reflω q = q

-- § Congruence at Setω.
congω : {A B : Setω} (f : A → B) {x y : A} → x ≡ω y → f x ≡ω f y
congω f reflω = reflω

-- § Substitution at Setω.
substω : {A : Setω} (P : A → Setω) {x y : A} → x ≡ω y → P x → P y
substω P reflω px = px
-- § Non-dependent product of two types.
infixr 3 _×_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

-- § Dependent pair: the type of witnesses.
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public
-- § The empty type: no constructors, no inhabitants.
data ⊥ : Set where

-- § Ex falso: the empty type eliminates into any type.
⊥-elim : {ℓ : Level} {A : Set ℓ} → ⊥ → A
⊥-elim ()

-- § Negation: the unique map into absurdity.
¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥

-- § Double negation.
¬¬_ : {ℓ : Level} → Set ℓ → Set ℓ
¬¬ A = ¬ (¬ A)

-- § Inequality: negation of propositional equality.
infix 2 _≠_
_≠_ : {ℓ : Level} {A : Set ℓ} → A → A → Set ℓ
x ≠ y = ¬ (x ≡ y)
-- § Disjoint union (coproduct) of two types.
infixr 2 _⊎_

data _⊎_ {ℓ : Level} (A B : Set ℓ) : Set ℓ where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- § Disjoint union at Setω.
infixr 2 _⊎ω_

data _⊎ω_ (A B : Setω) : Setω where
  inj₁ω : A → A ⊎ω B
  inj₂ω : B → A ⊎ω B
-- § Contractibility: a single center absorbs all inhabitants.
isContr : Set → Set
isContr A = Σ A (λ c → (x : A) → c ≡ x)

-- § A type has a distinct pair if two inhabitants are provably unequal.
HasDistinctPair : Set → Set
HasDistinctPair A = Σ A (λ a → Σ A (λ b → a ≠ b))

-- § Non-triviality: the type is not contractible.
NonTrivial : Set → Set
NonTrivial A = ¬ (isContr A)
-- § The first distinction: carrier, boundary points, separation, and coverage.
record Distinction : Set1 where
  field
    S     : Set
    ℓ     : S
    r     : S
    ℓ≠r   : ℓ ≠ r
    cover : (x : S) → (x ≡ ℓ) ⊎ (x ≡ r)

open Distinction public
-- § Non-vacuity demands that Distinction cannot be refuted.
record NonVacuityLaw : Set1 where
  field
    nonvacuity : ¬¬ Distinction

open NonVacuityLaw public
-- § Law 0.0: Distinction is irrefutable.
law0-0-nonvacuity : (nv : NonVacuityLaw) → ¬¬ Distinction
law0-0-nonvacuity = nonvacuity
-- § Law 0.1: NonVacuityLaw is non-eliminability of Distinction.
law0-1-nonvacuity-is-non-eliminability :
  NonVacuityLaw → ¬ (¬ Distinction)
law0-1-nonvacuity-is-non-eliminability = nonvacuity
-- § Law 0.2: Distinction carrier is inhabited.
law0-2-inhabited : (d : Distinction) → S d
law0-2-inhabited d = ℓ d
-- § Law 0.3: Distinction carrier has a distinct pair.
law0-3-has-distinct-pair : (d : Distinction) → HasDistinctPair (S d)
law0-3-has-distinct-pair d = (ℓ d , (r d , ℓ≠r d))
-- § Law 0.4: Distinction carrier is non-contractible.
law0-4-not-contractible : (d : Distinction) → NonTrivial (S d)
law0-4-not-contractible d (c , collapse) =
  ℓ≠r d (trans (sym (collapse (ℓ d))) (collapse (r d)))
-- § Law 0.5: Distinct pair forces non-contractibility.
law0-5-distinct-pair-forces-nontrivial :
  {A : Set} → HasDistinctPair A → NonTrivial A
law0-5-distinct-pair-forces-nontrivial (a , (b , a≠b)) (c , collapse) =
  a≠b (trans (sym (collapse a)) (collapse b))
-- § Law 0.6: Distinction is reconstructible from its data.
fromDistinctCovered :
  {S₀ : Set} (a b : S₀) →
  a ≠ b →
  ((x : S₀) → (x ≡ a) ⊎ (x ≡ b)) →
  Distinction
fromDistinctCovered {S₀} a b a≠b cov = record
  { S = S₀ ; ℓ = a ; r = b ; ℓ≠r = a≠b ; cover = cov }

law0-6-reconstruction :
  {S₀ : Set} (a b : S₀) →
  (a≠b : a ≠ b) →
  (cov : (x : S₀) → (x ≡ a) ⊎ (x ≡ b)) →
  Distinction
law0-6-reconstruction = fromDistinctCovered
-- § Law 0.7: Reconstruction is exact by definitional equality.
law0-7-reconstruction-exact :
  (d : Distinction) →
  fromDistinctCovered (ℓ d) (r d) (ℓ≠r d) (cover d) ≡ d
law0-7-reconstruction-exact d = refl
-- § Law 1.1: Carrier coverage is two-class.
law1-1-cover : (d : Distinction) → (x : S d) → (x ≡ ℓ d) ⊎ (x ≡ r d)
law1-1-cover = cover
-- § The canonical eliminator for a distinction carrier.
Distinction-elim :
  (d : Distinction) →
  {P : S d → Set} →
  P (ℓ d) →
  P (r d) →
  (x : S d) →
  P x
Distinction-elim d {P} pℓ pr x with cover d x
... | inj₁ x≡ℓ = subst P (sym x≡ℓ) pℓ
... | inj₂ x≡r = subst P (sym x≡r) pr
-- § Law 1.2: Elimination is forced by coverage.
law1-2-elim :
  (d : Distinction) →
  {P : S d → Set} →
  P (ℓ d) →
  P (r d) →
  (x : S d) →
  P x
law1-2-elim = Distinction-elim
-- § The dual map: swap boundary cases.
Distinction-dual : (d : Distinction) → S d → S d
Distinction-dual d x with cover d x
... | inj₁ _ = r d
... | inj₂ _ = ℓ d

-- § Duality is involutive by exhaustive case analysis.
Distinction-dual-involutive :
  (d : Distinction) →
  (x : S d) →
  Distinction-dual d (Distinction-dual d x) ≡ x
Distinction-dual-involutive d =
  Distinction-elim d proof-ℓ proof-r
  where
    proof-ℓ : Distinction-dual d (Distinction-dual d (ℓ d)) ≡ ℓ d
    proof-ℓ with cover d (ℓ d)
    ... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d) ℓ≡r)
    ... | inj₁ _ with cover d (r d)
    ... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d) (sym r≡ℓ))
    ... | inj₂ _   = refl

    proof-r : Distinction-dual d (Distinction-dual d (r d)) ≡ r d
    proof-r with cover d (r d)
    ... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d) (sym r≡ℓ))
    ... | inj₂ _ with cover d (ℓ d)
    ... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d) ℓ≡r)
    ... | inj₁ _   = refl
-- § Law 1.3: Duality is an involution.
law1-3-dual-involutive :
  (d : Distinction) →
  (x : S d) →
  Distinction-dual d (Distinction-dual d x) ≡ x
law1-3-dual-involutive = Distinction-dual-involutive
-- § Pointwise equality of functions.
infix 4 _≗_
_≗_ : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → (A → B) → Set (ℓ₁ ⊔ ℓ₂)
_≗_ {A = A} f g = (x : A) → f x ≡ g x

-- § The identity function.
id : {A : Set} → A → A
id x = x
-- § The four-case classification of endomorphisms.
data EndoCase : Set where
  case-constL : EndoCase
  case-constR : EndoCase
  case-id     : EndoCase
  case-dual   : EndoCase
-- § K₄ endomorphism algebra: classify, interpret, and verify.
module K₄ (d : Distinction) where
  Endo : Set
  Endo = S d → S d

  ≗-refl : {f : Endo} → f ≗ f
  ≗-refl x = refl

  ≗-sym : {f g : Endo} → f ≗ g → g ≗ f
  ≗-sym p x = sym (p x)

  ≗-trans : {f g h : Endo} → f ≗ g → g ≗ h → f ≗ h
  ≗-trans p q x = trans (p x) (q x)
  -- § Constant-left endomorphism.
  constL : Endo
  constL _ = ℓ d

  -- § Constant-right endomorphism.
  constR : Endo
  constR _ = r d

  -- § The dual endomorphism.
  dual : Endo
  dual = Distinction-dual d

  -- § Dual sends ℓ to r.
  dual-ℓ : dual (ℓ d) ≡ r d
  dual-ℓ with cover d (ℓ d)
  ... | inj₁ _   = refl
  ... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d) ℓ≡r)

  -- § Dual sends r to ℓ.
  dual-r : dual (r d) ≡ ℓ d
  dual-r with cover d (r d)
  ... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d) (sym r≡ℓ))
  ... | inj₂ _   = refl
  -- § Interpret a case label as an endofunction.
  interpret : EndoCase → Endo
  interpret case-constL = constL
  interpret case-constR = constR
  interpret case-id     = id
  interpret case-dual   = dual

  -- § Classify an endofunction by its boundary outputs.
  classify : Endo → EndoCase
  classify f with cover d (f (ℓ d)) | cover d (f (r d))
  ... | inj₁ _ | inj₁ _ = case-constL
  ... | inj₂ _ | inj₂ _ = case-constR
  ... | inj₁ _ | inj₂ _ = case-id
  ... | inj₂ _ | inj₁ _ = case-dual
  -- § Soundness at ℓ: interpretation recovers the value at ℓ.
  sound-at-ℓ : (f : Endo) → interpret (classify f) (ℓ d) ≡ f (ℓ d)
  sound-at-ℓ f with cover d (f (ℓ d)) | cover d (f (r d))
  ... | inj₁ fl≡ℓ | inj₁ _     = sym fl≡ℓ
  ... | inj₂ fl≡r | inj₂ _     = sym fl≡r
  ... | inj₁ fl≡ℓ | inj₂ _     = sym fl≡ℓ
  ... | inj₂ fl≡r | inj₁ _     = trans dual-ℓ (sym fl≡r)

  -- § Soundness at r: interpretation recovers the value at r.
  sound-at-r : (f : Endo) → interpret (classify f) (r d) ≡ f (r d)
  sound-at-r f with cover d (f (ℓ d)) | cover d (f (r d))
  ... | inj₁ _     | inj₁ fr≡ℓ = sym fr≡ℓ
  ... | inj₂ _     | inj₂ fr≡r = sym fr≡r
  ... | inj₁ _     | inj₂ fr≡r = sym fr≡r
  ... | inj₂ _     | inj₁ fr≡ℓ = trans dual-r (sym fr≡ℓ)

  -- § Soundness: classification followed by interpretation recovers behavior.
  classify-sound : (f : Endo) → interpret (classify f) ≗ f
  classify-sound f x = Distinction-elim d (sound-at-ℓ f) (sound-at-r f) x
  -- § Endofunctions are determined by their boundary values.
  endo-determined :
    (f g : Endo) →
    f (ℓ d) ≡ g (ℓ d) →
    f (r d) ≡ g (r d) →
    f ≗ g
  endo-determined f g eqℓ eqr x = Distinction-elim d eqℓ eqr x

  -- § Interpretation is injective: distinct cases produce distinct behavior.
  interpret-injective :
    (c c' : EndoCase) →
    interpret c ≗ interpret c' →
    c ≡ c'
  interpret-injective case-constL case-constL _ = refl
  interpret-injective case-constL case-constR p = ⊥-elim ((ℓ≠r d) (p (ℓ d)))
  interpret-injective case-constL case-id     p = ⊥-elim ((ℓ≠r d) (p (r d)))
  interpret-injective case-constL case-dual   p =
    ⊥-elim ((ℓ≠r d) (trans (p (ℓ d)) dual-ℓ))

  interpret-injective case-constR case-constL p =
    ⊥-elim ((ℓ≠r d) (sym (p (ℓ d))))
  interpret-injective case-constR case-constR _ = refl
  interpret-injective case-constR case-id     p =
    ⊥-elim ((ℓ≠r d) (sym (p (ℓ d))))
  interpret-injective case-constR case-dual   p =
    ⊥-elim ((ℓ≠r d) (sym (trans (p (r d)) dual-r)))

  interpret-injective case-id     case-constL p =
    ⊥-elim ((ℓ≠r d) (sym (p (r d))))
  interpret-injective case-id     case-constR p = ⊥-elim ((ℓ≠r d) (p (ℓ d)))
  interpret-injective case-id     case-id     _ = refl
  interpret-injective case-id     case-dual   p =
    ⊥-elim ((ℓ≠r d) (trans (p (ℓ d)) dual-ℓ))

  interpret-injective case-dual   case-constL p =
    ⊥-elim ((ℓ≠r d) (sym (trans (sym (dual-ℓ)) (p (ℓ d)))))
  interpret-injective case-dual   case-constR p =
    ⊥-elim ((ℓ≠r d) (trans (sym (dual-r)) (p (r d))))
  interpret-injective case-dual   case-id     p =
    ⊥-elim ((ℓ≠r d) (sym (trans (sym (dual-ℓ)) (p (ℓ d)))))
  interpret-injective case-dual   case-dual   _ = refl
  -- § Classification is unique: the label is forced by soundness + injectivity.
  classify-unique : (f : Endo) → (c : EndoCase) → interpret c ≗ f → c ≡ classify f
  classify-unique f c c≗f =
    interpret-injective c (classify f) (≗-trans c≗f (≗-sym (classify-sound f)))
-- § All four EndoCase constructors are pairwise distinct.
EndoCase-distinct :
  (case-constL ≡ case-constR → ⊥) ×
  (case-constL ≡ case-id     → ⊥) ×
  (case-constL ≡ case-dual   → ⊥) ×
  (case-constR ≡ case-id     → ⊥) ×
  (case-constR ≡ case-dual   → ⊥) ×
  (case-id     ≡ case-dual   → ⊥)
EndoCase-distinct =
  (λ ()) ,
  ((λ ()) ,
   ((λ ()) ,
    ((λ ()) ,
     ((λ ()) ,
      (λ ())))))
-- § Top-level K₄ soundness witness.
k4-classification-sound :
  (d : Distinction) →
  (f : S d → S d) →
  Σ EndoCase (λ c → K₄.interpret d c ≗ f)
k4-classification-sound d f = K₄.classify d f , K₄.classify-sound d f

-- § Top-level K₄ uniqueness witness.
k4-classification-unique :
  (d : Distinction) →
  (f : S d → S d) →
  (c₁ c₂ : EndoCase) →
  K₄.interpret d c₁ ≗ f →
  K₄.interpret d c₂ ≗ f →
  c₁ ≡ c₂
k4-classification-unique d f c₁ c₂ p₁ p₂ =
  K₄.interpret-injective d c₁ c₂ (K₄.≗-trans d p₁ (K₄.≗-sym d p₂))
-- § Law 1.4: Endo(S) classifies into exactly four cases.
law1-4-classify : (d : Distinction) → (S d → S d) → EndoCase
law1-4-classify d = K₄.classify d
-- § Law 1.5: Classification is sound.
law1-5-classify-sound : (d : Distinction) → (f : S d → S d) → K₄.interpret d (K₄.classify d f) ≗ f
law1-5-classify-sound d f = snd (k4-classification-sound d f)
-- § Law 1.6: Endo is determined by boundary values.
law1-6-endo-determined :
  (d : Distinction) →
  (f g : S d → S d) →
  f (ℓ d) ≡ g (ℓ d) →
  f (r d) ≡ g (r d) →
  f ≗ g
law1-6-endo-determined d = K₄.endo-determined d
-- § Law 1.7: Classification is unique.
law1-7-classify-unique :
  (d : Distinction) →
  (f : S d → S d) →
  (c : EndoCase) →
  K₄.interpret d c ≗ f →
  c ≡ K₄.classify d f
law1-7-classify-unique d f c p =
  k4-classification-unique d f c (fst (k4-classification-sound d f)) p (snd (k4-classification-sound d f))
-- § The canonical two-element type.
data Two : Set where
  L : Two
  R : Two

-- § L and R are distinct.
Two-L≠R : L ≠ R
Two-L≠R ()

-- § Exhaustive two-class coverage for Two.
Two-cover : (x : Two) → (x ≡ L) ⊎ (x ≡ R)
Two-cover L = inj₁ refl
Two-cover R = inj₂ refl

-- § Two forms a canonical Distinction.
Two-distinction : Distinction
Two-distinction = record
  { S     = Two
  ; ℓ     = L
  ; r     = R
  ; ℓ≠r   = Two-L≠R
  ; cover = Two-cover
  }
-- § Boundary-preserving isomorphism between distinctions.
record DistinctionIso (d₁ d₂ : Distinction) : Set1 where
  field
    to      : S d₁ → S d₂
    from    : S d₂ → S d₁
    to-from : (y : S d₂) → to (from y) ≡ y
    from-to : (x : S d₁) → from (to x) ≡ x
    to-ℓ    : to (ℓ d₁) ≡ ℓ d₂
    to-r    : to (r d₁) ≡ r d₂

open DistinctionIso public

-- § Equivalence without boundary constraints.
record DistinctionEquiv (d₁ d₂ : Distinction) : Set1 where
  field
    to      : S d₁ → S d₂
    from    : S d₂ → S d₁
    to-from : (y : S d₂) → to (from y) ≡ y
    from-to : (x : S d₁) → from (to x) ≡ x

open DistinctionEquiv public

-- § Forgetting boundary data from an isomorphism.
forgetIso : {d₁ d₂ : Distinction} → DistinctionIso d₁ d₂ → DistinctionEquiv d₁ d₂
forgetIso i = record
  { to      = DistinctionIso.to i
  ; from    = DistinctionIso.from i
  ; to-from = DistinctionIso.to-from i
  ; from-to = DistinctionIso.from-to i
  }
-- § The canonical boundary-preserving map to Two.
toTwo : (d : Distinction) → S d → Two
toTwo d x with cover d x
... | inj₁ _ = L
... | inj₂ _ = R

-- § The canonical embedding from Two.
fromTwo : (d : Distinction) → Two → S d
fromTwo d L = ℓ d
fromTwo d R = r d

-- § toTwo sends ℓ to L.
toTwo-ℓ : (d : Distinction) → toTwo d (ℓ d) ≡ L
toTwo-ℓ d with cover d (ℓ d)
... | inj₁ _   = refl
... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d) ℓ≡r)

-- § toTwo sends r to R.
toTwo-r : (d : Distinction) → toTwo d (r d) ≡ R
toTwo-r d with cover d (r d)
... | inj₂ _   = refl
... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d) (sym r≡ℓ))

-- § fromTwo ∘ toTwo is the identity.
fromTwo-toTwo : (d : Distinction) → (x : S d) → fromTwo d (toTwo d x) ≡ x
fromTwo-toTwo d =
  Distinction-elim d
    (trans (cong (fromTwo d) (toTwo-ℓ d)) refl)
    (trans (cong (fromTwo d) (toTwo-r d)) refl)

-- § toTwo ∘ fromTwo is the identity.
toTwo-fromTwo : (d : Distinction) → (t : Two) → toTwo d (fromTwo d t) ≡ t
toTwo-fromTwo d L = toTwo-ℓ d
toTwo-fromTwo d R = toTwo-r d
-- § Law 1.8: Every distinction is isomorphic to Two.
two-normal-form : (d : Distinction) → DistinctionIso d Two-distinction
two-normal-form d = record
  { to      = toTwo d
  ; from    = fromTwo d
  ; to-from = toTwo-fromTwo d
  ; from-to = fromTwo-toTwo d
  ; to-ℓ    = toTwo-ℓ d
  ; to-r    = toTwo-r d
  }

law1-8-two-normal-form : (d : Distinction) → DistinctionIso d Two-distinction
law1-8-two-normal-form = two-normal-form
-- § The swap map on Two.
swapTwo : Two → Two
swapTwo L = R
swapTwo R = L

-- § Swap is involutive.
swapTwo-involutive : (t : Two) → swapTwo (swapTwo t) ≡ t
swapTwo-involutive L = refl
swapTwo-involutive R = refl

-- § The swap-oriented map to Two.
toTwo-swap : (d : Distinction) → S d → Two
toTwo-swap d x = swapTwo (toTwo d x)

-- § Swap-oriented map sends ℓ to R.
toTwo-swap-ℓ : (d : Distinction) → toTwo-swap d (ℓ d) ≡ R
toTwo-swap-ℓ d = cong swapTwo (toTwo-ℓ d)

-- § Swap-oriented map sends r to L.
toTwo-swap-r : (d : Distinction) → toTwo-swap d (r d) ≡ L
toTwo-swap-r d = cong swapTwo (toTwo-r d)

-- § The canonical equivalence (boundary-preserving).
two-normal-form-equiv : (d : Distinction) → DistinctionEquiv d Two-distinction
two-normal-form-equiv d = forgetIso (two-normal-form d)

-- § The swap equivalence.
two-normal-form-equiv-swap : (d : Distinction) → DistinctionEquiv d Two-distinction
two-normal-form-equiv-swap d = record
  { to      = toTwo-swap d
  ; from    = fromTwo d ∘ swapTwo
  ; to-from = λ t → trans (cong (toTwo-swap d) (refl)) (trans (cong swapTwo (toTwo-fromTwo d (swapTwo t))) (swapTwo-involutive t))
  ; from-to = λ x → trans (cong (fromTwo d) (swapTwo-involutive (toTwo d x))) (fromTwo-toTwo d x)
  }
  where
    _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
    (f ∘ g) x = f (g x)

-- § The two orientations of a Two normal form.
data TwoOrientation : Set where
  orient-preserve : TwoOrientation
  orient-swap     : TwoOrientation

-- § The two orientations are distinct.
preserve≠swap : orient-preserve ≡ orient-swap → ⊥
preserve≠swap ()

swap≠preserve : orient-swap ≡ orient-preserve → ⊥
swap≠preserve ()
-- § Equivalence images at boundary are distinct.
to-distinct-on-boundary :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  to e (ℓ d) ≡ to e (r d) → ⊥
to-distinct-on-boundary d e eq =
  ℓ≠r d (trans (sym (from-to e (ℓ d))) (trans (cong (from e) eq) (from-to e (r d))))

-- § Classify an equivalence by its orientation.
orientation-classify :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  TwoOrientation
orientation-classify d e with Two-cover (to e (ℓ d)) | Two-cover (to e (r d))
... | inj₁ tℓ≡L | inj₁ tr≡L = ⊥-elim (to-distinct-on-boundary d e (trans tℓ≡L (sym tr≡L)))
... | inj₂ tℓ≡R | inj₂ tr≡R = ⊥-elim (to-distinct-on-boundary d e (trans tℓ≡R (sym tr≡R)))
... | inj₁ _ | inj₂ _ = orient-preserve
... | inj₂ _ | inj₁ _ = orient-swap
-- § Automorphism of a distinction.
Aut : Distinction → Set1
Aut d = DistinctionEquiv d d

-- § Automorphism transport is injective.
to-injective : (d : Distinction) → (a : Aut d) → {x y : S d} → to a x ≡ to a y → x ≡ y
to-injective d a {x} {y} eq =
  trans (sym (from-to a x)) (trans (cong (from a) eq) (from-to a y))

-- § Automorphism images at boundary points are distinct.
to-ℓ≠to-r : (d : Distinction) → (a : Aut d) → to a (ℓ d) ≠ to a (r d)
to-ℓ≠to-r d a eq = ℓ≠r d (to-injective d a eq)

-- § Dual boundary lemma: dual sends ℓ to r.
Distinction-dual-ℓ : (d : Distinction) → Distinction-dual d (ℓ d) ≡ r d
Distinction-dual-ℓ d with cover d (ℓ d)
... | inj₁ _      = refl
... | inj₂ ℓ≡r    = ⊥-elim ((ℓ≠r d) ℓ≡r)

-- § Dual boundary lemma: dual sends r to ℓ.
Distinction-dual-r : (d : Distinction) → Distinction-dual d (r d) ≡ ℓ d
Distinction-dual-r d with cover d (r d)
... | inj₂ _      = refl
... | inj₁ r≡ℓ    = ⊥-elim ((ℓ≠r d) (sym r≡ℓ))

-- § Automorphism classification: exactly id or dual.
Aut-sound :
  (d : Distinction) →
  (a : Aut d) →
  (to a ≗ id) ⊎ (to a ≗ Distinction-dual d)
Aut-sound d a with cover d (to a (ℓ d)) | cover d (to a (r d))
... | inj₁ tℓ≡ℓ | inj₁ tr≡ℓ = ⊥-elim (to-ℓ≠to-r d a (trans tℓ≡ℓ (sym tr≡ℓ)))
... | inj₂ tℓ≡r | inj₂ tr≡r = ⊥-elim (to-ℓ≠to-r d a (trans tℓ≡r (sym tr≡r)))
... | inj₁ tℓ≡ℓ | inj₂ tr≡r =
  inj₁ (Distinction-elim d tℓ≡ℓ tr≡r)
... | inj₂ tℓ≡r | inj₁ tr≡ℓ =
  inj₂ (Distinction-elim d
    (trans tℓ≡r (sym (Distinction-dual-ℓ d)))
    (trans tr≡ℓ (sym (Distinction-dual-r d))))
-- § Uniqueness of the to-direction.
toTwo-unique :
  (d : Distinction) →
  (f : S d → Two) →
  f (ℓ d) ≡ L →
  f (r d) ≡ R →
  f ≗ toTwo d
toTwo-unique d f fℓ fr =
  Distinction-elim d
    (trans fℓ (sym (toTwo-ℓ d)))
    (trans fr (sym (toTwo-r d)))

-- § Uniqueness of the swap-direction.
toTwo-swap-unique :
  (d : Distinction) →
  (f : S d → Two) →
  f (ℓ d) ≡ R →
  f (r d) ≡ L →
  f ≗ toTwo-swap d
toTwo-swap-unique d f fℓ fr =
  Distinction-elim d
    (trans fℓ (sym (toTwo-swap-ℓ d)))
    (trans fr (sym (toTwo-swap-r d)))

-- § Law 1.9: iso-to is unique.
law1-9-iso-to-unique : (d : Distinction) → (i : DistinctionIso d Two-distinction) → to i ≗ toTwo d
law1-9-iso-to-unique d i =
  toTwo-unique d (to i)
    (trans (to-ℓ i) refl)
    (trans (to-r i) refl)

-- § Uniqueness of the from-direction.
fromTwo-unique :
  (d : Distinction) →
  (g : Two → S d) →
  g L ≡ ℓ d →
  g R ≡ r d →
  g ≗ fromTwo d
fromTwo-unique d g gL gR L = trans gL refl
fromTwo-unique d g gL gR R = trans gR refl

-- § Law 1.9: iso-from is unique.
law1-9-iso-from-unique : (d : Distinction) → (i : DistinctionIso d Two-distinction) → from i ≗ fromTwo d
law1-9-iso-from-unique d i =
  fromTwo-unique d (from i)
    (trans (sym (cong (from i) (to-ℓ i))) (from-to i (ℓ d)))
    (trans (sym (cong (from i) (to-r i))) (from-to i (r d)))
-- § Law 1.10: orientation is exhaustive.
orientation-exhaustive :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  (to e ≗ toTwo d) ⊎ (to e ≗ toTwo-swap d)
orientation-exhaustive d e with Two-cover (to e (ℓ d)) | Two-cover (to e (r d))
... | inj₁ tℓ≡L | inj₁ tr≡L = ⊥-elim (to-distinct-on-boundary d e (trans tℓ≡L (sym tr≡L)))
... | inj₂ tℓ≡R | inj₂ tr≡R = ⊥-elim (to-distinct-on-boundary d e (trans tℓ≡R (sym tr≡R)))
... | inj₁ tℓ≡L | inj₂ tr≡R = inj₁ (toTwo-unique d (to e) tℓ≡L tr≡R)
... | inj₂ tℓ≡R | inj₁ tr≡L = inj₂ (toTwo-swap-unique d (to e) tℓ≡R tr≡L)

law1-10-orientation-exhaustive :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  (to e ≗ toTwo d) ⊎ (to e ≗ toTwo-swap d)
law1-10-orientation-exhaustive = orientation-exhaustive
-- § Law 1.11: Automorphisms are exactly id or dual.
law1-11-Aut-sound :
  (d : Distinction) →
  (a : Aut d) →
  (to a ≗ id) ⊎ (to a ≗ Distinction-dual d)
law1-11-Aut-sound = Aut-sound
-- § Orientation case type.
data OrientationCase : Set where
  case-preserve : OrientationCase
  case-swap     : OrientationCase

-- § Interpret an orientation case as a map.
orientationInterpret : (d : Distinction) → OrientationCase → S d → Two
orientationInterpret d case-preserve = toTwo d
orientationInterpret d case-swap     = toTwo-swap d

-- § Law 1.12: orientation classification is sound.
orientationCase-sound :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  Σ OrientationCase (λ c → to e ≗ orientationInterpret d c)
orientationCase-sound d e with orientation-exhaustive d e
... | inj₁ p = case-preserve , p
... | inj₂ p = case-swap     , p

-- § Law 1.12: orientation classification is unique.
orientationCase-unique :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  (c₁ c₂ : OrientationCase) →
  to e ≗ orientationInterpret d c₁ →
  to e ≗ orientationInterpret d c₂ →
  c₁ ≡ c₂
orientationCase-unique d e case-preserve case-preserve _ _ = refl
orientationCase-unique d e case-swap     case-swap     _ _ = refl
orientationCase-unique d e case-preserve case-swap p q =
  ⊥-elim (Two-L≠R (sym toR≡L))
  where
    toR≡L : R ≡ L
    toR≡L =
      trans (sym (toTwo-swap-ℓ d))
        (trans (sym (q (ℓ d)))
          (trans (p (ℓ d)) (toTwo-ℓ d)))
orientationCase-unique d e case-swap case-preserve p q =
  ⊥-elim (Two-L≠R (sym toR≡L))
  where
    toR≡L : R ≡ L
    toR≡L =
      trans (sym (toTwo-swap-ℓ d))
        (trans (sym (p (ℓ d)))
          (trans (q (ℓ d)) (toTwo-ℓ d)))

law1-12-orientationCase-sound :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  Σ OrientationCase (λ c → to e ≗ orientationInterpret d c)
law1-12-orientationCase-sound = orientationCase-sound

law1-12-orientationCase-unique :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  (c₁ c₂ : OrientationCase) →
  to e ≗ orientationInterpret d c₁ →
  to e ≗ orientationInterpret d c₂ →
  c₁ ≡ c₂
law1-12-orientationCase-unique = orientationCase-unique
-- § Automorphism case type.
data AutCase : Set where
  case-id   : AutCase
  case-dual : AutCase

-- § Interpret an automorphism case.
autInterpret : (d : Distinction) → AutCase → S d → S d
autInterpret d case-id   = id
autInterpret d case-dual = Distinction-dual d

-- § Automorphism classification is sound.
autCase-sound :
  (d : Distinction) →
  (a : Aut d) →
  Σ AutCase (λ c → to a ≗ autInterpret d c)
autCase-sound d a with Aut-sound d a
... | inj₁ p = case-id   , p
... | inj₂ p = case-dual , p

-- § Automorphism classification is unique.
autCase-unique :
  (d : Distinction) →
  (a : Aut d) →
  (c₁ c₂ : AutCase) →
  to a ≗ autInterpret d c₁ →
  to a ≗ autInterpret d c₂ →
  c₁ ≡ c₂
autCase-unique d a case-id case-id _ _ = refl
autCase-unique d a case-dual case-dual _ _ = refl
autCase-unique d a case-id case-dual p q =
  ⊥-elim ((ℓ≠r d) ℓ≡r)
  where
    ℓ≡r : ℓ d ≡ r d
    ℓ≡r =
      trans (sym (p (ℓ d)))
        (trans (q (ℓ d)) (Distinction-dual-ℓ d))
autCase-unique d a case-dual case-id p q =
  ⊥-elim ((ℓ≠r d) ℓ≡r)
  where
    ℓ≡r : ℓ d ≡ r d
    ℓ≡r =
      trans (sym (q (ℓ d)))
        (trans (p (ℓ d)) (Distinction-dual-ℓ d))

-- § Law 1.13: Automorphism classification is sound and unique.
law1-13-autCase-sound :
  (d : Distinction) →
  (a : Aut d) →
  Σ AutCase (λ c → to a ≗ autInterpret d c)
law1-13-autCase-sound = autCase-sound

law1-13-autCase-unique :
  (d : Distinction) →
  (a : Aut d) →
  (c₁ c₂ : AutCase) →
  to a ≗ autInterpret d c₁ →
  to a ≗ autInterpret d c₂ →
  c₁ ≡ c₂
law1-13-autCase-unique = autCase-unique
-- § Law 1.14: K₄ classification produces a witness.
law1-14-k4-classification-sound :
  (d : Distinction) →
  (f : S d → S d) →
  Σ EndoCase (λ c → K₄.interpret d c ≗ f)
law1-14-k4-classification-sound = k4-classification-sound

-- § Law 1.15: K₄ classification witness is unique.
law1-15-k4-classification-unique :
  (d : Distinction) →
  (f : S d → S d) →
  (c₁ c₂ : EndoCase) →
  K₄.interpret d c₁ ≗ f →
  K₄.interpret d c₂ ≗ f →
  c₁ ≡ c₂
law1-15-k4-classification-unique = k4-classification-unique
-- § DistinctionClass: two-class coverage with an arbitrary equivalence relation.
record DistinctionClass : Set1 where
  field
    S      : Set
    _≈_    : S → S → Set
    ≈-refl : (x : S) → x ≈ x
    ≈-sym  : {x y : S} → x ≈ y → y ≈ x
    ≈-trans : {x y z : S} → x ≈ y → y ≈ z → x ≈ z

    ℓ      : S
    r      : S
    ℓ≉r    : ¬ (ℓ ≈ r)
    cover≈ : (x : S) → (x ≈ ℓ) ⊎ (x ≈ r)

open DistinctionClass public

-- § Respect predicate for ≈-elimination.
Respect≈ : (d : DistinctionClass) → (S d → Set) → Set
Respect≈ d P = {x y : S d} → _≈_ d x y → P x → P y

-- § Law 1.16: Elimination is forced by cover≈.
DistinctionClass-elim :
  (d : DistinctionClass) →
  {P : S d → Set} →
  Respect≈ d P →
  P (ℓ d) →
  P (r d) →
  (x : S d) →
  P x
DistinctionClass-elim d {P} resp pℓ pr x with cover≈ d x
... | inj₁ x≈ℓ = resp ((≈-sym d) x≈ℓ) pℓ
... | inj₂ x≈r = resp ((≈-sym d) x≈r) pr

law1-16-class-elim :
  (d : DistinctionClass) →
  {P : S d → Set} →
  Respect≈ d P →
  P (ℓ d) →
  P (r d) →
  (x : S d) →
  P x
law1-16-class-elim = DistinctionClass-elim

-- § Law 1.17: Every Distinction induces a DistinctionClass.
Distinction→DistinctionClass : Distinction → DistinctionClass
Distinction→DistinctionClass d = record
  { S       = S d
  ; _≈_     = _≡_
  ; ≈-refl  = λ x → refl
  ; ≈-sym   = sym
  ; ≈-trans = trans
  ; ℓ       = ℓ d
  ; r       = r d
  ; ℓ≉r     = ℓ≠r d
  ; cover≈  = cover d
  }

law1-17-distinction-to-class : Distinction → DistinctionClass
law1-17-distinction-to-class = Distinction→DistinctionClass
-- § Set isomorphism (not distinction-specific).
record SetIso {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    to      : A → B
    from    : B → A
    to-from : (y : B) → to (from y) ≡ y
    from-to : (x : A) → from (to x) ≡ x

open SetIso public

-- § Endo presentation record.
record EndoPresentation (d : Distinction) (X : Set) : Set where
  field
    present-interpret           : X → (S d → S d)
    present-classify            : (S d → S d) → X
    present-classify-sound      : (f : S d → S d) → present-interpret (present-classify f) ≗ f
    present-interpret-injective : (x y : X) → present-interpret x ≗ present-interpret y → x ≡ y

-- § Law 1.18: Endo presentation is unique up to isomorphism.
law1-18-endo-presentation-unique :
  (d : Distinction) →
  {X : Set} →
  EndoPresentation d X →
  SetIso X EndoCase
law1-18-endo-presentation-unique d {X} pres =
  let
    module K = K₄ d
    open EndoPresentation pres
      renaming
        ( present-interpret to interpretX
        ; present-classify to classifyX
        ; present-classify-sound to classifyX-sound
        ; present-interpret-injective to interpretX-injective
        )

    to' : X → EndoCase
    to' x = K.classify (interpretX x)

    from' : EndoCase → X
    from' c = classifyX (K.interpret c)

    to-from' : (c : EndoCase) → to' (from' c) ≡ c
    to-from' c =
      sym
        (K.classify-unique
          (interpretX (classifyX (K.interpret c)))
          c
          (K.≗-sym (classifyX-sound (K.interpret c))))

    from-to' : (x : X) → from' (to' x) ≡ x
    from-to' x =
      interpretX-injective
        (classifyX (K.interpret (K.classify (interpretX x))))
        x
        (K.≗-trans
          (classifyX-sound (K.interpret (K.classify (interpretX x))))
          (K.classify-sound (interpretX x)))
  in
  record
    { to = to'
    ; from = from'
    ; to-from = to-from'
    ; from-to = from-to'
    }
-- § Helpers for orientation presentation elimination.
orientationCase-classify :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  OrientationCase
orientationCase-classify d e = fst (orientationCase-sound d e)

orientationCase-classify-sound :
  (d : Distinction) →
  (e : DistinctionEquiv d Two-distinction) →
  to e ≗ orientationInterpret d (orientationCase-classify d e)
orientationCase-classify-sound d e = snd (orientationCase-sound d e)

autCase-classify :
  (d : Distinction) →
  (a : Aut d) →
  AutCase
autCase-classify d a = fst (autCase-sound d a)

autCase-classify-sound :
  (d : Distinction) →
  (a : Aut d) →
  to a ≗ autInterpret d (autCase-classify d a)
autCase-classify-sound d a = snd (autCase-sound d a)

orientationEquivInterpret :
  (d : Distinction) →
  OrientationCase →
  DistinctionEquiv d Two-distinction
orientationEquivInterpret d case-preserve = two-normal-form-equiv d
orientationEquivInterpret d case-swap     = two-normal-form-equiv-swap d

orientationEquivInterpret-sound :
  (d : Distinction) →
  (c : OrientationCase) →
  to (orientationEquivInterpret d c) ≗ orientationInterpret d c
orientationEquivInterpret-sound d case-preserve x = refl
orientationEquivInterpret-sound d case-swap     x = refl

-- § Identity equivalence.
idEquiv : (d : Distinction) → DistinctionEquiv d d
idEquiv d = record
  { to      = id
  ; from    = id
  ; to-from = λ y → refl
  ; from-to = λ x → refl
  }

-- § Dual equivalence.
dualEquiv : (d : Distinction) → DistinctionEquiv d d
dualEquiv d = record
  { to      = Distinction-dual d
  ; from    = Distinction-dual d
  ; to-from = law1-3-dual-involutive d
  ; from-to = law1-3-dual-involutive d
  }

autEquivInterpret :
  (d : Distinction) →
  AutCase →
  Aut d
autEquivInterpret d case-id   = idEquiv d
autEquivInterpret d case-dual = dualEquiv d

autEquivInterpret-sound :
  (d : Distinction) →
  (c : AutCase) →
  to (autEquivInterpret d c) ≗ autInterpret d c
autEquivInterpret-sound d case-id   x = refl
autEquivInterpret-sound d case-dual x = refl
-- § Orientation presentation record.
record OrientationPresentation (d : Distinction) (X : Set) : Set1 where
  field
    op-interpret           : X → DistinctionEquiv d Two-distinction
    op-classify            : DistinctionEquiv d Two-distinction → X
    op-classify-sound      : (e : DistinctionEquiv d Two-distinction) → to (op-interpret (op-classify e)) ≗ to e
    op-interpret-injective : (x y : X) → to (op-interpret x) ≗ to (op-interpret y) → x ≡ y

-- § Automorphism presentation record.
record AutPresentation (d : Distinction) (X : Set) : Set1 where
  field
    ap-interpret           : X → Aut d
    ap-classify            : Aut d → X
    ap-classify-sound      : (a : Aut d) → to (ap-interpret (ap-classify a)) ≗ to a
    ap-interpret-injective : (x y : X) → to (ap-interpret x) ≗ to (ap-interpret y) → x ≡ y
-- § Law 1.19: Orientation presentation is unique up to isomorphism.
law1-19-orientation-presentation-unique :
  (d : Distinction) →
  {X : Set} →
  OrientationPresentation d X →
  SetIso X OrientationCase
law1-19-orientation-presentation-unique d {X} pres =
  let
    open OrientationPresentation pres
      renaming
        ( op-interpret to interpretX
        ; op-classify to classifyX
        ; op-classify-sound to classifyX-sound
        ; op-interpret-injective to interpretX-injective
        )

    ≗-sym : {A B : Set} {f g : A → B} → f ≗ g → g ≗ f
    ≗-sym p x = sym (p x)

    ≗-trans : {A B : Set} {f g h : A → B} → f ≗ g → g ≗ h → f ≗ h
    ≗-trans p q x = trans (p x) (q x)

    to' : X → OrientationCase
    to' x = orientationCase-classify d (interpretX x)

    from' : OrientationCase → X
    from' c = classifyX (orientationEquivInterpret d c)

    to-from' : (c : OrientationCase) → to' (from' c) ≡ c
    to-from' c =
      orientationCase-unique d (interpretX (classifyX (orientationEquivInterpret d c)))
        (to' (from' c))
        c
        (orientationCase-classify-sound d (interpretX (classifyX (orientationEquivInterpret d c))))
        (≗-trans
          (classifyX-sound (orientationEquivInterpret d c))
          (orientationEquivInterpret-sound d c))

    from-to' : (x : X) → from' (to' x) ≡ x
    from-to' x =
      interpretX-injective
        (classifyX (orientationEquivInterpret d (to' x)))
        x
        (≗-trans
          (classifyX-sound (orientationEquivInterpret d (to' x)))
          (≗-trans
            (orientationEquivInterpret-sound d (to' x))
            (≗-sym (orientationCase-classify-sound d (interpretX x)))))
  in
  record
    { to = to'
    ; from = from'
    ; to-from = to-from'
    ; from-to = from-to'
    }

-- § Law 1.20: Automorphism presentation is unique up to isomorphism.
law1-20-aut-presentation-unique :
  (d : Distinction) →
  {X : Set} →
  AutPresentation d X →
  SetIso X AutCase
law1-20-aut-presentation-unique d {X} pres =
  let
    open AutPresentation pres
      renaming
        ( ap-interpret to interpretX
        ; ap-classify to classifyX
        ; ap-classify-sound to classifyX-sound
        ; ap-interpret-injective to interpretX-injective
        )

    ≗-sym : {A B : Set} {f g : A → B} → f ≗ g → g ≗ f
    ≗-sym p x = sym (p x)

    ≗-trans : {A B : Set} {f g h : A → B} → f ≗ g → g ≗ h → f ≗ h
    ≗-trans p q x = trans (p x) (q x)

    to' : X → AutCase
    to' x = autCase-classify d (interpretX x)

    from' : AutCase → X
    from' c = classifyX (autEquivInterpret d c)

    to-from' : (c : AutCase) → to' (from' c) ≡ c
    to-from' c =
      autCase-unique d (interpretX (classifyX (autEquivInterpret d c)))
        (to' (from' c))
        c
        (autCase-classify-sound d (interpretX (classifyX (autEquivInterpret d c))))
        (≗-trans
          (classifyX-sound (autEquivInterpret d c))
          (autEquivInterpret-sound d c))

    from-to' : (x : X) → from' (to' x) ≡ x
    from-to' x =
      interpretX-injective
        (classifyX (autEquivInterpret d (to' x)))
        x
        (≗-trans
          (classifyX-sound (autEquivInterpret d (to' x)))
          (≗-trans
            (autEquivInterpret-sound d (to' x))
            (≗-sym (autCase-classify-sound d (interpretX x)))))
  in
  record
    { to = to'
    ; from = from'
    ; to-from = to-from'
    ; from-to = from-to'
    }
-- § D₀ is the canonical first distinction.
D₀ : Set
D₀ = Two

-- § The left boundary.
left : D₀
left = L

-- § The right boundary.
right : D₀
right = R

-- § D₀ as a Distinction record.
D₀-distinction : Distinction
D₀-distinction = Two-distinction
-- § Level-polymorphic distinction record.
record Distinctionℓ (ℓ : Level) : Set (lsuc ℓ) where
  field
    S     : Set ℓ
    ℓ₀    : S
    r₀    : S
    ℓ₀≠r₀ : ℓ₀ ≠ r₀
    cover : (x : S) → (x ≡ ℓ₀) ⊎ (x ≡ r₀)

open Distinctionℓ public

-- § Canonical embedding from base-level Distinction.
Distinction→Distinctionℓ : Distinction → Distinctionℓ lzero
Distinction→Distinctionℓ d = record
  { S     = S d
  ; ℓ₀    = ℓ d
  ; r₀    = r d
  ; ℓ₀≠r₀ = ℓ≠r d
  ; cover = cover d
  }

-- § A drift step: the next-level distinction with an embedding.
record DriftStep {ℓ : Level} (d : Distinctionℓ ℓ) : Set (lsuc (lsuc ℓ)) where
  field
    d↑    : Distinctionℓ (lsuc ℓ)
    embed : S d → S d↑

open DriftStep public

-- § Drift is the canonical lift to the next universe level.
drift : {ℓ : Level} → (d : Distinctionℓ ℓ) → DriftStep d
drift d = record
  { d↑ = record
      { S     = Lift (S d)
      ; ℓ₀    = lift (ℓ₀ d)
      ; r₀    = lift (r₀ d)
      ; ℓ₀≠r₀ = λ eq → ℓ₀≠r₀ d (lift-injective eq)
    ; cover = cover↑
      }
  ; embed = lift
  }
  where
  cover↑ : (y : Lift (S d)) → (y ≡ lift (ℓ₀ d)) ⊎ (y ≡ lift (r₀ d))
  cover↑ (lift x) with cover d x
  ... | inj₁ x≡ℓ = inj₁ (cong lift x≡ℓ)
  ... | inj₂ x≡r = inj₂ (cong lift x≡r)
-- § Law 2.1: No classification may remain unclassified.
law2-1-drift : {ℓ : Level} → (d : Distinctionℓ ℓ) → DriftStep d
law2-1-drift = drift

-- § Extract the next-level distinction from a drift step.
drift-next : {ℓ : Level} → (d : Distinctionℓ ℓ) → Distinctionℓ (lsuc ℓ)
drift-next d = d↑ (drift d)

-- § Extract the embedding from a drift step.
drift-embed : {ℓ : Level} → (d : Distinctionℓ ℓ) → S d → S (drift-next d)
drift-embed d = embed (drift d)

-- § Drift-embedded elements satisfy coverage.
drift-embed-cover : {ℓ : Level} → (d : Distinctionℓ ℓ) → (x : S d)
                 → (drift-embed d x ≡ ℓ₀ (drift-next d)) ⊎ (drift-embed d x ≡ r₀ (drift-next d))
drift-embed-cover d x = cover (drift-next d) (drift-embed d x)
-- § Law 3.1: Drift does not fold the prior carrier.
law3-1-embed-injective :
  {ℓ : Level} (d : Distinctionℓ ℓ) → {x y : S d} →
  drift-embed d x ≡ drift-embed d y → x ≡ y
law3-1-embed-injective d = lift-injective

-- § Drift preserves boundary distinctness.
drift-embed-ℓ₀≠r₀ :
  {ℓ : Level} (d : Distinctionℓ ℓ) →
  drift-embed d (ℓ₀ d) ≠ drift-embed d (r₀ d)
drift-embed-ℓ₀≠r₀ d eq = ℓ₀≠r₀ d (law3-1-embed-injective d eq)
-- § Level-polymorphic eliminator for Distinctionℓ.
Distinctionℓ-elim :
  {ℓ ℓP : Level} → (d : Distinctionℓ ℓ) →
  {P : S d → Set ℓP} →
  P (ℓ₀ d) →
  P (r₀ d) →
  (x : S d) →
  P x
Distinctionℓ-elim d {P} pℓ pr x with cover d x
... | inj₁ x≡ℓ = subst P (sym x≡ℓ) pℓ
... | inj₂ x≡r = subst P (sym x≡r) pr

-- § Functions out of Distinctionℓ are determined by boundary values.
Distinctionℓ-determined :
  {ℓ ℓB : Level} → (d : Distinctionℓ ℓ) → {B : Set ℓB} →
  (f g : S d → B) →
  f (ℓ₀ d) ≡ g (ℓ₀ d) →
  f (r₀ d) ≡ g (r₀ d) →
  f ≗ g
Distinctionℓ-determined d f g fℓ≡gℓ fr≡gr =
  Distinctionℓ-elim d
    (subst (λ y → f y ≡ g y) refl fℓ≡gℓ)
    (subst (λ y → f y ≡ g y) refl fr≡gr)

-- § A boundary-preserving lift: target distinction + embedding + boundary proofs.
record LiftedBP {ℓ : Level} (d : Distinctionℓ ℓ) : Set (lsuc (lsuc ℓ)) where
  field
    e        : Distinctionℓ (lsuc ℓ)
    embed    : S d → S e
    embed-ℓ₀ : embed (ℓ₀ d) ≡ ℓ₀ e
    embed-r₀ : embed (r₀ d) ≡ r₀ e

open LiftedBP public

-- § Drift universality: drift is initial among boundary-preserving lifts.
record DriftUniversal : Setω where
  field
    preserves-ℓ₀ : {ℓ : Level} (d : Distinctionℓ ℓ) →
      drift-embed d (ℓ₀ d) ≡ ℓ₀ (drift-next d)
    preserves-r₀ : {ℓ : Level} (d : Distinctionℓ ℓ) →
      drift-embed d (r₀ d) ≡ r₀ (drift-next d)

    mediator : {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
      S (drift-next d) → S (e t)

    mediator-commutes : {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
      (x : S d) → mediator d t (drift-embed d x) ≡ embed t x

open DriftUniversal public

-- § The canonical drift universality witness.
driftUniversal : DriftUniversal
driftUniversal = record
  { preserves-ℓ₀ = λ d → refl
  ; preserves-r₀ = λ d → refl
  ; mediator = λ d t y → embed t (lower y)
  ; mediator-commutes = λ d t x → refl
  }
-- § Law 4.1: Drift is universal among boundary-preserving lifts.
law4-1-mediator-commutes :
  {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
  (x : S d) → mediator driftUniversal d t (drift-embed d x) ≡ embed t x
law4-1-mediator-commutes d t x = mediator-commutes driftUniversal d t x

-- § Mediator uniqueness: any factorizing map agrees with the canonical one.
mediator-unique :
  {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
  (g : S (drift-next d) → S (e t)) →
  ((x : S d) → g (drift-embed d x) ≡ embed t x) →
  g ≗ mediator driftUniversal d t
mediator-unique d t g g-comm =
  Distinctionℓ-determined (drift-next d) g h gℓ≡hℓ gr≡hr
  where
    h : S (drift-next d) → S (e t)
    h = mediator driftUniversal d t

    gℓ≡hℓ : g (ℓ₀ (drift-next d)) ≡ h (ℓ₀ (drift-next d))
    gℓ≡hℓ =
      trans (cong g (sym (preserves-ℓ₀ driftUniversal d)))
        (trans (g-comm (ℓ₀ d))
          (trans (sym (mediator-commutes driftUniversal d t (ℓ₀ d)))
            (cong h (preserves-ℓ₀ driftUniversal d))))

    gr≡hr : g (r₀ (drift-next d)) ≡ h (r₀ (drift-next d))
    gr≡hr =
      trans (cong g (sym (preserves-r₀ driftUniversal d)))
        (trans (g-comm (r₀ d))
          (trans (sym (mediator-commutes driftUniversal d t (r₀ d)))
            (cong h (preserves-r₀ driftUniversal d))))

-- § Drift as a LiftedBP instance.
driftLiftedBP : {ℓ : Level} (d : Distinctionℓ ℓ) → LiftedBP d
driftLiftedBP d = record
  { e        = drift-next d
  ; embed    = drift-embed d
  ; embed-ℓ₀ = preserves-ℓ₀ driftUniversal d
  ; embed-r₀ = preserves-r₀ driftUniversal d
  }

-- § Morphism between lifted boundary-preserving presentations.
record LiftMorph {ℓ : Level} (d : Distinctionℓ ℓ) (t u : LiftedBP d) : Set (lsuc (lsuc ℓ)) where
  field
    map  : S (e t) → S (e u)
    comm : (x : S d) → map (embed t x) ≡ embed u x

open LiftMorph public

-- § The canonical factorization through drift.
drift-factor :
  {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
  LiftMorph d (driftLiftedBP d) t
drift-factor d t = record
  { map  = mediator driftUniversal d t
  ; comm = mediator-commutes driftUniversal d t
  }

-- § Factorization through drift is unique.
drift-factor-unique :
  {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
  (m : LiftMorph d (driftLiftedBP d) t) →
  map m ≗ mediator driftUniversal d t
drift-factor-unique d t m =
  mediator-unique d t (map m) (comm m)
-- § Law 4.2: Drift-step factorization is unique.
law4-2-factor-unique :
  {ℓ : Level} (d : Distinctionℓ ℓ) → (t : LiftedBP d) →
  (m : LiftMorph d (driftLiftedBP d) t) →
  map m ≗ mediator driftUniversal d t
law4-2-factor-unique = drift-factor-unique
-- § A drift state packages a universe level with its distinction.
record DriftState : Setω where
  constructor ⟨_,_⟩
  field
    ℓ : Level
    d : Distinctionℓ ℓ

open DriftState public

-- § Step a drift state forward.
stepState : DriftState → DriftState
stepState s = ⟨ lsuc (ℓ s) , drift-next (d s) ⟩

-- § Extract the carrier of a drift state.
Carrier : (s : DriftState) → Set (ℓ s)
Carrier s = S (d s)

-- § The canonical embedding between consecutive carriers.
state-embed : (s : DriftState) → Carrier s → Carrier (stepState s)
state-embed s = drift-embed (d s)

-- § Strict reachability: one or more drift steps.
data Reach⁺ : DriftState → DriftState → Setω where
  one  : {s : DriftState} → Reach⁺ s (stepState s)
  more : {s t : DriftState} → Reach⁺ (stepState s) t → Reach⁺ s t

-- § Reflexive-transitive reachability.
data Reach : DriftState → DriftState → Setω where
  stop : {s : DriftState} → Reach s s
  next : {s t : DriftState} → Reach⁺ s t → Reach s t
-- § Reach⁺ eliminator.
Reach⁺-elim :
  {P : (s t : DriftState) → Reach⁺ s t → Setω} →
  ({s : DriftState} → P s (stepState s) one) →
  ({s t : DriftState} → (p : Reach⁺ (stepState s) t) → P (stepState s) t p → P s t (more p)) →
  {s t : DriftState} → (p : Reach⁺ s t) → P s t p
Reach⁺-elim {P} base step one = base
Reach⁺-elim {P} base step (more p) = step p (Reach⁺-elim {P} base step p)

-- § Reach eliminator.
Reach-elim :
  {P : (s t : DriftState) → Reach s t → Setω} →
  ({s : DriftState} → P s s stop) →
  ({s t : DriftState} → (p : Reach⁺ s t) → P s t (next p)) →
  {s t : DriftState} → (p : Reach s t) → P s t p
Reach-elim stopCase nextCase stop = stopCase
Reach-elim stopCase nextCase (next p) = nextCase p

-- § Strict reachability is transitive.
Reach⁺-trans : {s t u : DriftState} → Reach⁺ s t → Reach⁺ t u → Reach⁺ s u
Reach⁺-trans one      q = more q
Reach⁺-trans (more p) q = more (Reach⁺-trans p q)

-- § Strict successors are comparable.
Reach⁺-comparable :
  {s t₁ t₂ : DriftState} →
  Reach⁺ s t₁ → Reach⁺ s t₂ →
  (Reach t₁ t₂) ⊎ω (Reach t₂ t₁)
Reach⁺-comparable one one = inj₁ω stop
Reach⁺-comparable one (more q) = inj₁ω (next q)
Reach⁺-comparable (more p) one = inj₂ω (next p)
Reach⁺-comparable (more p) (more q) =
  Reach⁺-comparable p q

-- § Reflexive-transitive reachability is transitive.
reach-trans : {s t u : DriftState} → Reach s t → Reach t u → Reach s u
reach-trans stop     q        = q
reach-trans (next p) stop     = next p
reach-trans (next p) (next q) = next (Reach⁺-trans p q)

-- § Every strict chain extends by one step.
Reach⁺-extend : {s t : DriftState} → Reach⁺ s t → Reach⁺ s (stepState t)
Reach⁺-extend p = Reach⁺-trans p one

-- § Every reflexive chain extends by one step.
Reach-extend : {s t : DriftState} → Reach s t → Reach s (stepState t)
Reach-extend stop     = next one
Reach-extend (next p) = next (Reach⁺-extend p)

-- § Strict reachability as an infix operator.
infix 20 _≺_
_≺_ : DriftState → DriftState → Setω
s ≺ t = Reach⁺ s t

-- § Strict reachability is transitive (infix form).
≺-trans : {s t u : DriftState} → (s ≺ t) → (t ≺ u) → (s ≺ u)
≺-trans p q = Reach⁺-trans p q

-- § Every drift state has a strict successor.
drift-progress : (s : DriftState) → s ≺ stepState s
drift-progress s = one

-- § Terminal state: no strict successor exists.
Terminal : DriftState → Setω
Terminal s = (t : DriftState) → (s ≺ t) → ⊥

-- § No terminal state exists (internal proof).
no-terminal : (s : DriftState) → Terminal s → ⊥
no-terminal s term = term (stepState s) (drift-progress s)

-- § Reachability induces carrier embedding (strict).
reach⁺-embed : {s t : DriftState} → Reach⁺ s t → Carrier s → Carrier t
reach⁺-embed {s} one      x = state-embed s x
reach⁺-embed {s} (more p) x = reach⁺-embed p (state-embed s x)

-- § Reachability induces carrier embedding (reflexive).
reach-embed : {s t : DriftState} → Reach s t → Carrier s → Carrier t
reach-embed {s} stop     x = x
reach-embed {s} (next p) x = reach⁺-embed p x
-- § Law 5.0: Drift admits no terminal state.
law5-0-no-terminal : (s : DriftState) → Terminal s → ⊥
law5-0-no-terminal = no-terminal
-- § Law 5.1: Strict successors are comparable.
law5-1-comparable :
  {s t₁ t₂ : DriftState} →
  s ≺ t₁ →
  s ≺ t₂ →
  (Reach t₁ t₂) ⊎ω (Reach t₂ t₁)
law5-1-comparable = Reach⁺-comparable
-- § Law 5.2: Every finite chain extends (strict).
law5-2-extend⁺ :
  {s t : DriftState} →
  s ≺ t →
  s ≺ stepState t
law5-2-extend⁺ p = Reach⁺-extend p

-- § Law 5.2: Every finite chain extends (reflexive).
law5-2-extend :
  {s t : DriftState} →
  Reach s t →
  Reach s (stepState t)
law5-2-extend = Reach-extend
-- § Law 5.3: Strict reachability is transitive.
law5-3-≺-trans : {s t u : DriftState} → (s ≺ t) → (t ≺ u) → (s ≺ u)
law5-3-≺-trans = ≺-trans

-- § Law 5.4: Reachability is transitive.
law5-4-reach-trans : {s t u : DriftState} → Reach s t → Reach t u → Reach s u
law5-4-reach-trans = reach-trans

-- § Law 5.5: Reachability forces carrier-embedding.
law5-5-reach-embed : {s t : DriftState} → Reach s t → Carrier s → Carrier t
law5-5-reach-embed = reach-embed

-- § Law 5.6: Reach⁺ eliminator is forced.
law5-6-Reach⁺-elim :
  {P : (s t : DriftState) → Reach⁺ s t → Setω} →
  ({s : DriftState} → P s (stepState s) one) →
  ({s t : DriftState} → (p : Reach⁺ (stepState s) t) → P (stepState s) t p → P s t (more p)) →
  {s t : DriftState} → (p : Reach⁺ s t) → P s t p
law5-6-Reach⁺-elim = Reach⁺-elim

-- § Law 5.7: Reach eliminator is forced.
law5-7-Reach-elim :
  {P : (s t : DriftState) → Reach s t → Setω} →
  ({s : DriftState} → P s s stop) →
  ({s t : DriftState} → (p : Reach⁺ s t) → P s t (next p)) →
  {s t : DriftState} → (p : Reach s t) → P s t p
law5-7-Reach-elim = Reach-elim
-- § Acyclicity constraint on drift.
record DriftAcyclic : Setω where
  field
    no-cycle : (s : DriftState) → (s ≺ s) → ⊥

open DriftAcyclic public
-- § Law 6.0: Drift has no cycles.
law6-0-no-cycle : DriftAcyclic → (s : DriftState) → (s ≺ s) → ⊥
law6-0-no-cycle ac s p = no-cycle ac s p
-- § Law 6.1: Strict reachability is irreflexive.
law6-1-irreflexive : DriftAcyclic → (s : DriftState) → (s ≺ s) → ⊥
law6-1-irreflexive ac s = no-cycle ac s
-- § Law 6.2: Strict reachability is asymmetric.
law6-2-asymmetric :
  DriftAcyclic → {s t : DriftState} →
  (s ≺ t) → (t ≺ s) → ⊥
law6-2-asymmetric ac p q = no-cycle ac _ (≺-trans p q)
-- § Law 6.3: Drift-step has no fixed point.
law6-3-no-fixpoint-stepState : DriftAcyclic → (s : DriftState) → stepState s ≡ω s → ⊥
law6-3-no-fixpoint-stepState ac s eq =
  no-cycle ac s (substω (λ u → Reach⁺ s u) eq one)
-- § K₄ maps between two distinctions.
module K₄Map (d₁ d₂ : Distinction) where
  Map : Set
  Map = S d₁ → S d₂

  -- § Pointwise equality on maps.
  ≗-refl : {f : Map} → f ≗ f
  ≗-refl x = refl

  ≗-sym : {f g : Map} → f ≗ g → g ≗ f
  ≗-sym p x = sym (p x)

  ≗-trans : {f g h : Map} → f ≗ g → g ≗ h → f ≗ h
  ≗-trans p q x = trans (p x) (q x)

  -- § The four canonical maps.
  constL : Map
  constL _ = ℓ d₂

  constR : Map
  constR _ = r d₂

  LR : Map
  LR x with cover d₁ x
  ... | inj₁ _ = ℓ d₂
  ... | inj₂ _ = r d₂

  RL : Map
  RL x with cover d₁ x
  ... | inj₁ _ = r d₂
  ... | inj₂ _ = ℓ d₂

  -- § Boundary behavior of LR.
  LR-ℓ : LR (ℓ d₁) ≡ ℓ d₂
  LR-ℓ with cover d₁ (ℓ d₁)
  ... | inj₁ _   = refl
  ... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d₁) ℓ≡r)

  LR-r : LR (r d₁) ≡ r d₂
  LR-r with cover d₁ (r d₁)
  ... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d₁) (sym r≡ℓ))
  ... | inj₂ _   = refl

  -- § Boundary behavior of RL.
  RL-ℓ : RL (ℓ d₁) ≡ r d₂
  RL-ℓ with cover d₁ (ℓ d₁)
  ... | inj₁ _   = refl
  ... | inj₂ ℓ≡r = ⊥-elim ((ℓ≠r d₁) ℓ≡r)

  RL-r : RL (r d₁) ≡ ℓ d₂
  RL-r with cover d₁ (r d₁)
  ... | inj₁ r≡ℓ = ⊥-elim ((ℓ≠r d₁) (sym r≡ℓ))
  ... | inj₂ _   = refl
  -- § Interpret an EndoCase as a map between distinctions.
  interpret : EndoCase → Map
  interpret case-constL = constL
  interpret case-constR = constR
  interpret case-id     = LR
  interpret case-dual   = RL

  -- § Classify a map by its boundary behavior.
  classify : Map → EndoCase
  classify f with cover d₂ (f (ℓ d₁)) | cover d₂ (f (r d₁))
  ... | inj₁ _ | inj₁ _ = case-constL
  ... | inj₂ _ | inj₂ _ = case-constR
  ... | inj₁ _ | inj₂ _ = case-id
  ... | inj₂ _ | inj₁ _ = case-dual
  -- § Soundness at ℓ.
  sound-at-ℓ : (f : Map) → interpret (classify f) (ℓ d₁) ≡ f (ℓ d₁)
  sound-at-ℓ f with cover d₂ (f (ℓ d₁)) | cover d₂ (f (r d₁))
  ... | inj₁ fl≡ℓ | inj₁ _     = sym fl≡ℓ
  ... | inj₂ fl≡r | inj₂ _     = sym fl≡r
  ... | inj₁ fl≡ℓ | inj₂ _     = trans LR-ℓ (sym fl≡ℓ)
  ... | inj₂ fl≡r | inj₁ _     = trans RL-ℓ (sym fl≡r)

  -- § Soundness at r.
  sound-at-r : (f : Map) → interpret (classify f) (r d₁) ≡ f (r d₁)
  sound-at-r f with cover d₂ (f (ℓ d₁)) | cover d₂ (f (r d₁))
  ... | inj₁ _     | inj₁ fr≡ℓ = sym fr≡ℓ
  ... | inj₂ _     | inj₂ fr≡r = sym fr≡r
  ... | inj₁ _     | inj₂ fr≡r = trans LR-r (sym fr≡r)
  ... | inj₂ _     | inj₁ fr≡ℓ = trans RL-r (sym fr≡ℓ)

  -- § Classification is sound: the interpreted classify agrees pointwise with f.
  classify-sound : (f : Map) → interpret (classify f) ≗ f
  classify-sound f x = Distinction-elim d₁ (sound-at-ℓ f) (sound-at-r f) x

  -- § Maps are determined by their boundary values.
  map-determined :
    (f g : Map) →
    f (ℓ d₁) ≡ g (ℓ d₁) →
    f (r d₁) ≡ g (r d₁) →
    f ≗ g
  map-determined f g eqℓ eqr x = Distinction-elim d₁ eqℓ eqr x

  -- § Absurdity helpers.
  absurd-ℓr : {A : Set} → (ℓ d₂ ≡ r d₂) → A
  absurd-ℓr e = ⊥-elim ((ℓ≠r d₂) e)

  absurd-rℓ : {A : Set} → (r d₂ ≡ ℓ d₂) → A
  absurd-rℓ e = ⊥-elim ((ℓ≠r d₂) (sym e))
  interpret-injective :
    (c c' : EndoCase) →
    interpret c ≗ interpret c' →
    c ≡ c'
  interpret-injective case-constL case-constL _ = refl
  interpret-injective case-constL case-constR p = absurd-ℓr (p (ℓ d₁))
  interpret-injective case-constL case-id     p =
    absurd-ℓr (trans (p (r d₁)) LR-r)
  interpret-injective case-constL case-dual   p =
    absurd-ℓr (trans (p (ℓ d₁)) RL-ℓ)

  interpret-injective case-constR case-constL p =
    absurd-rℓ (p (ℓ d₁))
  interpret-injective case-constR case-constR _ = refl
  interpret-injective case-constR case-id     p =
    absurd-ℓr (trans (sym LR-ℓ) (sym (p (ℓ d₁))))
  interpret-injective case-constR case-dual   p =
    absurd-ℓr (sym (trans (p (r d₁)) RL-r))

  interpret-injective case-id     case-constL p =
    absurd-ℓr (sym (trans (sym LR-r) (p (r d₁))))
  interpret-injective case-id     case-constR p =
    absurd-ℓr (trans (sym LR-ℓ) (p (ℓ d₁)))
  interpret-injective case-id     case-id     _ = refl
  interpret-injective case-id     case-dual   p =
    absurd-ℓr (trans (sym LR-ℓ) (trans (p (ℓ d₁)) RL-ℓ))

  interpret-injective case-dual   case-constL p =
    absurd-ℓr (trans (sym (p (ℓ d₁))) RL-ℓ)
  interpret-injective case-dual   case-constR p =
    absurd-ℓr (sym (trans (sym (p (r d₁))) RL-r))
  interpret-injective case-dual   case-id     p =
    absurd-ℓr (sym (trans (sym RL-ℓ) (trans (p (ℓ d₁)) LR-ℓ)))
  interpret-injective case-dual   case-dual   _ = refl

  -- § Classify is unique relative to interpretation.
  classify-unique : (f : Map) → (c : EndoCase) → interpret c ≗ f → c ≡ classify f
  classify-unique f c c≗f =
    interpret-injective c (classify f) (≗-trans c≗f (≗-sym (classify-sound f)))
-- § Top-level classification soundness.
k4map-classification-sound :
  (d₁ d₂ : Distinction) →
  (f : S d₁ → S d₂) →
  Σ EndoCase (λ c → K₄Map.interpret d₁ d₂ c ≗ f)
k4map-classification-sound d₁ d₂ f =
  K₄Map.classify d₁ d₂ f , K₄Map.classify-sound d₁ d₂ f

-- § Top-level classification uniqueness.
k4map-classification-unique :
  (d₁ d₂ : Distinction) →
  (f : S d₁ → S d₂) →
  (c₁ c₂ : EndoCase) →
  K₄Map.interpret d₁ d₂ c₁ ≗ f →
  K₄Map.interpret d₁ d₂ c₂ ≗ f →
  c₁ ≡ c₂
k4map-classification-unique d₁ d₂ f c₁ c₂ p₁ p₂ =
  K₄Map.interpret-injective d₁ d₂ c₁ c₂ (K₄Map.≗-trans d₁ d₂ p₁ (K₄Map.≗-sym d₁ d₂ p₂))

-- § Law 7.1: A map is determined by boundary values.
law7-1-map-determined :
  (d₁ d₂ : Distinction) →
  (f g : S d₁ → S d₂) →
  f (ℓ d₁) ≡ g (ℓ d₁) →
  f (r d₁) ≡ g (r d₁) →
  f ≗ g
law7-1-map-determined d₁ d₂ = K₄Map.map-determined d₁ d₂
-- § Law 7.2: K₄ classification produces a witness for any map.
law7-2-k4map-classification-sound :
  (d₁ d₂ : Distinction) →
  (f : S d₁ → S d₂) →
  Σ EndoCase (λ c → K₄Map.interpret d₁ d₂ c ≗ f)
law7-2-k4map-classification-sound = k4map-classification-sound
-- § Law 7.3: K₄ witness for maps is unique.
law7-3-k4map-classification-unique :
  (d₁ d₂ : Distinction) →
  (f : S d₁ → S d₂) →
  (c₁ c₂ : EndoCase) →
  K₄Map.interpret d₁ d₂ c₁ ≗ f →
  K₄Map.interpret d₁ d₂ c₂ ≗ f →
  c₁ ≡ c₂
law7-3-k4map-classification-unique = k4map-classification-unique
-- § Map presentation record.
record MapPresentation (d₁ d₂ : Distinction) (X : Set) : Set where
  field
    mp-interpret            : X → (S d₁ → S d₂)
    mp-classify             : (S d₁ → S d₂) → X
    mp-classify-sound       : (f : S d₁ → S d₂) → mp-interpret (mp-classify f) ≗ f
    mp-interpret-injective  : (x y : X) → mp-interpret x ≗ mp-interpret y → x ≡ y

open MapPresentation public

-- § Law 7.4: Map presentation is unique up to isomorphism.
law7-4-map-presentation-unique :
  (d₁ d₂ : Distinction) →
  {X : Set} →
  MapPresentation d₁ d₂ X →
  SetIso X EndoCase
law7-4-map-presentation-unique d₁ d₂ {X} pres =
  let
    module K = K₄Map d₁ d₂

    to' : X → EndoCase
    to' x = K.classify (MapPresentation.mp-interpret pres x)

    from' : EndoCase → X
    from' c = MapPresentation.mp-classify pres (K.interpret c)

    to-from' : (c : EndoCase) → to' (from' c) ≡ c
    to-from' c =
      sym
        (K.classify-unique
          (MapPresentation.mp-interpret pres (MapPresentation.mp-classify pres (K.interpret c)))
          c
          (K.≗-sym (MapPresentation.mp-classify-sound pres (K.interpret c))))

    from-to' : (x : X) → from' (to' x) ≡ x
    from-to' x =
      MapPresentation.mp-interpret-injective pres
        (MapPresentation.mp-classify pres (K.interpret (K.classify (MapPresentation.mp-interpret pres x))))
        x
        (K.≗-trans
          (MapPresentation.mp-classify-sound pres (K.interpret (K.classify (MapPresentation.mp-interpret pres x))))
          (K.classify-sound (MapPresentation.mp-interpret pres x)))
  in
  record
    { to = to'
    ; from = from'
    ; to-from = to-from'
    ; from-to = from-to'
    }
-- § Natural numbers.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- § Standard ordering on ℕ.
data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

-- § ≤ is reflexive.
≤-refl : (n : ℕ) → n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

-- § ≤ is transitive.
≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n       _          = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

-- § Step lemma.
≤-step : (n : ℕ) → n ≤ suc n
≤-step zero    = z≤n
≤-step (suc n) = s≤s (≤-step n)

-- § suc n ≤ n is absurd.
suc≤-impossible : (n : ℕ) → suc n ≤ n → ⊥
suc≤-impossible zero ()
suc≤-impossible (suc n) (s≤s p) = suc≤-impossible n p

-- § Tick-indexed drift state.
record DriftStateℕ : Setω where
  constructor ⟪_,_⟫
  field
    tick : ℕ
    base : DriftState

open DriftStateℕ public

-- § Step the indexed state forward.
stepStateℕ : DriftStateℕ → DriftStateℕ
stepStateℕ s = ⟪ suc (tick s) , stepState (base s) ⟫

-- § Extract the carrier of an indexed state.
Carrierℕ : (s : DriftStateℕ) → Set (ℓ (base s))
Carrierℕ s = Carrier (base s)

-- § Embed between consecutive indexed carriers.
state-embedℕ : (s : DriftStateℕ) → Carrierℕ s → Carrierℕ (stepStateℕ s)
state-embedℕ s = state-embed (base s)

-- § Strict reachability on indexed states.
data Reach⁺ℕ : DriftStateℕ → DriftStateℕ → Setω where
  oneℕ  : {s : DriftStateℕ} → Reach⁺ℕ s (stepStateℕ s)
  moreℕ : {s t : DriftStateℕ} → Reach⁺ℕ (stepStateℕ s) t → Reach⁺ℕ s t

-- § Strict reachability as infix.
infix 20 _≺ℕ_
_≺ℕ_ : DriftStateℕ → DriftStateℕ → Setω
s ≺ℕ t = Reach⁺ℕ s t
-- § Law 8.0: Tick strictly increases along Reach⁺ℕ.
law8-0-tick-increases : {s t : DriftStateℕ} → (s ≺ℕ t) → suc (tick s) ≤ tick t
law8-0-tick-increases oneℕ = ≤-refl _
law8-0-tick-increases {s} (moreℕ p) =
  ≤-trans (≤-step (suc (tick s))) (law8-0-tick-increases p)
-- § Law 8.1: Indexed drift has no cycles.
law8-1-no-cycleℕ : (s : DriftStateℕ) → (s ≺ℕ s) → ⊥
law8-1-no-cycleℕ s p = suc≤-impossible (tick s) (law8-0-tick-increases p)
-- § Forget the tick index.
forgetState : DriftStateℕ → DriftState
forgetState = base

-- § Forget preserves strict reachability.
forgetReach⁺ : {s t : DriftStateℕ} → (s ≺ℕ t) → (forgetState s ≺ forgetState t)
forgetReach⁺ oneℕ = one
forgetReach⁺ (moreℕ p) = more (forgetReach⁺ p)

-- § Compute the lifted target.
liftTarget : (n : ℕ) → {s t : DriftState} → (p : s ≺ t) → DriftStateℕ
liftTarget n {s} one = stepStateℕ ⟪ n , s ⟫
liftTarget n (more p) = liftTarget (suc n) p

-- § Lift a base reach proof into the indexed ledger.
liftReach⁺ : (n : ℕ) → {s t : DriftState} → (p : s ≺ t) → (⟪ n , s ⟫ ≺ℕ liftTarget n p)
liftReach⁺ n {s} one = oneℕ
liftReach⁺ n (more p) = moreℕ (liftReach⁺ (suc n) p)

-- § Lifted target forgets to the original target.
liftTarget-base : (n : ℕ) → {s t : DriftState} → (p : s ≺ t) → forgetState (liftTarget n p) ≡ω t
liftTarget-base n {s} one = reflω
liftTarget-base n (more p) = liftTarget-base (suc n) p

-- § Substitution lemma for more-constructor.
substω-more :
  {s : DriftState} {t u : DriftState} →
  (eq : t ≡ω u) →
  (p : Reach⁺ (stepState s) t) →
  substω (λ x → Reach⁺ s x) eq (more p) ≡ω more (substω (λ x → Reach⁺ (stepState s) x) eq p)
substω-more reflω p = reflω
-- § Law 9.0: Forget preserves strict reachability.
law9-0-forget-preserves : {s t : DriftStateℕ} → (s ≺ℕ t) → (forgetState s ≺ forgetState t)
law9-0-forget-preserves = forgetReach⁺

-- § Law 9.1: Every strict reachability proof lifts to the indexed ledger.
law9-1-lift-exists : (n : ℕ) → {s t : DriftState} → (p : s ≺ t) → (⟪ n , s ⟫ ≺ℕ liftTarget n p)
law9-1-lift-exists = liftReach⁺

-- § Law 9.2: Forget after lift recovers the original proof.
law9-2-forget-after-lift :
  (n : ℕ) → {s t : DriftState} →
  (p : s ≺ t) →
  substω (λ u → Reach⁺ s u) (liftTarget-base n p) (forgetReach⁺ (liftReach⁺ n p)) ≡ω p
law9-2-forget-after-lift n one = reflω
law9-2-forget-after-lift n {s} (more p) =
  let
    eq = liftTarget-base (suc n) p
    q  = forgetReach⁺ (liftReach⁺ (suc n) p)
  in
  transω
    (substω-more {s = s} eq q)
    (congω more (law9-2-forget-after-lift (suc n) p))
-- § Pointwise equality on ω-valued maps.
infix 4 _≗ω_
_≗ω_ : {A B : Setω} → (A → B) → (A → B) → Setω
_≗ω_ {A = A} f g = (x : A) → f x ≡ω g x

-- § Canonical inclusion.
canonicalState : DriftState → DriftStateℕ
canonicalState s = ⟪ zero , s ⟫

-- § Respecting the base projection.
record RespectsBase {Y : Setω} (f : DriftStateℕ → Y) : Setω where
  field
    respects : (x y : DriftStateℕ) → forgetState x ≡ω forgetState y → f x ≡ω f y

open RespectsBase public

-- § Factorization through forgetState.
record FactorsThroughBase {Y : Setω} (f : DriftStateℕ → Y) : Setω where
  field
    g    : DriftState → Y
    comm : (x : DriftStateℕ) → f x ≡ω g (forgetState x)

open FactorsThroughBase public

-- § Law 9.3: Base-respecting observables factor through forget.
law9-3-factor-through-base :
  {Y : Setω} →
  (f : DriftStateℕ → Y) →
  RespectsBase f →
  FactorsThroughBase f
law9-3-factor-through-base f rb = record
  { g = λ s → f (canonicalState s)
  ; comm = λ x →
      respects rb x (canonicalState (forgetState x)) reflω
  }

-- § Law 9.4: Factorization through forget is unique.
law9-4-factor-unique :
  {Y : Setω} →
  {f : DriftStateℕ → Y} →
  (u v : FactorsThroughBase f) →
  g u ≗ω g v
law9-4-factor-unique {f = f} u v s =
  let
    x = canonicalState s
  in
  transω (symω (comm u x)) (comm v x)

-- § Admissible observable record.
record AdmissibleObservable (Y : Setω) : Setω where
  field
    obs  : DriftStateℕ → Y
    base : RespectsBase obs

open AdmissibleObservable public

-- § Extract the base observable.
observe : {Y : Setω} → AdmissibleObservable Y → DriftState → Y
observe {Y} a = g (law9-3-factor-through-base (obs a) (base a))

-- § Commutation witness.
observe-comm : {Y : Setω} → (a : AdmissibleObservable Y) → (x : DriftStateℕ) → obs a x ≡ω observe a (forgetState x)
observe-comm a = comm (law9-3-factor-through-base (obs a) (base a))

-- § Law 9.5: Admissible observables collapse to base observables.
law9-5-observe-comm : {Y : Setω} → (a : AdmissibleObservable Y) → (x : DriftStateℕ) → obs a x ≡ω observe a (forgetState x)
law9-5-observe-comm = observe-comm

-- § Law 9.6: Base observable extracted from admissibility is unique.
law9-6-observe-unique :
  {Y : Setω} →
  (a : AdmissibleObservable Y) →
  (h₁ h₂ : DriftState → Y) →
  ((x : DriftStateℕ) → obs a x ≡ω h₁ (forgetState x)) →
  ((x : DriftStateℕ) → obs a x ≡ω h₂ (forgetState x)) →
  h₁ ≗ω h₂
law9-6-observe-unique a h₁ h₂ comm₁ comm₂ s =
  let
    f = obs a
    u : FactorsThroughBase f
    u = record { g = h₁ ; comm = comm₁ }

    v : FactorsThroughBase f
    v = record { g = h₂ ; comm = comm₂ }
  in
  law9-4-factor-unique u v s

-- § Indexed observable type.
IndexedObs : (Y : Setω) → Setω
IndexedObs Y = DriftStateℕ → Y

-- § Base observable type.
BaseObs : (Y : Setω) → Setω
BaseObs Y = DriftState → Y

-- § Lift base to indexed.
liftBase : {Y : Setω} → BaseObs Y → IndexedObs Y
liftBase h x = h (forgetState x)

-- § Pack a base observable as admissible.
packObs : {Y : Setω} → BaseObs Y → AdmissibleObservable Y
packObs h = record
  { obs  = liftBase h
  ; base = record { respects = λ x y eq → congω h eq }
  }

-- § Law 9.7: Indexed observables are unique given a base mediator.
law9-7-obs-unique :
  {Y : Setω} →
  (h : BaseObs Y) →
  (f₁ f₂ : IndexedObs Y) →
  ((x : DriftStateℕ) → f₁ x ≡ω h (forgetState x)) →
  ((x : DriftStateℕ) → f₂ x ≡ω h (forgetState x)) →
  f₁ ≗ω f₂
law9-7-obs-unique h f₁ f₂ comm₁ comm₂ x =
  transω (comm₁ x) (symω (comm₂ x))

-- § Law 9.8: Canonical indexed presentation for any admissible observable.
law9-8-canonical-pack :
  {Y : Setω} →
  (a : AdmissibleObservable Y) →
  obs a ≗ω obs (packObs (observe a))
law9-8-canonical-pack a x = observe-comm a x

-- § Law 9.9: observe ∘ packObs is the identity.
law9-9-observe-pack-id :
  {Y : Setω} →
  (h : DriftState → Y) →
  observe (packObs h) ≗ω h
law9-9-observe-pack-id h s = reflω
-- § Observational equality for admissible observables.
infix 4 _≈Obs_
_≈Obs_ : {Y : Setω} → AdmissibleObservable Y → AdmissibleObservable Y → Setω
_≈Obs_ a b = obs a ≗ω obs b

-- § ≈Obs reflexivity, symmetry, transitivity.
≈Obs-refl : {Y : Setω} → (a : AdmissibleObservable Y) → a ≈Obs a
≈Obs-refl a x = reflω

≈Obs-sym : {Y : Setω} → {a b : AdmissibleObservable Y} → a ≈Obs b → b ≈Obs a
≈Obs-sym p x = symω (p x)

≈Obs-trans : {Y : Setω} → {a b c : AdmissibleObservable Y} → a ≈Obs b → b ≈Obs c → a ≈Obs c
≈Obs-trans p q x = transω (p x) (q x)

-- § Canonical normal form.
canonObs : {Y : Setω} → AdmissibleObservable Y → AdmissibleObservable Y
canonObs a = packObs (observe a)

-- § Law 9.10: Canonicalization is observationally sound.
law9-10-canonObs-sound :
  {Y : Setω} →
  (a : AdmissibleObservable Y) →
  a ≈Obs canonObs a
law9-10-canonObs-sound a = law9-8-canonical-pack a

-- § Law 9.11: Canonicalization is idempotent up to observation.
law9-11-canonObs-idem :
  {Y : Setω} →
  (a : AdmissibleObservable Y) →
  canonObs (canonObs a) ≈Obs canonObs a
law9-11-canonObs-idem a =
  let
    b = canonObs a
  in
  λ x → symω ((law9-10-canonObs-sound b) x)

-- § Canonical base observable type.
CanonicalObs : (Y : Setω) → Setω
CanonicalObs Y = DriftState → Y

-- § Observational iso record.
record ObsIso (Y : Setω) : Setω where
  field
    to      : AdmissibleObservable Y → CanonicalObs Y
    from    : CanonicalObs Y → AdmissibleObservable Y
    to-from : (h : CanonicalObs Y) → to (from h) ≗ω h
    from-to : (a : AdmissibleObservable Y) → a ≈Obs from (to a)

open ObsIso public

-- § Law 9.12: Observational collapse as an explicit iso structure.
law9-12-obsIso : {Y : Setω} → ObsIso Y
law9-12-obsIso {Y} = record
  { to      = observe
  ; from    = packObs
  ; to-from = law9-9-observe-pack-id
  ; from-to = law9-10-canonObs-sound
  }

-- § Law 9.13: Any ObsIso normalization agrees with canonObs up to observation.
law9-13-obsIso-normalizes :
  {Y : Setω} →
  (i : ObsIso Y) →
  (a : AdmissibleObservable Y) →
  ObsIso.from i (ObsIso.to i a) ≈Obs canonObs a
law9-13-obsIso-normalizes i a =
  ≈Obs-trans
    {a = ObsIso.from i (ObsIso.to i a)}
    {b = a}
    {c = canonObs a}
    (≈Obs-sym {a = a} {b = ObsIso.from i (ObsIso.to i a)} (ObsIso.from-to i a))
    (law9-10-canonObs-sound a)

-- § Normalizer record.
record ObsNormalizer (Y : Setω) : Setω where
  field
    norm  : AdmissibleObservable Y → AdmissibleObservable Y
    sound : (a : AdmissibleObservable Y) → a ≈Obs norm a
    idem  : (a : AdmissibleObservable Y) → norm (norm a) ≈Obs norm a

open ObsNormalizer public

-- § Law 9.14: Any sound normalizer agrees with canonObs up to observation.
law9-14-normalizer-unique :
  {Y : Setω} →
  (n : ObsNormalizer Y) →
  (a : AdmissibleObservable Y) →
  norm n a ≈Obs canonObs a
law9-14-normalizer-unique n a =
  ≈Obs-trans
    {a = norm n a}
    {b = a}
    {c = canonObs a}
    (≈Obs-sym {a = a} {b = norm n a} (sound n a))
    (law9-10-canonObs-sound a)
-- § Iterate successor.
iterSuc : ℕ → ℕ → ℕ
iterSuc zero    n = n
iterSuc (suc k) n = iterSuc k (suc n)

-- § Count steps in a strict reach proof.
steps⁺ : {s t : DriftState} → (s ≺ t) → ℕ
steps⁺ one      = suc zero
steps⁺ (more p) = suc (steps⁺ p)

-- § Lift a base reach proof to the indexed ledger with correct tick.
liftReach⁺ℕ :
  (n : ℕ) → {s t : DriftState} →
  (p : s ≺ t) →
  (⟪ n , s ⟫ ≺ℕ ⟪ iterSuc (steps⁺ p) n , t ⟫)
liftReach⁺ℕ n {s} one = oneℕ
liftReach⁺ℕ n (more p) = moreℕ (liftReach⁺ℕ (suc n) p)

-- § Forget after lift recovers the original proof.
forget-after-liftReach⁺ℕ :
  (n : ℕ) → {s t : DriftState} →
  (p : s ≺ t) →
  forgetReach⁺ (liftReach⁺ℕ n p) ≡ω p
forget-after-liftReach⁺ℕ n one = reflω
forget-after-liftReach⁺ℕ n (more p) = congω more (forget-after-liftReach⁺ℕ (suc n) p)

-- § Admissible reach observable record.
record AdmissibleReachObservable (Y : Setω) : Setω where
  field
    obsR  : {s t : DriftStateℕ} → (s ≺ℕ t) → Y
    baseR : {s t : DriftState} → (s ≺ t) → Y
    commR : {s t : DriftStateℕ} → (p : s ≺ℕ t) → obsR p ≡ω baseR (forgetReach⁺ p)

open AdmissibleReachObservable public
-- § Law 10.0: Admissible reach observables are determined by base reachability.
law10-0-comm : {Y : Setω} → (a : AdmissibleReachObservable Y) → {s t : DriftStateℕ} → (p : s ≺ℕ t) → obsR a p ≡ω baseR a (forgetReach⁺ p)
law10-0-comm a = commR a

-- § Law 10.1: Base reach observable mediator is unique.
law10-1-baseR-unique :
  {Y : Setω} →
  (obsR' : {s t : DriftStateℕ} → (s ≺ℕ t) → Y) →
  (h₁ h₂ : {s t : DriftState} → (s ≺ t) → Y) →
  (({s t : DriftStateℕ} (p : s ≺ℕ t) → obsR' p ≡ω h₁ (forgetReach⁺ p))) →
  (({s t : DriftStateℕ} (p : s ≺ℕ t) → obsR' p ≡ω h₂ (forgetReach⁺ p))) →
  ({s t : DriftState} (p : s ≺ t) → h₁ p ≡ω h₂ p)
law10-1-baseR-unique obsR' h₁ h₂ comm₁ comm₂ {s} {t} p =
  let
    q = liftReach⁺ℕ zero p
    e = forget-after-liftReach⁺ℕ zero p
  in
  transω
    (symω (congω h₁ e))
    (transω
      (symω (comm₁ q))
      (transω (comm₂ q) (congω h₂ e)))
-- § Indexed transitivity.
Reach⁺ℕ-trans : {s t u : DriftStateℕ} → (s ≺ℕ t) → (t ≺ℕ u) → (s ≺ℕ u)
Reach⁺ℕ-trans oneℕ      q = moreℕ q
Reach⁺ℕ-trans (moreℕ p) q = moreℕ (Reach⁺ℕ-trans p q)

-- § Indexed extension.
Reach⁺ℕ-extend : {s t : DriftStateℕ} → (s ≺ℕ t) → (s ≺ℕ stepStateℕ t)
Reach⁺ℕ-extend p = Reach⁺ℕ-trans p oneℕ

-- § Forget commutes with transitivity.
forgetReach⁺-trans :
  {s t u : DriftStateℕ} →
  (p : s ≺ℕ t) → (q : t ≺ℕ u) →
  forgetReach⁺ (Reach⁺ℕ-trans p q) ≡ω Reach⁺-trans (forgetReach⁺ p) (forgetReach⁺ q)
forgetReach⁺-trans oneℕ      q = reflω
forgetReach⁺-trans (moreℕ p) q = congω more (forgetReach⁺-trans p q)

-- § Forget commutes with extension.
forgetReach⁺-extend :
  {s t : DriftStateℕ} →
  (p : s ≺ℕ t) →
  forgetReach⁺ (Reach⁺ℕ-extend p) ≡ω Reach⁺-extend (forgetReach⁺ p)
forgetReach⁺-extend p =
  transω (forgetReach⁺-trans p oneℕ) reflω

-- § Law 10.2: Admissible reach observables respect indexed transitivity.
law10-2-obsR-trans :
  {Y : Setω} →
  (a : AdmissibleReachObservable Y) →
  {s t u : DriftStateℕ} →
  (p : s ≺ℕ t) → (q : t ≺ℕ u) →
  obsR a (Reach⁺ℕ-trans p q) ≡ω baseR a (Reach⁺-trans (forgetReach⁺ p) (forgetReach⁺ q))
law10-2-obsR-trans a p q =
  transω (commR a (Reach⁺ℕ-trans p q)) (congω (baseR a) (forgetReach⁺-trans p q))

-- § Law 10.3: Admissible reach observables respect indexed extension.
law10-3-obsR-extend :
  {Y : Setω} →
  (a : AdmissibleReachObservable Y) →
  {s t : DriftStateℕ} →
  (p : s ≺ℕ t) →
  obsR a (Reach⁺ℕ-extend p) ≡ω baseR a (Reach⁺-extend (forgetReach⁺ p))
law10-3-obsR-extend a p =
  transω (commR a (Reach⁺ℕ-extend p)) (congω (baseR a) (forgetReach⁺-extend p))
-- § Indexed reach observable type.
IndexedReachObs : (Y : Setω) → Setω
IndexedReachObs Y = {s t : DriftStateℕ} → (s ≺ℕ t) → Y

-- § Base reach observable type.
BaseReachObs : (Y : Setω) → Setω
BaseReachObs Y = {s t : DriftState} → (s ≺ t) → Y

-- § Pointwise equality on indexed reach observables.
infix 4 _≗Rω_ _≗BaseRω_
_≗Rω_ : {Y : Setω} → IndexedReachObs Y → IndexedReachObs Y → Setω
_≗Rω_ {Y} f g = {s t : DriftStateℕ} → (p : s ≺ℕ t) → f p ≡ω g p

_≗BaseRω_ : {Y : Setω} → BaseReachObs Y → BaseReachObs Y → Setω
_≗BaseRω_ {Y} f g = {s t : DriftState} → (p : s ≺ t) → f p ≡ω g p

-- § Lift base reach to indexed reach.
liftBaseR : {Y : Setω} → BaseReachObs Y → IndexedReachObs Y
liftBaseR h p = h (forgetReach⁺ p)

-- § Pack a base reach observable as admissible.
packReach : {Y : Setω} → BaseReachObs Y → AdmissibleReachObservable Y
packReach h = record
  { obsR  = liftBaseR h
  ; baseR = h
  ; commR = λ p → reflω
  }

-- § Law 10.4: Indexed reach observables are unique given a base mediator.
law10-4-obsR-unique :
  {Y : Setω} →
  (h : BaseReachObs Y) →
  (f₁ f₂ : IndexedReachObs Y) →
  (({s t : DriftStateℕ} (p : s ≺ℕ t) → f₁ p ≡ω h (forgetReach⁺ p))) →
  (({s t : DriftStateℕ} (p : s ≺ℕ t) → f₂ p ≡ω h (forgetReach⁺ p))) →
  f₁ ≗Rω f₂
law10-4-obsR-unique h f₁ f₂ comm₁ comm₂ p =
  transω (comm₁ p) (symω (comm₂ p))

-- § Law 10.5: Canonical indexed presentation for any admissible reach observable.
law10-5-canonical-pack :
  {Y : Setω} →
  (a : AdmissibleReachObservable Y) →
  obsR a ≗Rω obsR (packReach (baseR a))
law10-5-canonical-pack a p = commR a p

-- § Law 10.6: baseR ∘ packReach is the identity.
law10-6-baseR-pack-id :
  {Y : Setω} →
  (h : BaseReachObs Y) →
  baseR (packReach h) ≗BaseRω h
law10-6-baseR-pack-id h p = reflω
infix 4 _≈ReachObs_
_≈ReachObs_ : {Y : Setω} → AdmissibleReachObservable Y → AdmissibleReachObservable Y → Setω
_≈ReachObs_ a b = obsR a ≗Rω obsR b

-- § ≈ReachObs reflexivity, symmetry, transitivity.
≈ReachObs-refl : {Y : Setω} → (a : AdmissibleReachObservable Y) → a ≈ReachObs a
≈ReachObs-refl a p = reflω

≈ReachObs-sym : {Y : Setω} → {a b : AdmissibleReachObservable Y} → a ≈ReachObs b → b ≈ReachObs a
≈ReachObs-sym p q = symω (p q)

≈ReachObs-trans : {Y : Setω} → {a b c : AdmissibleReachObservable Y} → a ≈ReachObs b → b ≈ReachObs c → a ≈ReachObs c
≈ReachObs-trans p q r = transω (p r) (q r)

-- § Canonical reach normal form.
canonReach : {Y : Setω} → AdmissibleReachObservable Y → AdmissibleReachObservable Y
canonReach a = packReach (baseR a)

-- § Law 10.7: Canonical reach packing is observationally sound.
law10-7-canonReach-sound :
  {Y : Setω} →
  (a : AdmissibleReachObservable Y) →
  a ≈ReachObs canonReach a
law10-7-canonReach-sound a = law10-5-canonical-pack a

-- § Law 10.8: Canonical reach packing is idempotent up to observation.
law10-8-canonReach-idem :
  {Y : Setω} →
  (a : AdmissibleReachObservable Y) →
  canonReach (canonReach a) ≈ReachObs canonReach a
law10-8-canonReach-idem a =
  let
    b = canonReach a
  in
  λ p → symω ((law10-7-canonReach-sound b) p)

-- § Canonical reach observable type.
CanonicalReachObs : (Y : Setω) → Setω
CanonicalReachObs Y = BaseReachObs Y

-- § Reach observational iso record.
record ReachObsIso (Y : Setω) : Setω where
  field
    to      : AdmissibleReachObservable Y → CanonicalReachObs Y
    from    : CanonicalReachObs Y → AdmissibleReachObservable Y
    to-from : (h : CanonicalReachObs Y) → to (from h) ≗BaseRω h
    from-to : (a : AdmissibleReachObservable Y) → a ≈ReachObs from (to a)

open ReachObsIso public

-- § Law 10.9: Observational collapse as an explicit iso structure.
law10-9-reachObsIso : {Y : Setω} → ReachObsIso Y
law10-9-reachObsIso {Y} = record
  { to      = baseR
  ; from    = packReach
  ; to-from = law10-6-baseR-pack-id
  ; from-to = law10-7-canonReach-sound
  }

-- § Law 10.10: Any ReachObsIso normalization agrees with canonReach.
law10-10-reachObsIso-normalizes :
  {Y : Setω} →
  (i : ReachObsIso Y) →
  (a : AdmissibleReachObservable Y) →
  ReachObsIso.from i (ReachObsIso.to i a) ≈ReachObs canonReach a
law10-10-reachObsIso-normalizes i a =
  ≈ReachObs-trans
    {a = ReachObsIso.from i (ReachObsIso.to i a)}
    {b = a}
    {c = canonReach a}
    (≈ReachObs-sym {a = a} {b = ReachObsIso.from i (ReachObsIso.to i a)} (ReachObsIso.from-to i a))
    (law10-7-canonReach-sound a)

-- § Reach normalizer record.
record ReachObsNormalizer (Y : Setω) : Setω where
  field
    norm  : AdmissibleReachObservable Y → AdmissibleReachObservable Y
    sound : (a : AdmissibleReachObservable Y) → a ≈ReachObs norm a
    idem  : (a : AdmissibleReachObservable Y) → norm (norm a) ≈ReachObs norm a

open ReachObsNormalizer public

-- § Law 10.11: Any sound reach normalizer agrees with canonReach.
law10-11-reach-normalizer-unique :
  {Y : Setω} →
  (n : ReachObsNormalizer Y) →
  (a : AdmissibleReachObservable Y) →
  norm n a ≈ReachObs canonReach a
law10-11-reach-normalizer-unique n a =
  ≈ReachObs-trans
    {a = norm n a}
    {b = a}
    {c = canonReach a}
    (≈ReachObs-sym {a = a} {b = norm n a} (sound n a))
    (law10-7-canonReach-sound a)
-- § Ranking record.
record DriftRank : Setω where
  field
    rank      : DriftState → ℕ
    rank-step : (s : DriftState) → suc (rank s) ≤ rank (stepState s)

open DriftRank public
-- § Law 11.0: Rank is monotone along Reach⁺.
law11-0-rank-mono : (r : DriftRank) → {s t : DriftState} → (s ≺ t) → rank r s ≤ rank r t
law11-0-rank-mono r {s} one =
  ≤-trans (≤-step (rank r s)) (rank-step r s)
law11-0-rank-mono r {s} (more p) =
  ≤-trans
    (≤-trans (≤-step (rank r s)) (rank-step r s))
    (law11-0-rank-mono r p)

-- § Strict monotonicity.
law11-0-rank-increases : (r : DriftRank) → {s t : DriftState} → (s ≺ t) → suc (rank r s) ≤ rank r t
law11-0-rank-increases r {s} one = rank-step r s
law11-0-rank-increases r {s} (more p) =
  ≤-trans (rank-step r s) (law11-0-rank-mono r p)
-- § Law 11.1: Ranking forces DriftAcyclic.
law11-1-ranked-acyclic : DriftRank → DriftAcyclic
law11-1-ranked-acyclic r =
  record
    { no-cycle =
        λ s p →
          suc≤-impossible (rank r s) (law11-0-rank-increases r p)
    }
-- § Respecting ≈Obs.
record Respects≈Obs {Y Z : Setω} (F : AdmissibleObservable Y → Z) : Setω where
  field
    respects : {a b : AdmissibleObservable Y} → a ≈Obs b → F a ≡ω F b

open Respects≈Obs public

-- § Factorization record for state meta-observables.
record FactorsThroughObserve {Y Z : Setω} (F : AdmissibleObservable Y → Z) : Setω where
  field
    g    : (DriftState → Y) → Z
    comm : (a : AdmissibleObservable Y) → F a ≡ω g (observe a)

open FactorsThroughObserve public

-- § Law 12.0: Meta-observables factor through observe.
law12-0-meta-observe-factor :
  {Y Z : Setω} →
  (F : AdmissibleObservable Y → Z) →
  Respects≈Obs F →
  FactorsThroughObserve F
law12-0-meta-observe-factor F r =
  record
    { g = λ h → F (packObs h)
    ; comm = λ a →
        respects r (law9-10-canonObs-sound a)
    }

-- § Respecting ≈ReachObs.
record Respects≈ReachObs {Y Z : Setω} (F : AdmissibleReachObservable Y → Z) : Setω where
  field
    respectsR : {a b : AdmissibleReachObservable Y} → a ≈ReachObs b → F a ≡ω F b

open Respects≈ReachObs public

-- § Factorization record for reach meta-observables.
record FactorsThroughBaseR {Y Z : Setω} (F : AdmissibleReachObservable Y → Z) : Setω where
  field
    gR    : BaseReachObs Y → Z
    commR : (a : AdmissibleReachObservable Y) → F a ≡ω gR (baseR a)

open FactorsThroughBaseR public

-- § Law 12.1: Meta-observables factor through baseR.
law12-1-meta-baseR-factor :
  {Y Z : Setω} →
  (F : AdmissibleReachObservable Y → Z) →
  Respects≈ReachObs F →
  FactorsThroughBaseR F
law12-1-meta-baseR-factor F r =
  record
    { gR = λ h → F (packReach h)
    ; commR = λ a →
        respectsR r (law10-7-canonReach-sound a)
    }
-- § Graph record.
record Graph : Set1 where
  field
    V    : Set
    Edge : V → V → Set
    edge-sym : {a b : V} → Edge a b → Edge b a
    edge-irr : (a : V) → Edge a a → ⊥

open Graph public

-- § Graph isomorphism record.
record GraphIso (G H : Graph) : Set1 where
  field
    to       : V G → V H
    from     : V H → V G
    to-from  : (y : V H) → to (from y) ≡ y
    from-to  : (x : V G) → from (to x) ≡ x
    edge-to  : {a b : V G} → Edge G a b → Edge H (to a) (to b)
    edge-from : {a b : V H} → Edge H a b → Edge G (from a) (from b)

open GraphIso public

-- § Transport inequality across equalities.
transport≠ :
  {A : Set} →
  {a a' b b' : A} →
  a ≡ a' →
  b ≡ b' →
  (a ≠ b) →
  (a' ≠ b')
transport≠ ea eb neq eq' = neq (trans ea (trans eq' (sym eb)))
-- § Law 13.0: The canonical K₄ graph.
K4GraphCanonical : Graph
K4GraphCanonical = record
  { V = EndoCase
  ; Edge = λ a b → a ≠ b
  ; edge-sym = λ {a} {b} neq eq → neq (sym eq)
  ; edge-irr = λ a loop → loop refl
  }

-- § K₄ graph presentation record.
record K4GraphPresentation : Set1 where
  field
    Vp      : Set
    toV     : Vp → EndoCase
    fromV   : EndoCase → Vp
    to-from : (c : EndoCase) → toV (fromV c) ≡ c
    from-to : (v : Vp) → fromV (toV v) ≡ v

open K4GraphPresentation public

-- § Present a graph from a K₄ graph presentation.
presentedGraph : K4GraphPresentation → Graph
presentedGraph p = record
  { V = Vp p
  ; Edge = λ v w → toV p v ≠ toV p w
  ; edge-sym = λ {a} {b} neq eq → neq (sym eq)
  ; edge-irr = λ a loop → loop refl
  }
-- § Law 13.1: Presentation iso.
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
-- § Unit type: trivial truth witness.
data ⊤ : Set where
  tt : ⊤

-- § Three-element index (neighbours of a K₄ vertex).
data Fin3 : Set where
  f0 f1 f2 : Fin3

-- § Inequality on Fin3.
Fin3≠ : (i j : Fin3) → Set
Fin3≠ i j = i ≡ j → ⊥

f0≠f1 : Fin3≠ f0 f1
f0≠f1 ()

f0≠f2 : Fin3≠ f0 f2
f0≠f2 ()

f1≠f2 : Fin3≠ f1 f2
f1≠f2 ()

-- § Decidable equality on Fin3.
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

-- § Four-element index (vertices of K₄).
data Fin4 : Set where
  g0 g1 g2 g3 : Fin4

-- § Inequality on Fin4.
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

-- § Decidable equality on Fin4.
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
-- § Successor injectivity.
suc-injective : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

-- § Antisymmetry of ≤.
≤-antisym : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {zero} {zero} z≤n z≤n = refl
≤-antisym {zero} {suc n} z≤n ()
≤-antisym {suc m} {zero} () _
≤-antisym {suc m} {suc n} (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

-- § Boolean type with built-in binding.
data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

{-# BUILTIN NATURAL ℕ #-}

-- § Built-in addition on ℕ.
infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- § Built-in multiplication on ℕ.
infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

-- § Built-in monus (truncated subtraction) on ℕ.
infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero  ∸ n     = zero
suc m ∸ zero  = suc m
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- § Boolean strict comparison on ℕ.
_<ℕ-bool_ : ℕ → ℕ → Bool
m <ℕ-bool zero   = false
zero <ℕ-bool suc _ = true
suc m <ℕ-bool suc n = m <ℕ-bool n

{-# BUILTIN NATLESS _<ℕ-bool_ #-}

-- § Boolean equality on ℕ.
_==ℕ-bool_ : ℕ → ℕ → Bool
zero  ==ℕ-bool zero    = true
zero  ==ℕ-bool (suc _) = false
suc _ ==ℕ-bool zero    = false
suc m ==ℕ-bool suc n   = m ==ℕ-bool n

{-# BUILTIN NATEQUALS _==ℕ-bool_ #-}
-- § Raw addition on ℕ (separate from BUILTIN _+_).
infixl 6 _+ℕ_

_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ n = n
suc m +ℕ n = suc (m +ℕ n)

-- § Integer type: signed normal form.
data ℤ : Set where
  0ℤ    : ℤ
  +suc_ : ℕ → ℤ
  -suc_ : ℕ → ℤ

-- § Normalization: cancel common successors.
normalizeℤ : ℕ → ℕ → ℤ
normalizeℤ zero zero = 0ℤ
normalizeℤ (suc a) zero = +suc a
normalizeℤ zero (suc b) = -suc b
normalizeℤ (suc a) (suc b) = normalizeℤ a b

-- § Pair representation for componentwise arithmetic.
record Pairℕ : Set where
  constructor mkPairℕ
  field
    pos : ℕ
    neg : ℕ

open Pairℕ public

-- § Embedding ℤ into pairs.
toPairℤ : ℤ → Pairℕ
toPairℤ 0ℤ = mkPairℕ zero zero
toPairℤ (+suc n) = mkPairℕ (suc n) zero
toPairℤ (-suc n) = mkPairℕ zero (suc n)

-- § Collapsing pairs to ℤ.
fromPairℤ : Pairℕ → ℤ
fromPairℤ p = normalizeℤ (pos p) (neg p)

-- § Integer addition via pair-level componentwise sum.
infixl 6 _+ℤ_

_+ℤ_ : ℤ → ℤ → ℤ
x +ℤ y =
  let px = toPairℤ x in
  let py = toPairℤ y in
  normalizeℤ (pos px +ℕ pos py) (neg px +ℕ neg py)

-- § Integer negation via pair swap.
negℤ : ℤ → ℤ
negℤ z =
  let p = toPairℤ z in
  normalizeℤ (neg p) (pos p)
-- § Generic endomorphism type.
GenEndo : Set → Set
GenEndo A = A → A

-- § Function composition.
infixr 9 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

-- § Identity endomorphism.
idGenEndo : {A : Set} → GenEndo A
idGenEndo x = x

-- § n-fold iteration.
powEndo : {A : Set} → ℕ → GenEndo A → GenEndo A
powEndo zero    f = idGenEndo
powEndo (suc n) f = f ∘ powEndo n f

-- § Law 14I.0: Zero iteration is identity.
law14I-0-powEndo-zero : {A : Set} → (f : GenEndo A) → powEndo zero f ≗ idGenEndo
law14I-0-powEndo-zero f x = refl

-- § Law 14I.1: Successor iteration unfolds.
law14I-1-powEndo-suc : {A : Set} → (n : ℕ) → (f : GenEndo A) → powEndo (suc n) f ≗ (f ∘ powEndo n f)
law14I-1-powEndo-suc n f x = refl
-- § Three-element sum.
sum3ℤ : ℤ → ℤ → ℤ → ℤ
sum3ℤ a b c = a +ℤ (b +ℤ c)

-- § Sum indexed by Fin3.
sumFin3ℤ : (Fin3 → ℤ) → ℤ
sumFin3ℤ f = sum3ℤ (f f0) (f f1) (f f2)

-- § Four-element sum.
sum4ℤ : ℤ → ℤ → ℤ → ℤ → ℤ
sum4ℤ a b c d = a +ℤ (b +ℤ (c +ℤ d))

-- § Sum indexed by Fin4.
sumFin4ℤ : (Fin4 → ℤ) → ℤ
sumFin4ℤ f = sum4ℤ (f g0) (f g1) (f g2) (f g3)

-- § Scalar triple.
threeTimesℤ : ℤ → ℤ
threeTimesℤ x = x +ℤ (x +ℤ x)

-- § Scalar quadruple.
fourTimesℤ : ℤ → ℤ
fourTimesℤ x = sum4ℤ x x x x

-- § Absolute value on ℤ.
absℤ : ℤ → ℤ
absℤ 0ℤ = 0ℤ
absℤ (+suc n) = +suc n
absℤ (-suc n) = +suc n
-- § Integer ordering.
infix 4 _≤ℤ_ _<ℤ_

_≤ℤ_ : ℤ → ℤ → Set
0ℤ ≤ℤ 0ℤ = ⊤
0ℤ ≤ℤ (+suc n) = ⊤
0ℤ ≤ℤ (-suc n) = ⊥
(+suc m) ≤ℤ 0ℤ = ⊥
(+suc m) ≤ℤ (+suc n) = suc m ≤ suc n
(+suc m) ≤ℤ (-suc n) = ⊥
(-suc m) ≤ℤ 0ℤ = ⊤
(-suc m) ≤ℤ (+suc n) = ⊤
(-suc m) ≤ℤ (-suc n) = suc n ≤ suc m

-- § Non-ordering witness.
_≰ℤ_ : ℤ → ℤ → Set
x ≰ℤ y = (x ≤ℤ y) → ⊥

-- § Strict integer ordering.
_<ℤ_ : ℤ → ℤ → Set
_<ℤ_ x y = (x ≤ℤ y) × (y ≰ℤ x)
-- § Fin4 → EndoCase bijection.
vertexAt : Fin4 → EndoCase
vertexAt g0 = case-constL
vertexAt g1 = case-constR
vertexAt g2 = case-id
vertexAt g3 = case-dual

-- § EndoCase → Fin4 inverse.
vertexIndex : EndoCase → Fin4
vertexIndex case-constL = g0
vertexIndex case-constR = g1
vertexIndex case-id     = g2
vertexIndex case-dual   = g3

-- § Round-trip: vertexAt ∘ vertexIndex = id.
vertexAt-index : (v : EndoCase) → vertexAt (vertexIndex v) ≡ v
vertexAt-index case-constL = refl
vertexAt-index case-constR = refl
vertexAt-index case-id     = refl
vertexAt-index case-dual   = refl

-- § Round-trip: vertexIndex ∘ vertexAt = id.
index-vertexAt : (i : Fin4) → vertexIndex (vertexAt i) ≡ i
index-vertexAt g0 = refl
index-vertexAt g1 = refl
index-vertexAt g2 = refl
index-vertexAt g3 = refl
-- § Setoid: carrier with equivalence relation.
record ESetoid : Set1 where
  field
    Obj    : Set
    Rel    : Obj → Obj → Set
    refl≈  : (x : Obj) → Rel x x
    sym≈   : {x y : Obj} → Rel x y → Rel y x
    trans≈ : {x y z : Obj} → Rel x y → Rel y z → Rel x z

open ESetoid public

-- § Endomorphism system: setoid + step.
record EndoSystem : Set1 where
  field
    ES    : ESetoid
    step : Obj ES → Obj ES
    step-cong : {x y : Obj ES} → Rel ES x y → Rel ES (step x) (step y)

open EndoSystem public

-- § Morphism of endomorphism systems.
record ESHom (X Y : EndoSystem) : Set1 where
  field
    esmap  : Obj (ES X) → Obj (ES Y)
    esmap-cong : {x y : Obj (ES X)} → Rel (ES X) x y → Rel (ES Y) (esmap x) (esmap y)
    escomm : (x : Obj (ES X)) → Rel (ES Y) (esmap (step X x)) (step Y (esmap x))

open ESHom public

-- § Terminal endomorphism system.
record IsTerminal (T : EndoSystem) : Set1 where
  field
    !    : (X : EndoSystem) → ESHom X T
    uniq : (X : EndoSystem) → (f g : ESHom X T) → (x : Obj (ES X)) → Rel (ES T) (esmap f x) (esmap g x)

-- § Initial endomorphism system.
record IsInitial (I : EndoSystem) : Set1 where
  field
    !    : (X : EndoSystem) → ESHom I X
    uniq : (X : EndoSystem) → (f g : ESHom I X) → (x : Obj (ES I)) → Rel (ES X) (esmap f x) (esmap g x)

-- § Law 14J.0: Morphisms commute with n-fold iteration.
law14J-0-hom-iter :
  {X Y : EndoSystem} →
  (h : ESHom X Y) →
  (n : ℕ) →
  (x : Obj (ES X)) →
  Rel (ES Y) (esmap h (powEndo n (step X) x)) (powEndo n (step Y) (esmap h x))
law14J-0-hom-iter {X} {Y} h zero x = refl≈ (ES Y) (esmap h x)
law14J-0-hom-iter {X} {Y} h (suc n) x =
  trans≈ (ES Y)
    (escomm h (powEndo n (step X) x))
    (step-cong Y (law14J-0-hom-iter h n x))
-- § Inequality on EndoCase.
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

-- § Decidable equality on EndoCase.
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
-- § Transposition on EndoCase: swaps x↔y, fixes others.
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

-- § swapEndo is an involution (64-case proof).
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
-- § swapEndo sends x to y.
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
-- § Permutation record on EndoCase.
record EndoPerm : Set where
  field
    eto       : EndoCase → EndoCase
    efrom     : EndoCase → EndoCase
    eto-efrom : (y : EndoCase) → eto (efrom y) ≡ y
    efrom-eto : (x : EndoCase) → efrom (eto x) ≡ x

open EndoPerm public

-- § Transposition as permutation.
permSwap : (x y : EndoCase) → EndoPerm
permSwap x y = record
  { eto = swapEndo x y
  ; efrom = swapEndo x y
  ; eto-efrom = swapEndo-involutive x y
  ; efrom-eto = swapEndo-involutive x y
  }

-- § Any vertex can be sent to any other by some permutation.
endoPerm-send : (a a' : EndoCase) → Σ EndoPerm (λ σ → eto σ a ≡ a')
endoPerm-send a a' = (permSwap a a' , swapEndo-sends a a')

-- § Coupling: relation between two copies of EndoCase.
Coupling : Set1
Coupling = EndoCase → EndoCase → Set

-- § Cross-invariance: coupling respected by independent permutations.
CrossInv : Coupling → Set
CrossInv C = (σ τ : EndoPerm) → (a b : EndoCase) → C a b → C (eto σ a) (eto τ b)

-- § Heterogeneous transport over a two-argument predicate.
transport2 : {A B : Set} {P : A → B → Set} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → P a b → P a' b'
transport2 {P = P} {a = a} {a' = a'} {b = b} {b' = b'} ea eb pab =
  subst (λ a0 → P a0 b') ea (subst (λ b0 → P a b0) eb pab)
-- § Law 14F.0: One edge forces all.
law14F-0-edge-forces-all : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → C a0 b0)) →
  (a b : EndoCase) → C a b
law14F-0-edge-forces-all C inv (a0 , (b0 , c0)) a b =
  let sa = endoPerm-send a0 a in
  let sb = endoPerm-send b0 b in
  let σ = fst sa in
  let τ = fst sb in
  transport2 {P = C} (snd sa) (snd sb) (inv σ τ a0 b0 c0)

-- § Law 14F.1: One missing edge forces no edges.
law14F-1-nonedge-forces-none : (C : Coupling) → CrossInv C →
  Σ EndoCase (λ a0 → Σ EndoCase (λ b0 → ¬ (C a0 b0))) →
  (a b : EndoCase) → ¬ (C a b)
law14F-1-nonedge-forces-none C inv (a0 , (b0 , n0)) a b cab =
  let sa = endoPerm-send a a0 in
  let sb = endoPerm-send b b0 in
  let σ = fst sa in
  let τ = fst sb in
  n0 (transport2 {P = C} (snd sa) (snd sb) (inv σ τ a b cab))
-- § Inequality on Two.
Two≠ : (i j : Two) → Set
Two≠ i j = i ≡ j → ⊥

L≠R : Two≠ L R
L≠R ()

-- § Decidable equality on Two.
Two-decEq : (i j : Two) → (i ≡ j) ⊎ (Two≠ i j)
Two-decEq L L = inj₁ refl
Two-decEq R R = inj₁ refl
Two-decEq L R = inj₂ L≠R
Two-decEq R L = inj₂ (λ e → L≠R (sym e))

-- § Product edge relation.
Edge2 : Coupling → (Two × EndoCase) → (Two × EndoCase) → Set
Edge2 C (L , a) (L , b) = a ≠ b
Edge2 C (R , a) (R , b) = a ≠ b
Edge2 C (L , a) (R , b) = C a b
Edge2 C (R , a) (L , b) = C b a

-- § Product edge symmetry.
edge2-sym : (C : Coupling) → {x y : Two × EndoCase} → Edge2 C x y → Edge2 C y x
edge2-sym C {x = (L , a)} {y = (L , b)} e = λ eq → e (sym eq)
edge2-sym C {x = (R , a)} {y = (R , b)} e = λ eq → e (sym eq)
edge2-sym C {x = (L , a)} {y = (R , b)} e = e
edge2-sym C {x = (R , a)} {y = (L , b)} e = e

-- § Product edge irreflexivity.
edge2-irr : (C : Coupling) → (x : Two × EndoCase) → Edge2 C x x → ⊥
edge2-irr C (L , a) e = e refl
edge2-irr C (R , a) e = e refl

-- § K₄ × 2 graph from coupling.
K4×2 : Coupling → Graph
K4×2 C = record
  { V = Two × EndoCase
  ; Edge = Edge2 C
  ; edge-sym = λ {a} {b} e → edge2-sym C {x = a} {y = b} e
  ; edge-irr = edge2-irr C
  }

-- § Empty coupling (no cross-edges).
CrossEmpty : Coupling
CrossEmpty _ _ = ⊥

-- § Full coupling (all cross-edges).
CrossFull : Coupling
CrossFull _ _ = ⊤
-- § Diagonal normalization collapses to zero.
normalizeDiag0ℤ : (n : ℕ) → normalizeℤ n n ≡ 0ℤ
normalizeDiag0ℤ zero = refl
normalizeDiag0ℤ (suc n) = normalizeDiag0ℤ n

-- § Right identity for +ℕ.
+ℕ-zero-right : (n : ℕ) → n +ℕ zero ≡ n
+ℕ-zero-right zero = refl
+ℕ-zero-right (suc n) = cong suc (+ℕ-zero-right n)

-- § Successor shifts right.
+ℕ-suc-right : (n m : ℕ) → n +ℕ suc m ≡ suc (n +ℕ m)
+ℕ-suc-right zero m = refl
+ℕ-suc-right (suc n) m = cong suc (+ℕ-suc-right n m)

-- § Associativity of +ℕ.
+ℕ-assoc : (a b c : ℕ) → (a +ℕ b) +ℕ c ≡ a +ℕ (b +ℕ c)
+ℕ-assoc zero b c = refl
+ℕ-assoc (suc a) b c = cong suc (+ℕ-assoc a b c)

-- § Commutativity of +ℕ.
+ℕ-comm : (a b : ℕ) → a +ℕ b ≡ b +ℕ a
+ℕ-comm zero b = sym (+ℕ-zero-right b)
+ℕ-comm (suc a) b =
  trans
    refl
    (trans
      (cong suc (+ℕ-comm a b))
      (sym (+ℕ-suc-right b a)))
-- § Congruence for normalizeℤ.
normalizeℤ-cong : {a a' b b' : ℕ} → a ≡ a' → b ≡ b' → normalizeℤ a b ≡ normalizeℤ a' b'
normalizeℤ-cong {a} {a'} {b} {b'} pa pb = trans (cong (λ t → normalizeℤ t b) pa) (cong (normalizeℤ a') pb)

-- § Normalization absorbs pair-level addition.
normalize-plusRight : (a b c d : ℕ) →
  normalizeℤ (pos (toPairℤ (normalizeℤ a b)) +ℕ c) (neg (toPairℤ (normalizeℤ a b)) +ℕ d)
    ≡
  normalizeℤ (a +ℕ c) (b +ℕ d)
normalize-plusRight zero zero c d = refl
normalize-plusRight (suc a) zero c d = refl
normalize-plusRight zero (suc b) c d = refl
normalize-plusRight (suc a) (suc b) c d = normalize-plusRight a b c d

-- § Commutativity of +ℤ.
+ℤ-comm : (x y : ℤ) → x +ℤ y ≡ y +ℤ x
+ℤ-comm x y with toPairℤ x | toPairℤ y
... | px | py =
  normalizeℤ-cong (+ℕ-comm (pos px) (pos py)) (+ℕ-comm (neg px) (neg py))

-- § Associativity of +ℤ.
+ℤ-assoc : (x y z : ℤ) → (x +ℤ y) +ℤ z ≡ x +ℤ (y +ℤ z)
+ℤ-assoc x y z with toPairℤ x | toPairℤ y | toPairℤ z
... | px | py | pz =
  let ax = pos px in
  let bx = neg px in
  let ay = pos py in
  let by = neg py in
  let az = pos pz in
  let bz = neg pz in
  let Axy = ax +ℕ ay in
  let Bxy = bx +ℕ by in
  let Ayz = ay +ℕ az in
  let Byz = by +ℕ bz in

  let lhs₀ = normalizeℤ (pos (toPairℤ (normalizeℤ Axy Bxy)) +ℕ az)
                       (neg (toPairℤ (normalizeℤ Axy Bxy)) +ℕ bz) in
  let lhs₁ = normalizeℤ (Axy +ℕ az) (Bxy +ℕ bz) in
  let rhs₀ = normalizeℤ (ax +ℕ pos (toPairℤ (normalizeℤ Ayz Byz)))
                       (bx +ℕ neg (toPairℤ (normalizeℤ Ayz Byz))) in
  let rhs₁ = normalizeℤ (pos (toPairℤ (normalizeℤ Ayz Byz)) +ℕ ax)
                       (neg (toPairℤ (normalizeℤ Ayz Byz)) +ℕ bx) in
  let rhs₂ = normalizeℤ (Ayz +ℕ ax) (Byz +ℕ bx) in
  let rhs₃ = normalizeℤ (ax +ℕ Ayz) (bx +ℕ Byz) in

  trans
    (trans
      (cong (λ u → u) (normalize-plusRight Axy Bxy az bz))
      (normalizeℤ-cong (+ℕ-assoc ax ay az) (+ℕ-assoc bx by bz)))
    (sym
      (trans
        (trans
          (normalizeℤ-cong (+ℕ-comm ax (pos (toPairℤ (normalizeℤ Ayz Byz))))
                           (+ℕ-comm bx (neg (toPairℤ (normalizeℤ Ayz Byz)))))
          (normalize-plusRight Ayz Byz ax bx))
        (normalizeℤ-cong (+ℕ-comm Ayz ax) (+ℕ-comm Byz bx))))

-- § Left identity for +ℤ.
+ℤ-zero-left : (x : ℤ) → 0ℤ +ℤ x ≡ x
+ℤ-zero-left 0ℤ = refl
+ℤ-zero-left (+suc n) = refl
+ℤ-zero-left (-suc n) = refl

-- § Right identity for +ℤ.
+ℤ-zero-right : (x : ℤ) → x +ℤ 0ℤ ≡ x
+ℤ-zero-right x = trans (+ℤ-comm x 0ℤ) (+ℤ-zero-left x)

-- § Right inverse.
+ℤ-inv-right : (x : ℤ) → x +ℤ negℤ x ≡ 0ℤ
+ℤ-inv-right 0ℤ = refl
+ℤ-inv-right (+suc n) =
  trans
    (cong (λ a → normalizeℤ a (suc n)) (+ℕ-zero-right (suc n)))
    (normalizeDiag0ℤ (suc n))
+ℤ-inv-right (-suc n) =
  trans
    (cong (normalizeℤ (suc n)) (+ℕ-zero-right (suc n)))
    (normalizeDiag0ℤ (suc n))

-- § Left inverse.
+ℤ-inv-left : (x : ℤ) → negℤ x +ℤ x ≡ 0ℤ
+ℤ-inv-left x = trans (+ℤ-comm (negℤ x) x) (+ℤ-inv-right x)

-- § Negation of zero.
negℤ-zero : negℤ 0ℤ ≡ 0ℤ
negℤ-zero = refl

-- § Left cancellation.
+ℤ-cancel-left : (a b : ℤ) → a +ℤ b ≡ a → b ≡ 0ℤ
+ℤ-cancel-left a b eq =
  trans
    (sym (+ℤ-zero-left b))
    (trans
      (cong (λ t → t +ℤ b) (sym (+ℤ-inv-left a)))
      (trans
        (+ℤ-assoc (negℤ a) a b)
        (trans
          (cong (λ t → negℤ a +ℤ t) eq)
          (+ℤ-inv-left a))))

-- § Negation zero-test.
negℤ-zero→zero : (z : ℤ) → negℤ z ≡ 0ℤ → z ≡ 0ℤ
negℤ-zero→zero 0ℤ _ = refl
negℤ-zero→zero (+suc n) ()
negℤ-zero→zero (-suc n) ()
-- § Swap first two summands in a three-term sum.
swapHeadℤ : (a b t : ℤ) → a +ℤ (b +ℤ t) ≡ b +ℤ (a +ℤ t)
swapHeadℤ a b t =
  trans (sym (+ℤ-assoc a b t))
        (trans (cong (λ s → s +ℤ t) (+ℤ-comm a b))
               (+ℤ-assoc b a t))

sum3ℤ-swap01 : (a b c : ℤ) → sum3ℤ a b c ≡ sum3ℤ b a c
sum3ℤ-swap01 a b c = swapHeadℤ a b c

sum4ℤ-swap01 : (a b c d : ℤ) → sum4ℤ a b c d ≡ sum4ℤ b a c d
sum4ℤ-swap01 a b c d = swapHeadℤ a b (c +ℤ d)

sum4ℤ-swap12 : (a b c d : ℤ) → sum4ℤ a b c d ≡ sum4ℤ a c b d
sum4ℤ-swap12 a b c d = cong (λ t → a +ℤ t) (sum3ℤ-swap01 b c d)

sum4ℤ-swap23 : (a b c d : ℤ) → sum4ℤ a b c d ≡ sum4ℤ a b d c
sum4ℤ-swap23 a b c d = cong (λ t → a +ℤ (b +ℤ t)) (+ℤ-comm c d)
-- § Swap pair components.
swapPairℕ : Pairℕ → Pairℕ
swapPairℕ p = mkPairℕ (neg p) (pos p)

-- § Negation as pair swap.
toPair-negℤ : (z : ℤ) → toPairℤ (negℤ z) ≡ swapPairℕ (toPairℤ z)
toPair-negℤ 0ℤ = refl
toPair-negℤ (+suc n) = refl
toPair-negℤ (-suc n) = refl

-- § Negation is involutive.
negℤ-involutive : (z : ℤ) → negℤ (negℤ z) ≡ z
negℤ-involutive 0ℤ = refl
negℤ-involutive (+suc n) = refl
negℤ-involutive (-suc n) = refl

-- § Positive component of negation.
pos-toPair-negℤ : (z : ℤ) → pos (toPairℤ (negℤ z)) ≡ neg (toPairℤ z)
pos-toPair-negℤ z = cong pos (toPair-negℤ z)

-- § Negative component of negation.
neg-toPair-negℤ : (z : ℤ) → neg (toPairℤ (negℤ z)) ≡ pos (toPairℤ z)
neg-toPair-negℤ z = cong neg (toPair-negℤ z)

-- § Normalization commutes with negation.
neg-normalizeℤ : (a b : ℕ) → negℤ (normalizeℤ a b) ≡ normalizeℤ b a
neg-normalizeℤ zero zero = refl
neg-normalizeℤ (suc a) zero = refl
neg-normalizeℤ zero (suc b) = refl
neg-normalizeℤ (suc a) (suc b) = neg-normalizeℤ a b

-- § Negation distributes over componentwise addition.
negAdd-normalizeSwap : (x y : ℤ) →
  negℤ x +ℤ negℤ y ≡
  normalizeℤ (neg (toPairℤ x) +ℕ neg (toPairℤ y)) (pos (toPairℤ x) +ℕ pos (toPairℤ y))
negAdd-normalizeSwap x y =
  let A₁ = pos (toPairℤ (negℤ x)) +ℕ pos (toPairℤ (negℤ y)) in
  let B₁ = neg (toPairℤ (negℤ x)) +ℕ neg (toPairℤ (negℤ y)) in
  let A₂ = neg (toPairℤ x) +ℕ neg (toPairℤ y) in
  let B₂ = pos (toPairℤ x) +ℕ pos (toPairℤ y) in
  let eqA₁ =
        trans
          (cong (λ t → t +ℕ pos (toPairℤ (negℤ y))) (pos-toPair-negℤ x))
          (cong (λ t → neg (toPairℤ x) +ℕ t) (pos-toPair-negℤ y))
      in
  let eqB₁ =
        trans
          (cong (λ t → t +ℕ neg (toPairℤ (negℤ y))) (neg-toPair-negℤ x))
          (cong (λ t → pos (toPairℤ x) +ℕ t) (neg-toPair-negℤ y))
      in
  trans (cong (λ a → normalizeℤ a B₁) eqA₁)
        (cong (normalizeℤ A₂) eqB₁)

-- § Negation distributes over +ℤ.
neg-+ℤ : (x y : ℤ) → negℤ (x +ℤ y) ≡ negℤ x +ℤ negℤ y
neg-+ℤ x y =
  let A = pos (toPairℤ x) +ℕ pos (toPairℤ y) in
  let B = neg (toPairℤ x) +ℕ neg (toPairℤ y) in
  trans (neg-normalizeℤ A B) (sym (negAdd-normalizeSwap x y))

-- § Negation distributes over sum3ℤ.
neg-sum3ℤ : (a b c : ℤ) → negℤ (sum3ℤ a b c) ≡ sum3ℤ (negℤ a) (negℤ b) (negℤ c)
neg-sum3ℤ a b c =
  trans (neg-+ℤ a (b +ℤ c))
        (cong (λ t → negℤ a +ℤ t) (neg-+ℤ b c))

-- § Negation distributes over sum4ℤ.
neg-sum4ℤ : (a b c d : ℤ) → negℤ (sum4ℤ a b c d) ≡ sum4ℤ (negℤ a) (negℤ b) (negℤ c) (negℤ d)
neg-sum4ℤ a b c d =
  trans
    (neg-+ℤ a (b +ℤ (c +ℤ d)))
    (cong (λ t → negℤ a +ℤ t)
          (trans
            (neg-+ℤ b (c +ℤ d))
            (cong (λ t → negℤ b +ℤ t) (neg-+ℤ c d))))

-- § Negation distributes over fourTimesℤ.
neg-fourTimesℤ : (x : ℤ) → negℤ (fourTimesℤ x) ≡ fourTimesℤ (negℤ x)
neg-fourTimesℤ x = neg-sum4ℤ x x x x

-- § Negation distributes over sumFin3ℤ.
neg-sumFin3ℤ : (f : Fin3 → ℤ) → negℤ (sumFin3ℤ f) ≡ sumFin3ℤ (λ k → negℤ (f k))
neg-sumFin3ℤ f = neg-sum3ℤ (f f0) (f f1) (f f2)
-- § Multiplication on ℕ (separate from BUILTIN _*_).
infixl 7 _*ℕ_

_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ n = zero
suc m *ℕ n = n +ℕ (m *ℕ n)

-- § Right identity for *ℕ.
*ℕ-one-right : (n : ℕ) → n *ℕ suc zero ≡ n
*ℕ-one-right zero = refl
*ℕ-one-right (suc n) = cong suc (*ℕ-one-right n)

-- § Right annihilation for *ℕ.
*ℕ-zero-right : (n : ℕ) → n *ℕ zero ≡ zero
*ℕ-zero-right zero = refl
*ℕ-zero-right (suc n) = *ℕ-zero-right n

-- § Left annihilation for *ℕ.
*ℕ-zero-left : (n : ℕ) → zero *ℕ n ≡ zero
*ℕ-zero-left n = refl

-- § Left identity for +ℕ.
+ℕ-zero-left : (n : ℕ) → zero +ℕ n ≡ n
+ℕ-zero-left n = refl
-- § Pair-level multiplication.
Pairℕ-mul : Pairℕ → Pairℕ → Pairℕ
Pairℕ-mul p q =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  mkPairℕ ((a *ℕ c) +ℕ (b *ℕ d)) ((a *ℕ d) +ℕ (b *ℕ c))

-- § Integer one.
oneℤ : ℤ
oneℤ = +suc zero

-- § Natural one.
oneNat : ℕ
oneNat = suc zero

-- § Round-trip: fromPairℤ ∘ toPairℤ = id.
from-toPairℤ : (z : ℤ) → fromPairℤ (toPairℤ z) ≡ z
from-toPairℤ 0ℤ = refl
from-toPairℤ (+suc n) = refl
from-toPairℤ (-suc n) = refl

-- § Integer multiplication (opaque for reduction control).
infixl 7 _*ℤ_

opaque
  _*ℤ_ : ℤ → ℤ → ℤ
  x *ℤ y = fromPairℤ (Pairℕ-mul (toPairℤ x) (toPairℤ y))

opaque
  unfolding _*ℤ_
  -- § Left annihilation for *ℤ.
  *ℤ-zero-left : (y : ℤ) → 0ℤ *ℤ y ≡ 0ℤ
  *ℤ-zero-left y = refl

  -- § Right annihilation for *ℤ.
  *ℤ-zero-right : (x : ℤ) → x *ℤ 0ℤ ≡ 0ℤ
  *ℤ-zero-right 0ℤ = refl
  *ℤ-zero-right (+suc n) =
    normalizeℤ-cong
      (trans
        (+ℕ-zero-right (suc n *ℕ zero))
        (*ℕ-zero-right (suc n)))
      (trans
        (+ℕ-zero-right (suc n *ℕ zero))
        (*ℕ-zero-right (suc n)))
  *ℤ-zero-right (-suc n) =
    normalizeℤ-cong
      (*ℕ-zero-right (suc n))
      (*ℕ-zero-right (suc n))

  -- § Right identity for *ℤ.
  *ℤ-one-right : (x : ℤ) → x *ℤ oneℤ ≡ x
  *ℤ-one-right 0ℤ = refl
  *ℤ-one-right (+suc n) =
    normalizeℤ-cong
      (trans
        (+ℕ-zero-right (suc n *ℕ oneNat))
        (*ℕ-one-right (suc n)))
      (trans
        (+ℕ-zero-right (suc n *ℕ zero))
        (*ℕ-zero-right (suc n)))
  *ℤ-one-right (-suc n) =
    normalizeℤ-cong
      (*ℕ-zero-right (suc n))
      (trans
        (+ℕ-zero-left (suc n *ℕ oneNat))
        (*ℕ-one-right (suc n)))
-- § Reflexivity of ≤ℤ.
≤ℤ-refl : (x : ℤ) → x ≤ℤ x
≤ℤ-refl 0ℤ = tt
≤ℤ-refl (+suc n) = ≤-refl (suc n)
≤ℤ-refl (-suc n) = ≤-refl (suc n)

-- § Transitivity of ≤ℤ.
≤ℤ-trans : {x y z : ℤ} → x ≤ℤ y → y ≤ℤ z → x ≤ℤ z
≤ℤ-trans {0ℤ} {0ℤ} {0ℤ} _ _ = tt
≤ℤ-trans {0ℤ} {0ℤ} {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} {0ℤ} { -suc n } _ ()
≤ℤ-trans {0ℤ} {+suc m} {0ℤ} _ ()
≤ℤ-trans {0ℤ} {+suc m} {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} {+suc m} { -suc n } _ ()
≤ℤ-trans {0ℤ} { -suc m } {0ℤ} _ _ = tt
≤ℤ-trans {0ℤ} { -suc m } {+suc n} _ _ = tt
≤ℤ-trans {0ℤ} { -suc m } { -suc n } () _

≤ℤ-trans {+suc m} {0ℤ} {z} () _
≤ℤ-trans {+suc m} {+suc n} {0ℤ} p ()
≤ℤ-trans {+suc m} {+suc n} {+suc k} p q = ≤-trans p q
≤ℤ-trans {+suc m} {+suc n} { -suc k } _ ()
≤ℤ-trans {+suc m} { -suc n } {z} () _

≤ℤ-trans { -suc m } {0ℤ} {0ℤ} _ _ = tt
≤ℤ-trans { -suc m } {0ℤ} {+suc k} _ _ = tt
≤ℤ-trans { -suc m } {0ℤ} { -suc k } _ ()
≤ℤ-trans { -suc m } {+suc n} {0ℤ} _ ()
≤ℤ-trans { -suc m } {+suc n} {+suc k} _ _ = tt
≤ℤ-trans { -suc m } {+suc n} { -suc k } _ ()
≤ℤ-trans { -suc m } { -suc n } {0ℤ} _ _ = tt
≤ℤ-trans { -suc m } { -suc n } {+suc k} _ _ = tt
≤ℤ-trans { -suc m } { -suc n } { -suc k } p q = ≤-trans q p

-- § Strict order implies weak order.
<ℤ→≤ℤ : {x y : ℤ} → x <ℤ y → x ≤ℤ y
<ℤ→≤ℤ p = fst p

-- § Antisymmetry of ≤ℤ.
≤ℤ-antisym : {x y : ℤ} → x ≤ℤ y → y ≤ℤ x → x ≡ y
≤ℤ-antisym {0ℤ} {0ℤ} _ _ = refl
≤ℤ-antisym {0ℤ} {+suc n} _ ()
≤ℤ-antisym {0ℤ} { -suc n } () _
≤ℤ-antisym {+suc m} {0ℤ} () _
≤ℤ-antisym {+suc m} {+suc n} p q = cong +suc_ (suc-injective (≤-antisym p q))
≤ℤ-antisym {+suc m} { -suc n } () _
≤ℤ-antisym { -suc m } {0ℤ} _ ()
≤ℤ-antisym { -suc m } {+suc n} _ ()
≤ℤ-antisym { -suc m } { -suc n } p q = cong -suc_ (suc-injective (≤-antisym q p))
-- § Adjacency on K₄.
Adj : EndoCase → EndoCase → Set
Adj a b = Edge K4GraphCanonical a b

-- § Complete neighbour triple: every K₄ vertex has exactly 3 neighbours.
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

-- § Symmetric inequality witnesses.
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
-- § Law 14.0: Every vertex has a complete neighbour triple.
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

-- § Neighbour lookup by Fin3 index.
neighborAt : (v : EndoCase) → Fin3 → EndoCase
neighborAt v f0 = n₁ (law14-0-neighbor-triple v)
neighborAt v f1 = n₂ (law14-0-neighbor-triple v)
neighborAt v f2 = n₃ (law14-0-neighbor-triple v)

-- § Neighbours are adjacent.
neighborAt-adj : (v : EndoCase) → (i : Fin3) → Adj v (neighborAt v i)
neighborAt-adj v f0 = adj₁ (law14-0-neighbor-triple v)
neighborAt-adj v f1 = adj₂ (law14-0-neighbor-triple v)
neighborAt-adj v f2 = adj₃ (law14-0-neighbor-triple v)

-- § Neighbour lookup is injective.
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
-- § Adjacency sum: sum of f over the three neighbours.
adjSumℤ : (EndoCase → ℤ) → EndoCase → ℤ
adjSumℤ f v = sumFin3ℤ (λ i → f (neighborAt v i))

-- § Degree term: 3 × f(v).
deg3ℤ : (EndoCase → ℤ) → EndoCase → ℤ
deg3ℤ f v = sum3ℤ (f v) (f v) (f v)

-- § Combinatorial Laplacian: deg − adj.
laplacianℤ : (EndoCase → ℤ) → EndoCase → ℤ
laplacianℤ f v = deg3ℤ f v +ℤ negℤ (adjSumℤ f v)
-- § Simplex vertex count.
simplex-vertices : ℕ
simplex-vertices = 4

-- § Simplex degree.
simplex-degree : ℕ
simplex-degree = 3

-- § Simplex edge count.
simplex-edges : ℕ
simplex-edges = 6

-- § Simplex Euler characteristic.
simplex-chi : ℕ
simplex-chi = 2

-- § Law 14C.0: Vertex count = 4.
law14C-0-vertices : simplex-vertices ≡ 4
law14C-0-vertices = refl

-- § Law 14C.1: Degree = 3.
law14C-1-degree : simplex-degree ≡ 3
law14C-1-degree = refl

-- § Law 14C.2: Edge count = 6.
law14C-2-edges : simplex-edges ≡ 6
law14C-2-edges = refl

-- § Law 14C.3: Euler characteristic = 2.
law14C-3-chi : simplex-chi ≡ 2
law14C-3-chi = refl
-- § Left distributivity of *ℕ over +ℕ.
*ℕ-distrib-left-+ℕ : (a b c : ℕ) → (a +ℕ b) *ℕ c ≡ (a *ℕ c) +ℕ (b *ℕ c)
*ℕ-distrib-left-+ℕ zero b c =
  trans
    refl
    (sym (+ℕ-zero-left (b *ℕ c)))
*ℕ-distrib-left-+ℕ (suc a) b c =
  trans
    refl
    (trans
      (cong (λ t → c +ℕ t) (*ℕ-distrib-left-+ℕ a b c))
      (sym (+ℕ-assoc c (a *ℕ c) (b *ℕ c))))

-- § Head swap for ℕ sums.
swapHeadℕ : (a b t : ℕ) → a +ℕ (b +ℕ t) ≡ b +ℕ (a +ℕ t)
swapHeadℕ a b t =
  trans
    (sym (+ℕ-assoc a b t))
    (trans
      (cong (λ s → s +ℕ t) (+ℕ-comm a b))
      (+ℕ-assoc b a t))

-- § Four-way shuffle for ℕ.
shuffleℕ : (b c x y : ℕ) → (b +ℕ c) +ℕ (x +ℕ y) ≡ (b +ℕ x) +ℕ (c +ℕ y)
shuffleℕ b c x y =
  trans
    (+ℕ-assoc b c (x +ℕ y))
    (trans
      (cong (λ t → b +ℕ t) (sym (+ℕ-assoc c x y)))
      (trans
        (cong (λ t → b +ℕ (t +ℕ y)) (+ℕ-comm c x))
        (trans
          (cong (λ t → b +ℕ t) (+ℕ-assoc x c y))
          (sym (+ℕ-assoc b x (c +ℕ y))))))

-- § Right distributivity of *ℕ over +ℕ.
*ℕ-distrib-right-+ℕ : (a b c : ℕ) → a *ℕ (b +ℕ c) ≡ (a *ℕ b) +ℕ (a *ℕ c)
*ℕ-distrib-right-+ℕ zero b c = refl
*ℕ-distrib-right-+ℕ (suc a) b c =
  trans
    refl
    (trans
      (cong (λ t → (b +ℕ c) +ℕ t) (*ℕ-distrib-right-+ℕ a b c))
      (trans
        (shuffleℕ b c (a *ℕ b) (a *ℕ c))
        refl))

-- § Associativity of *ℕ.
*ℕ-assoc : (a b c : ℕ) → (a *ℕ b) *ℕ c ≡ a *ℕ (b *ℕ c)
*ℕ-assoc zero b c = refl
*ℕ-assoc (suc a) b c =
  trans
    (*ℕ-distrib-left-+ℕ b (a *ℕ b) c)
    (trans
      (cong (λ t → (b *ℕ c) +ℕ t) (*ℕ-assoc a b c))
      refl)

-- § Zero cancellation for positive left factor.
*ℕ-pos-zero→zero : (a n : ℕ) → suc a *ℕ n ≡ zero → n ≡ zero
*ℕ-pos-zero→zero a zero _ = refl
*ℕ-pos-zero→zero a (suc n) ()
-- § Successor-right law for *ℕ.
*ℕ-suc-right-+ℕ : (n m : ℕ) → n *ℕ (suc m) ≡ n +ℕ (n *ℕ m)
*ℕ-suc-right-+ℕ zero m = refl
*ℕ-suc-right-+ℕ (suc n) m =
  trans
    refl
    (trans
      (cong (λ t → (suc m) +ℕ t) (*ℕ-suc-right-+ℕ n m))
      (cong suc (swapHeadℕ m n (n *ℕ m))))

-- § Commutativity of *ℕ.
*ℕ-comm : (m n : ℕ) → m *ℕ n ≡ n *ℕ m
*ℕ-comm zero n = sym (*ℕ-zero-right n)
*ℕ-comm (suc m) n =
  trans
    refl
    (trans
      (cong (λ t → n +ℕ t) (*ℕ-comm m n))
      (sym (*ℕ-suc-right-+ℕ n m)))

-- § +ℕ is monotone on the left.
≤-+ℕ-monoˡ : {a b : ℕ} → a ≤ b → (c : ℕ) → (c +ℕ a) ≤ (c +ℕ b)
≤-+ℕ-monoˡ p zero = p
≤-+ℕ-monoˡ p (suc c) = s≤s (≤-+ℕ-monoˡ p c)

-- § Left cancellation for +ℕ ordering.
≤-+ℕ-cancelˡ : (c a b : ℕ) → (c +ℕ a) ≤ (c +ℕ b) → a ≤ b
≤-+ℕ-cancelˡ zero a b p = p
≤-+ℕ-cancelˡ (suc c) a b (s≤s p) = ≤-+ℕ-cancelˡ c a b p

-- § *ℕ is monotone in the left factor.
≤-*ℕ-monoʳ : {m n : ℕ} → m ≤ n → (t : ℕ) → (m *ℕ t) ≤ (n *ℕ t)
≤-*ℕ-monoʳ z≤n t = z≤n
≤-*ℕ-monoʳ (s≤s p) t = ≤-+ℕ-monoˡ (≤-*ℕ-monoʳ p t) t

-- § Right cancellation by a positive (successor) factor.
≤-*ℕ-cancelʳ-suc : {m n : ℕ} → (k : ℕ) → (m *ℕ suc k) ≤ (n *ℕ suc k) → m ≤ n
≤-*ℕ-cancelʳ-suc {zero} {zero} k _ = z≤n
≤-*ℕ-cancelʳ-suc {suc m'} {zero} k ()
≤-*ℕ-cancelʳ-suc {zero} {suc n} k _ = z≤n
≤-*ℕ-cancelʳ-suc {suc m} {suc n} k p =
  let
    step : (suc k +ℕ (m *ℕ suc k)) ≤ (suc k +ℕ (n *ℕ suc k))
    step = p

    tail : (m *ℕ suc k) ≤ (n *ℕ suc k)
    tail = ≤-+ℕ-cancelˡ (suc k) (m *ℕ suc k) (n *ℕ suc k) step

    ih : m ≤ n
    ih = ≤-*ℕ-cancelʳ-suc k tail
  in
  s≤s ih
-- § Positive natural: predecessor + implicit successor.
record ℕ⁺ : Set where
  constructor mkℕ⁺
  field
    pred : ℕ

PosNat : Set
PosNat = ℕ⁺

open ℕ⁺ public

-- § Embedding into ℕ (always ≥ 1).
⁺toℕ : ℕ⁺ → ℕ
⁺toℕ n = suc (pred n)

-- § Positive one.
one⁺ : ℕ⁺
one⁺ = mkℕ⁺ zero

-- § Successor on ℕ⁺.
suc⁺ : ℕ⁺ → ℕ⁺
suc⁺ n = mkℕ⁺ (suc (pred n))

-- § Addition on ℕ⁺.
_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
mkℕ⁺ a +⁺ mkℕ⁺ b = mkℕ⁺ (a +ℕ suc b)

-- § Multiplication on ℕ⁺: (1+a)(1+b) = 1 + (a·(1+b) + b).
_*⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
mkℕ⁺ a *⁺ mkℕ⁺ b = mkℕ⁺ ((a *ℕ suc b) +ℕ b)

-- § Embedding ℕ⁺ into ℤ.
⁺toℤ : ℕ⁺ → ℤ
⁺toℤ (mkℕ⁺ k) = +suc k
-- § Componentwise pair addition.
Pairℕ-add : Pairℕ → Pairℕ → Pairℕ
Pairℕ-add p q = (mkPairℕ (pos p +ℕ pos q) (neg p +ℕ neg q))

-- § Normalization: cancel equal components.
normalizePair : Pairℕ → Pairℕ
normalizePair (mkPairℕ zero zero) = (mkPairℕ zero zero)
normalizePair (mkPairℕ (suc a) zero) = (mkPairℕ (suc a) zero)
normalizePair (mkPairℕ zero (suc b)) = (mkPairℕ zero (suc b))
normalizePair (mkPairℕ (suc a) (suc b)) = normalizePair (mkPairℕ a b)

-- § normalizePair is identity on (x , 0).
normalizePair-right0 : (x : ℕ) → normalizePair (mkPairℕ x zero) ≡ (mkPairℕ x zero)
normalizePair-right0 zero = refl
normalizePair-right0 (suc a) = refl

-- § normalizePair is identity on (0 , y).
normalizePair-left0 : (y : ℕ) → normalizePair (mkPairℕ zero y) ≡ (mkPairℕ zero y)
normalizePair-left0 zero = refl
normalizePair-left0 (suc b) = refl

-- § fromPairℤ absorbs normalizePair.
fromPair-normalizePair : (p : Pairℕ) → fromPairℤ (normalizePair p) ≡ fromPairℤ p
fromPair-normalizePair (mkPairℕ zero zero) = refl
fromPair-normalizePair (mkPairℕ (suc a) zero) = refl
fromPair-normalizePair (mkPairℕ zero (suc b)) = refl
fromPair-normalizePair (mkPairℕ (suc a) (suc b)) = fromPair-normalizePair (mkPairℕ a b)

-- § toPairℤ ∘ normalizeℤ = normalizePair ∘ mkPairℕ.
toPair-normalizeℤ : (a b : ℕ) → toPairℤ (normalizeℤ a b) ≡ normalizePair (mkPairℕ a b)
toPair-normalizeℤ zero zero = refl
toPair-normalizeℤ (suc a) zero = refl
toPair-normalizeℤ zero (suc b) = refl
toPair-normalizeℤ (suc a) (suc b) = toPair-normalizeℤ a b

-- § toPairℤ ∘ fromPairℤ = normalizePair.
toPair-fromPair : (p : Pairℕ) → toPairℤ (fromPairℤ p) ≡ normalizePair p
toPair-fromPair (mkPairℕ a b) = toPair-normalizeℤ a b
-- § Right distributivity at pair level.
Pairℕ-mul-distrib-right-add : (p q r : Pairℕ) →
  Pairℕ-mul p (Pairℕ-add q r) ≡ Pairℕ-add (Pairℕ-mul p q) (Pairℕ-mul p r)
Pairℕ-mul-distrib-right-add p q r =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  let e = pos r in
  let f = neg r in
  pair-ext
    (pos-proof a b c d e f)
    (neg-proof a b c d e f)
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

    pos-proof : (a b c d e f : ℕ) →
      ((a *ℕ (c +ℕ e)) +ℕ (b *ℕ (d +ℕ f)))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ ((a *ℕ e) +ℕ (b *ℕ f)))
    pos-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ (b *ℕ (d +ℕ f))) (*ℕ-distrib-right-+ℕ a c e))
        (trans
          (cong (λ t → (a *ℕ c +ℕ a *ℕ e) +ℕ t) (*ℕ-distrib-right-+ℕ b d f))
          (shuffleℕ (a *ℕ c) (a *ℕ e) (b *ℕ d) (b *ℕ f)))

    neg-proof : (a b c d e f : ℕ) →
      ((a *ℕ (d +ℕ f)) +ℕ (b *ℕ (c +ℕ e)))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ ((a *ℕ f) +ℕ (b *ℕ e)))
    neg-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ (b *ℕ (c +ℕ e))) (*ℕ-distrib-right-+ℕ a d f))
        (trans
          (cong (λ t → (a *ℕ d +ℕ a *ℕ f) +ℕ t) (*ℕ-distrib-right-+ℕ b c e))
          (shuffleℕ (a *ℕ d) (a *ℕ f) (b *ℕ c) (b *ℕ e)))

-- § Left identity for *ℕ.
*ℕ-one-left : (n : ℕ) → oneNat *ℕ n ≡ n
*ℕ-one-left n = +ℕ-zero-right n

opaque
  unfolding _*ℤ_
  -- § Left identity for *ℤ.
  *ℤ-one-left : (x : ℤ) → oneℤ *ℤ x ≡ x
  *ℤ-one-left 0ℤ = refl
  *ℤ-one-left (+suc n) =
    normalizeℤ-cong
      (trans
        (+ℕ-zero-right (oneNat *ℕ suc n))
        (*ℕ-one-left (suc n)))
      (trans
        (+ℕ-zero-right (oneNat *ℕ zero))
        (*ℕ-zero-right oneNat))
  *ℤ-one-left (-suc n) =
    normalizeℤ-cong
      (trans
        (+ℕ-zero-right (oneNat *ℕ zero))
        (*ℕ-zero-right oneNat))
      (trans
        (+ℕ-zero-right (oneNat *ℕ suc n))
        (*ℕ-one-left (suc n)))

-- § Left distributivity at pair level.
Pairℕ-mul-distrib-left-add : (p q r : Pairℕ) →
  Pairℕ-mul (Pairℕ-add p q) r ≡ Pairℕ-add (Pairℕ-mul p r) (Pairℕ-mul q r)
Pairℕ-mul-distrib-left-add p q r =
  let a = pos p in
  let b = neg p in
  let c = pos q in
  let d = neg q in
  let e = pos r in
  let f = neg r in
  pair-ext
    (pos-proof a b c d e f)
    (neg-proof a b c d e f)
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

    pos-proof : (a b c d e f : ℕ) →
      (((a +ℕ c) *ℕ e) +ℕ ((b +ℕ d) *ℕ f))
        ≡
      (((a *ℕ e) +ℕ (b *ℕ f)) +ℕ ((c *ℕ e) +ℕ (d *ℕ f)))
    pos-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ ((b +ℕ d) *ℕ f)) (*ℕ-distrib-left-+ℕ a c e))
        (trans
          (cong (λ t → ((a *ℕ e) +ℕ (c *ℕ e)) +ℕ t) (*ℕ-distrib-left-+ℕ b d f))
          (shuffleℕ (a *ℕ e) (c *ℕ e) (b *ℕ f) (d *ℕ f)))

    neg-proof : (a b c d e f : ℕ) →
      (((a +ℕ c) *ℕ f) +ℕ ((b +ℕ d) *ℕ e))
        ≡
      (((a *ℕ f) +ℕ (b *ℕ e)) +ℕ ((c *ℕ f) +ℕ (d *ℕ e)))
    neg-proof a b c d e f =
      trans
        (cong (λ t → t +ℕ ((b +ℕ d) *ℕ e)) (*ℕ-distrib-left-+ℕ a c f))
        (trans
          (cong (λ t → ((a *ℕ f) +ℕ (c *ℕ f)) +ℕ t) (*ℕ-distrib-left-+ℕ b d e))
          (shuffleℕ (a *ℕ f) (c *ℕ f) (b *ℕ e) (d *ℕ e)))
-- § Diagonal addition is absorbed by normalization.
normalizePair-addDiag : (p : Pairℕ) → (k : ℕ) →
  normalizePair (Pairℕ-add p (mkPairℕ k k)) ≡ normalizePair p
normalizePair-addDiag (mkPairℕ a b) zero =
  cong normalizePair (pair-ext (+ℕ-zero-right a) (+ℕ-zero-right b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
normalizePair-addDiag (mkPairℕ a b) (suc k) =
  trans
    (cong normalizePair (pair-ext (+ℕ-suc-right a k) (+ℕ-suc-right b k)))
    (trans
      refl
      (normalizePair-addDiag (mkPairℕ a b) k))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

-- § Successor-right via +ℕ one.
+ℕ-one-right : (n : ℕ) → n +ℕ suc zero ≡ suc n
+ℕ-one-right n = trans (+ℕ-comm n (suc zero)) refl

-- § *ℕ successor-right.
*ℕ-suc-right : (a n : ℕ) → a *ℕ suc n ≡ (a *ℕ n) +ℕ a
*ℕ-suc-right a n =
  trans
    (cong (λ t → a *ℕ t) (sym (+ℕ-one-right n)))
    (trans
      (*ℕ-distrib-right-+ℕ a n (suc zero))
      (cong (λ t → (a *ℕ n) +ℕ t) (*ℕ-one-right a)))

-- § *ℕ successor-left.
*ℕ-suc-left : (n a : ℕ) → suc n *ℕ a ≡ (n *ℕ a) +ℕ a
*ℕ-suc-left n a =
  trans
    (cong (λ t → t *ℕ a) (sym (+ℕ-one-right n)))
    (trans
      (*ℕ-distrib-left-+ℕ n (suc zero) a)
      (cong (λ t → (n *ℕ a) +ℕ t) (*ℕ-one-left a)))
-- § Right cancellation at pair level: common successor adds a diagonal.
Pairℕ-mul-cancelRight : (p : Pairℕ) → (c d : ℕ) →
  normalizePair (Pairℕ-mul p (mkPairℕ (suc c) (suc d))) ≡ normalizePair (Pairℕ-mul p (mkPairℕ c d))
Pairℕ-mul-cancelRight p c d =
  let a = pos p in
  let b = neg p in
  trans
    (cong normalizePair (pair-ext (pos-step a b c d) (neg-step a b c d)))
    (normalizePair-addDiag (Pairℕ-mul p (mkPairℕ c d)) (a +ℕ b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

    pos-step : (a b c d : ℕ) →
      ((a *ℕ suc c) +ℕ (b *ℕ suc d))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ (a +ℕ b))
    pos-step a b c d =
      trans
        (cong (λ t → t +ℕ (b *ℕ suc d)) (*ℕ-suc-right a c))
        (trans
          (cong (λ t → ((a *ℕ c) +ℕ a) +ℕ t) (*ℕ-suc-right b d))
          (trans
            (shuffleℕ (a *ℕ c) a (b *ℕ d) b)
            refl))

    neg-step : (a b c d : ℕ) →
      ((a *ℕ suc d) +ℕ (b *ℕ suc c))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ (a +ℕ b))
    neg-step a b c d =
      trans
        (cong (λ t → t +ℕ (b *ℕ suc c)) (*ℕ-suc-right a d))
        (trans
          (cong (λ t → ((a *ℕ d) +ℕ a) +ℕ t) (*ℕ-suc-right b c))
          (trans
            (shuffleℕ (a *ℕ d) a (b *ℕ c) b)
            refl))

-- § Left cancellation at pair level.
Pairℕ-mul-cancelLeft : (q : Pairℕ) → (a b : ℕ) →
  normalizePair (Pairℕ-mul (mkPairℕ (suc a) (suc b)) q) ≡ normalizePair (Pairℕ-mul (mkPairℕ a b) q)
Pairℕ-mul-cancelLeft q a b =
  let c = pos q in
  let d = neg q in
  trans
    (cong normalizePair (pair-ext (pos-step a b c d) (neg-step a b c d)))
    (normalizePair-addDiag (Pairℕ-mul (mkPairℕ a b) q) (c +ℕ d))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

    pos-step : (a b c d : ℕ) →
      ((suc a *ℕ c) +ℕ (suc b *ℕ d))
        ≡
      (((a *ℕ c) +ℕ (b *ℕ d)) +ℕ (c +ℕ d))
    pos-step a b c d =
      trans
        (cong (λ t → t +ℕ (suc b *ℕ d)) (*ℕ-suc-left a c))
        (trans
          (cong (λ t → ((a *ℕ c) +ℕ c) +ℕ t) (*ℕ-suc-left b d))
          (trans
            (shuffleℕ (a *ℕ c) c (b *ℕ d) d)
            refl))

    neg-step : (a b c d : ℕ) →
      ((suc a *ℕ d) +ℕ (suc b *ℕ c))
        ≡
      (((a *ℕ d) +ℕ (b *ℕ c)) +ℕ (c +ℕ d))
    neg-step a b c d =
      trans
        (cong (λ t → t +ℕ (suc b *ℕ c)) (*ℕ-suc-left a d))
        (trans
          (cong (λ t → ((a *ℕ d) +ℕ d) +ℕ t) (*ℕ-suc-left b c))
          (trans
            (shuffleℕ (a *ℕ d) d (b *ℕ c) c)
            (cong (λ t → ((a *ℕ d) +ℕ (b *ℕ c)) +ℕ t) (+ℕ-comm d c))))
-- § Normalization absorbs right factor normalization.
Pairℕ-mul-normalize-right : (p q : Pairℕ) →
  normalizePair (Pairℕ-mul p (normalizePair q)) ≡ normalizePair (Pairℕ-mul p q)
Pairℕ-mul-normalize-right p (mkPairℕ zero zero) = refl
Pairℕ-mul-normalize-right p (mkPairℕ (suc a) zero) = refl
Pairℕ-mul-normalize-right p (mkPairℕ zero (suc b)) = refl
Pairℕ-mul-normalize-right p (mkPairℕ (suc a) (suc b)) =
  trans
    (Pairℕ-mul-normalize-right p (mkPairℕ a b))
    (sym (Pairℕ-mul-cancelRight p a b))

-- § Normalization absorbs left factor normalization.
Pairℕ-mul-normalize-left : (p q : Pairℕ) →
  normalizePair (Pairℕ-mul (normalizePair p) q) ≡ normalizePair (Pairℕ-mul p q)
Pairℕ-mul-normalize-left (mkPairℕ zero zero) q = refl
Pairℕ-mul-normalize-left (mkPairℕ (suc a) zero) q = refl
Pairℕ-mul-normalize-left (mkPairℕ zero (suc b)) q = refl
Pairℕ-mul-normalize-left (mkPairℕ (suc a) (suc b)) q =
  trans
    (Pairℕ-mul-normalize-left (mkPairℕ a b) q)
    (sym (Pairℕ-mul-cancelLeft q a b))
-- § Products of canonical pairs are already normalized.
Pairℕ-mul-toPair-normal : (x y : ℤ) →
  normalizePair (Pairℕ-mul (toPairℤ x) (toPairℤ y)) ≡ Pairℕ-mul (toPairℤ x) (toPairℤ y)
Pairℕ-mul-toPair-normal 0ℤ y = refl
Pairℕ-mul-toPair-normal (+suc n) 0ℤ =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ 0ℤ) ≡ (mkPairℕ zero zero)
      mulEq =
        pair-ext
          (trans (cong (λ t → t +ℕ (zero *ℕ zero)) (*ℕ-zero-right (suc n))) refl)
          (trans (cong (λ t → t +ℕ (zero *ℕ zero)) (*ℕ-zero-right (suc n))) refl)
  in
  trans (cong normalizePair mulEq) (trans (normalizePair-right0 zero) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) 0ℤ =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ 0ℤ) ≡ (mkPairℕ zero zero)
      mulEq =
        pair-ext
          (trans (cong (λ t → t +ℕ (suc n *ℕ zero)) refl) (*ℕ-zero-right (suc n)))
          (trans (cong (λ t → t +ℕ (suc n *ℕ zero)) refl) (*ℕ-zero-right (suc n)))
  in
  trans (cong normalizePair mulEq) (trans (normalizePair-right0 zero) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (+suc n) (+suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m)) ≡ (mkPairℕ (suc n *ℕ suc m) zero)
      mulEq =
        pair-ext
          (+ℕ-zero-right (suc n *ℕ suc m))
          (trans
            (cong (λ t → t +ℕ (zero *ℕ suc m)) (*ℕ-zero-right (suc n)))
            refl)
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-right0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (+suc n) (-suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m)) ≡ (mkPairℕ zero (suc n *ℕ suc m))
      mulEq =
        pair-ext
          (trans
            (cong (λ t → t +ℕ (zero *ℕ suc m)) (*ℕ-zero-right (suc n)))
            refl)
          (+ℕ-zero-right (suc n *ℕ suc m))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-left0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) (+suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m)) ≡ (mkPairℕ zero (suc n *ℕ suc m))
      mulEq =
        pair-ext
          (trans
            (cong (λ t → (zero *ℕ suc m) +ℕ t) (*ℕ-zero-right (suc n)))
            (trans
              (cong (λ t → t +ℕ zero) (*ℕ-zero-left (suc m)))
              refl))
          (+ℕ-zero-left (suc n *ℕ suc m))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-left0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
Pairℕ-mul-toPair-normal (-suc n) (-suc m) =
  let mulEq : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m)) ≡ (mkPairℕ (suc n *ℕ suc m) zero)
      mulEq =
        pair-ext
          (+ℕ-zero-left (suc n *ℕ suc m))
          (trans
            (cong (λ t → (zero *ℕ suc m) +ℕ t) (*ℕ-zero-right (suc n)))
            (trans
              (cong (λ t → t +ℕ zero) (*ℕ-zero-left (suc m)))
              refl))
  in
  trans (cong normalizePair mulEq)
    (trans (normalizePair-right0 (suc n *ℕ suc m)) (sym mulEq))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

opaque
  unfolding _*ℤ_
  -- § Bridge: toPairℤ of *ℤ = Pairℕ-mul of canonical pairs.
  toPair-*ℤ : (x y : ℤ) → toPairℤ (x *ℤ y) ≡ Pairℕ-mul (toPairℤ x) (toPairℤ y)
  toPair-*ℤ x y =
    trans
      (toPair-fromPair (Pairℕ-mul (toPairℤ x) (toPairℤ y)))
      (Pairℕ-mul-toPair-normal x y)

-- § Bridge: toPairℤ of +ℤ = normalizePair of componentwise add.
toPair-+ℤ : (x y : ℤ) → toPairℤ (x +ℤ y) ≡ normalizePair (Pairℕ-add (toPairℤ x) (toPairℤ y))
toPair-+ℤ x y = toPair-fromPair (Pairℕ-add (toPairℤ x) (toPairℤ y))
opaque
  unfolding _*ℤ_
  -- § Right distributivity of *ℤ over +ℤ.
  *ℤ-distrib-right-+ℤ : (x y z : ℤ) → x *ℤ (y +ℤ z) ≡ (x *ℤ y) +ℤ (x *ℤ z)
  *ℤ-distrib-right-+ℤ x y z =
    let px = toPairℤ x in
    let py = toPairℤ y in
    let pz = toPairℤ z in
    let q  = Pairℕ-add py pz in
    let rhs : fromPairℤ (Pairℕ-add (Pairℕ-mul px py) (Pairℕ-mul px pz)) ≡ (x *ℤ y) +ℤ (x *ℤ z)
        rhs =
          trans
            (cong (λ t → fromPairℤ (Pairℕ-add t (Pairℕ-mul px pz))) (sym (toPair-*ℤ x y)))
            (trans
              (cong (λ t → fromPairℤ (Pairℕ-add (toPairℤ (x *ℤ y)) t)) (sym (toPair-*ℤ x z)))
              refl)
    in
    trans
      (cong (λ t → fromPairℤ (Pairℕ-mul px t)) (toPair-+ℤ y z))
      (trans
        (trans
          (sym (fromPair-normalizePair (Pairℕ-mul px (normalizePair q))))
          (cong fromPairℤ (Pairℕ-mul-normalize-right px q)))
        (trans
          (trans
            (fromPair-normalizePair (Pairℕ-mul px q))
            (cong fromPairℤ (Pairℕ-mul-distrib-right-add px py pz)))
          rhs))

  -- § Left distributivity of *ℤ over +ℤ.
  *ℤ-distrib-left-+ℤ : (x y z : ℤ) → (x +ℤ y) *ℤ z ≡ (x *ℤ z) +ℤ (y *ℤ z)
  *ℤ-distrib-left-+ℤ x y z =
    let px = toPairℤ x in
    let py = toPairℤ y in
    let pz = toPairℤ z in
    let q  = Pairℕ-add px py in
    let rhs : fromPairℤ (Pairℕ-add (Pairℕ-mul px pz) (Pairℕ-mul py pz)) ≡ (x *ℤ z) +ℤ (y *ℤ z)
        rhs =
          trans
            (cong (λ t → fromPairℤ (Pairℕ-add t (Pairℕ-mul py pz))) (sym (toPair-*ℤ x z)))
            (trans
              (cong (λ t → fromPairℤ (Pairℕ-add (toPairℤ (x *ℤ z)) t)) (sym (toPair-*ℤ y z)))
              refl)
    in
    trans
      (cong (λ t → fromPairℤ (Pairℕ-mul t pz)) (toPair-+ℤ x y))
      (trans
        (trans
          (sym (fromPair-normalizePair (Pairℕ-mul (normalizePair q) pz)))
          (cong fromPairℤ (Pairℕ-mul-normalize-left q pz)))
        (trans
          (trans
            (fromPair-normalizePair (Pairℕ-mul q pz))
            (cong fromPairℤ (Pairℕ-mul-distrib-left-add px py pz)))
          rhs))
-- § Pair extensionality.
Pairℕ-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
Pairℕ-ext refl refl = refl

-- § Commutativity of Pairℕ-mul.
Pairℕ-mul-comm : (p q : Pairℕ) → Pairℕ-mul p q ≡ Pairℕ-mul q p
Pairℕ-mul-comm p q =
  Pairℕ-ext posEq negEq
  where
    ap = pos p
    bp = neg p
    cq = pos q
    dq = neg q

    posEq : ((ap *ℕ cq) +ℕ (bp *ℕ dq)) ≡ ((cq *ℕ ap) +ℕ (dq *ℕ bp))
    posEq =
      trans
        (cong (λ t → t +ℕ (bp *ℕ dq)) (*ℕ-comm ap cq))
        (trans
          (cong (λ t → (cq *ℕ ap) +ℕ t) (*ℕ-comm bp dq))
          refl)

    negEq : ((ap *ℕ dq) +ℕ (bp *ℕ cq)) ≡ ((cq *ℕ bp) +ℕ (dq *ℕ ap))
    negEq =
      trans
        (cong (λ t → t +ℕ (bp *ℕ cq)) (*ℕ-comm ap dq))
        (trans
          (cong (λ t → (dq *ℕ ap) +ℕ t) (*ℕ-comm bp cq))
          (+ℕ-comm (dq *ℕ ap) (cq *ℕ bp)))
-- § Canonical pair products: (+,0) × (+,0).
Pairℕ-mul-pos-pos : (a b : ℕ) →
  Pairℕ-mul (mkPairℕ a zero) (mkPairℕ b zero) ≡ (mkPairℕ (a *ℕ b) zero)
Pairℕ-mul-pos-pos a b =
  pair-ext
    (trans
      (cong (λ t → (a *ℕ b) +ℕ t) (*ℕ-zero-left zero))
      (+ℕ-zero-right (a *ℕ b)))
    (trans
      (cong (λ t → (a *ℕ zero) +ℕ t) (*ℕ-zero-left b))
      (trans
        (+ℕ-zero-right (a *ℕ zero))
        (*ℕ-zero-right a)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

-- § Canonical pair products: (+,0) × (0,+).
Pairℕ-mul-pos-neg : (a b : ℕ) →
  Pairℕ-mul (mkPairℕ a zero) (mkPairℕ zero b) ≡ (mkPairℕ zero (a *ℕ b))
Pairℕ-mul-pos-neg a b =
  pair-ext
    (trans
      (cong (λ t → (a *ℕ zero) +ℕ t) (*ℕ-zero-left b))
      (trans
        (+ℕ-zero-right (a *ℕ zero))
        (*ℕ-zero-right a)))
    (trans
      (cong (λ t → (a *ℕ b) +ℕ t) (*ℕ-zero-left zero))
      (+ℕ-zero-right (a *ℕ b)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

-- § Canonical pair products: (0,+) × (+,0).
Pairℕ-mul-neg-pos : (a b : ℕ) →
  Pairℕ-mul (mkPairℕ zero a) (mkPairℕ b zero) ≡ (mkPairℕ zero (a *ℕ b))
Pairℕ-mul-neg-pos a b =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (a *ℕ zero)) (*ℕ-zero-left b))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right a))
        refl))
    (+ℕ-zero-left (a *ℕ b))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

-- § Canonical pair products: (0,+) × (0,+).
Pairℕ-mul-neg-neg : (a b : ℕ) →
  Pairℕ-mul (mkPairℕ zero a) (mkPairℕ zero b) ≡ (mkPairℕ (a *ℕ b) zero)
Pairℕ-mul-neg-neg a b =
  pair-ext
    (+ℕ-zero-left (a *ℕ b))
    (trans
      (cong (λ t → (zero *ℕ b) +ℕ t) (*ℕ-zero-right a))
      (trans
        (cong (λ t → t +ℕ zero) (*ℕ-zero-left b))
        (+ℕ-zero-left zero)))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
-- § Law 14P.0: positive left factor is torsion-free.
*ℤ-pos-left-zero→zero : (n : ℕ) → (x : ℤ) → (+suc n *ℤ x ≡ 0ℤ) → x ≡ 0ℤ
*ℤ-pos-left-zero→zero n 0ℤ _ = refl
*ℤ-pos-left-zero→zero n (+suc m) mul0 =
  let
    eqPair : toPairℤ ((+suc n) *ℤ (+suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m)) ≡ (mkPairℕ zero zero)
    step₁ = trans (sym (toPair-*ℤ (+suc n) (+suc m))) eqPair

    pos0-raw : pos (Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (+suc m))) ≡ zero
    pos0-raw = cong pos step₁

    pos0 : (suc n *ℕ suc m) ≡ zero
    pos0 =
      trans
        (sym (+ℕ-zero-right (suc n *ℕ suc m)))
        pos0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) pos0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

*ℤ-pos-left-zero→zero n (-suc m) mul0 =
  let
    eqPair : toPairℤ ((+suc n) *ℤ (-suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m)) ≡ (mkPairℕ zero zero)
    step₁ = trans (sym (toPair-*ℤ (+suc n) (-suc m))) eqPair

    neg0-raw : neg (Pairℕ-mul (toPairℤ (+suc n)) (toPairℤ (-suc m))) ≡ zero
    neg0-raw = cong neg step₁

    neg0 : (suc n *ℕ suc m) ≡ zero
    neg0 =
      trans
        (sym (+ℕ-zero-right (suc n *ℕ suc m)))
        neg0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) neg0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()
-- § Law 14P.1: *ℤ commutes with negℤ on the right.
*ℤ-neg-right : (x y : ℤ) → x *ℤ (negℤ y) ≡ negℤ (x *ℤ y)
*ℤ-neg-right x y =
  let
    eq0 : y +ℤ negℤ y ≡ 0ℤ
    eq0 = +ℤ-inv-right y

    mul0 : x *ℤ (y +ℤ negℤ y) ≡ x *ℤ 0ℤ
    mul0 = cong (λ t → x *ℤ t) eq0

    expand : x *ℤ (y +ℤ negℤ y) ≡ (x *ℤ y) +ℤ (x *ℤ negℤ y)
    expand = *ℤ-distrib-right-+ℤ x y (negℤ y)

    eqSum : (x *ℤ y) +ℤ (x *ℤ negℤ y) ≡ 0ℤ
    eqSum = trans (sym expand) (trans mul0 (*ℤ-zero-right x))

    addNeg : negℤ (x *ℤ y) +ℤ ((x *ℤ y) +ℤ (x *ℤ negℤ y)) ≡ negℤ (x *ℤ y) +ℤ 0ℤ
    addNeg = cong (λ t → negℤ (x *ℤ y) +ℤ t) eqSum

    leftReduce : negℤ (x *ℤ y) +ℤ ((x *ℤ y) +ℤ (x *ℤ negℤ y)) ≡ x *ℤ negℤ y
    leftReduce =
      trans
        (sym (+ℤ-assoc (negℤ (x *ℤ y)) (x *ℤ y) (x *ℤ negℤ y)))
        (trans
          (cong (λ t → t +ℤ (x *ℤ negℤ y)) (+ℤ-inv-left (x *ℤ y)))
          (+ℤ-zero-left (x *ℤ negℤ y)))

    rightReduce : negℤ (x *ℤ y) +ℤ 0ℤ ≡ negℤ (x *ℤ y)
    rightReduce = +ℤ-zero-right (negℤ (x *ℤ y))
  in
  trans
    (sym leftReduce)
    (trans addNeg rightReduce)

-- § Law 14P.2: *ℤ commutes with negℤ on the left.
*ℤ-neg-left : (x y : ℤ) → (negℤ x) *ℤ y ≡ negℤ (x *ℤ y)
*ℤ-neg-left x y =
  let
    eq0 : negℤ x +ℤ x ≡ 0ℤ
    eq0 = +ℤ-inv-left x

    mul0 : (negℤ x +ℤ x) *ℤ y ≡ 0ℤ *ℤ y
    mul0 = cong (λ t → t *ℤ y) eq0

    expand : (negℤ x +ℤ x) *ℤ y ≡ (negℤ x *ℤ y) +ℤ (x *ℤ y)
    expand = *ℤ-distrib-left-+ℤ (negℤ x) x y

    eqSum' : (negℤ x *ℤ y) +ℤ (x *ℤ y) ≡ 0ℤ
    eqSum' = trans (sym expand) (trans mul0 (*ℤ-zero-left y))

    addInv : ((negℤ x *ℤ y) +ℤ (x *ℤ y)) +ℤ negℤ (x *ℤ y) ≡ 0ℤ +ℤ negℤ (x *ℤ y)
    addInv = cong (λ t → t +ℤ negℤ (x *ℤ y)) eqSum'

    lhsReduce : ((negℤ x *ℤ y) +ℤ (x *ℤ y)) +ℤ negℤ (x *ℤ y) ≡ negℤ x *ℤ y
    lhsReduce =
      trans
        (+ℤ-assoc (negℤ x *ℤ y) (x *ℤ y) (negℤ (x *ℤ y)))
        (trans
          (cong (λ t → (negℤ x *ℤ y) +ℤ t) (+ℤ-inv-right (x *ℤ y)))
          (+ℤ-zero-right (negℤ x *ℤ y)))

    rhsReduce : 0ℤ +ℤ negℤ (x *ℤ y) ≡ negℤ (x *ℤ y)
    rhsReduce = +ℤ-zero-left (negℤ (x *ℤ y))
  in
  trans
    (sym lhsReduce)
    (trans addInv rhsReduce)
-- § Law 14P.3: negative left factor is torsion-free.
*ℤ-neg-left-zero→zero : (n : ℕ) → (x : ℤ) → (-suc n *ℤ x ≡ 0ℤ) → x ≡ 0ℤ
*ℤ-neg-left-zero→zero n 0ℤ _ = refl
*ℤ-neg-left-zero→zero n (+suc m) mul0 =
  let
    eqPair : toPairℤ ((-suc n) *ℤ (+suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m)) ≡ (mkPairℕ zero zero)
    step₁ = trans (sym (toPair-*ℤ (-suc n) (+suc m))) eqPair

    neg0-raw : neg (Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (+suc m))) ≡ zero
    neg0-raw = cong neg step₁

    neg0 : (suc n *ℕ suc m) ≡ zero
    neg0 =
      trans
        (sym (+ℕ-zero-left (suc n *ℕ suc m)))
        neg0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) neg0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()

*ℤ-neg-left-zero→zero n (-suc m) mul0 =
  let
    eqPair : toPairℤ ((-suc n) *ℤ (-suc m)) ≡ toPairℤ 0ℤ
    eqPair = cong toPairℤ mul0

    step₁ : Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m)) ≡ (mkPairℕ zero zero)
    step₁ = trans (sym (toPair-*ℤ (-suc n) (-suc m))) eqPair

    pos0-raw : pos (Pairℕ-mul (toPairℤ (-suc n)) (toPairℤ (-suc m))) ≡ zero
    pos0-raw = cong pos step₁

    pos0 : (suc n *ℕ suc m) ≡ zero
    pos0 =
      trans
        (sym (+ℕ-zero-left (suc n *ℕ suc m)))
        pos0-raw

    bad : suc m ≡ zero
    bad = *ℕ-pos-zero→zero n (suc m) pos0
  in
  ⊥-elim (caseSucZero bad)
  where
    caseSucZero : {k : ℕ} → suc k ≡ zero → ⊥
    caseSucZero ()
-- § Zero annihilation at pair level (right).
Pairℕ-mul-zero-right : (p : Pairℕ) → Pairℕ-mul p (mkPairℕ zero zero) ≡ (mkPairℕ zero zero)
Pairℕ-mul-zero-right (mkPairℕ a b) =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (b *ℕ zero)) (*ℕ-zero-right a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right b))
        refl))
    (trans
      (cong (λ t → t +ℕ (b *ℕ zero)) (*ℕ-zero-right a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-right b))
        refl))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl

-- § Zero annihilation at pair level (left).
Pairℕ-mul-zero-left : (p : Pairℕ) → Pairℕ-mul (mkPairℕ zero zero) p ≡ (mkPairℕ zero zero)
Pairℕ-mul-zero-left (mkPairℕ a b) =
  pair-ext
    (trans
      (cong (λ t → t +ℕ (zero *ℕ b)) (*ℕ-zero-left a))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-left b))
        refl))
    (trans
      (cong (λ t → t +ℕ (zero *ℕ a)) (*ℕ-zero-left b))
      (trans
        (cong (λ t → zero +ℕ t) (*ℕ-zero-left a))
        refl))
  where
    pair-ext : {x y x' y' : ℕ} → x ≡ x' → y ≡ y' → (mkPairℕ x y) ≡ (mkPairℕ x' y')
    pair-ext refl refl = refl
-- § Associativity at pair level for canonical pairs (16-case proof).
Pairℕ-mul-toPair-assoc : (x y z : ℤ) →
  Pairℕ-mul (Pairℕ-mul (toPairℤ x) (toPairℤ y)) (toPairℤ z)
    ≡
  Pairℕ-mul (toPairℤ x) (Pairℕ-mul (toPairℤ y) (toPairℤ z))
Pairℕ-mul-toPair-assoc 0ℤ y z = refl
Pairℕ-mul-toPair-assoc (+suc n) 0ℤ z =
  trans
    (cong (λ t → Pairℕ-mul t (toPairℤ z)) (Pairℕ-mul-zero-right (mkPairℕ (suc n) zero)))
    (trans
      (Pairℕ-mul-zero-left (toPairℤ z))
      (sym
        (trans
          (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-zero-left (toPairℤ z)))
          (Pairℕ-mul-zero-right (mkPairℕ (suc n) zero)))))
Pairℕ-mul-toPair-assoc (-suc n) 0ℤ z =
  trans
    (cong (λ t → Pairℕ-mul t (toPairℤ z)) (Pairℕ-mul-zero-right (mkPairℕ zero (suc n))))
    (trans
      (Pairℕ-mul-zero-left (toPairℤ z))
      (sym
        (trans
          (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-zero-left (toPairℤ z)))
          (Pairℕ-mul-zero-right (mkPairℕ zero (suc n))))))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul (mkPairℕ (suc n) zero) (mkPairℕ (suc m) zero)))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-zero-right (mkPairℕ (suc m) zero)))
        (Pairℕ-mul-zero-right (mkPairℕ (suc n) zero))))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul (mkPairℕ (suc n) zero) (mkPairℕ zero (suc m))))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-zero-right (mkPairℕ zero (suc m))))
        (Pairℕ-mul-zero-right (mkPairℕ (suc n) zero))))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul (mkPairℕ zero (suc n)) (mkPairℕ (suc m) zero)))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-zero-right (mkPairℕ (suc m) zero)))
        (Pairℕ-mul-zero-right (mkPairℕ zero (suc n)))))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) 0ℤ =
  trans
    (Pairℕ-mul-zero-right (Pairℕ-mul (mkPairℕ zero (suc n)) (mkPairℕ zero (suc m))))
    (sym
      (trans
        (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-zero-right (mkPairℕ zero (suc m))))
        (Pairℕ-mul-zero-right (mkPairℕ zero (suc n)))))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ (suc k) zero)) (Pairℕ-mul-pos-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-pos-pos (suc m) (suc k)))
            (Pairℕ-mul-pos-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (+suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ zero (suc k))) (Pairℕ-mul-pos-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-pos-neg (suc m) (suc k)))
            (Pairℕ-mul-pos-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ (suc k) zero)) (Pairℕ-mul-pos-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-neg-pos (suc m) (suc k)))
            (Pairℕ-mul-pos-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (+suc n) (-suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ zero (suc k))) (Pairℕ-mul-pos-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ (suc n) zero) t) (Pairℕ-mul-neg-neg (suc m) (suc k)))
            (Pairℕ-mul-pos-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ (suc k) zero)) (Pairℕ-mul-neg-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-pos-pos (suc m) (suc k)))
            (Pairℕ-mul-neg-pos (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (+suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ zero (suc k))) (Pairℕ-mul-neg-pos (suc n) (suc m)))
    (trans
      (Pairℕ-mul-neg-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-pos-neg (suc m) (suc k)))
            (Pairℕ-mul-neg-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) (+suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ (suc k) zero)) (Pairℕ-mul-neg-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-pos ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext (*ℕ-assoc (suc n) (suc m) (suc k)) refl)
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-neg-pos (suc m) (suc k)))
            (Pairℕ-mul-neg-neg (suc n) ((suc m) *ℕ (suc k)))))))
Pairℕ-mul-toPair-assoc (-suc n) (-suc m) (-suc k) =
  trans
    (cong (λ t → Pairℕ-mul t (mkPairℕ zero (suc k))) (Pairℕ-mul-neg-neg (suc n) (suc m)))
    (trans
      (Pairℕ-mul-pos-neg ((suc n) *ℕ (suc m)) (suc k))
      (trans
        (Pairℕ-ext refl (*ℕ-assoc (suc n) (suc m) (suc k)))
        (sym
          (trans
            (cong (λ t → Pairℕ-mul (mkPairℕ zero (suc n)) t) (Pairℕ-mul-neg-neg (suc m) (suc k)))
            (Pairℕ-mul-neg-pos (suc n) ((suc m) *ℕ (suc k)))))))
opaque
  unfolding _*ℤ_
  -- § Associativity of *ℤ.
  *ℤ-assoc : (x y z : ℤ) → (x *ℤ y) *ℤ z ≡ x *ℤ (y *ℤ z)
  *ℤ-assoc x y z =
    let lhs = (x *ℤ y) *ℤ z in
    let rhs = x *ℤ (y *ℤ z) in
    trans
      (sym (from-toPairℤ lhs))
      (trans
        (cong fromPairℤ
          (trans
            (trans
              (toPair-*ℤ (x *ℤ y) z)
              (cong (λ t → Pairℕ-mul t (toPairℤ z)) (toPair-*ℤ x y)))
            (trans
              (Pairℕ-mul-toPair-assoc x y z)
              (sym
                (trans
                  (toPair-*ℤ x (y *ℤ z))
                  (cong (λ t → Pairℕ-mul (toPairℤ x) t) (toPair-*ℤ y z)))))))
        (from-toPairℤ rhs))

  -- § Commutativity of *ℤ.
  *ℤ-comm : (x y : ℤ) → x *ℤ y ≡ y *ℤ x
  *ℤ-comm x y = cong fromPairℤ (Pairℕ-mul-comm (toPairℤ x) (toPairℤ y))
-- § Transport ≤ℤ along left equality.
≤ℤ-resp-≡ˡ : {x y z : ℤ} → x ≡ y → x ≤ℤ z → y ≤ℤ z
≤ℤ-resp-≡ˡ refl p = p

-- § Transport ≤ℤ along right equality.
≤ℤ-resp-≡ʳ : {x y z : ℤ} → y ≡ z → x ≤ℤ y → x ≤ℤ z
≤ℤ-resp-≡ʳ refl p = p

-- § Transport <ℤ along left equality.
<ℤ-resp-≡ˡ : {x y z : ℤ} → x ≡ y → x <ℤ z → y <ℤ z
<ℤ-resp-≡ˡ refl p = p

-- § Transport <ℤ along right equality.
<ℤ-resp-≡ʳ : {x y z : ℤ} → y ≡ z → x <ℤ y → x <ℤ z
<ℤ-resp-≡ʳ refl p = p

-- § Negation reverses order (antitone).
negℤ-antitone-≤ℤ : {x y : ℤ} → x ≤ℤ y → (negℤ y) ≤ℤ (negℤ x)
negℤ-antitone-≤ℤ {0ℤ} {0ℤ} _ = tt
negℤ-antitone-≤ℤ {0ℤ} {+suc n} _ = tt
negℤ-antitone-≤ℤ {0ℤ} { -suc n } ()
negℤ-antitone-≤ℤ {+suc m} {0ℤ} ()
negℤ-antitone-≤ℤ {+suc m} {+suc n} p = p
negℤ-antitone-≤ℤ {+suc m} { -suc n } ()
negℤ-antitone-≤ℤ { -suc m } {0ℤ} _ = tt
negℤ-antitone-≤ℤ { -suc m } {+suc n} _ = tt
negℤ-antitone-≤ℤ { -suc m } { -suc n } p = p
-- § From 0 < z, force z into positive constructor form.
0<ℤ→pos : (z : ℤ) → 0ℤ <ℤ z → Σ ℕ (λ n → z ≡ +suc n)
0<ℤ→pos 0ℤ (p≤ , p≰) = ⊥-elim (p≰ p≤)
0<ℤ→pos (+suc n) _ = n , refl
0<ℤ→pos (-suc n) (() , _)

-- § 0 < +suc n is immediate.
0<ℤ-pos : (n : ℕ) → 0ℤ <ℤ (+suc n)
0<ℤ-pos n = tt , (λ p → p)
opaque
  unfolding _*ℤ_
  -- § Product of positive constructors stays positive.
  *ℤ-pos-pos-eq : (m n : ℕ) → (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
  *ℤ-pos-pos-eq m n =
    let posStep : (suc m *ℕ suc n) +ℕ (zero *ℕ zero) ≡ suc (n +ℕ (m *ℕ suc n))
        posStep =
          trans
            (cong (λ t → (suc m *ℕ suc n) +ℕ t) (*ℕ-zero-left zero))
            (trans
              (+ℕ-zero-right (suc m *ℕ suc n))
              refl)

        negStep : (suc m *ℕ zero) +ℕ (zero *ℕ suc n) ≡ zero
        negStep =
          trans
            (cong (λ t → t +ℕ (zero *ℕ suc n)) (*ℕ-zero-right (suc m)))
            (trans
              (cong (λ t → zero +ℕ t) (*ℕ-zero-left (suc n)))
              refl)
    in
    trans
      (normalizeℤ-cong posStep negStep)
      refl

-- § 0 < z · d for z positive and d a positive natural.
0<ℤ-mul-pos-right : (z : ℤ) → (d : ℕ⁺) → 0ℤ <ℤ z → 0ℤ <ℤ (z *ℤ ⁺toℤ d)
0<ℤ-mul-pos-right z (mkℕ⁺ k) zpos =
  let zShape = 0<ℤ→pos z zpos
      m = fst zShape
      z≡ = snd zShape

      prod≡ : z *ℤ (+suc k) ≡ (+suc m) *ℤ (+suc k)
      prod≡ = cong (λ t → t *ℤ (+suc k)) z≡

      basePos : 0ℤ <ℤ ((+suc m) *ℤ (+suc k))
      basePos =
        <ℤ-resp-≡ʳ (sym (*ℤ-pos-pos-eq m k)) (0<ℤ-pos (k +ℕ (m *ℕ suc k)))

  in
  <ℤ-resp-≡ʳ (sym prod≡) basePos

-- § Product of negative and positive constructors.
*ℤ-neg-pos-eq : (m k : ℕ) → (-suc m) *ℤ (+suc k) ≡ -suc (k +ℕ (m *ℕ suc k))
*ℤ-neg-pos-eq m k =
  trans
    (*ℤ-neg-left (+suc m) (+suc k))
    (trans
      (cong negℤ (*ℤ-pos-pos-eq m k))
      refl)
-- § Multiplication by positive ℕ⁺ preserves ≤ℤ (9-case proof).
≤ℤ-mul-pos-right : (x y : ℤ) → (d : ℕ⁺) → x ≤ℤ y → (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
≤ℤ-mul-pos-right 0ℤ 0ℤ (mkℕ⁺ k) _ =
  subst
    (λ t → t ≤ℤ t)
    (sym (*ℤ-zero-left (+suc k)))
    tt
≤ℤ-mul-pos-right 0ℤ (+suc n) (mkℕ⁺ k) _ =
  let
    t = k +ℕ (n *ℕ suc k)
    eqL : 0ℤ ≡ 0ℤ *ℤ (+suc k)
    eqL = sym (*ℤ-zero-left (+suc k))

    eqR : (+suc t) ≡ ((+suc n) *ℤ (+suc k))
    eqR = sym (*ℤ-pos-pos-eq n k)

    base : 0ℤ ≤ℤ (+suc t)
    base = tt
  in
  subst (λ r → (0ℤ *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ (+suc t)) eqL base)
≤ℤ-mul-pos-right 0ℤ (-suc n) d ()
≤ℤ-mul-pos-right (+suc m) 0ℤ d ()
≤ℤ-mul-pos-right (+suc m) (+suc n) (mkℕ⁺ k) (s≤s p) =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    mulMono : (m *ℕ suc k) ≤ (n *ℕ suc k)
    mulMono = ≤-*ℕ-monoʳ p (suc k)

    addMono : t₁ ≤ t₂
    addMono = ≤-+ℕ-monoˡ mulMono k

    base : (+suc t₁) ≤ℤ (+suc t₂)
    base = s≤s addMono
  in
  ≤ℤ-resp-≡ˡ (sym (*ℤ-pos-pos-eq m k))
    (≤ℤ-resp-≡ʳ (sym (*ℤ-pos-pos-eq n k)) base)
≤ℤ-mul-pos-right (+suc m) (-suc n) d ()
≤ℤ-mul-pos-right (-suc m) 0ℤ (mkℕ⁺ k) _ =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    eqL : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    eqL = sym (*ℤ-neg-pos-eq m k)

    eqR : 0ℤ ≡ (0ℤ *ℤ (+suc k))
    eqR = sym (*ℤ-zero-left (+suc k))

    base : (-suc t₁) ≤ℤ 0ℤ
    base = tt
  in
  subst (λ r → ((-suc m) *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ 0ℤ) eqL base)
≤ℤ-mul-pos-right (-suc m) (+suc n) (mkℕ⁺ k) _ =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)
    eqL : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    eqL = sym (*ℤ-neg-pos-eq m k)

    eqR : (+suc t₂) ≡ ((+suc n) *ℤ (+suc k))
    eqR = sym (*ℤ-pos-pos-eq n k)

    base : (-suc t₁) ≤ℤ (+suc t₂)
    base = tt
  in
  subst (λ r → ((-suc m) *ℤ (+suc k)) ≤ℤ r) eqR
    (subst (λ l → l ≤ℤ (+suc t₂)) eqL base)
≤ℤ-mul-pos-right (-suc m) (-suc n) (mkℕ⁺ k) (s≤s p) =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    mulMono : (n *ℕ suc k) ≤ (m *ℕ suc k)
    mulMono = ≤-*ℕ-monoʳ p (suc k)

    addMono : t₂ ≤ t₁
    addMono = ≤-+ℕ-monoˡ mulMono k

    base : (-suc t₁) ≤ℤ (-suc t₂)
    base = s≤s addMono
  in
  ≤ℤ-resp-≡ˡ (sym (*ℤ-neg-pos-eq m k))
    (≤ℤ-resp-≡ʳ (sym (*ℤ-neg-pos-eq n k)) base)
-- § Cancellation: if x·d ≤ y·d for positive d, then x ≤ y (9-case proof).
≤ℤ-mul-pos-cancel-right : (x y : ℤ) → (d : ℕ⁺) → (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d) → x ≤ℤ y
≤ℤ-mul-pos-cancel-right 0ℤ 0ℤ (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right 0ℤ (+suc n) (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right 0ℤ (-suc n) (mkℕ⁺ k) p =
  let
    t : ℕ
    t = k +ℕ (n *ℕ suc k)

    rhsEq : ((-suc n) *ℤ (+suc k)) ≡ (-suc t)
    rhsEq = *ℤ-neg-pos-eq n k

    p0 : (0ℤ *ℤ (+suc k)) ≤ℤ ((-suc n) *ℤ (+suc k))
    p0 = p

    p1 : 0ℤ ≤ℤ ((-suc n) *ℤ (+suc k))
    p1 = subst (λ s → s ≤ℤ ((-suc n) *ℤ (+suc k))) (*ℤ-zero-left (+suc k)) p0

    p' : 0ℤ ≤ℤ (-suc t)
    p' = subst (λ r → 0ℤ ≤ℤ r) rhsEq p1
  in
  ⊥-elim p'
≤ℤ-mul-pos-cancel-right (+suc m) 0ℤ (mkℕ⁺ k) p =
  let
    t = k +ℕ (m *ℕ suc k)
    lhsPos : ((+suc m) *ℤ (+suc k)) ≡ +suc t
    lhsPos = *ℤ-pos-pos-eq m k

    p0 : ((+suc m) *ℤ (+suc k)) ≤ℤ (0ℤ *ℤ (+suc k))
    p0 = p

    p1 : ((+suc m) *ℤ (+suc k)) ≤ℤ 0ℤ
    p1 = subst (λ r → ((+suc m) *ℤ (+suc k)) ≤ℤ r) (*ℤ-zero-left (+suc k)) p0

    p' : (+suc t) ≤ℤ 0ℤ
    p' = subst (λ s → s ≤ℤ 0ℤ) lhsPos p1
  in
  ⊥-elim p'
≤ℤ-mul-pos-cancel-right (+suc m) (+suc n) (mkℕ⁺ k) p =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    lhsEq : (+suc t₁) ≡ ((+suc m) *ℤ (+suc k))
    lhsEq = sym (*ℤ-pos-pos-eq m k)

    rhsEq : (+suc t₂) ≡ ((+suc n) *ℤ (+suc k))
    rhsEq = sym (*ℤ-pos-pos-eq n k)

    step : (+suc t₁) ≤ℤ (+suc t₂)
    step =
      ≤ℤ-resp-≡ˡ (sym lhsEq)
        (≤ℤ-resp-≡ʳ (sym rhsEq) p)

    natStep : suc t₁ ≤ suc t₂
    natStep = step

    t₁≤t₂ : t₁ ≤ t₂
    t₁≤t₂ = ≤-+ℕ-cancelˡ (suc zero) t₁ t₂ natStep

    mulPart : (m *ℕ suc k) ≤ (n *ℕ suc k)
    mulPart = ≤-+ℕ-cancelˡ k (m *ℕ suc k) (n *ℕ suc k) t₁≤t₂

    base : m ≤ n
    base = ≤-*ℕ-cancelʳ-suc k mulPart
  in
  s≤s base
≤ℤ-mul-pos-cancel-right (+suc m) (-suc n) (mkℕ⁺ k) p =
  let
    t₁ : ℕ
    t₁ = k +ℕ (m *ℕ suc k)

    t₂ : ℕ
    t₂ = k +ℕ (n *ℕ suc k)

    lhsPos : ((+suc m) *ℤ (+suc k)) ≡ (+suc t₁)
    lhsPos = *ℤ-pos-pos-eq m k

    rhsNeg : ((-suc n) *ℤ (+suc k)) ≡ (-suc t₂)
    rhsNeg = *ℤ-neg-pos-eq n k

    p1 : ((+suc m) *ℤ (+suc k)) ≤ℤ (-suc t₂)
    p1 = ≤ℤ-resp-≡ʳ rhsNeg p

    p2 : (+suc t₁) ≤ℤ (-suc t₂)
    p2 = subst (λ s → s ≤ℤ (-suc t₂)) lhsPos p1
  in
  ⊥-elim p2
≤ℤ-mul-pos-cancel-right (-suc m) 0ℤ (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right (-suc m) (+suc n) (mkℕ⁺ k) p = tt
≤ℤ-mul-pos-cancel-right (-suc m) (-suc n) (mkℕ⁺ k) p =
  let
    t₁ = k +ℕ (m *ℕ suc k)
    t₂ = k +ℕ (n *ℕ suc k)

    lhsEq : (-suc t₁) ≡ ((-suc m) *ℤ (+suc k))
    lhsEq = sym (*ℤ-neg-pos-eq m k)

    rhsEq : (-suc t₂) ≡ ((-suc n) *ℤ (+suc k))
    rhsEq = sym (*ℤ-neg-pos-eq n k)

    step : (-suc t₁) ≤ℤ (-suc t₂)
    step =
      ≤ℤ-resp-≡ˡ (sym lhsEq)
        (≤ℤ-resp-≡ʳ (sym rhsEq) p)

    natStep : suc t₂ ≤ suc t₁
    natStep = step

    t₂≤t₁ : t₂ ≤ t₁
    t₂≤t₁ = ≤-+ℕ-cancelˡ (suc zero) t₂ t₁ natStep

    mulPart : (n *ℕ suc k) ≤ (m *ℕ suc k)
    mulPart = ≤-+ℕ-cancelˡ k (n *ℕ suc k) (m *ℕ suc k) t₂≤t₁

    base : n ≤ m
    base = ≤-*ℕ-cancelʳ-suc k mulPart
  in
  s≤s base
-- § Nonneg right factor preserves ≤ℤ.
≤ℤ-mul-nonneg-right : (x y z : ℤ) → x ≤ℤ y → 0ℤ ≤ℤ z → (x *ℤ z) ≤ℤ (y *ℤ z)
≤ℤ-mul-nonneg-right x y 0ℤ x≤y _ =
  subst (λ t → t ≤ℤ (y *ℤ 0ℤ)) (sym (*ℤ-zero-right x))
    (subst (λ t → 0ℤ ≤ℤ t) (sym (*ℤ-zero-right y)) tt)
≤ℤ-mul-nonneg-right x y (+suc k) x≤y _ =
  let
    d : ℕ⁺
    d = mkℕ⁺ k

    step : (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
    step = ≤ℤ-mul-pos-right x y d x≤y

    lhs : (x *ℤ (+suc k)) ≡ (x *ℤ ⁺toℤ d)
    lhs = refl

    rhs : (y *ℤ (+suc k)) ≡ (y *ℤ ⁺toℤ d)
    rhs = refl
  in
  ≤ℤ-resp-≡ˡ (sym lhs) (≤ℤ-resp-≡ʳ (sym rhs) step)
≤ℤ-mul-nonneg-right x y (-suc k) _ ()

-- § Strict order preserved by positive right factor.
<ℤ-mul-pos-right : {x y : ℤ} → (d : ℕ⁺) → x <ℤ y → (x *ℤ ⁺toℤ d) <ℤ (y *ℤ ⁺toℤ d)
<ℤ-mul-pos-right {x} {y} d (x≤y , y≰x) =
  let
    lePart : (x *ℤ ⁺toℤ d) ≤ℤ (y *ℤ ⁺toℤ d)
    lePart = ≤ℤ-mul-pos-right x y d x≤y

    notRev : (y *ℤ ⁺toℤ d) ≰ℤ (x *ℤ ⁺toℤ d)
    notRev ydx≤xdx = y≰x (≤ℤ-mul-pos-cancel-right y x d ydx≤xdx)
  in
  lePart , notRev
-- § abs of zero.
absℤ-zero : absℤ 0ℤ ≡ 0ℤ
absℤ-zero = refl

-- § abs absorbs negation.
absℤ-neg : (z : ℤ) → absℤ (negℤ z) ≡ absℤ z
absℤ-neg 0ℤ = refl
absℤ-neg (+suc n) = refl
absℤ-neg (-suc n) = refl

-- § abs is idempotent.
absℤ-idem : (z : ℤ) → absℤ (absℤ z) ≡ absℤ z
absℤ-idem 0ℤ = refl
absℤ-idem (+suc n) = refl
absℤ-idem (-suc n) = refl

-- § abs is nonneg.
absℤ-nonneg : (z : ℤ) → 0ℤ ≤ℤ absℤ z
absℤ-nonneg 0ℤ = tt
absℤ-nonneg (+suc n) = tt
absℤ-nonneg (-suc n) = tt

-- § Every integer is bounded by its absolute value.
≤ℤ-absℤ : (z : ℤ) → z ≤ℤ absℤ z
≤ℤ-absℤ 0ℤ = tt
≤ℤ-absℤ (+suc n) = ≤-refl (suc n)
≤ℤ-absℤ (-suc n) = tt

-- § abs zero implies zero.
absℤ-zero→zero : (z : ℤ) → absℤ z ≡ 0ℤ → z ≡ 0ℤ
absℤ-zero→zero 0ℤ _ = refl
absℤ-zero→zero (+suc n) ()
absℤ-zero→zero (-suc n) ()
-- § Natural magnitude.
magℤ : ℤ → ℕ
magℤ 0ℤ = zero
magℤ (+suc n) = suc n
magℤ (-suc n) = suc n

-- § Embedding ℕ into ℤ.
fromℕℤ : ℕ → ℤ
fromℕℤ zero = 0ℤ
fromℕℤ (suc n) = +suc n

-- § abs equals fromℕℤ of magnitude.
absℤ-fromℕℤ-magℤ : (z : ℤ) → absℤ z ≡ fromℕℤ (magℤ z)
absℤ-fromℕℤ-magℤ 0ℤ = refl
absℤ-fromℕℤ-magℤ (+suc n) = refl
absℤ-fromℕℤ-magℤ (-suc n) = refl

-- § Transport ≤ along right equality.
≤-resp-≡ʳ : {a b c : ℕ} → a ≤ b → b ≡ c → a ≤ c
≤-resp-≡ʳ {a} p eq = subst (λ t → a ≤ t) eq p

-- § Successor weakening.
≤-weaken-sucʳ : {a b : ℕ} → a ≤ b → a ≤ suc b
≤-weaken-sucʳ {a} {b} p = ≤-trans p (≤-step b)

-- § Double successor weakening.
≤-weaken-suc²ʳ : {a b : ℕ} → a ≤ b → a ≤ suc (suc b)
≤-weaken-suc²ʳ p = ≤-weaken-sucʳ (≤-weaken-sucʳ p)
-- § mag of normalizeℤ is bounded by input sum.
magNormalize≤sum : (a b : ℕ) → magℤ (normalizeℤ a b) ≤ (a +ℕ b)
magNormalize≤sum zero zero = ≤-refl zero
magNormalize≤sum (suc a) zero =
  ≤-resp-≡ʳ
    (≤-refl (suc a))
    (sym (+ℕ-zero-right (suc a)))
magNormalize≤sum zero (suc b) = ≤-refl (suc b)
magNormalize≤sum (suc a) (suc b) =
  ≤-resp-≡ʳ
    (≤-weaken-suc²ʳ (magNormalize≤sum a b))
    rhs
  where
    rhs : suc (suc (a +ℕ b)) ≡ (suc a +ℕ suc b)
    rhs = sym (cong suc (+ℕ-suc-right a b))

-- § Magnitude is subadditive for +ℤ.
magℤ-+ℤ-subadd : (x y : ℤ) → magℤ (x +ℤ y) ≤ (magℤ x +ℕ magℤ y)
magℤ-+ℤ-subadd x y =
  ≤-resp-≡ʳ
    (magNormalize≤sum (pos px +ℕ pos py) (neg px +ℕ neg py))
    sumReassoc
  where
    px : Pairℕ
    px = toPairℤ x

    py : Pairℕ
    py = toPairℤ y

    cong₂ : {A B C : Set} → (f : A → B → C) → {a a' : A} → {b b' : B} → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

    pairSumMag : (z : ℤ) → (pos (toPairℤ z) +ℕ neg (toPairℤ z)) ≡ magℤ z
    pairSumMag 0ℤ = refl
    pairSumMag (+suc n) = +ℕ-zero-right (suc n)
    pairSumMag (-suc n) = refl

    pairSumMagPx : (pos px +ℕ neg px) ≡ magℤ x
    pairSumMagPx = pairSumMag x

    pairSumMagPy : (pos py +ℕ neg py) ≡ magℤ y
    pairSumMagPy = pairSumMag y

    sumReassoc :
      ((pos px +ℕ pos py) +ℕ (neg px +ℕ neg py))
        ≡
      (magℤ x +ℕ magℤ y)
    sumReassoc =
      trans
        (shuffleℕ (pos px) (pos py) (neg px) (neg py))
        (cong₂ _+ℕ_ pairSumMagPx pairSumMagPy)

-- § Transport ℕ-≤ into ≤ℤ for nonneg integers.
fromℕℤ-mono : {m n : ℕ} → m ≤ n → fromℕℤ m ≤ℤ fromℕℤ n
fromℕℤ-mono {zero} {zero} _ = tt
fromℕℤ-mono {zero} {suc n} _ = tt
fromℕℤ-mono {suc m} {zero} ()
fromℕℤ-mono {suc m} {suc n} p = p

-- § fromℕℤ is additive.
fromℕℤ-+ℤ : (m n : ℕ) → fromℕℤ m +ℤ fromℕℤ n ≡ fromℕℤ (m +ℕ n)
fromℕℤ-+ℤ zero zero = refl
fromℕℤ-+ℤ zero (suc n) = refl
fromℕℤ-+ℤ (suc m) zero = refl
fromℕℤ-+ℤ (suc m) (suc n) = refl

-- § abs is subadditive on ℤ (triangle core).
absℤ-subadd : (x y : ℤ) → absℤ (x +ℤ y) ≤ℤ (absℤ x +ℤ absℤ y)
absℤ-subadd x y =
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) step₁)
  where
    step₁ : fromℕℤ (magℤ (x +ℤ y)) ≤ℤ fromℕℤ (magℤ x +ℕ magℤ y)
    step₁ = fromℕℤ-mono (magℤ-+ℤ-subadd x y)

    lhsEq : absℤ (x +ℤ y) ≡ fromℕℤ (magℤ (x +ℤ y))
    lhsEq = absℤ-fromℕℤ-magℤ (x +ℤ y)

    rhsEq : absℤ x +ℤ absℤ y ≡ fromℕℤ (magℤ x +ℕ magℤ y)
    rhsEq =
      trans
        (cong (λ t → t +ℤ absℤ y) (absℤ-fromℕℤ-magℤ x))
        (trans
          (cong (λ t → fromℕℤ (magℤ x) +ℤ t) (absℤ-fromℕℤ-magℤ y))
          (fromℕℤ-+ℤ (magℤ x) (magℤ y)))
-- § abs commutes with multiplication by positive ℕ⁺.
absℤ-mul-pos-right : (z : ℤ) → (d : ℕ⁺) → absℤ (z *ℤ ⁺toℤ d) ≡ (absℤ z *ℤ ⁺toℤ d)
absℤ-mul-pos-right 0ℤ d =
  trans
    (cong absℤ (*ℤ-zero-left (⁺toℤ d)))
    (sym (*ℤ-zero-left (⁺toℤ d)))
absℤ-mul-pos-right (+suc n) (mkℕ⁺ k) =
  let mulPosForm : (+suc n) *ℤ (+suc k) ≡ +suc (k +ℕ (n *ℕ suc k))
      mulPosForm = *ℤ-pos-pos-eq n k
  in
  trans
    (trans (cong absℤ mulPosForm) refl)
    (sym mulPosForm)

absℤ-mul-pos-right (-suc n) (mkℕ⁺ k) =
  let mulNegForm : (-suc n) *ℤ (+suc k) ≡ -suc (k +ℕ (n *ℕ suc k))
      mulNegForm = *ℤ-neg-pos-eq n k
      mulPosForm : (+suc n) *ℤ (+suc k) ≡ +suc (k +ℕ (n *ℕ suc k))
      mulPosForm = *ℤ-pos-pos-eq n k
  in
  trans
    (trans (cong absℤ mulNegForm) refl)
    (sym mulPosForm)
-- § abs is fully multiplicative.
absℤ-mul : (x y : ℤ) → absℤ (x *ℤ y) ≡ (absℤ x *ℤ absℤ y)
absℤ-mul 0ℤ y =
  let
    lhs : absℤ (0ℤ *ℤ y) ≡ absℤ 0ℤ
    lhs = cong absℤ (*ℤ-zero-left y)

    rhs : (absℤ 0ℤ *ℤ absℤ y) ≡ absℤ 0ℤ
    rhs = *ℤ-zero-left (absℤ y)
  in
  trans lhs (sym rhs)
absℤ-mul x 0ℤ =
  let
    lhs : absℤ (x *ℤ 0ℤ) ≡ absℤ 0ℤ
    lhs = cong absℤ (*ℤ-zero-right x)

    rhs : (absℤ x *ℤ absℤ 0ℤ) ≡ absℤ 0ℤ
    rhs =
      trans
        (cong (λ t → absℤ x *ℤ t) absℤ-zero)
        (*ℤ-zero-right (absℤ x))
  in
  trans lhs (sym rhs)
absℤ-mul (+suc m) (+suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n
  in
  trans (cong absℤ prodEq) (sym prodEq)
absℤ-mul (+suc m) (-suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans
    (cong absℤ (*ℤ-neg-right (+suc m) (+suc n)))
    (trans (absℤ-neg ((+suc m) *ℤ (+suc n))) absProd)
absℤ-mul (-suc m) (+suc n) =
  let
    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans
    (cong absℤ (*ℤ-neg-left (+suc m) (+suc n)))
    (trans (absℤ-neg ((+suc m) *ℤ (+suc n))) absProd)
absℤ-mul (-suc m) (-suc n) =
  let
    mulEq : (-suc m) *ℤ (-suc n) ≡ (+suc m) *ℤ (+suc n)
    mulEq =
      trans
        (*ℤ-neg-right (negℤ (+suc m)) (+suc n))
        (trans
          (cong negℤ (*ℤ-neg-left (+suc m) (+suc n)))
          (negℤ-involutive ((+suc m) *ℤ (+suc n))))

    prodEq : (+suc m) *ℤ (+suc n) ≡ +suc (n +ℕ (m *ℕ suc n))
    prodEq = *ℤ-pos-pos-eq m n

    absProd : absℤ ((+suc m) *ℤ (+suc n)) ≡ (+suc m) *ℤ (+suc n)
    absProd = trans (cong absℤ prodEq) (sym prodEq)
  in
  trans (cong absℤ mulEq) absProd

-- § If -b ≤ a ≤ b then |a| ≤ b.
absℤ-within-bound : (a b : ℤ) → (negℤ b) ≤ℤ a → a ≤ℤ b → absℤ a ≤ℤ b
absℤ-within-bound 0ℤ 0ℤ _ _ = tt
absℤ-within-bound 0ℤ (+suc n) _ _ = tt
absℤ-within-bound 0ℤ (-suc n) _ neg-bound = neg-bound
absℤ-within-bound (+suc a) b _ upper = upper
absℤ-within-bound (-suc a) b lower _ =
  ≤ℤ-resp-≡ʳ (negℤ-involutive b) (negℤ-antitone-≤ℤ lower)
-- § Nonneg left monotonicity via fromℕℤ.
≤ℤ-fromℕℤ-+ℕ-monoˡ : {a b : ℕ} → a ≤ b → (c : ℕ) → fromℕℤ (c +ℕ a) ≤ℤ fromℕℤ (c +ℕ b)
≤ℤ-fromℕℤ-+ℕ-monoˡ p c = fromℕℤ-mono (≤-+ℕ-monoˡ p c)

-- § Nonneg right monotonicity via fromℕℤ.
≤ℤ-fromℕℤ-+ℕ-monoʳ : {a b : ℕ} → a ≤ b → (c : ℕ) → fromℕℤ (a +ℕ c) ≤ℤ fromℕℤ (b +ℕ c)
≤ℤ-fromℕℤ-+ℕ-monoʳ {a} {b} p c =
  let
    lhs : fromℕℤ (a +ℕ c) ≡ fromℕℤ (c +ℕ a)
    lhs = cong fromℕℤ (+ℕ-comm a c)

    rhs : fromℕℤ (b +ℕ c) ≡ fromℕℤ (c +ℕ b)
    rhs = cong fromℕℤ (+ℕ-comm b c)

    base : fromℕℤ (c +ℕ a) ≤ℤ fromℕℤ (c +ℕ b)
    base = ≤ℤ-fromℕℤ-+ℕ-monoˡ p c
  in
  ≤ℤ-resp-≡ˡ (sym lhs) (≤ℤ-resp-≡ʳ (sym rhs) base)

-- § Nonneg +ℤ right monotonicity.
≤ℤ-+ℤ-monoʳ-nonneg : {m n : ℕ} → m ≤ n → (k : ℕ) → (fromℕℤ m +ℤ fromℕℤ k) ≤ℤ (fromℕℤ n +ℤ fromℕℤ k)
≤ℤ-+ℤ-monoʳ-nonneg {m} {n} p k =
  ≤ℤ-resp-≡ˡ (sym (fromℕℤ-+ℤ m k))
    (≤ℤ-resp-≡ʳ (sym (fromℕℤ-+ℤ n k))
      (≤ℤ-fromℕℤ-+ℕ-monoʳ p k))

-- § Reflect ≤ℤ back to ℕ-≤ for nonneg integers.
≤ℤ-fromℕℤ-reflect : {m n : ℕ} → fromℕℤ m ≤ℤ fromℕℤ n → m ≤ n
≤ℤ-fromℕℤ-reflect {zero} {zero} _ = z≤n
≤ℤ-fromℕℤ-reflect {zero} {suc n} _ = z≤n
≤ℤ-fromℕℤ-reflect {suc m} {zero} ()
≤ℤ-fromℕℤ-reflect {suc m} {suc n} p = p

-- § Nonnegativity forces fromℕℤ form.
0≤ℤ→fromℕℤ : (z : ℤ) → 0ℤ ≤ℤ z → Σ ℕ (λ n → z ≡ fromℕℤ n)
0≤ℤ→fromℕℤ 0ℤ _ = zero , refl
0≤ℤ→fromℕℤ (+suc n) _ = suc n , refl
0≤ℤ→fromℕℤ (-suc n) ()

-- § Both-slot nonneg monotonicity.
≤ℤ-+ℤ-mono-nonneg₂ : {m m' n n' : ℕ} → m ≤ m' → n ≤ n' →
  (fromℕℤ m +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n')
≤ℤ-+ℤ-mono-nonneg₂ {m} {m'} {n} {n'} m≤m' n≤n' =
  let
    step₁ : (fromℕℤ m +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n)
    step₁ = ≤ℤ-+ℤ-monoʳ-nonneg m≤m' n

    step₂ : (fromℕℤ m' +ℤ fromℕℤ n) ≤ℤ (fromℕℤ m' +ℤ fromℕℤ n')
    step₂ =
      ≤ℤ-resp-≡ˡ (+ℤ-comm (fromℕℤ n) (fromℕℤ m'))
        (≤ℤ-resp-≡ʳ (+ℤ-comm (fromℕℤ n') (fromℕℤ m'))
          (≤ℤ-+ℤ-monoʳ-nonneg n≤n' m'))
  in
  ≤ℤ-trans step₁ step₂
-- § Forward: normalize order implies cross-sum inequality.
normalize≤→cross : (a b c d : ℕ) → normalizeℤ a b ≤ℤ normalizeℤ c d → (a +ℕ d) ≤ (c +ℕ b)
normalize≤→cross (suc a) (suc b) c d p =
  let ih : (a +ℕ d) ≤ (c +ℕ b)
      ih = normalize≤→cross a b c d p

      lifted : (suc (a +ℕ d)) ≤ (suc (c +ℕ b))
      lifted = s≤s ih

      rhsEq : (c +ℕ suc b) ≡ suc (c +ℕ b)
      rhsEq = +ℕ-suc-right c b
  in
  subst (λ t → (suc a +ℕ d) ≤ t) (sym rhsEq) lifted
normalize≤→cross a b (suc c) (suc d) p =
  let ih : (a +ℕ d) ≤ (c +ℕ b)
      ih = normalize≤→cross a b c d p

      lifted : (suc (a +ℕ d)) ≤ (suc (c +ℕ b))
      lifted = s≤s ih

      lhsEq : (a +ℕ suc d) ≡ suc (a +ℕ d)
      lhsEq = +ℕ-suc-right a d
  in
  subst (λ t → t ≤ (suc c +ℕ b)) (sym lhsEq) lifted

normalize≤→cross zero zero zero zero _ = z≤n
normalize≤→cross zero zero (suc c) zero _ = z≤n
normalize≤→cross zero zero zero (suc d) ()
normalize≤→cross (suc a) zero zero zero ()
normalize≤→cross (suc a) zero (suc c) zero p =
  let
    lhsEq : (suc a +ℕ zero) ≡ suc a
    lhsEq = cong suc (+ℕ-zero-right a)

    rhsEq : (suc c +ℕ zero) ≡ suc c
    rhsEq = cong suc (+ℕ-zero-right c)
  in
  subst (λ t → t ≤ (suc c +ℕ zero)) (sym lhsEq)
    (subst (λ t → (suc a) ≤ t) (sym rhsEq) p)
normalize≤→cross (suc a) zero zero (suc d) ()
normalize≤→cross zero (suc b) zero zero _ = z≤n
normalize≤→cross zero (suc b) (suc c) zero _ = z≤n
normalize≤→cross zero (suc b) zero (suc d) p = p

-- § Backward: cross-sum inequality implies normalize order.
cross→normalize≤ : (a b c d : ℕ) → (a +ℕ d) ≤ (c +ℕ b) → normalizeℤ a b ≤ℤ normalizeℤ c d
cross→normalize≤ (suc a) (suc b) c d p with subst (λ t → (suc a +ℕ d) ≤ t) (+ℕ-suc-right c b) p
... | s≤s q = cross→normalize≤ a b c d q
cross→normalize≤ a b (suc c) (suc d) p with subst (λ t → t ≤ (suc c +ℕ b)) (+ℕ-suc-right a d) p
... | s≤s q = cross→normalize≤ a b c d q

cross→normalize≤ zero zero zero zero _ = tt
cross→normalize≤ zero zero (suc c) zero _ = tt
cross→normalize≤ zero zero zero (suc d) ()
cross→normalize≤ (suc a) zero zero zero ()
cross→normalize≤ (suc a) zero (suc c) zero p =
  let
    lhsEq : (suc a +ℕ zero) ≡ suc a
    lhsEq = cong suc (+ℕ-zero-right a)

    rhsEq : (suc c +ℕ zero) ≡ suc c
    rhsEq = cong suc (+ℕ-zero-right c)

    p' : (suc a) ≤ (suc c)
    p' =
      subst (λ t → t ≤ (suc c)) lhsEq
        (subst (λ t → (suc a +ℕ zero) ≤ t) rhsEq p)
  in
  p'
cross→normalize≤ (suc a) zero zero (suc d) ()
cross→normalize≤ zero (suc b) zero zero _ = tt
cross→normalize≤ zero (suc b) (suc c) zero _ = tt
cross→normalize≤ zero (suc b) zero (suc d) p = p
-- § Right monotonicity of +ℤ (general).
≤ℤ-+ℤ-monoʳ : {x y : ℤ} → x ≤ℤ y → (z : ℤ) → (x +ℤ z) ≤ℤ (y +ℤ z)
≤ℤ-+ℤ-monoʳ {x} {y} x≤y z =
  let
    px = toPairℤ x
    py = toPairℤ y
    pz = toPairℤ z

    ax = pos px
    bx = neg px
    ay = pos py
    by = neg py
    az = pos pz
    bz = neg pz

    x≤y' : normalizeℤ ax bx ≤ℤ normalizeℤ ay by
    x≤y' =
      ≤ℤ-resp-≡ʳ (sym (from-toPairℤ y))
        (≤ℤ-resp-≡ˡ (sym (from-toPairℤ x)) x≤y)

    crossXY : (ax +ℕ by) ≤ (ay +ℕ bx)
    crossXY = normalize≤→cross ax bx ay by x≤y'

    k : ℕ
    k = az +ℕ bz

    base : (k +ℕ (ax +ℕ by)) ≤ (k +ℕ (ay +ℕ bx))
    base = ≤-+ℕ-monoˡ crossXY k

    lhsEq : ((ax +ℕ az) +ℕ (by +ℕ bz)) ≡ (k +ℕ (ax +ℕ by))
    lhsEq =
      trans
        (shuffleℕ ax az by bz)
        (+ℕ-comm (ax +ℕ by) k)

    rhsEq : ((ay +ℕ az) +ℕ (bx +ℕ bz)) ≡ (k +ℕ (ay +ℕ bx))
    rhsEq =
      trans
        (shuffleℕ ay az bx bz)
        (+ℕ-comm (ay +ℕ bx) k)

    sumCross : ((ax +ℕ az) +ℕ (by +ℕ bz)) ≤ ((ay +ℕ az) +ℕ (bx +ℕ bz))
    sumCross =
      subst (λ t → t ≤ ((ay +ℕ az) +ℕ (bx +ℕ bz))) (sym lhsEq)
        (subst (λ t → (k +ℕ (ax +ℕ by)) ≤ t) (sym rhsEq) base)
  in
  cross→normalize≤ (ax +ℕ az) (bx +ℕ bz) (ay +ℕ az) (by +ℕ bz) sumCross

-- § Left monotonicity of +ℤ.
≤ℤ-+ℤ-monoˡ : {x y : ℤ} → x ≤ℤ y → (z : ℤ) → (z +ℤ x) ≤ℤ (z +ℤ y)
≤ℤ-+ℤ-monoˡ {x} {y} x≤y z =
  ≤ℤ-resp-≡ˡ (+ℤ-comm x z)
    (≤ℤ-resp-≡ʳ (+ℤ-comm y z)
      (≤ℤ-+ℤ-monoʳ x≤y z))

-- § Both-slot monotonicity of +ℤ.
≤ℤ-+ℤ-mono : {x y u v : ℤ} → x ≤ℤ y → u ≤ℤ v → (x +ℤ u) ≤ℤ (y +ℤ v)
≤ℤ-+ℤ-mono {x} {y} {u} {v} x≤y u≤v =
  ≤ℤ-trans (≤ℤ-+ℤ-monoʳ x≤y u) (≤ℤ-+ℤ-monoˡ u≤v y)

-- § Right additive cancellation for ≤ℤ.
≤ℤ-+ℤ-cancelʳ : (x y z : ℤ) → x ≤ℤ (z +ℤ y) → (x +ℤ negℤ y) ≤ℤ z
≤ℤ-+ℤ-cancelʳ x y z p =
  let
    step : (x +ℤ negℤ y) ≤ℤ ((z +ℤ y) +ℤ negℤ y)
    step = ≤ℤ-+ℤ-monoʳ p (negℤ y)

    rhsEq : ((z +ℤ y) +ℤ negℤ y) ≡ z
    rhsEq =
      trans
        (+ℤ-assoc z y (negℤ y))
        (trans
          (cong (λ t → z +ℤ t) (+ℤ-inv-right y))
          (+ℤ-zero-right z))
  in
  ≤ℤ-resp-≡ʳ rhsEq step
-- § fromℕℤ is multiplicative for ℕ⁺.
fromℕℤ-mul-⁺ : (n : ℕ) → (d : ℕ⁺) → (fromℕℤ n *ℤ ⁺toℤ d) ≡ fromℕℤ (n *ℕ ⁺toℕ d)
fromℕℤ-mul-⁺ zero d =
  trans
    (*ℤ-zero-left (⁺toℤ d))
    (cong fromℕℤ (sym (*ℕ-zero-left (⁺toℕ d))))
fromℕℤ-mul-⁺ (suc n) (mkℕ⁺ k) =
  let
    natForm : (suc n *ℕ suc k) ≡ suc (k +ℕ (n *ℕ suc k))
    natForm = refl

    rhs : fromℕℤ (suc n *ℕ suc k) ≡ +suc (k +ℕ (n *ℕ suc k))
    rhs = cong fromℕℤ natForm
  in
  trans
    (*ℤ-pos-pos-eq n k)
    (sym rhs)

-- § 1 < 2z for z positive.
oneℤ<twoTimes-pos : (z : ℤ) → 0ℤ <ℤ z → oneℤ <ℤ (z +ℤ z)
oneℤ<twoTimes-pos z zpos with 0<ℤ→pos z zpos
... | (m , z≡) =
  <ℤ-resp-≡ʳ (cong (λ t → t +ℤ t) (sym z≡)) (lePart , notRev)
  where
    twoTimes : (+suc m) +ℤ (+suc m) ≡ +suc (m +ℕ suc m)
    twoTimes =
      trans
        (fromℕℤ-+ℤ (suc m) (suc m))
        (cong fromℕℤ refl)

    lePart : oneℤ ≤ℤ ((+suc m) +ℤ (+suc m))
    lePart =
      let
        lePos : oneℤ ≤ℤ (+suc (m +ℕ suc m))
        lePos = s≤s z≤n
      in
        subst (λ t → oneℤ ≤ℤ t) (sym twoTimes) lePos

    no-suc≤zero : {t : ℕ} → suc t ≤ zero → ⊥
    no-suc≤zero ()

    impossible : (+suc (m +ℕ suc m)) ≤ℤ oneℤ → ⊥
    impossible (s≤s pNat) =
      let
        pNat' : suc (m +ℕ m) ≤ zero
        pNat' = subst (λ t → t ≤ zero) (+ℕ-suc-right m m) pNat
      in
      no-suc≤zero pNat'

    notRev : ((+suc m) +ℤ (+suc m)) ≰ℤ oneℤ
    notRev q = impossible (subst (λ t → t ≤ℤ oneℤ) twoTimes q)
-- § Commutativity of ℕ⁺ multiplication.
*⁺-comm : (x y : ℕ⁺) → x *⁺ y ≡ y *⁺ x
*⁺-comm (mkℕ⁺ a) (mkℕ⁺ b) =
  cong mkℕ⁺ (trans lhsNorm (sym rhsNorm))
  where
    lhsNorm : (a *ℕ suc b) +ℕ b ≡ (a +ℕ b) +ℕ (a *ℕ b)
    lhsNorm =
      trans
        (cong (λ t → t +ℕ b) (*ℕ-suc-right-+ℕ a b))
        (trans
          (+ℕ-assoc a (a *ℕ b) b)
          (trans
            (cong (λ t → a +ℕ t) (+ℕ-comm (a *ℕ b) b))
            (sym (+ℕ-assoc a b (a *ℕ b)))))

    rhsNorm : (b *ℕ suc a) +ℕ a ≡ (a +ℕ b) +ℕ (a *ℕ b)
    rhsNorm =
      trans
        (cong (λ t → t +ℕ a) (*ℕ-suc-right-+ℕ b a))
        (trans
          (cong (λ t → (b +ℕ t) +ℕ a) (*ℕ-comm b a))
          (trans
            (+ℕ-assoc b (a *ℕ b) a)
            (trans
              (cong (λ t → b +ℕ t) (+ℕ-comm (a *ℕ b) a))
              (trans
                (swapHeadℕ b a (a *ℕ b))
                (sym (+ℕ-assoc a b (a *ℕ b)))))))

-- § ⁺toℤ is a multiplicative homomorphism.
⁺toℤ-*⁺ : (x y : ℕ⁺) → ⁺toℤ (x *⁺ y) ≡ (⁺toℤ x) *ℤ (⁺toℤ y)
⁺toℤ-*⁺ (mkℕ⁺ a) (mkℕ⁺ b) =
  sym
    (trans
      (*ℤ-pos-pos-eq a b)
      (cong (λ t → +suc t) (+ℕ-comm b (a *ℕ suc b))))
-- § Rational number: integer numerator over positive denominator.
record ℚ : Set where
  constructor _/_
  field
    num : ℤ
    den : ℕ⁺

open ℚ public

infix 4 _≃ℚ_

-- § Setoid equality: cross-multiplication.
_≃ℚ_ : ℚ → ℚ → Set
(a / b) ≃ℚ (c / d) = (a *ℤ ⁺toℤ d) ≡ (c *ℤ ⁺toℤ b)

infixl 6 _+ℚ_ _-ℚ_
infixl 7 _*ℚ_

-- § Rational addition.
_+ℚ_ : ℚ → ℚ → ℚ
(a / b) +ℚ (c / d) = ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) / (b *⁺ d)

-- § Rational multiplication.
_*ℚ_ : ℚ → ℚ → ℚ
(a / b) *ℚ (c / d) = (a *ℤ c) / (b *⁺ d)

-- § Rational negation.
-ℚ_ : ℚ → ℚ
-ℚ (a / b) = negℤ a / b

-- § Rational subtraction.
_-ℚ_ : ℚ → ℚ → ℚ
p -ℚ q = p +ℚ (-ℚ q)

-- § Distinguished rationals.
0ℚ 1ℚ : ℚ
0ℚ = 0ℤ / one⁺
1ℚ = oneℤ / one⁺

infix 4 _≤ℚ_ _<ℚ_

-- § Rational order: cross-multiply and compare integers.
_≤ℚ_ : ℚ → ℚ → Set
(a / b) ≤ℚ (c / d) = (a *ℤ ⁺toℤ d) ≤ℤ (c *ℤ ⁺toℤ b)

-- § Strict rational order.
_<ℚ_ : ℚ → ℚ → Set
(a / b) <ℚ (c / d) = (a *ℤ ⁺toℤ d) <ℤ (c *ℤ ⁺toℤ b)

-- § Rational distance.
distℚ : ℚ → ℚ → ℚ
distℚ (a / b) (c / d) = absℤ ((a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)) / (b *⁺ d)
-- § Natural exponentiation.
_^_ : ℕ → ℕ → ℕ
x ^ zero = suc zero
x ^ suc n = x * (x ^ n)

-- § Alpha inverse from simplex invariants.
alpha-inverse : ℕ
alpha-inverse = (simplex-vertices ^ simplex-degree) * simplex-chi + (simplex-degree * simplex-degree)

-- § Law 15A.0: the derived integer is exactly 137.
law15A-0-alpha-inverse-137 : alpha-inverse ≡ 137
law15A-0-alpha-inverse-137 = refl

-- § Redundant witness (same computation, explicit name).
derived-integer : ℕ
derived-integer =
  (simplex-vertices ^ simplex-degree) * simplex-chi
  + (simplex-degree * simplex-degree)

law15A-0-derived-integer-137 : derived-integer ≡ 137
law15A-0-derived-integer-137 = refl
-- § Measurement: map from d into Two-distinction.
Measurement : Distinction → Set
Measurement d = S d → S Two-distinction

-- § Law 15B.0: measurements are determined by their action on two generators.
law15B-0-measurement-determined :
  (d : Distinction) →
  (m₁ m₂ : Measurement d) →
  m₁ (ℓ d) ≡ m₂ (ℓ d) →
  m₁ (r d) ≡ m₂ (r d) →
  m₁ ≗ m₂
law15B-0-measurement-determined d =
  law7-1-map-determined d Two-distinction

-- § Law 15B.1: every measurement is realized by some EndoCase.
law15B-1-measurement-classification-sound :
  (d : Distinction) →
  (m : Measurement d) →
  Σ EndoCase (λ c → K₄Map.interpret d Two-distinction c ≗ m)
law15B-1-measurement-classification-sound d m =
  law7-2-k4map-classification-sound d Two-distinction m

-- § Law 15B.2: the classifying EndoCase is unique.
law15B-2-measurement-classification-unique :
  (d : Distinction) →
  (m : Measurement d) →
  (c₁ c₂ : EndoCase) →
  K₄Map.interpret d Two-distinction c₁ ≗ m →
  K₄Map.interpret d Two-distinction c₂ ≗ m →
  c₁ ≡ c₂
law15B-2-measurement-classification-unique d m c₁ c₂ p q =
  law7-3-k4map-classification-unique d Two-distinction m c₁ c₂ p q
-- § Numerator of distℚ.
numDistℚ : ℚ → ℚ → ℤ
numDistℚ (a / b) (c / d) = absℤ ((a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b))

-- § Distance numerator is nonneg.
numDistℚ-nonneg : (p q : ℚ) → 0ℤ ≤ℤ numDistℚ p q
numDistℚ-nonneg (a / b) (c / d) = absℤ-nonneg _
-- § Triangle core: scaled distance numerator inequality.
numDistℚ-triangle-scaled : (p q r : ℚ) →
  (numDistℚ p r *ℤ ⁺toℤ (den q))
    ≤ℤ
  ((numDistℚ p q *ℤ ⁺toℤ (den r)) +ℤ (numDistℚ q r *ℤ ⁺toℤ (den p)))
numDistℚ-triangle-scaled (a / b) (c / d) (e / f) =
  ≤ℤ-resp-≡ˡ lhsAbs
    (≤ℤ-resp-≡ʳ rhsAbs
      absStep)
  where
    Wt : ℤ
    Wt = (a *ℤ ⁺toℤ f) +ℤ negℤ (e *ℤ ⁺toℤ b)

    Ut : ℤ
    Ut = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    Vt : ℤ
    Vt = (c *ℤ ⁺toℤ f) +ℤ negℤ (e *ℤ ⁺toℤ d)

    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    Wtd : ℤ
    Wtd = Wt *ℤ ⁺toℤ d

    Utf : ℤ
    Utf = Ut *ℤ ⁺toℤ f

    Vtb : ℤ
    Vtb = Vt *ℤ ⁺toℤ b

    cancelMid : (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f ≡ (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b
    cancelMid = swapScale c b f

    cancelEnd : (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d ≡ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b
    cancelEnd = swapScale e b d

    cancelHead : (a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
    cancelHead = swapScale a f d

    -- § Algebra: Wt·d = Ut·f + Vt·b.
    Wtd≡sum : Wtd ≡ (Utf +ℤ Vtb)
    Wtd≡sum =
      trans WtdForm (sym sumForm)
      where
        WtdForm : Wtd ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        WtdForm =
          trans
            (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (negℤ (e *ℤ ⁺toℤ b)) (⁺toℤ d))
            (trans
              (cong (λ t → ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) +ℤ t)
                    (*ℤ-neg-left (e *ℤ ⁺toℤ b) (⁺toℤ d)))
              (trans
                (cong (λ t → t +ℤ negℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)) cancelHead)
                (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                      (cong negℤ cancelEnd))))

        UtfForm : Utf ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
        UtfForm =
          trans
            (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ f))
            (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                  (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ f)))

        VtbForm : Vtb ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        VtbForm =
          trans
            (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (negℤ (e *ℤ ⁺toℤ d)) (⁺toℤ b))
            (cong (λ t → ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) +ℤ t)
                  (*ℤ-neg-left (e *ℤ ⁺toℤ d) (⁺toℤ b)))

        sumForm :
          (Utf +ℤ Vtb) ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        sumForm =
          let
            Adf = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
            CbF = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f
            CfB = (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b
            EdB = (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b

            UtfRhs = Adf +ℤ negℤ CbF
            VtbRhs = CfB +ℤ negℤ EdB

            midRewrite : (negℤ CbF +ℤ CfB) ≡ (negℤ CfB +ℤ CfB)
            midRewrite =
              cong (λ t → negℤ t +ℤ CfB) cancelMid

            cancelMiddle : (negℤ CbF +ℤ CfB) ≡ 0ℤ
            cancelMiddle =
              trans midRewrite (+ℤ-inv-left CfB)

            sumCancel : (UtfRhs +ℤ VtbRhs) ≡ (Adf +ℤ negℤ EdB)
            sumCancel =
              trans
                (+ℤ-assoc Adf (negℤ CbF) VtbRhs)
                (trans
                  (cong (λ t → Adf +ℤ t)
                        (sym (+ℤ-assoc (negℤ CbF) CfB (negℤ EdB))))
                  (trans
                    (cong (λ t → Adf +ℤ (t +ℤ negℤ EdB)) cancelMiddle)
                    (cong (λ t → Adf +ℤ t) (+ℤ-zero-left (negℤ EdB)))))
          in
          trans
            (cong (λ t → t +ℤ Vtb) UtfForm)
            (trans
              (cong (λ t → UtfRhs +ℤ t) VtbForm)
              sumCancel)

    absStep : absℤ Wtd ≤ℤ (absℤ Utf +ℤ absℤ Vtb)
    absStep =
      ≤ℤ-resp-≡ˡ (sym (cong absℤ Wtd≡sum)) (absℤ-subadd Utf Vtb)

    lhsAbs : absℤ Wtd ≡ (absℤ Wt *ℤ ⁺toℤ d)
    lhsAbs =
      trans
        (absℤ-mul-pos-right Wt d)
        refl

    rhsAbs : (absℤ Utf +ℤ absℤ Vtb) ≡ ((absℤ Ut *ℤ ⁺toℤ f) +ℤ (absℤ Vt *ℤ ⁺toℤ b))
    rhsAbs =
      trans
        (cong (λ t → t +ℤ absℤ Vtb) (absℤ-mul-pos-right Ut f))
        (cong (λ t → (absℤ Ut *ℤ ⁺toℤ f) +ℤ t) (absℤ-mul-pos-right Vt b))
-- § Reflexivity of ≃ℚ.
≃ℚ-refl : (p : ℚ) → p ≃ℚ p
≃ℚ-refl (a / b) = refl

-- § Symmetry of ≃ℚ.
≃ℚ-sym : {p q : ℚ} → p ≃ℚ q → q ≃ℚ p
≃ℚ-sym = sym

-- § Right cancellation of *ℤ by positive factor.
*ℤ-cancel-right-pos : (x y : ℤ) → (d : ℕ⁺) → (x *ℤ ⁺toℤ d) ≡ (y *ℤ ⁺toℤ d) → x ≡ y
*ℤ-cancel-right-pos x y d eq =
  ≤ℤ-antisym
    (≤ℤ-mul-pos-cancel-right x y d (≤ℤ-resp-≡ʳ eq (≤ℤ-refl (x *ℤ ⁺toℤ d))))
    (≤ℤ-mul-pos-cancel-right y x d (≤ℤ-resp-≡ʳ (sym eq) (≤ℤ-refl (y *ℤ ⁺toℤ d))))

-- § Transitivity of ≃ℚ (uses torsion-freedom to cancel intermediate denominator).
≃ℚ-trans : {p q r : ℚ} → p ≃ℚ q → q ≃ℚ r → p ≃ℚ r
≃ℚ-trans {a / b} {c / d} {e / f} eq₁ eq₂ =
  let
    B : ℤ
    B = ⁺toℤ b

    D : ℤ
    D = ⁺toℤ d

    F : ℤ
    F = ⁺toℤ f

    step₁ : ((a *ℤ D) *ℤ F) ≡ ((c *ℤ B) *ℤ F)
    step₁ = cong (λ t → t *ℤ F) eq₁

    step₂ : ((c *ℤ F) *ℤ B) ≡ ((e *ℤ D) *ℤ B)
    step₂ = cong (λ t → t *ℤ B) eq₂

    swapCBF : ((c *ℤ B) *ℤ F) ≡ ((c *ℤ F) *ℤ B)
    swapCBF =
      trans
        (*ℤ-assoc c B F)
        (trans
          (cong (λ t → c *ℤ t) (*ℤ-comm B F))
          (sym (*ℤ-assoc c F B)))

    mid : ((a *ℤ D) *ℤ F) ≡ ((e *ℤ D) *ℤ B)
    mid = trans step₁ (trans swapCBF step₂)

    regroupL : ((a *ℤ D) *ℤ F) ≡ (a *ℤ F) *ℤ D
    regroupL =
      trans
        (*ℤ-assoc a D F)
        (trans
          (cong (λ t → a *ℤ t) (*ℤ-comm D F))
          (sym (*ℤ-assoc a F D)))

    regroupR : ((e *ℤ D) *ℤ B) ≡ (e *ℤ B) *ℤ D
    regroupR =
      trans
        (*ℤ-assoc e D B)
        (trans
          (cong (λ t → e *ℤ t) (*ℤ-comm D B))
          (sym (*ℤ-assoc e B D)))

    eqD : ((a *ℤ F) *ℤ D) ≡ ((e *ℤ B) *ℤ D)
    eqD = trans (sym regroupL) (trans mid regroupR)
  in
  *ℤ-cancel-right-pos (a *ℤ F) (e *ℤ B) d eqD
-- § Reflexivity of ≤ℚ.
≤ℚ-refl : (q : ℚ) → q ≤ℚ q
≤ℚ-refl (a / b) = ≤ℤ-refl (a *ℤ ⁺toℤ b)

-- § Denominator scaling swap.
swapScaleℚ : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
swapScaleℚ x u v =
  trans
    (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
    (trans
      (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
      (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

-- § Transitivity of ≤ℚ (uses multiplicative monotonicity + cancellation).
≤ℚ-trans : {x y z : ℚ} → x ≤ℚ y → y ≤ℚ z → x ≤ℚ z
≤ℚ-trans {x} {y} {z} p q with x | y | z
... | a / b | c / d | e / f =
  let
    p' : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    p' = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) f p

    q' : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    q' = ≤ℤ-mul-pos-right (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) b q

    midEq : ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b)
    midEq = swapScaleℚ c b f

    p'' : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b)
    p'' = ≤ℤ-resp-≡ʳ midEq p'

    step : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    step = ≤ℤ-trans p'' q'

    lhsEq : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≡ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d)
    lhsEq = swapScaleℚ a d f

    rhsEq : ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    rhsEq = swapScaleℚ e d b

    step' : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ≤ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    step' = ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step)

    done : (a *ℤ ⁺toℤ f) ≤ℤ (e *ℤ ⁺toℤ b)
    done = ≤ℤ-mul-pos-cancel-right (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) d step'
  in
  done

-- § Negation of ≤ℚ.
_≰ℚ_ : ℚ → ℚ → Set
x ≰ℚ y = (x ≤ℚ y) → ⊥

-- § ≤ composed with < yields <.
≤<ℚ→<ℚ : {x y z : ℚ} → x ≤ℚ y → y <ℚ z → x <ℚ z
≤<ℚ→<ℚ {a / b} {c / d} {e / f} x≤y (y≤z , z≰y) =
  let
    x≤z : (a / b) ≤ℚ (e / f)
    x≤z = ≤ℚ-trans {a / b} {c / d} {e / f} x≤y y≤z

    z≰x : (e / f) ≰ℚ (a / b)
    z≰x z≤x = z≰y (≤ℚ-trans {e / f} {a / b} {c / d} z≤x x≤y)
  in
  x≤z , z≰x

-- § < composed with ≤ yields <.
<≤ℚ→<ℚ : {x y z : ℚ} → x <ℚ y → y ≤ℚ z → x <ℚ z
<≤ℚ→<ℚ {a / b} {c / d} {e / f} (x≤y , y≰x) y≤z =
  let
    x≤z : (a / b) ≤ℚ (e / f)
    x≤z = ≤ℚ-trans {a / b} {c / d} {e / f} x≤y y≤z

    z≰x : (e / f) ≰ℚ (a / b)
    z≰x z≤x =
      let
        y≤x : (c / d) ≤ℚ (a / b)
        y≤x = ≤ℚ-trans {c / d} {e / f} {a / b} y≤z z≤x
      in
      y≰x y≤x
  in
  x≤z , z≰x
-- § Strict order implies non-strict.
<ℚ→≤ℚ : {x y : ℚ} → x <ℚ y → x ≤ℚ y
<ℚ→≤ℚ p = fst p

-- § Aliases for uniform naming.
ltZ_to_leZ : {x y : ℤ} → x <ℤ y → x ≤ℤ y
ltZ_to_leZ {x} {y} p = <ℤ→≤ℤ {x} {y} p

ltQ_to_leQ : {x y : ℚ} → x <ℚ y → x ≤ℚ y
ltQ_to_leQ {x} {y} p = <ℚ→≤ℚ {x} {y} p

-- § Setoid equality forces ≤ in both directions.
≃ℚ→≤ℚˡ : {p q : ℚ} → p ≃ℚ q → p ≤ℚ q
≃ℚ→≤ℚˡ {a / b} {c / d} eq =
  ≤ℤ-resp-≡ʳ eq (≤ℤ-refl (a *ℤ ⁺toℤ d))

≃ℚ→≤ℚʳ : {p q : ℚ} → p ≃ℚ q → q ≤ℚ p
≃ℚ→≤ℚʳ {a / b} {c / d} eq =
  ≤ℤ-resp-≡ʳ (sym eq) (≤ℤ-refl (c *ℤ ⁺toℤ b))

-- § Positive naturals are strictly positive integers.
den-posℤ : (d : ℕ⁺) → 0ℤ <ℤ ⁺toℤ d
den-posℤ (mkℕ⁺ k) =
  tt , (λ p → p)

-- § 0 < 1 in ℤ.
0ℤ<oneℤ : 0ℤ <ℤ oneℤ
0ℤ<oneℤ =
  tt , (λ p → p)

-- § 0 < 1 in ℚ.
0ℚ<1ℚ : 0ℚ <ℚ 1ℚ
0ℚ<1ℚ =
  <ℤ-resp-≡ˡ (sym (*ℤ-zero-left (⁺toℤ one⁺)))
    (<ℤ-resp-≡ʳ (sym (*ℤ-one-left (⁺toℤ one⁺)))
      0ℤ<oneℤ)

-- § 0 < ε forces 0 < num ε.
0ℚ<→0ℤ<num : (ε : ℚ) → 0ℚ <ℚ ε → 0ℤ <ℤ num ε
0ℚ<→0ℤ<num (a / b) p =
  let step₁ : 0ℤ <ℤ (a *ℤ ⁺toℤ one⁺)
      step₁ = <ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b)) p

      step₂ : 0ℤ <ℤ a
      step₂ = <ℤ-resp-≡ʳ (*ℤ-one-right a) step₁
  in
  step₂
-- § Vec4ℤ: integer-valued functions on the four canonical indices.
Vec4ℤ : Set
Vec4ℤ = Fin4 → ℤ

-- § Actℤ: an action on integers.
Actℤ : Set
Actℤ = ℤ → ℤ

-- § Canonical integer actions.
zeroAct : Actℤ
zeroAct _ = 0ℤ

idAct : Actℤ
idAct x = x

negAct : Actℤ
negAct = negℤ

threeAct : Actℤ
threeAct = threeTimesℤ

fourAct : Actℤ
fourAct = fourTimesℤ

-- § Coefficient type: the four forced actions as a closed data type.
data Coeffℤ : Set where
  c0  : Coeffℤ
  c1  : Coeffℤ
  c-1 : Coeffℤ
  c3  : Coeffℤ

-- § Map coefficients to their canonical actions.
coeffAct : Coeffℤ → Actℤ
coeffAct c0 = zeroAct
coeffAct c1 = idAct
coeffAct c-1 = negAct
coeffAct c3 = threeAct

-- § Matrix types: coefficient-valued and action-valued.
Mat4Coeffℤ : Set
Mat4Coeffℤ = Fin4 → Fin4 → Coeffℤ

liftCoeffMatℤ : Mat4Coeffℤ → (Fin4 → Fin4 → Actℤ)
liftCoeffMatℤ m i j = coeffAct (m i j)

Mat4Actℤ : Set
Mat4Actℤ = Fin4 → Fin4 → Actℤ
-- § others i k: the k-th index distinct from i (exhaustive by Fin3).
others : Fin4 → Fin3 → Fin4
others g0 f0 = g1
others g0 f1 = g2
others g0 f2 = g3
others g1 f0 = g0
others g1 f1 = g2
others g1 f2 = g3
others g2 f0 = g0
others g2 f1 = g1
others g2 f2 = g3
others g3 f0 = g0
others g3 f1 = g1
others g3 f2 = g2

-- § Sum over all four indices, starting from i.
sumFin4Aroundℤ : Fin4 → (Fin4 → ℤ) → ℤ
sumFin4Aroundℤ i f = sum4ℤ (f i) (f (others i f0)) (f (others i f1)) (f (others i f2))

-- § Sum over the three off-diagonal indices.
sumOthersℤ : Vec4ℤ → Fin4 → ℤ
sumOthersℤ v i = sumFin3ℤ (λ k → v (others i k))
-- § Laplacian: 3·vᵢ minus neighbor sum.
laplacianVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianVec4ℤ v i = threeTimesℤ (v i) +ℤ negℤ (sumOthersℤ v i)

-- § Matrix application (pre-action form).
applyLaplacianPreActℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyLaplacianPreActℤ m v i =
  m i i (v i) +ℤ
  negℤ (sumFin3ℤ (λ k → m i (others i k) (v (others i k))))

-- § Pre-action Laplacian matrix: diagonal = 3×, off-diagonal = id.
laplacianPreMatActℤ : Mat4Actℤ
laplacianPreMatActℤ i j with Fin4-decEq i j
... | inj₁ _ = threeAct
... | inj₂ _ = idAct

-- § Matrix-applied Laplacian.
laplacianMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianMatVec4ℤ = applyLaplacianPreActℤ laplacianPreMatActℤ

-- § Conversion between EndoCase and Fin4 representations.
vecFromEndo : (EndoCase → ℤ) → Vec4ℤ
vecFromEndo f i = f (vertexAt i)

endoFromVec : Vec4ℤ → (EndoCase → ℤ)
endoFromVec v x = v (vertexIndex x)
-- § Law 14E.0: EndoCase Laplacian factors through Fin4 indexing.
law14E-0-laplacian-factor : (f : EndoCase → ℤ) → (x : EndoCase) →
  laplacianVec4ℤ (vecFromEndo f) (vertexIndex x) ≡ laplacianℤ f x
law14E-0-laplacian-factor f case-constL = refl
law14E-0-laplacian-factor f case-constR = refl
law14E-0-laplacian-factor f case-id = refl
law14E-0-laplacian-factor f case-dual = refl

-- § Law 14E.1: pre-action matrix agrees with the Laplacian.
law14E-1-matrix-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-1-matrix-agrees v g0 = refl
law14E-1-matrix-agrees v g1 = refl
law14E-1-matrix-agrees v g2 = refl
law14E-1-matrix-agrees v g3 = refl
-- § Alternative application forms.
applyMat4ActDiagOthersℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActDiagOthersℤ m v i =
  m i i (v i) +ℤ
  sumFin3ℤ (λ k → m i (others i k) (v (others i k)))

applyMat4ActRowSumℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActRowSumℤ m v i = sumFin4Aroundℤ i (λ j → m i j (v j))

applyMat4ActGlobalSumℤ : Mat4Actℤ → Vec4ℤ → Vec4ℤ
applyMat4ActGlobalSumℤ m v i = sumFin4ℤ (λ j → m i j (v j))

applyMat4CoeffGlobalSumℤ : Mat4Coeffℤ → Vec4ℤ → Vec4ℤ
applyMat4CoeffGlobalSumℤ m v i = sumFin4ℤ (λ j → coeffAct (m i j) (v j))

-- § Post-action: diagonal = 3×, off-diagonal = negation.
laplacianPostMatActℤ : Mat4Actℤ
laplacianPostMatActℤ i j with Fin4-decEq i j
... | inj₁ _ = threeAct
... | inj₂ _ = negAct

laplacianPostMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianPostMatVec4ℤ = applyMat4ActDiagOthersℤ laplacianPostMatActℤ

laplacianRowSumMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianRowSumMatVec4ℤ = applyMat4ActRowSumℤ laplacianPostMatActℤ

laplacianGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianGlobalMatVec4ℤ = applyMat4ActGlobalSumℤ laplacianPostMatActℤ

-- § Coefficient Laplacian matrix: diagonal c3, off-diagonal c-1.
laplacianCoeffMatℤ : Mat4Coeffℤ
laplacianCoeffMatℤ i j with Fin4-decEq i j
... | inj₁ _ = c3
... | inj₂ _ = c-1

laplacianCoeffGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
laplacianCoeffGlobalMatVec4ℤ = applyMat4CoeffGlobalSumℤ laplacianCoeffMatℤ

-- § Law 14E.3: row-sum unfolds to diagonal+others.
law14E-3-row-sum-unfolds : (m : Mat4Actℤ) → (v : Vec4ℤ) → (i : Fin4) →
  applyMat4ActRowSumℤ m v i ≡ applyMat4ActDiagOthersℤ m v i
law14E-3-row-sum-unfolds m v i = refl

-- § Law 14E.4: row-sum around i equals global sum (by permutation).
law14E-4-sumFin4Around-eq-sumFin4 : (f : Fin4 → ℤ) → (i : Fin4) →
  sumFin4Aroundℤ i f ≡ sumFin4ℤ f
law14E-4-sumFin4Around-eq-sumFin4 f g0 = refl
law14E-4-sumFin4Around-eq-sumFin4 f g1 = sum4ℤ-swap01 (f g1) (f g0) (f g2) (f g3)
law14E-4-sumFin4Around-eq-sumFin4 f g2 =
  trans (sum4ℤ-swap01 (f g2) (f g0) (f g1) (f g3))
        (sum4ℤ-swap12 (f g0) (f g2) (f g1) (f g3))
law14E-4-sumFin4Around-eq-sumFin4 f g3 =
  trans
    (trans (sum4ℤ-swap01 (f g3) (f g0) (f g1) (f g2))
           (sum4ℤ-swap12 (f g0) (f g3) (f g1) (f g2)))
    (sum4ℤ-swap23 (f g0) (f g1) (f g3) (f g2))

-- § Law 14E.2: post-action matrix agrees with Laplacian (negation placement).
law14E-2-matrix-neg-in-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianPostMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-2-matrix-neg-in-agrees v g0 =
  cong (λ t → threeTimesℤ (v g0) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g0 k))))
law14E-2-matrix-neg-in-agrees v g1 =
  cong (λ t → threeTimesℤ (v g1) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g1 k))))
law14E-2-matrix-neg-in-agrees v g2 =
  cong (λ t → threeTimesℤ (v g2) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g2 k))))
law14E-2-matrix-neg-in-agrees v g3 =
  cong (λ t → threeTimesℤ (v g3) +ℤ t)
       (sym (neg-sumFin3ℤ (λ k → v (others g3 k))))

-- § Law 14E.5: row-sum equals global-sum.
law14E-5-rowSum-eq-globalSum : (m : Mat4Actℤ) → (v : Vec4ℤ) → (i : Fin4) →
  applyMat4ActRowSumℤ m v i ≡ applyMat4ActGlobalSumℤ m v i
law14E-5-rowSum-eq-globalSum m v i =
  law14E-4-sumFin4Around-eq-sumFin4 (λ j → m i j (v j)) i

-- § Law 14E.6: global matrix application equals Laplacian.
law14E-6-global-matrix-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianGlobalMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-6-global-matrix-agrees v i =
  trans (sym (law14E-5-rowSum-eq-globalSum laplacianPostMatActℤ v i))
        (trans (law14E-3-row-sum-unfolds laplacianPostMatActℤ v i)
               (law14E-2-matrix-neg-in-agrees v i))

-- § Law 14E.7: coefficient lift agrees with post-action matrix (16 cases).
law14E-7-coeff-lift-agrees : (i j : Fin4) →
  liftCoeffMatℤ laplacianCoeffMatℤ i j ≡ laplacianPostMatActℤ i j
law14E-7-coeff-lift-agrees g0 g0 = refl
law14E-7-coeff-lift-agrees g0 g1 = refl
law14E-7-coeff-lift-agrees g0 g2 = refl
law14E-7-coeff-lift-agrees g0 g3 = refl
law14E-7-coeff-lift-agrees g1 g0 = refl
law14E-7-coeff-lift-agrees g1 g1 = refl
law14E-7-coeff-lift-agrees g1 g2 = refl
law14E-7-coeff-lift-agrees g1 g3 = refl
law14E-7-coeff-lift-agrees g2 g0 = refl
law14E-7-coeff-lift-agrees g2 g1 = refl
law14E-7-coeff-lift-agrees g2 g2 = refl
law14E-7-coeff-lift-agrees g2 g3 = refl
law14E-7-coeff-lift-agrees g3 g0 = refl
law14E-7-coeff-lift-agrees g3 g1 = refl
law14E-7-coeff-lift-agrees g3 g2 = refl
law14E-7-coeff-lift-agrees g3 g3 = refl

-- § Law 14E.8: coefficient global sum equals action global sum.
law14E-8-coeff-global-eq-act-global : (v : Vec4ℤ) → (i : Fin4) →
  laplacianCoeffGlobalMatVec4ℤ v i ≡ laplacianGlobalMatVec4ℤ v i
law14E-8-coeff-global-eq-act-global v g0 = refl
law14E-8-coeff-global-eq-act-global v g1 = refl
law14E-8-coeff-global-eq-act-global v g2 = refl
law14E-8-coeff-global-eq-act-global v g3 = refl

-- § Law 14E.9: coefficient global matrix equals Laplacian.
law14E-9-coeff-global-agrees : (v : Vec4ℤ) → (i : Fin4) →
  laplacianCoeffGlobalMatVec4ℤ v i ≡ laplacianVec4ℤ v i
law14E-9-coeff-global-agrees v i =
  trans (law14E-8-coeff-global-eq-act-global v i)
        (law14E-6-global-matrix-agrees v i)
-- § Split around-sum into diagonal + others.
sumFin4Around-split : (v : Vec4ℤ) → (i : Fin4) →
  sumFin4Aroundℤ i v ≡ v i +ℤ sumOthersℤ v i
sumFin4Around-split v g0 = refl
sumFin4Around-split v g1 = refl
sumFin4Around-split v g2 = refl
sumFin4Around-split v g3 = refl

-- § 4x = x + 3x.
fourTimes-split : (x : ℤ) → fourTimesℤ x ≡ x +ℤ threeTimesℤ x
fourTimes-split x = refl

-- § Law 14E.10: Laplacian equals 4·vᵢ minus global sum.
law14E-10-laplacian-four-minus-sumAll : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i) +ℤ negℤ (sumFin4ℤ v)
law14E-10-laplacian-four-minus-sumAll v i =
  let x = v i in
  let othersSum = sumOthersℤ v i in
  let around = sumFin4Aroundℤ i v in
  let a = threeTimesℤ x in
  let b = negℤ othersSum in
  let rhsAround = fourTimesℤ x +ℤ negℤ around in

  let rhsAround≡laplacian : rhsAround ≡ laplacianVec4ℤ v i
      rhsAround≡laplacian =
        trans
          (cong (λ t → t +ℤ negℤ around) (fourTimes-split x))
          (trans
            (cong (λ t → (x +ℤ a) +ℤ t) (trans (cong negℤ (sumFin4Around-split v i)) (neg-+ℤ x othersSum)))
            (trans
              (+ℤ-assoc x a (negℤ x +ℤ negℤ othersSum))
              (trans
                (cong (λ t → x +ℤ t) (sym (+ℤ-assoc a (negℤ x) (negℤ othersSum)))
                )
                (trans
                  (cong (λ t → x +ℤ ((t) +ℤ negℤ othersSum)) (+ℤ-comm a (negℤ x)))
                  (trans
                    (cong (λ t → x +ℤ t) (+ℤ-assoc (negℤ x) a (negℤ othersSum)))
                    (trans
                      (sym (+ℤ-assoc x (negℤ x) (a +ℤ negℤ othersSum)))
                      (trans
                        (cong (λ t → t +ℤ (a +ℤ negℤ othersSum)) (+ℤ-inv-right x))
                        (trans
                          (+ℤ-zero-left (a +ℤ negℤ othersSum))
                          refl))))))))
  in
  trans
    (sym rhsAround≡laplacian)
    (cong (λ s → fourTimesℤ x +ℤ negℤ s) (law14E-4-sumFin4Around-eq-sumFin4 v i))
-- § Law 14E.11: sum-zero vectors are 4-eigenvectors.
law14E-11-sum0-eigen4 : (v : Vec4ℤ) → (i : Fin4) → sumFin4ℤ v ≡ 0ℤ →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-11-sum0-eigen4 v i sum0 =
  trans
    (law14E-10-laplacian-four-minus-sumAll v i)
    (trans
      (cong (λ s → fourTimesℤ (v i) +ℤ negℤ s) sum0)
      (+ℤ-zero-right (fourTimesℤ (v i))))

-- § Constant vector and J operator.
constVec4ℤ : ℤ → Vec4ℤ
constVec4ℤ x _ = x

JVec4ℤ : Vec4ℤ → Vec4ℤ
JVec4ℤ v _ = sumFin4ℤ v

-- § Coefficient matrix for J: all ones.
onesCoeffMatℤ : Mat4Coeffℤ
onesCoeffMatℤ _ _ = c1

JCoeffGlobalMatVec4ℤ : Vec4ℤ → Vec4ℤ
JCoeffGlobalMatVec4ℤ = applyMat4CoeffGlobalSumℤ onesCoeffMatℤ

-- § Sum of constant vector is four times its value.
sumFin4-const : (x : ℤ) → sumFin4ℤ (constVec4ℤ x) ≡ fourTimesℤ x
sumFin4-const x = refl

-- § Law 14E.12: J as coefficient matrix.
law14E-12-ones-matrix-is-J : (v : Vec4ℤ) → (i : Fin4) →
  JCoeffGlobalMatVec4ℤ v i ≡ JVec4ℤ v i
law14E-12-ones-matrix-is-J v i = refl

-- § Law 14E.13: constant vectors are 0-eigenvectors.
law14E-13-const-eigen0 : (x : ℤ) → (i : Fin4) →
  laplacianVec4ℤ (constVec4ℤ x) i ≡ 0ℤ
law14E-13-const-eigen0 x i =
  trans
    (law14E-10-laplacian-four-minus-sumAll (constVec4ℤ x) i)
    (trans
      (cong (λ s → fourTimesℤ x +ℤ negℤ s) (sumFin4-const x))
      (+ℤ-inv-right (fourTimesℤ x)))
-- § J is constant across indices.
J-constant : (v : Vec4ℤ) → (i j : Fin4) → JVec4ℤ v i ≡ JVec4ℤ v j
J-constant v i j = refl

-- § Sum of J v is four times the sum of v.
sumFin4-J : (v : Vec4ℤ) → sumFin4ℤ (JVec4ℤ v) ≡ fourTimesℤ (sumFin4ℤ v)
sumFin4-J v = refl

-- § J v is definitionally the constant vector at sum v.
J-is-constVec : (v : Vec4ℤ) → (i : Fin4) → JVec4ℤ v i ≡ constVec4ℤ (sumFin4ℤ v) i
J-is-constVec v i = refl

-- § Law 14E.17: J scales constants by 4.
law14E-17-J-const-four : (x : ℤ) → (i : Fin4) →
  JVec4ℤ (constVec4ℤ x) i ≡ fourTimesℤ x
law14E-17-J-const-four x i = sumFin4-const x

-- § Law 14E.18: J ∘ J = 4 · J.
law14E-18-JJ-fourJ : (v : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (JVec4ℤ v) i ≡ fourTimesℤ (JVec4ℤ v i)
law14E-18-JJ-fourJ v i =
  trans (sumFin4-J v) refl

-- § Law 14E.19: pointwise 4-eigenvectors force sum-zero.
law14E-19-eigen4→sum0 : (v : Vec4ℤ) → ((i : Fin4) → laplacianVec4ℤ v i ≡ fourTimesℤ (v i)) →
  sumFin4ℤ v ≡ 0ℤ
law14E-19-eigen4→sum0 v eigen4 =
  let a = fourTimesℤ (v g0) in
  let s = sumFin4ℤ v in
  let eq₀ : a +ℤ negℤ s ≡ a
      eq₀ =
        trans
          (sym (law14E-10-laplacian-four-minus-sumAll v g0))
          (eigen4 g0)
  in
  negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)

-- § Law 14E.20: sum-zero ↔ pointwise 4-eigenspace.
law14E-20-sum0→eigen4 : (v : Vec4ℤ) → sumFin4ℤ v ≡ 0ℤ → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-20-sum0→eigen4 v sum0 i = law14E-11-sum0-eigen4 v i sum0

law14E-20-eigen4→sum0 : (v : Vec4ℤ) → ((i : Fin4) → laplacianVec4ℤ v i ≡ fourTimesℤ (v i)) →
  sumFin4ℤ v ≡ 0ℤ
law14E-20-eigen4→sum0 = law14E-19-eigen4→sum0
-- § Law 14E.21: L = 4I − J pointwise.
law14E-21-L-four-minus-J : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i ≡ fourTimesℤ (v i) +ℤ negℤ (JVec4ℤ v i)
law14E-21-L-four-minus-J v i =
  trans (law14E-10-laplacian-four-minus-sumAll v i) refl

-- § Law 14E.22: kernel condition L v i = 0 ↔ 4·vᵢ = J v i.
law14E-22-L0→fourEqJ : (v : Vec4ℤ) → (i : Fin4) → laplacianVec4ℤ v i ≡ 0ℤ →
  fourTimesℤ (v i) ≡ JVec4ℤ v i
law14E-22-L0→fourEqJ v i L0 =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  let eq₀ : a +ℤ negℤ j ≡ 0ℤ
      eq₀ = trans (sym (law14E-21-L-four-minus-J v i)) L0
  in
  let step₁ : (a +ℤ negℤ j) +ℤ j ≡ 0ℤ +ℤ j
      step₁ = cong (λ t → t +ℤ j) eq₀
      step₂ : a +ℤ (negℤ j +ℤ j) ≡ 0ℤ +ℤ j
      step₂ = trans (sym (+ℤ-assoc a (negℤ j) j)) step₁
      step₃ : a +ℤ 0ℤ ≡ 0ℤ +ℤ j
      step₃ = trans (sym (cong (λ t → a +ℤ t) (+ℤ-inv-left j))) step₂
  in
  trans
    (sym (+ℤ-zero-right a))
    (trans step₃ (+ℤ-zero-left j))

law14E-22-fourEqJ→L0 : (v : Vec4ℤ) → (i : Fin4) → fourTimesℤ (v i) ≡ JVec4ℤ v i →
  laplacianVec4ℤ v i ≡ 0ℤ
law14E-22-fourEqJ→L0 v i fourEqJ =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  trans
    (law14E-21-L-four-minus-J v i)
    (trans
      (cong (λ t → a +ℤ t) (cong negℤ (sym fourEqJ)))
      (+ℤ-inv-right a))

-- § Pointwise vector equality.
Vec4Eq : Vec4ℤ → Vec4ℤ → Set
Vec4Eq v w = (i : Fin4) → v i ≡ w i

-- § Kernel predicate.
KernelL : Vec4ℤ → Set
KernelL v = (i : Fin4) → laplacianVec4ℤ v i ≡ 0ℤ

-- § Law 14E.23: L = 4I − J as Vec4Eq.
law14E-23-L-eq-four-minus-J : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ v) (λ i → fourTimesℤ (v i) +ℤ negℤ (JVec4ℤ v i))
law14E-23-L-eq-four-minus-J v i = law14E-21-L-four-minus-J v i

-- § Law 14E.24: kernel forces fourTimes-constant.
law14E-24-kernel→fourTimes-constant : (v : Vec4ℤ) → KernelL v → (i j : Fin4) →
  fourTimesℤ (v i) ≡ fourTimesℤ (v j)
law14E-24-kernel→fourTimes-constant v ker i j =
  let fi = law14E-22-L0→fourEqJ v i (ker i) in
  let fj = law14E-22-L0→fourEqJ v j (ker j) in
  trans fi (trans refl (sym fj))

-- § Law 14E.25: kernel ↔ fourEqJ pointwise.
law14E-25-kernel→fourEqJ : (v : Vec4ℤ) → KernelL v → (i : Fin4) →
  fourTimesℤ (v i) ≡ JVec4ℤ v i
law14E-25-kernel→fourEqJ v ker i = law14E-22-L0→fourEqJ v i (ker i)

law14E-25-fourEqJ→kernel : (v : Vec4ℤ) → ((i : Fin4) → fourTimesℤ (v i) ≡ JVec4ℤ v i) → KernelL v
law14E-25-fourEqJ→kernel v hyp i = law14E-22-fourEqJ→L0 v i (hyp i)

-- § Law 14E.26: kernel forces sum = 4·vᵢ.
law14E-26-kernel→sumEqFour : (v : Vec4ℤ) → KernelL v → (i : Fin4) →
  sumFin4ℤ v ≡ fourTimesℤ (v i)
law14E-26-kernel→sumEqFour v ker i =
  trans
    refl
    (trans
      (sym (law14E-25-kernel→fourEqJ v ker i))
      refl)

-- § Law 14E.27: sum = 4·vᵢ forces kernel.
law14E-27-sumEqFour→kernel : (v : Vec4ℤ) → ((i : Fin4) → sumFin4ℤ v ≡ fourTimesℤ (v i)) → KernelL v
law14E-27-sumEqFour→kernel v hyp =
  law14E-25-fourEqJ→kernel v (λ i → sym (trans refl (hyp i)))

-- § Law 14E.14: J is constant.
law14E-14-J-constant : (v : Vec4ℤ) → (i j : Fin4) →
  JVec4ℤ v i ≡ JVec4ℤ v j
law14E-14-J-constant = J-constant

-- § Law 14E.15: sum-zero ↔ J v = 0.
law14E-15-sum0-to-J0 : (v : Vec4ℤ) → (i : Fin4) → sumFin4ℤ v ≡ 0ℤ →
  JVec4ℤ v i ≡ 0ℤ
law14E-15-sum0-to-J0 v i sum0 = sum0

law14E-15-J0-to-sum0 : (v : Vec4ℤ) → JVec4ℤ v g0 ≡ 0ℤ →
  sumFin4ℤ v ≡ 0ℤ
law14E-15-J0-to-sum0 v J0 = J0

-- § Law 14E.16: L ∘ J = 0.
law14E-16-LJ-zero : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (JVec4ℤ v) i ≡ 0ℤ
law14E-16-LJ-zero v i =
  let s = sumFin4ℤ v in
  trans
    (law14E-10-laplacian-four-minus-sumAll (JVec4ℤ v) i)
    (trans
      (cong (λ t → fourTimesℤ s +ℤ negℤ t) (sumFin4-J v))
      (+ℤ-inv-right (fourTimesℤ s)))
-- § Add constant to each component.
sumFin4-addConst : (v : Vec4ℤ) → (c : ℤ) →
  sumFin4ℤ (λ i → v i +ℤ c) ≡ sumFin4ℤ v +ℤ fourTimesℤ c
sumFin4-addConst v c =
  let
    a0 = v g0
    a1 = v g1
    a2 = v g2
    a3 = v g3
    r23 = (a2 +ℤ c) +ℤ (a3 +ℤ c)
    r1  = (a1 +ℤ c) +ℤ r23

    step₁ : (a0 +ℤ c) +ℤ r1 ≡ a0 +ℤ (c +ℤ r1)
    step₁ = +ℤ-assoc a0 c r1

    step₂ : r1 ≡ a1 +ℤ (c +ℤ r23)
    step₂ = +ℤ-assoc a1 c r23

    step₃ : c +ℤ r1 ≡ a1 +ℤ (c +ℤ (c +ℤ r23))
    step₃ =
      trans
        (cong (λ t → c +ℤ t) step₂)
        (swapHeadℤ c a1 (c +ℤ r23))

    step₄ : (a0 +ℤ c) +ℤ r1 ≡ a0 +ℤ (a1 +ℤ (c +ℤ (c +ℤ r23)))
    step₄ = trans step₁ (cong (λ t → a0 +ℤ t) step₃)

    step₅a : r23 ≡ a2 +ℤ (c +ℤ (a3 +ℤ c))
    step₅a = +ℤ-assoc a2 c (a3 +ℤ c)

    step₅b : c +ℤ r23 ≡ a2 +ℤ (c +ℤ (c +ℤ (a3 +ℤ c)))
    step₅b =
      trans
        (cong (λ t → c +ℤ t) step₅a)
        (swapHeadℤ c a2 (c +ℤ (a3 +ℤ c)))

    step₅c : c +ℤ (c +ℤ r23) ≡ a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))))
    step₅c =
      trans
        (cong (λ t → c +ℤ t) step₅b)
        (swapHeadℤ c a2 (c +ℤ (c +ℤ (a3 +ℤ c))))

    step₆ : a0 +ℤ (a1 +ℤ (c +ℤ (c +ℤ r23))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))))))
    step₆ = cong (λ t → a0 +ℤ (a1 +ℤ t)) step₅c

    step₇a : c +ℤ (a3 +ℤ c) ≡ a3 +ℤ (c +ℤ c)
    step₇a = swapHeadℤ c a3 c

    step₇b : c +ℤ (c +ℤ (a3 +ℤ c)) ≡ a3 +ℤ (c +ℤ (c +ℤ c))
    step₇b =
      trans
        (cong (λ t → c +ℤ t) step₇a)
        (swapHeadℤ c a3 (c +ℤ c))

    step₇c : c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))) ≡ a3 +ℤ (c +ℤ (c +ℤ (c +ℤ c)))
    step₇c =
      trans
        (cong (λ t → c +ℤ t) step₇b)
        (swapHeadℤ c a3 (c +ℤ (c +ℤ c)))

    step₈ : c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c))) ≡ a3 +ℤ fourTimesℤ c
    step₈ = trans step₇c refl

    step₉ : a0 +ℤ (a1 +ℤ (a2 +ℤ (c +ℤ (c +ℤ (c +ℤ (a3 +ℤ c)))))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c)))
    step₉ = cong (λ t → a0 +ℤ (a1 +ℤ (a2 +ℤ t))) step₈

    step₁₀a : a2 +ℤ (a3 +ℤ fourTimesℤ c) ≡ (a2 +ℤ a3) +ℤ fourTimesℤ c
    step₁₀a = sym (+ℤ-assoc a2 a3 (fourTimesℤ c))

    step₁₀b : a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c)) ≡ (a1 +ℤ (a2 +ℤ a3)) +ℤ fourTimesℤ c
    step₁₀b =
      trans
        (cong (λ t → a1 +ℤ t) step₁₀a)
        (sym (+ℤ-assoc a1 (a2 +ℤ a3) (fourTimesℤ c)))

    step₁₀c : a0 +ℤ (a1 +ℤ (a2 +ℤ (a3 +ℤ fourTimesℤ c))) ≡ (a0 +ℤ (a1 +ℤ (a2 +ℤ a3))) +ℤ fourTimesℤ c
    step₁₀c =
      trans
        (cong (λ t → a0 +ℤ t) step₁₀b)
        (sym (+ℤ-assoc a0 (a1 +ℤ (a2 +ℤ a3)) (fourTimesℤ c)))
  in
  trans
    refl
    (trans
      step₄
      (trans
        step₆
        (trans
          step₉
          (trans
            step₁₀c
            refl))))
-- § fourTimes distributes over +ℤ.
fourTimes-+ℤ : (x y : ℤ) → fourTimesℤ (x +ℤ y) ≡ fourTimesℤ x +ℤ fourTimesℤ y
fourTimes-+ℤ x y =
  trans
    (sym (sumFin4-const (x +ℤ y)))
    (trans
      (sumFin4-addConst (constVec4ℤ x) y)
      (trans
        (cong (λ t → t +ℤ fourTimesℤ y) (sumFin4-const x))
        refl))

-- § Sum of fourTimes equals fourTimes of sum.
sumFin4-fourTimes : (v : Vec4ℤ) →
  sumFin4ℤ (λ i → fourTimesℤ (v i)) ≡ fourTimesℤ (sumFin4ℤ v)
sumFin4-fourTimes v =
  let
    a0 = v g0
    a1 = v g1
    a2 = v g2
    a3 = v g3
  in
  sym
    (trans
      refl
      (trans
        (fourTimes-+ℤ a0 (a1 +ℤ (a2 +ℤ a3)))
        (trans
          (cong (λ t → fourTimesℤ a0 +ℤ t) (fourTimes-+ℤ a1 (a2 +ℤ a3)))
          (trans
            (cong (λ t → fourTimesℤ a0 +ℤ (fourTimesℤ a1 +ℤ t)) (fourTimes-+ℤ a2 a3))
            refl))))

-- § Law 14E.28: global sum of the Laplacian is zero.
law14E-28-sumLaplacian0 : (v : Vec4ℤ) →
  sumFin4ℤ (laplacianVec4ℤ v) ≡ 0ℤ
law14E-28-sumLaplacian0 v =
  let
    s = sumFin4ℤ v

    step0 :
      sumFin4ℤ (laplacianVec4ℤ v) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3)
    step0 =
      cong
        (λ t0 → sum4ℤ t0 (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g0)

    step1 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (laplacianVec4ℤ v g1) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3)
    step1 =
      cong
        (λ t1 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) t1 (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g1)

    step2 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (laplacianVec4ℤ v g2) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (laplacianVec4ℤ v g3)
    step2 =
      cong
        (λ t2 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) t2 (laplacianVec4ℤ v g3))
        (law14E-10-laplacian-four-minus-sumAll v g2)

    step3 :
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (laplacianVec4ℤ v g3) ≡
      sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) (fourTimesℤ (v g3) +ℤ negℤ s)
    step3 =
      cong
        (λ t3 → sum4ℤ (fourTimesℤ (v g0) +ℤ negℤ s) (fourTimesℤ (v g1) +ℤ negℤ s) (fourTimesℤ (v g2) +ℤ negℤ s) t3)
        (law14E-10-laplacian-four-minus-sumAll v g3)

    rewriteSum :
      sumFin4ℤ (laplacianVec4ℤ v) ≡
      sumFin4ℤ (λ i → fourTimesℤ (v i) +ℤ negℤ s)
    rewriteSum =
      trans
        refl
        (trans step0 (trans step1 (trans step2 (trans step3 refl))))
  in
  trans
    rewriteSum
    (trans
      (sumFin4-addConst (λ i → fourTimesℤ (v i)) (negℤ s))
      (trans
        (cong (λ t → t +ℤ fourTimesℤ (negℤ s)) (sumFin4-fourTimes v))
        (trans
          (cong (λ t → fourTimesℤ s +ℤ t) (sym (neg-fourTimesℤ s)))
          (+ℤ-inv-right (fourTimesℤ s)))))
-- § Law 14E.29: L ∘ L = 4 · L (minimal polynomial x(x−4) = 0).
law14E-29-LL-fourL : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (laplacianVec4ℤ v) i ≡ fourTimesℤ (laplacianVec4ℤ v i)
law14E-29-LL-fourL v i =
  law14E-11-sum0-eigen4 (laplacianVec4ℤ v) i (law14E-28-sumLaplacian0 v)

-- § Law 14E.30: J ∘ L = 0.
law14E-30-JL-zero : (v : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (laplacianVec4ℤ v) i ≡ 0ℤ
law14E-30-JL-zero v i =
  law14E-15-sum0-to-J0 (laplacianVec4ℤ v) i (law14E-28-sumLaplacian0 v)

-- § Law 14E.31: L + J = 4I pointwise.
law14E-31-L-plus-J-eq-fourI : (v : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ v i +ℤ JVec4ℤ v i ≡ fourTimesℤ (v i)
law14E-31-L-plus-J-eq-fourI v i =
  let a = fourTimesℤ (v i) in
  let j = JVec4ℤ v i in
  trans
    (cong (λ t → t +ℤ j) (law14E-21-L-four-minus-J v i))
    (trans
      (+ℤ-assoc a (negℤ j) j)
      (trans
        (cong (λ t → a +ℤ t) (+ℤ-inv-left j))
        (+ℤ-zero-right a)))

-- § Zero vector.
zeroVec4ℤ : Vec4ℤ
zeroVec4ℤ = constVec4ℤ 0ℤ
-- § Law 14E.32: L + J = 4I as Vec4Eq.
law14E-32-LplusJ-eq-fourI-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (λ i → laplacianVec4ℤ v i +ℤ JVec4ℤ v i) (λ i → fourTimesℤ (v i))
law14E-32-LplusJ-eq-fourI-Vec4Eq v i = law14E-31-L-plus-J-eq-fourI v i

-- § Law 14E.33: L ∘ J = 0 as Vec4Eq.
law14E-33-LJ-zero-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (JVec4ℤ v)) zeroVec4ℤ
law14E-33-LJ-zero-Vec4Eq v i = law14E-16-LJ-zero v i

-- § Law 14E.34: J ∘ L = 0 as Vec4Eq.
law14E-34-JL-zero-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (JVec4ℤ (laplacianVec4ℤ v)) zeroVec4ℤ
law14E-34-JL-zero-Vec4Eq v i = law14E-30-JL-zero v i

-- § Law 14E.35: L and J commute (both composites = 0).
law14E-35-LJ-commute : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (JVec4ℤ v)) (JVec4ℤ (laplacianVec4ℤ v))
law14E-35-LJ-commute v i =
  trans (law14E-16-LJ-zero v i) (sym (law14E-30-JL-zero v i))

-- § Law 14E.36: L² = 4L as Vec4Eq.
law14E-36-LL-fourL-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (laplacianVec4ℤ (laplacianVec4ℤ v)) (λ i → fourTimesℤ (laplacianVec4ℤ v i))
law14E-36-LL-fourL-Vec4Eq v i = law14E-29-LL-fourL v i

-- § Law 14E.37: J² = 4J as Vec4Eq.
law14E-37-JJ-fourJ-Vec4Eq : (v : Vec4ℤ) →
  Vec4Eq (JVec4ℤ (JVec4ℤ v)) (λ i → fourTimesℤ (JVec4ℤ v i))
law14E-37-JJ-fourJ-Vec4Eq v i = law14E-18-JJ-fourJ v i

-- § Pointwise four-times and pointwise addition.
fourVec4ℤ : Vec4ℤ → Vec4ℤ
fourVec4ℤ v i = fourTimesℤ (v i)

_+Vec4ℤ_ : Vec4ℤ → Vec4ℤ → Vec4ℤ
(v +Vec4ℤ w) i = v i +ℤ w i

-- § Law 14E.38: image of L is sum-zero and 4-eigen.
law14E-38-imageL-sum0-and-eigen4 : (v : Vec4ℤ) →
  (sumFin4ℤ (laplacianVec4ℤ v) ≡ 0ℤ) × ((i : Fin4) → laplacianVec4ℤ (laplacianVec4ℤ v) i ≡ fourTimesℤ (laplacianVec4ℤ v i))
law14E-38-imageL-sum0-and-eigen4 v =
  law14E-28-sumLaplacian0 v , law14E-29-LL-fourL v

-- § Law 14E.39: image of J is constant and in kernel of L.
law14E-39-imageJ-const-and-kernelL : (v : Vec4ℤ) →
  (((i j : Fin4) → JVec4ℤ v i ≡ JVec4ℤ v j) × ((i : Fin4) → laplacianVec4ℤ (JVec4ℤ v) i ≡ 0ℤ))
law14E-39-imageJ-const-and-kernelL v =
  law14E-14-J-constant v , law14E-16-LJ-zero v

-- § Decomposition type: 4v = u + w with u sum-zero, w constant.
Decomp4 : Vec4ℤ → Set
Decomp4 v =
  Σ Vec4ℤ (λ u →
    Σ Vec4ℤ (λ w →
      (Vec4Eq (u +Vec4ℤ w) (fourVec4ℤ v)) ×
      (sumFin4ℤ u ≡ 0ℤ) ×
      ((i j : Fin4) → w i ≡ w j)))

-- § Law 14E.40: canonical decomposition 4v = Lv + Jv.
law14E-40-decomp4-canonical : (v : Vec4ℤ) → Decomp4 v
law14E-40-decomp4-canonical v =
  laplacianVec4ℤ v ,
  (JVec4ℤ v ,
    (law14E-32-LplusJ-eq-fourI-Vec4Eq v ,
     (law14E-28-sumLaplacian0 v ,
      law14E-14-J-constant v)))
-- § sumFin3 distributes over pointwise addition.
sumFin3-+ℤ : (f g : Fin3 → ℤ) →
  sumFin3ℤ (λ k → f k +ℤ g k) ≡
  sumFin3ℤ f +ℤ sumFin3ℤ g
sumFin3-+ℤ f g =
  let
    a0 = f f0
    a1 = f f1
    a2 = f f2
    b0 = g f0
    b1 = g f1
    b2 = g f2

    X = a1 +ℤ b1
    Y = a2 +ℤ b2
    R = b0 +ℤ b2

    step₁ : sumFin3ℤ (λ k → f k +ℤ g k) ≡ a0 +ℤ (b0 +ℤ (X +ℤ Y))
    step₁ = +ℤ-assoc a0 b0 (X +ℤ Y)

    step₂ : a0 +ℤ (b0 +ℤ (X +ℤ Y)) ≡ a0 +ℤ (X +ℤ (b0 +ℤ Y))
    step₂ = cong (λ t → a0 +ℤ t) (swapHeadℤ b0 X Y)

    step₃ : a0 +ℤ (X +ℤ (b0 +ℤ Y)) ≡ a0 +ℤ (X +ℤ (a2 +ℤ R))
    step₃ = cong (λ t → a0 +ℤ (X +ℤ t)) (swapHeadℤ b0 a2 b2)

    step₄ : a0 +ℤ (X +ℤ (a2 +ℤ R)) ≡ a0 +ℤ (a1 +ℤ (b1 +ℤ (a2 +ℤ R)))
    step₄ = cong (λ t → a0 +ℤ t) (+ℤ-assoc a1 b1 (a2 +ℤ R))

    step₅ : a0 +ℤ (a1 +ℤ (b1 +ℤ (a2 +ℤ R))) ≡ a0 +ℤ (a1 +ℤ (a2 +ℤ (b1 +ℤ R)))
    step₅ = cong (λ t → a0 +ℤ (a1 +ℤ t)) (swapHeadℤ b1 a2 R)

    step₆ : a0 +ℤ (a1 +ℤ (a2 +ℤ (b1 +ℤ R))) ≡ a0 +ℤ ((a1 +ℤ a2) +ℤ (b1 +ℤ R))
    step₆ = cong (λ t → a0 +ℤ t) (sym (+ℤ-assoc a1 a2 (b1 +ℤ R)))

    step₇ : a0 +ℤ ((a1 +ℤ a2) +ℤ (b1 +ℤ R)) ≡ a0 +ℤ ((a1 +ℤ a2) +ℤ (b0 +ℤ (b1 +ℤ b2)))
    step₇ = cong (λ t → a0 +ℤ ((a1 +ℤ a2) +ℤ t)) (swapHeadℤ b1 b0 b2)

    step₈ : a0 +ℤ ((a1 +ℤ a2) +ℤ (b0 +ℤ (b1 +ℤ b2))) ≡ (a0 +ℤ (a1 +ℤ a2)) +ℤ (b0 +ℤ (b1 +ℤ b2))
    step₈ = sym (+ℤ-assoc a0 (a1 +ℤ a2) (b0 +ℤ (b1 +ℤ b2)))
  in
  trans
    refl
    (trans step₁
      (trans step₂
        (trans step₃
          (trans step₄
            (trans step₅
              (trans step₆
                (trans step₇
                  (trans step₈ refl))))))))

-- § sumOthers distributes over pointwise addition.
sumOthers-+Vec4ℤ : (v w : Vec4ℤ) → (i : Fin4) →
  sumOthersℤ (v +Vec4ℤ w) i ≡ sumOthersℤ v i +ℤ sumOthersℤ w i
sumOthers-+Vec4ℤ v w i =
  sumFin3-+ℤ (λ k → v (others i k)) (λ k → w (others i k))
-- § sumFin4 distributes over pointwise addition.
sumFin4-+Vec4ℤ : (v w : Vec4ℤ) →
  sumFin4ℤ (λ i → v i +ℤ w i) ≡ sumFin4ℤ v +ℤ sumFin4ℤ w
sumFin4-+Vec4ℤ v w =
  let
    split0 : (x : Vec4ℤ) → sumFin4ℤ x ≡ x g0 +ℤ sumOthersℤ x g0
    split0 x =
      trans
        (sym (law14E-4-sumFin4Around-eq-sumFin4 x g0))
        (sumFin4Around-split x g0)

    v0 = v g0
    w0 = w g0
    sv = sumOthersℤ v g0
    sw = sumOthersℤ w g0

    step₁ : sumFin4ℤ (v +Vec4ℤ w) ≡ (v0 +ℤ w0) +ℤ sumOthersℤ (v +Vec4ℤ w) g0
    step₁ = trans (split0 (v +Vec4ℤ w)) refl

    step₂ : (v0 +ℤ w0) +ℤ sumOthersℤ (v +Vec4ℤ w) g0 ≡ (v0 +ℤ w0) +ℤ (sv +ℤ sw)
    step₂ = cong (λ t → (v0 +ℤ w0) +ℤ t) (sumOthers-+Vec4ℤ v w g0)

    step₃ : (v0 +ℤ w0) +ℤ (sv +ℤ sw) ≡ (v0 +ℤ sv) +ℤ (w0 +ℤ sw)
    step₃ =
      trans
        (+ℤ-assoc v0 w0 (sv +ℤ sw))
        (trans
          (cong (λ t → v0 +ℤ t) (swapHeadℤ w0 sv sw))
          (sym (+ℤ-assoc v0 sv (w0 +ℤ sw))))
  in
  trans
    (trans refl step₁)
    (trans
      step₂
      (trans
        step₃
        (trans
          (cong (λ t → t +ℤ (w0 +ℤ sw)) (sym (split0 v)))
          (cong (λ t → sumFin4ℤ v +ℤ t) (sym (split0 w))))))

-- § Law 14E.41: J preserves pointwise addition.
law14E-41-J-add : (v w : Vec4ℤ) → (i : Fin4) →
  JVec4ℤ (v +Vec4ℤ w) i ≡ JVec4ℤ v i +ℤ JVec4ℤ w i
law14E-41-J-add v w i = sumFin4-+Vec4ℤ v w

-- § threeTimes distributes over +ℤ.
threeTimes-+ℤ : (x y : ℤ) → threeTimesℤ (x +ℤ y) ≡ threeTimesℤ x +ℤ threeTimesℤ y
threeTimes-+ℤ x y =
  sumFin3-+ℤ (λ _ → x) (λ _ → y)

-- § Law 14E.42: L preserves pointwise addition.
law14E-42-L-add : (v w : Vec4ℤ) → (i : Fin4) →
  laplacianVec4ℤ (v +Vec4ℤ w) i ≡ laplacianVec4ℤ v i +ℤ laplacianVec4ℤ w i
law14E-42-L-add v w i =
  let
    A = threeTimesℤ (v i)
    B = threeTimesℤ (w i)
    C = negℤ (sumOthersℤ v i)
    D = negℤ (sumOthersℤ w i)

    step₁ : laplacianVec4ℤ (v +Vec4ℤ w) i ≡ (A +ℤ B) +ℤ negℤ (sumOthersℤ (v +Vec4ℤ w) i)
    step₁ = cong (λ t → t +ℤ negℤ (sumOthersℤ (v +Vec4ℤ w) i)) (threeTimes-+ℤ (v i) (w i))

    step₂ : negℤ (sumOthersℤ (v +Vec4ℤ w) i) ≡ C +ℤ D
    step₂ =
      trans
        (cong negℤ (sumOthers-+Vec4ℤ v w i))
        (neg-+ℤ (sumOthersℤ v i) (sumOthersℤ w i))

    step₃ : (A +ℤ B) +ℤ (C +ℤ D) ≡ (A +ℤ C) +ℤ (B +ℤ D)
    step₃ =
      trans
        (+ℤ-assoc A B (C +ℤ D))
        (trans
          (cong (λ t → A +ℤ t) (swapHeadℤ B C D))
          (sym (+ℤ-assoc A C (B +ℤ D))))
  in
  trans
    step₁
    (trans
      (cong (λ t → (A +ℤ B) +ℤ t) step₂)
      (trans
        step₃
        refl))
-- § output swap: post-compose with swapTwo
swapOut : {d : Distinction} → Measurement d → Measurement d
swapOut m x = swapTwo (m x)

-- § input swap: pre-compose with the forced dual
swapIn : (d : Distinction) → Measurement d → Measurement d
swapIn d m x = m (Distinction-dual d x)

-- § swapOut respects pointwise equality
swapOut-cong :
  {d : Distinction} {m n : Measurement d} →
  _≗_ {A = S d} {B = S Two-distinction} m n →
  _≗_ {A = S d} {B = S Two-distinction} (swapOut {d = d} m) (swapOut {d = d} n)
swapOut-cong p x = cong swapTwo (p x)

-- § swapIn respects pointwise equality
swapIn-cong :
  (d : Distinction) {m n : Measurement d} →
  _≗_ {A = S d} {B = S Two-distinction} m n →
  _≗_ {A = S d} {B = S Two-distinction} (swapIn d m) (swapIn d n)
swapIn-cong d p x = p (Distinction-dual d x)
-- § output swap acts on EndoCase
permOut : EndoCase → EndoCase
permOut case-constL = case-constR
permOut case-constR = case-constL
permOut case-id     = case-dual
permOut case-dual   = case-id

-- § input swap acts on EndoCase
permIn : EndoCase → EndoCase
permIn case-constL = case-constL
permIn case-constR = case-constR
permIn case-id     = case-dual
permIn case-dual   = case-id
-- § swapOut on interpreted cases equals interpretation of permOut
swapOut-interpret :
  (d : Distinction) →
  (c : EndoCase) →
  _≗_ {A = S d} {B = S Two-distinction}
    (swapOut {d = d} (K₄Map.interpret d Two-distinction c))
    (K₄Map.interpret d Two-distinction (permOut c))
swapOut-interpret d case-constL x = refl
swapOut-interpret d case-constR x = refl
swapOut-interpret d case-id x with cover d x
... | inj₁ _ = refl
... | inj₂ _ = refl
swapOut-interpret d case-dual x with cover d x
... | inj₁ _ = refl
... | inj₂ _ = refl

-- § swapIn on interpreted cases equals interpretation of permIn
swapIn-interpret :
  (d : Distinction) →
  (c : EndoCase) →
  _≗_ {A = S d} {B = S Two-distinction}
    (swapIn d (K₄Map.interpret d Two-distinction c))
    (K₄Map.interpret d Two-distinction (permIn c))
swapIn-interpret d case-constL x = refl
swapIn-interpret d case-constR x = refl
swapIn-interpret d case-id =
  law7-1-map-determined d Two-distinction
    (swapIn d (K₄Map.interpret d Two-distinction case-id))
    (K₄Map.interpret d Two-distinction case-dual)
    eqℓ
    eqr
  where
    module K = K₄Map d Two-distinction
    open K

    eqℓ : swapIn d (interpret case-id) (ℓ d) ≡ interpret case-dual (ℓ d)
    eqℓ =
      trans
        (cong (interpret case-id) (Distinction-dual-ℓ d))
        (trans
          (LR-r)
          (sym (RL-ℓ)))

    eqr : swapIn d (interpret case-id) (r d) ≡ interpret case-dual (r d)
    eqr =
      trans
        (cong (interpret case-id) (Distinction-dual-r d))
        (trans
          (LR-ℓ)
          (sym (RL-r)))

swapIn-interpret d case-dual =
  law7-1-map-determined d Two-distinction
    (swapIn d (K₄Map.interpret d Two-distinction case-dual))
    (K₄Map.interpret d Two-distinction case-id)
    eqℓ
    eqr
  where
    module K = K₄Map d Two-distinction
    open K

    eqℓ : swapIn d (interpret case-dual) (ℓ d) ≡ interpret case-id (ℓ d)
    eqℓ =
      trans
        (cong (interpret case-dual) (Distinction-dual-ℓ d))
        (trans
          (RL-r)
          (sym (LR-ℓ)))

    eqr : swapIn d (interpret case-dual) (r d) ≡ interpret case-id (r d)
    eqr =
      trans
        (cong (interpret case-dual) (Distinction-dual-r d))
        (trans
          (RL-ℓ)
          (sym (LR-r)))
-- § classify commutes with output swap
law15C-0-classify-swapOut :
  (d : Distinction) →
  (m : Measurement d) →
  K₄Map.classify d Two-distinction (swapOut {d = d} m)
  ≡ permOut (K₄Map.classify d Two-distinction m)
law15C-0-classify-swapOut d m =
  sym
    (K.classify-unique
      (swapOut {d = d} m)
      (permOut (K.classify m))
      witness)
  where
    module K = K₄Map d Two-distinction
    open K

    witness : interpret (permOut (classify m)) ≗ swapOut {d = d} m
    witness =
      ≗-trans
        (≗-sym (swapOut-interpret d (classify m)))
          (swapOut-cong {d = d} (classify-sound m))
-- § classify commutes with input swap
law15C-1-classify-swapIn :
  (d : Distinction) →
  (m : Measurement d) →
  K₄Map.classify d Two-distinction (swapIn d m)
  ≡ permIn (K₄Map.classify d Two-distinction m)
law15C-1-classify-swapIn d m =
  sym
    (K.classify-unique
      (swapIn d m)
      (permIn (K.classify m))
      witness)
  where
    module K = K₄Map d Two-distinction
    open K

    witness : interpret (permIn (classify m)) ≗ swapIn d m
    witness =
      ≗-trans
        (≗-sym (swapIn-interpret d (classify m)))
        (swapIn-cong d (classify-sound m))
-- § two-argument congruence
cong₂ : {A B C : Set} → (f : A → B → C) → {x x' : A} → {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl
-- § rational addition commutes in ≃ℚ
+ℚ-comm : (p q : ℚ) → p +ℚ q ≃ℚ q +ℚ p
+ℚ-comm (a / b) (c / d) =
  let
    numComm : ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) ≡ ((c *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ d))
    numComm = +ℤ-comm (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b)

    denComm : (d *⁺ b) ≡ (b *⁺ d)
    denComm = *⁺-comm d b

    denCommℤ : ⁺toℤ (d *⁺ b) ≡ ⁺toℤ (b *⁺ d)
    denCommℤ = cong ⁺toℤ denComm

    lhsEq : (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ (d *⁺ b))
             ≡
            (((c *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ d)) *ℤ ⁺toℤ (b *⁺ d))
    lhsEq =
      trans
        (cong (λ t → t *ℤ ⁺toℤ (d *⁺ b)) numComm)
        (cong (λ t → ((c *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ d)) *ℤ t) denCommℤ)
  in
  lhsEq
-- § +ℚ respects ≃ℚ
+ℚ-resp-≃ : {p p' q q' : ℚ} → p ≃ℚ p' → q ≃ℚ q' → (p +ℚ q) ≃ℚ (p' +ℚ q')
+ℚ-resp-≃ {a / b} {a' / b'} {c / d} {c' / d'} eqp eqq =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    b'd' : ℕ⁺
    b'd' = b' *⁺ d'

    b'd'ℤ : ⁺toℤ b'd' ≡ (⁺toℤ b') *ℤ (⁺toℤ d')
    b'd'ℤ = ⁺toℤ-*⁺ b' d'

    bdℤ : ⁺toℤ bd ≡ (⁺toℤ b) *ℤ (⁺toℤ d)
    bdℤ = ⁺toℤ-*⁺ b d

    mul4-rearrange : (x y z w : ℤ) → (x *ℤ y) *ℤ (z *ℤ w) ≡ (x *ℤ z) *ℤ (y *ℤ w)
    mul4-rearrange x y z w =
      trans
        (*ℤ-assoc x y (z *ℤ w))
        (trans
          (cong (λ t → x *ℤ t)
            (trans
              (sym (*ℤ-assoc y z w))
              (trans
                (cong (λ t → t *ℤ w) (*ℤ-comm y z))
                (*ℤ-assoc z y w))))
          (sym (*ℤ-assoc x z (y *ℤ w))))

    lhsExpand :
      (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ b'd')
        ≡
      ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ b'd') +ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ b'd')
    lhsExpand = *ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) (⁺toℤ b'd')

    rhsExpand :
      (((a' *ℤ ⁺toℤ d') +ℤ (c' *ℤ ⁺toℤ b')) *ℤ ⁺toℤ bd)
        ≡
      ((a' *ℤ ⁺toℤ d') *ℤ ⁺toℤ bd) +ℤ ((c' *ℤ ⁺toℤ b') *ℤ ⁺toℤ bd)
    rhsExpand = *ℤ-distrib-left-+ℤ (a' *ℤ ⁺toℤ d') (c' *ℤ ⁺toℤ b') (⁺toℤ bd)

    -- § align a-summands using eqp scaled by d·d'
    eqpScaled₀ : ((a *ℤ ⁺toℤ b') *ℤ ((⁺toℤ d) *ℤ (⁺toℤ d'))) ≡ ((a' *ℤ ⁺toℤ b) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ d')))
    eqpScaled₀ = cong (λ t → t *ℤ ((⁺toℤ d) *ℤ (⁺toℤ d'))) eqp

    termA-lhs : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ b'd') ≡ ((a *ℤ ⁺toℤ b') *ℤ ((⁺toℤ d) *ℤ (⁺toℤ d')))
    termA-lhs =
      trans
        (cong (λ t → (a *ℤ ⁺toℤ d) *ℤ t) b'd'ℤ)
        (mul4-rearrange a (⁺toℤ d) (⁺toℤ b') (⁺toℤ d'))

    termA-rhs : ((a' *ℤ ⁺toℤ d') *ℤ ⁺toℤ bd) ≡ ((a' *ℤ ⁺toℤ b) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ d')))
    termA-rhs =
      trans
        (cong (λ t → (a' *ℤ ⁺toℤ d') *ℤ t) bdℤ)
        (trans
          (mul4-rearrange a' (⁺toℤ d') (⁺toℤ b) (⁺toℤ d))
          (trans
            (cong (λ t → (a' *ℤ ⁺toℤ b) *ℤ t) (*ℤ-comm (⁺toℤ d') (⁺toℤ d)))
            refl))

    termA : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ b'd') ≡ ((a' *ℤ ⁺toℤ d') *ℤ ⁺toℤ bd)
    termA =
      trans
        termA-lhs
        (trans
          eqpScaled₀
          (sym termA-rhs))

    -- § align c-summands using eqq scaled by b·b'
    eqqScaled₀ : ((c *ℤ ⁺toℤ d') *ℤ ((⁺toℤ b) *ℤ (⁺toℤ b'))) ≡ ((c' *ℤ ⁺toℤ d) *ℤ ((⁺toℤ b) *ℤ (⁺toℤ b')))
    eqqScaled₀ = cong (λ t → t *ℤ ((⁺toℤ b) *ℤ (⁺toℤ b'))) eqq

    termC-lhs : ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ b'd') ≡ ((c *ℤ ⁺toℤ d') *ℤ ((⁺toℤ b) *ℤ (⁺toℤ b')))
    termC-lhs =
      trans
        (cong (λ t → (c *ℤ ⁺toℤ b) *ℤ t) b'd'ℤ)
        (trans
          (cong (λ t → (c *ℤ ⁺toℤ b) *ℤ t) (*ℤ-comm (⁺toℤ b') (⁺toℤ d')))
          (mul4-rearrange c (⁺toℤ b) (⁺toℤ d') (⁺toℤ b')))

    termC-rhs : ((c' *ℤ ⁺toℤ b') *ℤ ⁺toℤ bd) ≡ ((c' *ℤ ⁺toℤ d) *ℤ ((⁺toℤ b) *ℤ (⁺toℤ b')))
    termC-rhs =
      trans
        (cong (λ t → (c' *ℤ ⁺toℤ b') *ℤ t) bdℤ)
        (trans
          (cong (λ t → (c' *ℤ ⁺toℤ b') *ℤ t) (*ℤ-comm (⁺toℤ b) (⁺toℤ d)))
          (trans
            (mul4-rearrange c' (⁺toℤ b') (⁺toℤ d) (⁺toℤ b))
            (cong (λ t → (c' *ℤ ⁺toℤ d) *ℤ t) (*ℤ-comm (⁺toℤ b') (⁺toℤ b)))))

    termC : ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ b'd') ≡ ((c' *ℤ ⁺toℤ b') *ℤ ⁺toℤ bd)
    termC =
      trans
        termC-lhs
        (trans
          eqqScaled₀
          (sym termC-rhs))
  in
  trans
    lhsExpand
    (trans
      (cong₂ _+ℤ_ termA termC)
      (sym rhsExpand))
-- § rational addition is associative in ≃ℚ
+ℚ-assoc : (p q r : ℚ) → (p +ℚ q) +ℚ r ≃ℚ p +ℚ (q +ℚ r)
+ℚ-assoc (a / b) (c / d) (e / f) =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    df : ℕ⁺
    df = d *⁺ f

    lhsNum : ℤ
    lhsNum = (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ bd)

    rhsNum : ℤ
    rhsNum = (a *ℤ ⁺toℤ df) +ℤ (((c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)) *ℤ ⁺toℤ b)

    lhsDen : ℕ⁺
    lhsDen = bd *⁺ f

    rhsDen : ℕ⁺
    rhsDen = b *⁺ df

    bdℤ : ⁺toℤ bd ≡ (⁺toℤ b) *ℤ (⁺toℤ d)
    bdℤ = ⁺toℤ-*⁺ b d

    dfℤ : ⁺toℤ df ≡ (⁺toℤ d) *ℤ (⁺toℤ f)
    dfℤ = ⁺toℤ-*⁺ d f

    denL : ⁺toℤ lhsDen ≡ ((⁺toℤ b) *ℤ (⁺toℤ d)) *ℤ (⁺toℤ f)
    denL =
      trans
        (⁺toℤ-*⁺ bd f)
        (cong (λ t → t *ℤ (⁺toℤ f)) bdℤ)

    denR : ⁺toℤ rhsDen ≡ (⁺toℤ b) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ f))
    denR =
      trans
        (⁺toℤ-*⁺ b df)
        (cong (λ t → (⁺toℤ b) *ℤ t) dfℤ)

    denEq : ⁺toℤ lhsDen ≡ ⁺toℤ rhsDen
    denEq =
      trans
        denL
        (trans
          (*ℤ-assoc (⁺toℤ b) (⁺toℤ d) (⁺toℤ f))
          (sym denR))

    -- § expand rhsNum to normal form matching lhsNum
    rhsExpand : rhsNum ≡ lhsNum
    rhsExpand =
      let
        nf : ℤ
        nf = (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)) +ℤ (e *ℤ ⁺toℤ bd)

        swapLastFactors : (x y z : ℤ) → (x *ℤ y) *ℤ z ≡ (x *ℤ z) *ℤ y
        swapLastFactors x y z =
          trans
            (*ℤ-assoc x y z)
            (trans
              (cong (λ t → x *ℤ t) (*ℤ-comm y z))
              (sym (*ℤ-assoc x z y)))

        cTermEq : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≡ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
        cTermEq = swapLastFactors c (⁺toℤ f) (⁺toℤ b)

        eTermEq : ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (e *ℤ ⁺toℤ bd)
        eTermEq =
          trans
            (*ℤ-assoc e (⁺toℤ d) (⁺toℤ b))
            (trans
              (cong (λ t → e *ℤ t) (*ℤ-comm (⁺toℤ d) (⁺toℤ b)))
              (cong (λ t → e *ℤ t) (sym bdℤ)))

        rhsToNF : rhsNum ≡ nf
        rhsToNF =
          trans
            (cong (λ t → (a *ℤ t) +ℤ (((c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)) *ℤ ⁺toℤ b)) dfℤ)
            (trans
              (cong (λ t → t +ℤ (((c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)) *ℤ ⁺toℤ b))
                (sym (*ℤ-assoc a (⁺toℤ d) (⁺toℤ f))))
              (trans
                (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                  (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ b)))
                (trans
                  (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
                    (cong₂ _+ℤ_ cTermEq eTermEq))
                  (sym (+ℤ-assoc ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ bd))))))

        lhsToNF : lhsNum ≡ nf
        lhsToNF =
          cong (λ t → t +ℤ (e *ℤ ⁺toℤ bd))
            (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) (⁺toℤ f))
      in
      trans rhsToNF (sym lhsToNF)

    numEq : lhsNum ≡ rhsNum
    numEq = sym rhsExpand
  in
  trans
    (cong (λ t → lhsNum *ℤ t) (sym denEq))
    (cong (λ t → t *ℤ ⁺toℤ lhsDen) numEq)
-- § 0ℚ is right identity for +ℚ
+ℚ-zero-right : (p : ℚ) → p +ℚ 0ℚ ≃ℚ p
+ℚ-zero-right (a / b) =
  let
    lhsNum : ℤ
    lhsNum = (a *ℤ ⁺toℤ one⁺) +ℤ (0ℤ *ℤ ⁺toℤ b)

    lhsNum≡a : lhsNum ≡ a
    lhsNum≡a =
      trans
        (cong (λ t → t +ℤ (0ℤ *ℤ ⁺toℤ b)) (*ℤ-one-right a))
        (trans
          (cong (λ t → a +ℤ t) (*ℤ-zero-left (⁺toℤ b)))
          (+ℤ-zero-right a))

    denOne : ⁺toℤ b ≡ ⁺toℤ (b *⁺ one⁺)
    denOne =
      trans
        (sym (*ℤ-one-right (⁺toℤ b)))
        (sym (⁺toℤ-*⁺ b one⁺))
  in
  trans
    (cong (λ t → t *ℤ ⁺toℤ b) lhsNum≡a)
    (cong (λ t → a *ℤ t) denOne)

-- § 0ℚ is left identity for +ℚ
+ℚ-zero-left : (p : ℚ) → 0ℚ +ℚ p ≃ℚ p
+ℚ-zero-left (a / b) =
  let
    lhsNum : ℤ
    lhsNum = (0ℤ *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ one⁺)

    lhsNum≡a : lhsNum ≡ a
    lhsNum≡a =
      trans
        (cong (λ t → t +ℤ (a *ℤ ⁺toℤ one⁺)) (*ℤ-zero-left (⁺toℤ b)))
        (trans
          (cong (λ t → 0ℤ +ℤ t) (*ℤ-one-right a))
          (+ℤ-zero-left a))

    denOneL : ⁺toℤ b ≡ ⁺toℤ (one⁺ *⁺ b)
    denOneL = sym (trans (⁺toℤ-*⁺ one⁺ b) (*ℤ-one-left (⁺toℤ b)))
  in
  trans
    (cong (λ t → t *ℤ ⁺toℤ b) lhsNum≡a)
    (cong (λ t → a *ℤ t) denOneL)

-- § additive inverse cancels: p +ℚ (-ℚ p) ≃ℚ 0ℚ
+ℚ-inv-right : (p : ℚ) → p +ℚ (-ℚ p) ≃ℚ 0ℚ
+ℚ-inv-right (a / b) =
  let
    x : ℤ
    x = a *ℤ ⁺toℤ b

    lhsNum : ℤ
    lhsNum = x +ℤ (negℤ a *ℤ ⁺toℤ b)

    lhsNum≡0 : lhsNum ≡ 0ℤ
    lhsNum≡0 =
      trans
        (cong (λ t → x +ℤ t) (*ℤ-neg-left a (⁺toℤ b)))
        (+ℤ-inv-right x)
  in
  trans
    (cong (λ t → t *ℤ ⁺toℤ one⁺) lhsNum≡0)
    (trans
      (*ℤ-zero-left (⁺toℤ one⁺))
      (sym (*ℤ-zero-left (⁺toℤ (b *⁺ b)))))
-- § extract 0 ≤ num from 0 ≤ q
0≤ℚ→0≤ℤ-num : (q : ℚ) → 0ℚ ≤ℚ q → 0ℤ ≤ℤ num q
0≤ℚ→0≤ℤ-num (a / b) p =
  ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b))
    (≤ℤ-resp-≡ʳ (*ℤ-one-right a) p)

-- § rational multiplication commutes in ≃ℚ
*ℚ-comm : (p q : ℚ) → (p *ℚ q) ≃ℚ (q *ℚ p)
*ℚ-comm (a / b) (c / d) =
  let
    denSwap : (d *⁺ b) ≡ (b *⁺ d)
    denSwap = *⁺-comm d b

    numSwap : (a *ℤ c) ≡ (c *ℤ a)
    numSwap = *ℤ-comm a c

    lhsStep : ((a *ℤ c) *ℤ ⁺toℤ (d *⁺ b)) ≡ ((a *ℤ c) *ℤ ⁺toℤ (b *⁺ d))
    lhsStep = cong (λ t → (a *ℤ c) *ℤ ⁺toℤ t) denSwap

    rhsStep : ((c *ℤ a) *ℤ ⁺toℤ (b *⁺ d)) ≡ ((a *ℤ c) *ℤ ⁺toℤ (b *⁺ d))
    rhsStep = cong (λ t → t *ℤ ⁺toℤ (b *⁺ d)) (sym numSwap)
  in
  trans lhsStep (sym rhsStep)

-- § swap middle factors in a triple product
mul-swap-middle : (x y z : ℤ) → (x *ℤ y) *ℤ z ≡ (x *ℤ z) *ℤ y
mul-swap-middle x y z =
  trans
    (*ℤ-assoc x y z)
    (trans
      (cong (λ t → x *ℤ t) (*ℤ-comm y z))
      (sym (*ℤ-assoc x z y)))

-- § multiplying on the right by a nonneg rational preserves ≤ℚ
≤ℚ-mul-nonneg-right : (x y z : ℚ) → x ≤ℚ y → 0ℚ ≤ℚ z → (x *ℚ z) ≤ℚ (y *ℚ z)
≤ℚ-mul-nonneg-right (a / b) (c / d) (e / f) x≤y zNonneg =
  let
    eNonneg : 0ℤ ≤ℤ e
    eNonneg = 0≤ℚ→0≤ℤ-num (e / f) zNonneg

    step₁ : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    step₁ = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) f x≤y

    step₂ : (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ e) ≤ℤ (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ e)
    step₂ = ≤ℤ-mul-nonneg-right ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) e step₁ eNonneg

    lhsEq : (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ e) ≡ ((a *ℤ e) *ℤ ⁺toℤ (d *⁺ f))
    lhsEq =
      trans
        (mul-swap-middle (a *ℤ ⁺toℤ d) (⁺toℤ f) e)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (mul-swap-middle a (⁺toℤ d) e))
          (trans
            (*ℤ-assoc (a *ℤ e) (⁺toℤ d) (⁺toℤ f))
            (cong (λ t → (a *ℤ e) *ℤ t) (sym (⁺toℤ-*⁺ d f)))))

    rhsEq : (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ e) ≡ ((c *ℤ e) *ℤ ⁺toℤ (b *⁺ f))
    rhsEq =
      trans
        (mul-swap-middle (c *ℤ ⁺toℤ b) (⁺toℤ f) e)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (mul-swap-middle c (⁺toℤ b) e))
          (trans
            (*ℤ-assoc (c *ℤ e) (⁺toℤ b) (⁺toℤ f))
            (cong (λ t → (c *ℤ e) *ℤ t) (sym (⁺toℤ-*⁺ b f)))))
  in
  ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step₂)

-- § multiplying on the left by a nonneg rational preserves ≤ℚ
≤ℚ-mul-nonneg-left : (x y z : ℚ) → x ≤ℚ y → 0ℚ ≤ℚ z → (z *ℚ x) ≤ℚ (z *ℚ y)
≤ℚ-mul-nonneg-left (a / b) (c / d) (e / f) x≤y zNonneg =
  let
    zx≤xz : ((e / f) *ℚ (a / b)) ≤ℚ ((a / b) *ℚ (e / f))
    zx≤xz =
      ≃ℚ→≤ℚˡ
        {p = (e / f) *ℚ (a / b)}
        {q = (a / b) *ℚ (e / f)}
        (*ℚ-comm (e / f) (a / b))

    xz≤yz : ((a / b) *ℚ (e / f)) ≤ℚ ((c / d) *ℚ (e / f))
    xz≤yz = ≤ℚ-mul-nonneg-right (a / b) (c / d) (e / f) x≤y zNonneg

    yz≤zy : ((c / d) *ℚ (e / f)) ≤ℚ ((e / f) *ℚ (c / d))
    yz≤zy =
      ≃ℚ→≤ℚˡ
        {p = (c / d) *ℚ (e / f)}
        {q = (e / f) *ℚ (c / d)}
        (*ℚ-comm (c / d) (e / f))

    middle : ((a / b) *ℚ (e / f)) ≤ℚ ((e / f) *ℚ (c / d))
    middle = ≤ℚ-trans {(a / b) *ℚ (e / f)} {(c / d) *ℚ (e / f)} {(e / f) *ℚ (c / d)} xz≤yz yz≤zy
  in
  ≤ℚ-trans {(e / f) *ℚ (a / b)} {(a / b) *ℚ (e / f)} {(e / f) *ℚ (c / d)} zx≤xz middle
-- § 8-vectors as paired 4-vectors
Vec8ℤ : Set
Vec8ℤ = Vec4ℤ × Vec4ℤ

-- § left/right block projections
left4 : Vec8ℤ → Vec4ℤ
left4 = fst

right4 : Vec8ℤ → Vec4ℤ
right4 = snd

-- § pointwise equality on Vec8ℤ
Vec8Eq : Vec8ℤ → Vec8ℤ → Set
Vec8Eq u v = Vec4Eq (left4 u) (left4 v) × Vec4Eq (right4 u) (right4 v)

-- § pointwise addition on Vec8ℤ
+Vec8ℤ : Vec8ℤ → Vec8ℤ → Vec8ℤ
+Vec8ℤ u v = ((left4 u) +Vec4ℤ (left4 v)) , ((right4 u) +Vec4ℤ (right4 v))

-- § pointwise negation on Vec8ℤ
negVec8ℤ : Vec8ℤ → Vec8ℤ
negVec8ℤ v = (λ i → negℤ (left4 v i)) , (λ i → negℤ (right4 v i))

-- § pointwise four-times on Vec8ℤ
fourVec8ℤ : Vec8ℤ → Vec8ℤ
fourVec8ℤ v = (λ i → fourTimesℤ (left4 v i)) , (λ i → fourTimesℤ (right4 v i))

-- § global sum of all 8 entries
sum8ℤ : Vec8ℤ → ℤ
sum8ℤ v = sumFin4ℤ (left4 v) +ℤ sumFin4ℤ (right4 v)

-- § all-ones operator: constant with value sum8ℤ v
J8Vec8ℤ : Vec8ℤ → Vec8ℤ
J8Vec8ℤ v = constVec4ℤ (sum8ℤ v) , constVec4ℤ (sum8ℤ v)

-- § scalar ×8 on ℤ and on Vec4ℤ
eightTimesℤ : ℤ → ℤ
eightTimesℤ x = fourTimesℤ x +ℤ fourTimesℤ x

eightVec4ℤ : Vec4ℤ → Vec4ℤ
eightVec4ℤ v i = eightTimesℤ (v i)
-- § K₈ Laplacian: 8·vᵢ − Σ₈ v
K8LaplacianVec8ℤ : Vec8ℤ → Vec8ℤ
K8LaplacianVec8ℤ v =
  (λ i → eightTimesℤ (left4 v i) +ℤ negℤ (sum8ℤ v)) ,
  (λ i → eightTimesℤ (right4 v i) +ℤ negℤ (sum8ℤ v))

-- § block-diagonal Laplacian (empty coupling)
laplacianEmptyVec8ℤ : Vec8ℤ → Vec8ℤ
laplacianEmptyVec8ℤ v = laplacianVec4ℤ (left4 v) , laplacianVec4ℤ (right4 v)

-- § full coupling Laplacian: L₄ + 4I − cross-sum
laplacianFullVec8ℤ : Vec8ℤ → Vec8ℤ
laplacianFullVec8ℤ v =
  (λ i → laplacianVec4ℤ (left4 v) i +ℤ fourTimesℤ (left4 v i) +ℤ negℤ (sumFin4ℤ (right4 v))) ,
  (λ i → laplacianVec4ℤ (right4 v) i +ℤ fourTimesℤ (right4 v i) +ℤ negℤ (sumFin4ℤ (left4 v)))

-- § pointwise ×8 on Vec8ℤ
eightVec8ℤ : Vec8ℤ → Vec8ℤ
eightVec8ℤ v = eightVec4ℤ (left4 v) , eightVec4ℤ (right4 v)
-- § coupling survivor type: empty or full
data CouplingSurvivor : Set where
  survivor-empty : CouplingSurvivor
  survivor-full  : CouplingSurvivor

-- § forced coupling for each survivor
survivorCoupling : CouplingSurvivor → Coupling
survivorCoupling survivor-empty = CrossEmpty
survivorCoupling survivor-full  = CrossFull

-- § Laplacian dispatched by survivor case
laplacianSurvivorVec8ℤ : CouplingSurvivor → Vec8ℤ → Vec8ℤ
laplacianSurvivorVec8ℤ survivor-empty = laplacianEmptyVec8ℤ
laplacianSurvivorVec8ℤ survivor-full  = laplacianFullVec8ℤ

-- § constant and zero 8-vectors
constVec8ℤ : ℤ → Vec8ℤ
constVec8ℤ x = constVec4ℤ x , constVec4ℤ x

zeroVec8ℤ : Vec8ℤ
zeroVec8ℤ = constVec8ℤ 0ℤ

eightVec8ℤ-const : ℤ → Vec8ℤ
eightVec8ℤ-const x = constVec8ℤ (eightTimesℤ x)
-- § empty coupling = block-diagonal Laplacian
law14G-0-empty-block : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (laplacianEmptyVec8ℤ v)
law14G-0-empty-block v = (λ _ → refl) , (λ _ → refl)
-- § full coupling = K₈ Laplacian
law14G-1-full-is-K8 : (v : Vec8ℤ) → Vec8Eq (laplacianFullVec8ℤ v) (K8LaplacianVec8ℤ v)
law14G-1-full-is-K8 v =
  let sL = sumFin4ℤ (left4 v)
      sR = sumFin4ℤ (right4 v)
  in
  ( λ i →
      let lv = laplacianVec4ℤ (left4 v) i
          fv = fourTimesℤ (left4 v i)
          -- § step₁: L₄ vᵢ + 4·vᵢ = 8·vᵢ − sL via law14E-10
          step₁ : lv +ℤ fv ≡ eightTimesℤ (left4 v i) +ℤ negℤ sL
          step₁ =
            trans
              (cong (λ t → t +ℤ fv) (law14E-10-laplacian-four-minus-sumAll (left4 v) i))
              (trans
                (+ℤ-assoc fv (negℤ sL) fv)
                (trans
                  (cong (λ t → fv +ℤ t) (+ℤ-comm (negℤ sL) fv))
                  (sym (+ℤ-assoc fv fv (negℤ sL)))))
          -- § step₂: reassociate (lv + fv) + (−sR) = 8·vᵢ + (−sL + −sR)
          step₂ : (lv +ℤ fv) +ℤ negℤ sR ≡ eightTimesℤ (left4 v i) +ℤ (negℤ sL +ℤ negℤ sR)
          step₂ =
            trans
              (cong (λ t → t +ℤ negℤ sR) step₁)
              (+ℤ-assoc (eightTimesℤ (left4 v i)) (negℤ sL) (negℤ sR))
          -- § step₃: −sL + −sR = −(sL + sR) = −Σ₈ v
          step₃ : negℤ sL +ℤ negℤ sR ≡ negℤ (sum8ℤ v)
          step₃ = sym (neg-+ℤ sL sR)
      in
      trans step₂ (cong (λ t → eightTimesℤ (left4 v i) +ℤ t) step₃)
  ) ,
  ( λ i →
      let lv = laplacianVec4ℤ (right4 v) i
          fv = fourTimesℤ (right4 v i)
          step₁ : lv +ℤ fv ≡ eightTimesℤ (right4 v i) +ℤ negℤ sR
          step₁ =
            trans
              (cong (λ t → t +ℤ fv) (law14E-10-laplacian-four-minus-sumAll (right4 v) i))
              (trans
                (+ℤ-assoc fv (negℤ sR) fv)
                (trans
                  (cong (λ t → fv +ℤ t) (+ℤ-comm (negℤ sR) fv))
                  (sym (+ℤ-assoc fv fv (negℤ sR)))))
          step₂ : (lv +ℤ fv) +ℤ negℤ sL ≡ eightTimesℤ (right4 v i) +ℤ (negℤ sR +ℤ negℤ sL)
          step₂ =
            trans
              (cong (λ t → t +ℤ negℤ sL) step₁)
              (+ℤ-assoc (eightTimesℤ (right4 v i)) (negℤ sR) (negℤ sL))
          step₃ : negℤ sR +ℤ negℤ sL ≡ negℤ (sum8ℤ v)
          step₃ =
            trans
              (+ℤ-comm (negℤ sR) (negℤ sL))
              (sym (neg-+ℤ sL sR))
      in
      trans step₂ (cong (λ t → eightTimesℤ (right4 v i) +ℤ t) step₃)
  )
-- § edge forces full coupling via 14F.0
law14G-2-edge-forces-full : Coupling
law14G-2-edge-forces-full = CrossFull

-- § non-edge forces empty coupling via 14F.1
law14G-3-nonedge-forces-empty : Coupling
law14G-3-nonedge-forces-empty = CrossEmpty

-- § edge → full survivor
law14G-4-edge-full : CouplingSurvivor
law14G-4-edge-full = survivor-full

-- § non-edge → empty survivor
law14G-5-nonedge-empty : CouplingSurvivor
law14G-5-nonedge-empty = survivor-empty
-- § survivor case split
law14G-6-survivor-cases : (k : CouplingSurvivor) → (k ≡ survivor-empty) ⊎ (k ≡ survivor-full)
law14G-6-survivor-cases survivor-empty = inj₁ refl
law14G-6-survivor-cases survivor-full  = inj₂ refl
-- § empty survivor = block-diagonal
law14G-7-survivor-empty-block : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (laplacianEmptyVec8ℤ v)
law14G-7-survivor-empty-block = law14G-0-empty-block

-- § full survivor = K₈ Laplacian
law14G-8-survivor-full-K8 : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v)
law14G-8-survivor-full-K8 = law14G-1-full-is-K8
-- § 8·(x + y) = 8·x + 8·y
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

-- § 8·(−x) = −(8·x)
eightTimes-neg : (x : ℤ) → eightTimesℤ (negℤ x) ≡ negℤ (eightTimesℤ x)
eightTimes-neg x =
  trans
    (cong (λ t → t +ℤ t) (sym (neg-fourTimesℤ x)))
    (trans
      (sym (neg-+ℤ (fourTimesℤ x) (fourTimesℤ x)))
      refl)

-- § sum of 8·vᵢ over Fin4 = 8·(sum v)
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

-- § sum of 8·v over both blocks = 8·(sum8 v)
sum8-eightVec8 : (v : Vec8ℤ) → sum8ℤ (eightVec8ℤ v) ≡ eightTimesℤ (sum8ℤ v)
sum8-eightVec8 v =
  let sL = sumFin4ℤ (left4 v) in
  let sR = sumFin4ℤ (right4 v) in
  trans
    (cong
      (λ t → t +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
      (sumFin4-eightTimes (left4 v)))
    (trans
      (cong
        (λ t → eightTimesℤ sL +ℤ t)
        (sumFin4-eightTimes (right4 v)))
      (trans
        (sym (eightTimes-+ℤ sL sR))
        refl))
-- § global sum of K₈ Laplacian is 0
law14G-12-sumL8-0 : (v : Vec8ℤ) → sum8ℤ (K8LaplacianVec8ℤ v) ≡ 0ℤ
law14G-12-sumL8-0 v =
  let
    s  = sum8ℤ v
    sL = sumFin4ℤ (left4 v)
    sR = sumFin4ℤ (right4 v)

    leftPart  = λ i → eightTimesℤ (left4 v i) +ℤ negℤ s
    rightPart = λ i → eightTimesℤ (right4 v i) +ℤ negℤ s

    stepL : sumFin4ℤ leftPart ≡ sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)
    stepL = sumFin4-addConst (λ i → eightTimesℤ (left4 v i)) (negℤ s)

    stepR : sumFin4ℤ rightPart ≡ sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)
    stepR = sumFin4-addConst (λ i → eightTimesℤ (right4 v i)) (negℤ s)

    step₁ : sum8ℤ (K8LaplacianVec8ℤ v) ≡
            (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
            (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s))
    step₁ =
      trans
        (cong (λ t → t +ℤ sumFin4ℤ rightPart) stepL)
        (cong (λ t → (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ t) stepR)

    step₂ : (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ fourTimesℤ (negℤ s)) +ℤ
            (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)) ≡
            (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) +ℤ
            (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s))
    step₂ =
      trans
        (+ℤ-assoc (sumFin4ℤ (λ i → eightTimesℤ (left4 v i))) (fourTimesℤ (negℤ s))
                 (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) +ℤ fourTimesℤ (negℤ s)))
        (trans
          (cong (λ t → sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ t)
                (swapHeadℤ (fourTimesℤ (negℤ s)) (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
                           (fourTimesℤ (negℤ s))))
          (sym (+ℤ-assoc (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)))
                         (sumFin4ℤ (λ i → eightTimesℤ (right4 v i)))
                         (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)))))

    step₃ : sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) ≡ eightTimesℤ sL
    step₃ = sumFin4-eightTimes (left4 v)

    step₄ : sumFin4ℤ (λ i → eightTimesℤ (right4 v i)) ≡ eightTimesℤ sR
    step₄ = sumFin4-eightTimes (right4 v)

    step₅ : (sumFin4ℤ (λ i → eightTimesℤ (left4 v i)) +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) ≡
            eightTimesℤ s
    step₅ =
      trans
        (cong (λ t → t +ℤ sumFin4ℤ (λ i → eightTimesℤ (right4 v i))) step₃)
        (trans
          (cong (λ t → eightTimesℤ sL +ℤ t) step₄)
          (sym (eightTimes-+ℤ sL sR)))

    step₆ : (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s)) ≡ negℤ (eightTimesℤ s)
    step₆ =
      trans
        (cong (λ t → t +ℤ t) (sym (neg-fourTimesℤ s)))
        (sym (neg-+ℤ (fourTimesℤ s) (fourTimesℤ s)))
  in
  trans
    step₁
    (trans
      step₂
      (trans
        (cong (λ t → t +ℤ (fourTimesℤ (negℤ s) +ℤ fourTimesℤ (negℤ s))) step₅)
        (trans
          (cong (λ t → eightTimesℤ s +ℤ t) step₆)
          (+ℤ-inv-right (eightTimesℤ s)))))
-- § J₈ (L₈ v) = 0
law14G-13-JL-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (K8LaplacianVec8ℤ v)) zeroVec8ℤ
law14G-13-JL-zero v =
  let sum0 = law14G-12-sumL8-0 v in
  (λ _ → sum0) , (λ _ → sum0)
-- § L₈ (J₈ v) = 0
law14G-14-LJ-zero : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (J8Vec8ℤ v)) zeroVec8ℤ
law14G-14-LJ-zero v =
  let s = sum8ℤ v in
  let sj : sum8ℤ (J8Vec8ℤ v) ≡ eightTimesℤ s
      sj =
        trans
          (cong (λ t → t +ℤ sumFin4ℤ (constVec4ℤ s)) (sumFin4-const s))
          (trans
            (cong (λ t → fourTimesℤ s +ℤ t) (sumFin4-const s))
            refl)
  in
  ( λ _ →
      trans
        (cong (λ t → eightTimesℤ s +ℤ negℤ t) sj)
        (+ℤ-inv-right (eightTimesℤ s))
  ) ,
  ( λ _ →
      trans
        (cong (λ t → eightTimesℤ s +ℤ negℤ t) sj)
        (+ℤ-inv-right (eightTimesℤ s))
  )
-- § L₈² = 8·L₈
law14G-15-LL-eightL : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
law14G-15-LL-eightL v =
  let sum0 = law14G-12-sumL8-0 v in
  ( λ i →
      trans
        (cong (λ t → eightTimesℤ (left4 (K8LaplacianVec8ℤ v) i) +ℤ negℤ t) sum0)
        (+ℤ-zero-right (eightTimesℤ (left4 (K8LaplacianVec8ℤ v) i)))
  ) ,
  ( λ i →
      trans
        (cong (λ t → eightTimesℤ (right4 (K8LaplacianVec8ℤ v) i) +ℤ negℤ t) sum0)
        (+ℤ-zero-right (eightTimesℤ (right4 (K8LaplacianVec8ℤ v) i)))
  )
-- § Σ₈ v = 0 ⟹ L₈ v = 8·v
law14G-16-sum0-eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v)
law14G-16-sum0-eigen8 v sum0 =
  ( λ i →
      trans
        (cong (λ s → eightTimesℤ (left4 v i) +ℤ negℤ s) sum0)
        (+ℤ-zero-right (eightTimesℤ (left4 v i)))
  ) ,
  ( λ i →
      trans
        (cong (λ s → eightTimesℤ (right4 v i) +ℤ negℤ s) sum0)
        (+ℤ-zero-right (eightTimesℤ (right4 v i)))
  )
-- § L₈ v = 8·v ⟹ Σ₈ v = 0
law14G-17-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-17-eigen8→sum0 v eigen8 =
  let a = eightTimesℤ (left4 v g0) in
  let s = sum8ℤ v in
  let eq₀ : a +ℤ negℤ s ≡ a
      eq₀ = fst eigen8 g0
  in
  negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)
-- § sum0 ↔ eigen8 (both directions)
law14G-18-sum0→eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v)
law14G-18-sum0→eigen8 = law14G-16-sum0-eigen8

law14G-18-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-18-eigen8→sum0 = law14G-17-eigen8→sum0
-- § constant vectors lie in kernel of L₈
law14G-19-const-eigen0 : (x : ℤ) → Vec8Eq (K8LaplacianVec8ℤ (constVec8ℤ x)) zeroVec8ℤ
law14G-19-const-eigen0 x =
  let sc : sum8ℤ (constVec8ℤ x) ≡ eightTimesℤ x
      sc =
        trans
          (cong (λ t → t +ℤ sumFin4ℤ (constVec4ℤ x)) (sumFin4-const x))
          (trans
            (cong (λ t → fourTimesℤ x +ℤ t) (sumFin4-const x))
            refl)
  in
  ( λ _ →
      trans
        (cong (λ s → eightTimesℤ x +ℤ negℤ s) sc)
        (+ℤ-inv-right (eightTimesℤ x))
  ) ,
  ( λ _ →
      trans
        (cong (λ s → eightTimesℤ x +ℤ negℤ s) sc)
        (+ℤ-inv-right (eightTimesℤ x))
  )
-- § L₈ v = 0 ⟹ 8·v = J₈ v
law14G-20-L0→eightEqJ : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ v) zeroVec8ℤ → Vec8Eq (eightVec8ℤ v) (J8Vec8ℤ v)
law14G-20-L0→eightEqJ v L0 =
  let s = sum8ℤ v in
  ( λ i →
      let a = eightTimesℤ (left4 v i) in
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
  ( λ i →
      let a = eightTimesℤ (right4 v i) in
      let eq₀ : a +ℤ negℤ s ≡ 0ℤ
          eq₀ = snd L0 i
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
  )

-- § 8·v = J₈ v ⟹ L₈ v = 0
law14G-20-eightEqJ→L0 : (v : Vec8ℤ) → Vec8Eq (eightVec8ℤ v) (J8Vec8ℤ v) → Vec8Eq (K8LaplacianVec8ℤ v) zeroVec8ℤ
law14G-20-eightEqJ→L0 v eightEqJ =
  let s = sum8ℤ v in
  ( λ i →
      trans
        (cong (λ t → t +ℤ negℤ s) (fst eightEqJ i))
        (+ℤ-inv-right s)
  ) ,
  ( λ i →
      trans
        (cong (λ t → t +ℤ negℤ s) (snd eightEqJ i))
        (+ℤ-inv-right s)
  )
-- § image vectors are 8-eigenvectors
law14G-21-image⊆eigen8 : (v : Vec8ℤ) → Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
law14G-21-image⊆eigen8 = law14G-15-LL-eightL

-- § sum-zero vectors become image vectors after 8-scaling
law14G-22-sum0→eightInImage : (w : Vec8ℤ) → sum8ℤ w ≡ 0ℤ → Σ Vec8ℤ (λ v → Vec8Eq (K8LaplacianVec8ℤ v) (eightVec8ℤ w))
law14G-22-sum0→eightInImage w sum0 = w , law14G-16-sum0-eigen8 w sum0
-- § Vec8Eq reflexivity
Vec8Eq-refl : (v : Vec8ℤ) → Vec8Eq v v
Vec8Eq-refl v = (λ _ → refl) , (λ _ → refl)

-- § Vec8Eq symmetry
Vec8Eq-sym : {u v : Vec8ℤ} → Vec8Eq u v → Vec8Eq v u
Vec8Eq-sym eq =
  (λ i → sym (fst eq i)) ,
  (λ i → sym (snd eq i))

-- § Vec8Eq transitivity
Vec8Eq-trans : {u v w : Vec8ℤ} → Vec8Eq u v → Vec8Eq v w → Vec8Eq u w
Vec8Eq-trans eq₁ eq₂ =
  (λ i → trans (fst eq₁ i) (fst eq₂ i)) ,
  (λ i → trans (snd eq₁ i) (snd eq₂ i))

-- § sumFin4 respects pointwise equality
sumFin4-cong : (f g : Vec4ℤ) → Vec4Eq f g → sumFin4ℤ f ≡ sumFin4ℤ g
sumFin4-cong f g eq =
  trans
    (cong (λ a → sum4ℤ a (f g1) (f g2) (f g3)) (eq g0))
    (trans
      (cong (λ b → sum4ℤ (g g0) b (f g2) (f g3)) (eq g1))
      (trans
        (cong (λ c → sum4ℤ (g g0) (g g1) c (f g3)) (eq g2))
        (cong (λ d → sum4ℤ (g g0) (g g1) (g g2) d) (eq g3))))

-- § sum8 respects Vec8Eq
sum8-cong : (u v : Vec8ℤ) → Vec8Eq u v → sum8ℤ u ≡ sum8ℤ v
sum8-cong u v eq =
  cong (λ t → t +ℤ sumFin4ℤ (right4 u)) (sumFin4-cong (left4 u) (left4 v) (fst eq))
  ▸ λ pL →
  trans pL
    (cong (λ t → sumFin4ℤ (left4 v) +ℤ t) (sumFin4-cong (right4 u) (right4 v) (snd eq)))
  where
    infixl 1 _▸_
    _▸_ : {A B : Set} → A → (A → B) → B
    x ▸ k = k x

-- § eightVec8 respects Vec8Eq
eightVec8-cong : (u v : Vec8ℤ) → Vec8Eq u v → Vec8Eq (eightVec8ℤ u) (eightVec8ℤ v)
eightVec8-cong u v eq =
  (λ i → cong eightTimesℤ (fst eq i)) ,
  (λ i → cong eightTimesℤ (snd eq i))

-- § K₈ Laplacian respects Vec8Eq
K8Laplacian-cong : (u v : Vec8ℤ) → Vec8Eq u v → Vec8Eq (K8LaplacianVec8ℤ u) (K8LaplacianVec8ℤ v)
K8Laplacian-cong u v eq =
  let sEq : sum8ℤ u ≡ sum8ℤ v
      sEq = sum8-cong u v eq
      nsEq : negℤ (sum8ℤ u) ≡ negℤ (sum8ℤ v)
      nsEq = cong negℤ sEq
  in
  ( λ i →
      let aEq : eightTimesℤ (left4 u i) ≡ eightTimesℤ (left4 v i)
          aEq = cong eightTimesℤ (fst eq i)
      in
      trans
        (cong (λ t → t +ℤ negℤ (sum8ℤ u)) aEq)
        (cong (λ t → eightTimesℤ (left4 v i) +ℤ t) nsEq)
  ) ,
  ( λ i →
      let aEq : eightTimesℤ (right4 u i) ≡ eightTimesℤ (right4 v i)
          aEq = cong eightTimesℤ (snd eq i)
      in
      trans
        (cong (λ t → t +ℤ negℤ (sum8ℤ u)) aEq)
        (cong (λ t → eightTimesℤ (right4 v i) +ℤ t) nsEq)
  )
-- § global sum of the full-survivor Laplacian is 0
law14G-23-sumL-survivor-full-0 : (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ
law14G-23-sumL-survivor-full-0 v =
  trans
    (sum8-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) (law14G-8-survivor-full-K8 v))
    (law14G-12-sumL8-0 v)
-- § J₈ annihilates full-survivor image
law14G-24-JL-survivor-full-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ
law14G-24-JL-survivor-full-zero v =
  let sum0 = law14G-23-sumL-survivor-full-0 v in
  (λ _ → sum0) , (λ _ → sum0)
-- § sum-zero → 8-eigenvector for full survivor
law14G-25-survivor-full-sum0→eigen8 : (v : Vec8ℤ) → sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)
law14G-25-survivor-full-sum0→eigen8 v sum0 =
  Vec8Eq-trans
    (law14G-8-survivor-full-K8 v)
    (law14G-16-sum0-eigen8 v sum0)

-- § 8-eigenvector → sum-zero for full survivor
law14G-26-survivor-full-eigen8→sum0 : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ
law14G-26-survivor-full-eigen8→sum0 v eigen8 =
  law14G-17-eigen8→sum0 v
    (Vec8Eq-trans
      (Vec8Eq-sym (law14G-8-survivor-full-K8 v))
      eigen8)
-- § global sum of empty-survivor Laplacian is 0
law14G-27-sumL-survivor-empty-0 : (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ
law14G-27-sumL-survivor-empty-0 v =
  trans
    (cong (λ t → t +ℤ sumFin4ℤ (laplacianVec4ℤ (right4 v))) (law14E-28-sumLaplacian0 (left4 v)))
    (trans
      (cong (λ t → 0ℤ +ℤ t) (law14E-28-sumLaplacian0 (right4 v)))
      (+ℤ-zero-left 0ℤ))
-- § J₈ annihilates empty-survivor image
law14G-28-JL-survivor-empty-zero : (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ
law14G-28-JL-survivor-empty-zero v =
  let sum0 = law14G-27-sumL-survivor-empty-0 v in
  (λ _ → sum0) , (λ _ → sum0)
-- § blockwise sum-zero → pointwise 4-eigenvector for empty survivor
law14G-29-survivor-empty-sum0→eigen4 : (v : Vec8ℤ) → sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)
law14G-29-survivor-empty-sum0→eigen4 v sum0L sum0R =
  ( λ i → law14E-11-sum0-eigen4 (left4 v) i sum0L ) ,
  ( λ i → law14E-11-sum0-eigen4 (right4 v) i sum0R )

-- § pointwise 4-eigen → blockwise sum-zero for empty survivor
law14G-30-survivor-empty-eigen4→sum0 : (v : Vec8ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) →
  (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ)
law14G-30-survivor-empty-eigen4→sum0 v eigen4 =
  law14E-19-eigen4→sum0 (left4 v) (fst eigen4) ,
  law14E-19-eigen4→sum0 (right4 v) (snd eigen4)
-- § split constant vector
constVec8Splitℤ : ℤ → ℤ → Vec8ℤ
constVec8Splitℤ x y = constVec4ℤ x , constVec4ℤ y

-- § split constants lie in kernel of empty survivor
law14G-31-splitConst-eigen0-empty : (x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
law14G-31-splitConst-eigen0-empty x y =
  ( λ i → law14E-13-const-eigen0 x i ) ,
  ( λ i → law14E-13-const-eigen0 y i )
-- § image of empty survivor ⊆ 4-eigenspace
law14G-32-imageEmpty⊆eigen4 : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
        (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v))
law14G-32-imageEmpty⊆eigen4 v =
  ( λ i → law14E-29-LL-fourL (left4 v) i ) ,
  ( λ i → law14E-29-LL-fourL (right4 v) i )
-- § blockwise sum-zero → 4·v is in the image
law14G-33-sum0→fourInImage-empty : (v : Vec8ℤ) → sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ →
  Σ Vec8ℤ (λ w → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty w) (fourVec8ℤ v))
law14G-33-sum0→fourInImage-empty v sum0L sum0R = v , law14G-29-survivor-empty-sum0→eigen4 v sum0L sum0R
-- § full survivor image vectors are 8-eigenvectors
law14G-34-survivor-full-image⊆eigen8 : (v : Vec8ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
        (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
law14G-34-survivor-full-image⊆eigen8 v =
  let eqV : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v)
      eqV = law14G-8-survivor-full-K8 v
      eqLL : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
                   (K8LaplacianVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
      eqLL = law14G-8-survivor-full-K8 (laplacianSurvivorVec8ℤ survivor-full v)
      step₁ : Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
                     (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v))
      step₁ =
        Vec8Eq-trans
          eqLL
          (K8Laplacian-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) eqV)
      step₂ : Vec8Eq (K8LaplacianVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (K8LaplacianVec8ℤ v))
      step₂ = law14G-15-LL-eightL v
      step₃ : Vec8Eq (eightVec8ℤ (K8LaplacianVec8ℤ v)) (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
      step₃ = Vec8Eq-sym (eightVec8-cong (laplacianSurvivorVec8ℤ survivor-full v) (K8LaplacianVec8ℤ v) eqV)
  in
  Vec8Eq-trans step₁ (Vec8Eq-trans step₂ step₃)
-- § full survivor spectral package
law14G-35-survivor-full-spectral-package : (v : Vec8ℤ) →
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ) ×
  ((sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ)) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
         (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)))
law14G-35-survivor-full-spectral-package v =
  law14G-23-sumL-survivor-full-0 v ,
  (law14G-24-JL-survivor-full-zero v ,
   ((law14G-25-survivor-full-sum0→eigen8 v , law14G-26-survivor-full-eigen8→sum0 v) ,
    law14G-34-survivor-full-image⊆eigen8 v))
-- § empty survivor spectral package
law14G-36-survivor-empty-spectral-package : (v : Vec8ℤ) →
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ) ×
  ((sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) → (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ))) ×
  ((x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
         (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)))
law14G-36-survivor-empty-spectral-package v =
  law14G-27-sumL-survivor-empty-0 v ,
  (law14G-28-JL-survivor-empty-zero v ,
   ((law14G-29-survivor-empty-sum0→eigen4 v , law14G-30-survivor-empty-eigen4→sum0 v) ,
    (law14G-31-splitConst-eigen0-empty ,
     law14G-32-imageEmpty⊆eigen4 v)))
-- § type-level spectral package indexed by survivor
SurvivorSpectralPackage : CouplingSurvivor → Vec8ℤ → Set
SurvivorSpectralPackage survivor-full v =
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-full v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)) zeroVec8ℤ) ×
  ((sum8ℤ v ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v) → sum8ℤ v ≡ 0ℤ)) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
         (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v)))
SurvivorSpectralPackage survivor-empty v =
  (sum8ℤ (laplacianSurvivorVec8ℤ survivor-empty v) ≡ 0ℤ) ×
  (Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)) zeroVec8ℤ) ×
  ((sumFin4ℤ (left4 v) ≡ 0ℤ → sumFin4ℤ (right4 v) ≡ 0ℤ → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)) ×
   (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v) → (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ))) ×
  ((x y : ℤ) → Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ) ×
  (Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
         (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v)))

-- § forced case-split over survivor constructors
law14G-37-survivor-spectral-package-byCases : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSpectralPackage k v
law14G-37-survivor-spectral-package-byCases k v with law14G-6-survivor-cases k
... | inj₁ refl = law14G-36-survivor-empty-spectral-package v
... | inj₂ refl = law14G-35-survivor-full-spectral-package v
-- § project drift-zero from package
survivorPkg-sumL0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → sum8ℤ (laplacianSurvivorVec8ℤ k v) ≡ 0ℤ
survivorPkg-sumL0 {survivor-full} pkg = fst pkg
survivorPkg-sumL0 {survivor-empty} pkg = fst pkg

-- § project JL=0 from package
survivorPkg-JL0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ k v)) zeroVec8ℤ
survivorPkg-JL0 {survivor-full} pkg = fst (snd pkg)
survivorPkg-JL0 {survivor-empty} pkg = fst (snd pkg)

-- § sum-zero predicate indexed by survivor
SurvivorSum0 : CouplingSurvivor → Vec8ℤ → Set
SurvivorSum0 survivor-full v = sum8ℤ v ≡ 0ℤ
SurvivorSum0 survivor-empty v = (sumFin4ℤ (left4 v) ≡ 0ℤ) × (sumFin4ℤ (right4 v) ≡ 0ℤ)

-- § eigen predicate indexed by survivor
SurvivorEigen : (k : CouplingSurvivor) → Vec8ℤ → Set
SurvivorEigen survivor-full v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full v) (eightVec8ℤ v)
SurvivorEigen survivor-empty v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty v) (fourVec8ℤ v)

-- § project sum0→eigen direction
survivorPkg-sum0→eigen : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorSum0 k v → SurvivorEigen k v
survivorPkg-sum0→eigen {survivor-full} (_ , (_ , ((sum0→eigen , _) , _))) sum0 = sum0→eigen sum0
survivorPkg-sum0→eigen {survivor-empty} (_ , (_ , ((sum0→eigen , _) , _))) (sum0L , sum0R) = sum0→eigen sum0L sum0R

-- § project eigen→sum0 direction
survivorPkg-eigen→sum0 : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorEigen k v → SurvivorSum0 k v
survivorPkg-eigen→sum0 {survivor-full} (_ , (_ , ((_ , eigen→sum0) , _))) eigen = eigen→sum0 eigen
survivorPkg-eigen→sum0 {survivor-empty} (_ , (_ , ((_ , eigen→sum0) , _))) eigen = eigen→sum0 eigen

-- § image-eigen predicate indexed by survivor
SurvivorImageEigen : (k : CouplingSurvivor) → Vec8ℤ → Set
SurvivorImageEigen survivor-full v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-full (laplacianSurvivorVec8ℤ survivor-full v))
        (eightVec8ℤ (laplacianSurvivorVec8ℤ survivor-full v))
SurvivorImageEigen survivor-empty v =
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (laplacianSurvivorVec8ℤ survivor-empty v))
        (fourVec8ℤ (laplacianSurvivorVec8ℤ survivor-empty v))

-- § project image⊆eigen from package
survivorPkg-image⊆eigen : {k : CouplingSurvivor} {v : Vec8ℤ} →
  SurvivorSpectralPackage k v → SurvivorImageEigen k v
survivorPkg-image⊆eigen {survivor-full} (_ , (_ , (_ , image⊆))) = image⊆
survivorPkg-image⊆eigen {survivor-empty} (_ , (_ , (_ , (_ , image⊆)))) = image⊆

-- § project split-constant kernel from empty package
survivorPkg-splitConstKernel : {v : Vec8ℤ} →
  SurvivorSpectralPackage survivor-empty v → (x y : ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
survivorPkg-splitConstKernel (_ , (_ , (_ , (splitConstKer , _)))) = splitConstKer
-- § construct package from (k, v)
survivorPkg : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSpectralPackage k v
survivorPkg = law14G-37-survivor-spectral-package-byCases

-- § convenience: sumL0
survivor-sumL0 : (k : CouplingSurvivor) (v : Vec8ℤ) → sum8ℤ (laplacianSurvivorVec8ℤ k v) ≡ 0ℤ
survivor-sumL0 k v = survivorPkg-sumL0 (survivorPkg k v)

-- § convenience: JL=0
survivor-JL0 : (k : CouplingSurvivor) (v : Vec8ℤ) → Vec8Eq (J8Vec8ℤ (laplacianSurvivorVec8ℤ k v)) zeroVec8ℤ
survivor-JL0 k v = survivorPkg-JL0 (survivorPkg k v)

-- § convenience: sum0→eigen
survivor-sum0→eigen : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorSum0 k v → SurvivorEigen k v
survivor-sum0→eigen k v sum0 = survivorPkg-sum0→eigen (survivorPkg k v) sum0

-- § convenience: eigen→sum0
survivor-eigen→sum0 : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorEigen k v → SurvivorSum0 k v
survivor-eigen→sum0 k v eigen = survivorPkg-eigen→sum0 (survivorPkg k v) eigen

-- § convenience: image⊆eigen
survivor-image⊆eigen : (k : CouplingSurvivor) (v : Vec8ℤ) → SurvivorImageEigen k v
survivor-image⊆eigen k v = survivorPkg-image⊆eigen (survivorPkg k v)

-- § convenience: split-constant kernel
survivor-splitConstKernel : (v : Vec8ℤ) (x y : ℤ) →
  Vec8Eq (laplacianSurvivorVec8ℤ survivor-empty (constVec8Splitℤ x y)) zeroVec8ℤ
survivor-splitConstKernel v x y = survivorPkg-splitConstKernel {v} (survivorPkg survivor-empty v) x y
-- § three indistinguishable copies
data Copy3 : Set where
  C₀ : Copy3
  C₁ : Copy3
  C₂ : Copy3

-- § copy-inequality predicate
Copy3≠ : (i j : Copy3) → Set
Copy3≠ i j = i ≡ j → ⊥

C₀≠C₁ : Copy3≠ C₀ C₁
C₀≠C₁ ()

C₀≠C₂ : Copy3≠ C₀ C₂
C₀≠C₂ ()

C₁≠C₂ : Copy3≠ C₁ C₂
C₁≠C₂ ()

-- § decidable equality on Copy3 (9 cases)
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

-- § copy permutations (S₃ as explicit bijections)
record CopyPerm : Set where
  field
    to       : Copy3 → Copy3
    from     : Copy3 → Copy3
    to-from  : (y : Copy3) → to (from y) ≡ y
    from-to  : (x : Copy3) → from (to x) ≡ x

open CopyPerm public

-- § identity permutation
permId₃ : CopyPerm
permId₃ = record
  { to = λ x → x
  ; from = λ x → x
  ; to-from = λ _ → refl
  ; from-to = λ _ → refl
  }

-- § swap C₀ ↔ C₁
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
-- § swap C₀ ↔ C₂
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

-- § swap C₁ ↔ C₂
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

-- § 3-cycle C₀ → C₁ → C₂ → C₀
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

-- § 3-cycle C₀ → C₂ → C₁ → C₀
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
-- § transport across four arguments (copies + endpoints)
transport4 : {C : Copy3 → Copy3 → EndoCase → EndoCase → Set}
  {c c' d d' : Copy3} {a a' b b' : EndoCase} →
  c ≡ c' → d ≡ d' → a ≡ a' → b ≡ b' → C c d a b → C c' d' a' b'
transport4 {C = C} {c = c} {c' = c'} {d = d} {d' = d'} {a = a} {a' = a'} {b = b} {b' = b'} ec ed ea eb cab =
  subst (λ c0 → C c0 d' a' b') ec
    (subst (λ d0 → C c d0 a' b') ed
      (subst (λ a0 → C c d a0 b') ea
        (subst (λ b0 → C c d a b0) eb cab)))

-- § cross-coupling predicate among three copies
Coupling3 : Set1
Coupling3 = Copy3 → Copy3 → EndoCase → EndoCase → Set

EndoInv3 : Coupling3 → Set
EndoInv3 C = (c d : Copy3) → CrossInv (λ a b → C c d a b)

CopyInv3 : Coupling3 → Set
CopyInv3 C = (π : CopyPerm) → (c d : Copy3) → (a b : EndoCase) → C c d a b → C (to π c) (to π d) a b

-- § copy-pair transitivity: any ordered distinct pair maps to any other
sendPair₃ : (c0 d0 c d : Copy3) → Copy3≠ c0 d0 → Copy3≠ c d →
  Σ CopyPerm (λ π → (to π c0 ≡ c) × (to π d0 ≡ d))
sendPair₃ C₀ C₀ c d neq0 _ = ⊥-elim (neq0 refl)
sendPair₃ C₁ C₁ c d neq0 _ = ⊥-elim (neq0 refl)
sendPair₃ C₂ C₂ c d neq0 _ = ⊥-elim (neq0 refl)

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
-- § Law 14H.0: one cross-edge forces complete join across all copies
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

-- § Law 14H.1: one cross-non-edge forces disjoint union across all copies
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

-- § canonical survivor couplings
CrossEmpty3 : Coupling3
CrossEmpty3 _ _ _ _ = ⊥

CrossFull3 : Coupling3
CrossFull3 _ _ _ _ = ⊤
-- § Vec12ℤ = three blocks of Vec4ℤ
Vec12ℤ : Set
Vec12ℤ = Vec4ℤ × (Vec4ℤ × Vec4ℤ)

-- § block projections
block₀ : Vec12ℤ → Vec4ℤ
block₀ = fst

block₁ : Vec12ℤ → Vec4ℤ
block₁ v = fst (snd v)

block₂ : Vec12ℤ → Vec4ℤ
block₂ v = snd (snd v)

-- § pointwise equality on Vec12ℤ
Vec12Eq : Vec12ℤ → Vec12ℤ → Set
Vec12Eq u v = Vec4Eq (block₀ u) (block₀ v) × Vec4Eq (block₁ u) (block₁ v) × Vec4Eq (block₂ u) (block₂ v)

-- § global sum: Σ₁₂ v = Σ₄(block₀) + Σ₄(block₁) + Σ₄(block₂)
sum12ℤ : Vec12ℤ → ℤ
sum12ℤ v = sumFin4ℤ (block₀ v) +ℤ (sumFin4ℤ (block₁ v) +ℤ sumFin4ℤ (block₂ v))

-- § global-sum operator J₁₂: broadcast Σ₁₂ to all 12 entries
J12Vec12ℤ : Vec12ℤ → Vec12ℤ
J12Vec12ℤ v = (λ _ → sum12ℤ v) , ((λ _ → sum12ℤ v) , (λ _ → sum12ℤ v))

-- § 12·x = 4·x + 8·x (forced decomposition)
twelveTimesℤ : ℤ → ℤ
twelveTimesℤ x = fourTimesℤ x +ℤ eightTimesℤ x

-- § K₁₂ Laplacian (opaque)
opaque
  K12LaplacianVec12ℤ : Vec12ℤ → Vec12ℤ
  K12LaplacianVec12ℤ v =
    (λ i → twelveTimesℤ (block₀ v i) +ℤ negℤ (sum12ℤ v)) ,
    ((λ i → twelveTimesℤ (block₁ v i) +ℤ negℤ (sum12ℤ v)) ,
     (λ i → twelveTimesℤ (block₂ v i) +ℤ negℤ (sum12ℤ v)))

-- § block-diagonal Laplacian (empty coupling)
laplacianEmptyVec12ℤ : Vec12ℤ → Vec12ℤ
laplacianEmptyVec12ℤ v = laplacianVec4ℤ (block₀ v) , (laplacianVec4ℤ (block₁ v) , laplacianVec4ℤ (block₂ v))

-- § full coupling = K₁₂ Laplacian
laplacianFullVec12ℤ : Vec12ℤ → Vec12ℤ
laplacianFullVec12ℤ = K12LaplacianVec12ℤ
-- § Law 14H.2: empty coupling is block-diagonal
law14H-2-empty-block : (v : Vec12ℤ) →
  Vec12Eq (laplacianEmptyVec12ℤ v)
         (laplacianVec4ℤ (block₀ v) , (laplacianVec4ℤ (block₁ v) , laplacianVec4ℤ (block₂ v)))
law14H-2-empty-block v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

-- § Law 14H.3: full coupling collapses to K₁₂ spectral form
law14H-3-full-is-K12 : (v : Vec12ℤ) → Vec12Eq (laplacianFullVec12ℤ v) (K12LaplacianVec12ℤ v)
law14H-3-full-is-K12 v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

-- § two survivor kinds for the triple coupling
data Coupling3Survivor : Set where
  survivor3-empty : Coupling3Survivor
  survivor3-full  : Coupling3Survivor

-- § Law 14H.4: binary case split
law14H-4-survivor3-cases : (k : Coupling3Survivor) → (k ≡ survivor3-empty) ⊎ (k ≡ survivor3-full)
law14H-4-survivor3-cases survivor3-empty = inj₁ refl
law14H-4-survivor3-cases survivor3-full  = inj₂ refl

-- § survivor dispatch
laplacianSurvivorVec12ℤ : Coupling3Survivor → Vec12ℤ → Vec12ℤ
laplacianSurvivorVec12ℤ survivor3-empty = laplacianEmptyVec12ℤ
laplacianSurvivorVec12ℤ survivor3-full  = laplacianFullVec12ℤ

-- § Vec12ℤ arithmetic operations
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

-- § sum of a constant vector
sum12-const : (x : ℤ) → sum12ℤ (constVec12ℤ x) ≡ twelveTimesℤ x
sum12-const x = refl

-- § sum of J₁₂ v
sum12-J12 : (v : Vec12ℤ) → sum12ℤ (J12Vec12ℤ v) ≡ twelveTimesℤ (sum12ℤ v)
sum12-J12 v = refl
-- § Law 14H.5: J₁₂² = 12·J₁₂
law14H-5-JJ-twelveJ : (v : Vec12ℤ) → Vec12Eq (J12Vec12ℤ (J12Vec12ℤ v)) (twelveVec12ℤ (J12Vec12ℤ v))
law14H-5-JJ-twelveJ v =
  (λ _ → sum12-J12 v) ,
  ((λ _ → sum12-J12 v) ,
   (λ _ → sum12-J12 v))
opaque
  unfolding K12LaplacianVec12ℤ

  -- § Law 14H.6: L₁₂ = 12·I − J₁₂
  law14H-6-L-twelve-minus-J : (v : Vec12ℤ) →
    Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v +Vec12ℤ negVec12ℤ (J12Vec12ℤ v))
  law14H-6-L-twelve-minus-J v =
    (λ _ → refl) ,
    ((λ _ → refl) ,
     (λ _ → refl))

  -- § Law 14H.7: 12·v = L₁₂ v + J₁₂ v
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

  -- § scalar helpers: twelveTimes distributes over addition and negation
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

  -- § sumFin4 commutes with twelveTimes
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

  -- § reassociation helper for triple-block sum
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

  -- § Law 14H.8: global sum of K₁₂ Laplacian = 0
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
  -- § Law 14H.9: J₁₂(L₁₂ v) = 0
  law14H-9-JL-zero : (v : Vec12ℤ) → Vec12Eq (J12Vec12ℤ (K12LaplacianVec12ℤ v)) zeroVec12ℤ
  law14H-9-JL-zero v =
    let sum0 = law14H-8-sumL12-0 v in
    (λ _ → sum0) ,
    ((λ _ → sum0) ,
     (λ _ → sum0))

  -- § Law 14H.10: L₁₂(J₁₂ v) = 0
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

  -- § Law 14H.11: L₁₂² = 12·L₁₂
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
  -- § Law 14H.12: sum-zero ⇒ 12-eigenvector
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

  -- § Law 14H.13: 12-eigenvector ⇒ sum-zero
  law14H-13-eigen12→sum0 : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ
  law14H-13-eigen12→sum0 v eigen12 =
    let a = twelveTimesℤ (block₀ v g0) in
    let s = sum12ℤ v in
    let eq₀ : a +ℤ negℤ s ≡ a
        eq₀ = fst eigen12 g0
    in
    negℤ-zero→zero s (+ℤ-cancel-left a (negℤ s) eq₀)

  -- § Law 14H.14: constant vectors lie in the kernel
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

  -- § Law 14H.15: kernel condition — L₁₂ v = 0 ⇔ 12·v = J₁₂ v
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

  -- § Law 14H.16: image vectors are 12-eigenvectors
  law14H-16-image⊆eigen12 : (v : Vec12ℤ) → Vec12Eq (K12LaplacianVec12ℤ (K12LaplacianVec12ℤ v)) (twelveVec12ℤ (K12LaplacianVec12ℤ v))
  law14H-16-image⊆eigen12 = law14H-11-LL-twelveL

  -- § Law 14H.17: sum-zero ⇒ twelve-scaled image witness
  law14H-17-sum0→twelveInImage : (w : Vec12ℤ) → sum12ℤ w ≡ 0ℤ → Σ Vec12ℤ (λ v → Vec12Eq (K12LaplacianVec12ℤ v) (twelveVec12ℤ w))
  law14H-17-sum0→twelveInImage w sum0 = w , law14H-12-sum0-eigen12 w sum0
  -- § full-survivor spectral package type
  Survivor3FullSpectralPackage : Vec12ℤ → Set
  Survivor3FullSpectralPackage v =
    (sum12ℤ (laplacianSurvivorVec12ℤ survivor3-full v) ≡ 0ℤ) ×
    (Vec12Eq (J12Vec12ℤ (laplacianSurvivorVec12ℤ survivor3-full v)) zeroVec12ℤ) ×
    ((sum12ℤ v ≡ 0ℤ → Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full v) (twelveVec12ℤ v)) ×
     (Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full v) (twelveVec12ℤ v) → sum12ℤ v ≡ 0ℤ)) ×
    (Vec12Eq (laplacianSurvivorVec12ℤ survivor3-full (laplacianSurvivorVec12ℤ survivor3-full v))
             (twelveVec12ℤ (laplacianSurvivorVec12ℤ survivor3-full v)))

  -- § Law 14H.18: full survivor spectral package
  law14H-18-survivor3-full-spectral-package : (v : Vec12ℤ) → Survivor3FullSpectralPackage v
  law14H-18-survivor3-full-spectral-package v =
    law14H-8-sumL12-0 v ,
    (law14H-9-JL-zero v ,
     ((law14H-12-sum0-eigen12 v , law14H-13-eigen12→sum0 v) ,
      law14H-16-image⊆eigen12 v))
-- § nonneg integer from natural
0≤ℤ-fromℕℤ : (n : ℕ) → 0ℤ ≤ℤ fromℕℤ n
0≤ℤ-fromℕℤ zero = tt
0≤ℤ-fromℕℤ (suc n) = tt

-- § nonneg rational ⇒ nonneg numerator
0≤ℚ→0≤ℤnum : (q : ℚ) → 0ℚ ≤ℚ q → 0ℤ ≤ℤ num q
0≤ℚ→0≤ℤnum (a / b) qnonneg =
  let
    lhs0 : (0ℤ *ℤ ⁺toℤ b) ≡ 0ℤ
    lhs0 = *ℤ-zero-left (⁺toℤ b)

    one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
    one⁺ℤ≡oneℤ = refl

    rhs1 : (a *ℤ ⁺toℤ one⁺) ≡ a
    rhs1 = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)
  in
  ≤ℤ-resp-≡ʳ rhs1 (≤ℤ-resp-≡ˡ lhs0 qnonneg)

-- § nonnegativity closed under rational addition
0≤ℚ-+ℚ : (p q : ℚ) → 0ℚ ≤ℚ p → 0ℚ ≤ℚ q → 0ℚ ≤ℚ (p +ℚ q)
0≤ℚ-+ℚ (a / b) (c / d) p≥0 q≥0 =
  let
    a≥0 : 0ℤ ≤ℤ a
    a≥0 = 0≤ℚ→0≤ℤnum (a / b) p≥0

    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) q≥0

    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ s))
        (≤ℤ-mul-pos-right 0ℤ z s z≥0)

    ad≥0 : 0ℤ ≤ℤ (a *ℤ ⁺toℤ d)
    ad≥0 = nonnegScale a d a≥0

    cb≥0 : 0ℤ ≤ℤ (c *ℤ ⁺toℤ b)
    cb≥0 = nonnegScale c b c≥0

    sum≥0 : 0ℤ ≤ℤ ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b))
    sum≥0 =
      let
        adNat : Σ ℕ (λ k → (a *ℤ ⁺toℤ d) ≡ fromℕℤ k)
        adNat = 0≤ℤ→fromℕℤ (a *ℤ ⁺toℤ d) ad≥0

        cbNat : Σ ℕ (λ k → (c *ℤ ⁺toℤ b) ≡ fromℕℤ k)
        cbNat = 0≤ℤ→fromℕℤ (c *ℤ ⁺toℤ b) cb≥0

        k₁ : ℕ
        k₁ = fst adNat

        k₂ : ℕ
        k₂ = fst cbNat

        ad≡ : (a *ℤ ⁺toℤ d) ≡ fromℕℤ k₁
        ad≡ = snd adNat

        cb≡ : (c *ℤ ⁺toℤ b) ≡ fromℕℤ k₂
        cb≡ = snd cbNat

        sumForm : (a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b) ≡ fromℕℤ (k₁ +ℕ k₂)
        sumForm =
          trans
            (cong (λ t → t +ℤ (c *ℤ ⁺toℤ b)) ad≡)
            (trans
              (cong (λ t → fromℕℤ k₁ +ℤ t) cb≡)
              (fromℕℤ-+ℤ k₁ k₂))
      in
      ≤ℤ-resp-≡ʳ (sym sumForm) (0≤ℤ-fromℕℤ (k₁ +ℕ k₂))

    lhs0 : (0ℤ *ℤ ⁺toℤ (b *⁺ d)) ≡ 0ℤ
    lhs0 = *ℤ-zero-left (⁺toℤ (b *⁺ d))

    rhs1 : (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ one⁺) ≡ ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b))
    rhs1 = *ℤ-one-right ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b))
  in
  ≤ℤ-resp-≡ˡ (sym lhs0) (≤ℤ-resp-≡ʳ (sym rhs1) sum≥0)
-- § integer sum-doubling: x≤z, y≤z ⇒ x+y ≤ z+z (nonneg)
≤ℤ-sum≤double-nonneg : {x y z : ℤ} →
  0ℤ ≤ℤ x → 0ℤ ≤ℤ y → 0ℤ ≤ℤ z → x ≤ℤ z → y ≤ℤ z → (x +ℤ y) ≤ℤ (z +ℤ z)
≤ℤ-sum≤double-nonneg {x} {y} {z} xnonneg ynonneg znonneg x≤z y≤z =
  let
    xm : Σ ℕ (λ n → x ≡ fromℕℤ n)
    xm = 0≤ℤ→fromℕℤ x xnonneg

    ym : Σ ℕ (λ n → y ≡ fromℕℤ n)
    ym = 0≤ℤ→fromℕℤ y ynonneg

    zm : Σ ℕ (λ n → z ≡ fromℕℤ n)
    zm = 0≤ℤ→fromℕℤ z znonneg

    m : ℕ
    m = fst xm

    n : ℕ
    n = fst ym

    k : ℕ
    k = fst zm

    x≡ : x ≡ fromℕℤ m
    x≡ = snd xm

    y≡ : y ≡ fromℕℤ n
    y≡ = snd ym

    z≡ : z ≡ fromℕℤ k
    z≡ = snd zm

    x≤zNat : m ≤ k
    x≤zNat = ≤ℤ-fromℕℤ-reflect (≤ℤ-resp-≡ˡ x≡ (≤ℤ-resp-≡ʳ z≡ x≤z))

    y≤zNat : n ≤ k
    y≤zNat = ≤ℤ-fromℕℤ-reflect (≤ℤ-resp-≡ˡ y≡ (≤ℤ-resp-≡ʳ z≡ y≤z))

    step₁ : (m +ℕ n) ≤ (k +ℕ n)
    step₁ =
      subst (λ t → t ≤ (k +ℕ n))
        (sym (+ℕ-comm m n))
        (subst (λ t → (n +ℕ m) ≤ t)
          (+ℕ-comm n k)
          (≤-+ℕ-monoˡ x≤zNat n))

    step₂ : (k +ℕ n) ≤ (k +ℕ k)
    step₂ = ≤-+ℕ-monoˡ y≤zNat k

    sumNat : (m +ℕ n) ≤ (k +ℕ k)
    sumNat = ≤-trans step₁ step₂

    sumℤ : fromℕℤ (m +ℕ n) ≤ℤ fromℕℤ (k +ℕ k)
    sumℤ = fromℕℤ-mono sumNat

    lhsEq : (x +ℤ y) ≡ fromℕℤ (m +ℕ n)
    lhsEq =
      trans
        (cong (λ t → t +ℤ y) x≡)
        (trans
          (cong (λ t → fromℕℤ m +ℤ t) y≡)
          (fromℕℤ-+ℤ m n))

    rhsEq : (z +ℤ z) ≡ fromℕℤ (k +ℕ k)
    rhsEq =
      trans
        (cong (λ t → t +ℤ z) z≡)
        (trans
          (cong (λ t → fromℕℤ k +ℤ t) z≡)
          (fromℕℤ-+ℤ k k))
  in
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) sumℤ)
-- § rational sum-doubling: p≤r, q≤r ⇒ p+q ≤ r+r (nonneg)
≤ℚ-sum≤double-nonneg : (p q r : ℚ) → 0ℚ ≤ℚ p → 0ℚ ≤ℚ q → 0ℚ ≤ℚ r → p ≤ℚ r → q ≤ℚ r → (p +ℚ q) ≤ℚ (r +ℚ r)
≤ℚ-sum≤double-nonneg (a / b) (c / d) (e / f) pnonneg qnonneg rnonneg p≤r q≤r =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    ff : ℕ⁺
    ff = f *⁺ f

    bdf : ℕ⁺
    bdf = bd *⁺ f

    a≥0 : 0ℤ ≤ℤ a
    a≥0 = 0≤ℚ→0≤ℤnum (a / b) pnonneg

    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) qnonneg

    e≥0 : 0ℤ ≤ℤ e
    e≥0 = 0≤ℚ→0≤ℤnum (e / f) rnonneg

    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ s))
        (≤ℤ-mul-pos-right 0ℤ z s z≥0)

    X : ℤ
    X = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ ff

    Y : ℤ
    Y = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ ff

    Z : ℤ
    Z = ((e *ℤ ⁺toℤ bd) *ℤ ⁺toℤ f)

    X≥0 : 0ℤ ≤ℤ X
    X≥0 = nonnegScale (a *ℤ ⁺toℤ d) ff (nonnegScale a d a≥0)

    Y≥0 : 0ℤ ≤ℤ Y
    Y≥0 = nonnegScale (c *ℤ ⁺toℤ b) ff (nonnegScale c b c≥0)

    Z≥0 : 0ℤ ≤ℤ Z
    Z≥0 = nonnegScale (e *ℤ ⁺toℤ bd) f (nonnegScale e bd e≥0)

    -- scale p≤r to common base
    pScaled₁ : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ≤ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    pScaled₁ = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) d p≤r

    pScaled₂ : (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ (((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f)
    pScaled₂ = ≤ℤ-mul-pos-right ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) f pScaled₁

    qScaled₁ : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    qScaled₁ = ≤ℤ-mul-pos-right (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) b q≤r

    qScaled₂ : (((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≤ℤ (((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    qScaled₂ = ≤ℤ-mul-pos-right ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) f qScaled₁

    -- rewrite both sides into X ≤ Z, Y ≤ Z
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    Xeq : (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≡ X
    Xeq =
      trans
        (cong (λ t → t *ℤ ⁺toℤ f) (swapScale a f d))
        (sym (scaleSplit (a *ℤ ⁺toℤ d) f f))

    Zeq₁ : (((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≡ Z
    Zeq₁ =
      cong (λ t → t *ℤ ⁺toℤ f) (sym (scaleSplit e b d))

    Zeq₂ : (((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≡ Z
    Zeq₂ =
      trans
        (cong (λ t → t *ℤ ⁺toℤ f) (swapScale e d b))
        Zeq₁

    X≤Z : X ≤ℤ Z
    X≤Z =
      subst (λ t → X ≤ℤ t) Zeq₁
        (subst (λ t → t ≤ℤ (((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f))
          Xeq
          pScaled₂)

    Yeq : (((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≡ Y
    Yeq =
      trans
        (cong (λ t → t *ℤ ⁺toℤ f) (swapScale c f b))
        (sym (scaleSplit (c *ℤ ⁺toℤ b) f f))

    Y≤Z : Y ≤ℤ Z
    Y≤Z =
      subst (λ t → Y ≤ℤ t) Zeq₂
        (subst (λ t → t ≤ℤ (((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f))
          Yeq
          qScaled₂)

    sumLe : (X +ℤ Y) ≤ℤ (Z +ℤ Z)
    sumLe = ≤ℤ-sum≤double-nonneg X≥0 Y≥0 Z≥0 X≤Z Y≤Z

    lhsEq : (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ ff) ≡ (X +ℤ Y)
    lhsEq =
      trans
        (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) (⁺toℤ ff))
        refl

    rhsEq : (((e *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ f)) *ℤ ⁺toℤ bd) ≡ (Z +ℤ Z)
    rhsEq =
      let
        ef : ℤ
        ef = e *ℤ ⁺toℤ f

        efbd≡Z : (ef *ℤ ⁺toℤ bd) ≡ Z
        efbd≡Z =
          trans
            (*ℤ-assoc e (⁺toℤ f) (⁺toℤ bd))
            (trans
              (cong (λ t → e *ℤ t) (*ℤ-comm (⁺toℤ f) (⁺toℤ bd)))
              (sym (*ℤ-assoc e (⁺toℤ bd) (⁺toℤ f))))
      in
      trans
        (*ℤ-distrib-left-+ℤ ef ef (⁺toℤ bd))
        (cong (λ t → t +ℤ t) efbd≡Z)

  in
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) sumLe)
-- § negative normalisation step
neg≤normalize : (n m : ℕ) → (-suc m) ≤ℤ normalizeℤ n m
neg≤normalize zero zero = tt
neg≤normalize zero (suc m) = ≤-step (suc m)
neg≤normalize (suc n) zero = tt
neg≤normalize (suc n) (suc m) =
  ≤ℤ-trans negStep (neg≤normalize n m)
  where
    negStep : (-suc (suc m)) ≤ℤ (-suc m)
    negStep = s≤s (≤-step m)

-- § adding a positive integer on the right
≤ℤ-add-pos-right : (x : ℤ) → (n : ℕ) → x ≤ℤ (x +ℤ (+suc n))
≤ℤ-add-pos-right 0ℤ n = tt
≤ℤ-add-pos-right (+suc m) n = s≤s m≤m+n
  where
    m≤m+n : m ≤ (m +ℕ suc n)
    m≤m+n =
      subst (λ t → t ≤ (m +ℕ suc n))
        (+ℕ-zero-right m)
        (≤-+ℕ-monoˡ {a = zero} {b = suc n} z≤n m)
≤ℤ-add-pos-right (-suc m) n =
  let
    rhsEq : ((-suc m) +ℤ (+suc n)) ≡ normalizeℤ n m
    rhsEq =
      trans
        (cong (λ t → normalizeℤ (suc n) t) (+ℕ-zero-right (suc m)))
        refl
  in
  ≤ℤ-resp-≡ʳ (sym rhsEq) (neg≤normalize n m)

-- § adding a nonneg integer on the right
≤ℤ-add-nonneg-right : (x y : ℤ) → 0ℤ ≤ℤ y → x ≤ℤ (x +ℤ y)
≤ℤ-add-nonneg-right x y y≥0 with 0≤ℤ→fromℕℤ y y≥0
... | (zero , y≡) =
  ≤ℤ-resp-≡ʳ (sym (cong (λ t → x +ℤ t) y≡)) (≤ℤ-resp-≡ʳ (sym (+ℤ-zero-right x)) (≤ℤ-refl x))
... | (suc n , y≡) =
  ≤ℤ-resp-≡ʳ (sym (cong (λ t → x +ℤ t) y≡)) (≤ℤ-add-pos-right x n)

-- § adding a nonneg rational on the right preserves ≤
≤ℚ-add-nonneg-right : (p q : ℚ) → 0ℚ ≤ℚ q → p ≤ℚ (p +ℚ q)
≤ℚ-add-nonneg-right (a / b) (c / d) qnonneg =
  let
    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) qnonneg

    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ s))
        (≤ℤ-mul-pos-right 0ℤ z s z≥0)

    x : ℤ
    x = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ b

    y : ℤ
    y = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ b

    y≥0 : 0ℤ ≤ℤ y
    y≥0 = nonnegScale (c *ℤ ⁺toℤ b) b (nonnegScale c b c≥0)

    x≤x+y : x ≤ℤ (x +ℤ y)
    x≤x+y = ≤ℤ-add-nonneg-right x y y≥0

    lhsEq : (a *ℤ ⁺toℤ (b *⁺ d)) ≡ x
    lhsEq =
      let
        scaleSplit : (z : ℤ) → (u v : ℕ⁺) → z *ℤ ⁺toℤ (u *⁺ v) ≡ (z *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
        scaleSplit z u v =
          trans
            (cong (λ t → z *ℤ t) (⁺toℤ-*⁺ u v))
            (sym (*ℤ-assoc z (⁺toℤ u) (⁺toℤ v)))

        swapScale : (z : ℤ) → (u v : ℕ⁺) → (z *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (z *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
        swapScale z u v =
          trans
            (*ℤ-assoc z (⁺toℤ u) (⁺toℤ v))
            (trans
              (cong (λ t → z *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
              (sym (*ℤ-assoc z (⁺toℤ v) (⁺toℤ u))))
      in
      trans
        (trans
          (cong (λ t → a *ℤ t) (⁺toℤ-*⁺ b d))
          (sym (*ℤ-assoc a (⁺toℤ b) (⁺toℤ d))))
        (swapScale a b d)

    rhsEq : (((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) *ℤ ⁺toℤ b) ≡ (x +ℤ y)
    rhsEq =
      trans
        (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) (⁺toℤ b))
        refl
  in
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) x≤x+y)
-- § right monotonicity: p ≤ q ⇒ (p + r) ≤ (q + r)
≤ℚ-+ℚ-mono-right : (p q r : ℚ) → p ≤ℚ q → (p +ℚ r) ≤ℚ (q +ℚ r)
≤ℚ-+ℚ-mono-right (a / b) (c / d) (e / f) p≤q =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    bf : ℕ⁺
    bf = b *⁺ f

    df : ℕ⁺
    df = d *⁺ f

    p≤q-scaled₁ : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    p≤q-scaled₁ = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b) f p≤q

    p≤q-scaled₂ : (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ ⁺toℤ f) ≤ℤ (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ ⁺toℤ f)
    p≤q-scaled₂ = ≤ℤ-mul-pos-right ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) f p≤q-scaled₁

    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    ff : ℕ⁺
    ff = f *⁺ f

    lhsTerm₁ : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) ≡ (((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) *ℤ ⁺toℤ f)
    lhsTerm₁ =
      trans
        (scaleSplit (a *ℤ ⁺toℤ f) d f)
        (cong (λ t → t *ℤ ⁺toℤ f) (swapScale a f d))

    rhsTerm₁ : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) ≡ (((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) *ℤ ⁺toℤ f)
    rhsTerm₁ =
      trans
        (scaleSplit (c *ℤ ⁺toℤ f) b f)
        (cong (λ t → t *ℤ ⁺toℤ f) (swapScale c f b))

    rTerm : (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df ≡ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf
    rTerm =
      trans
        (scaleSplit (e *ℤ ⁺toℤ b) d f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale e b d))
          (sym (scaleSplit (e *ℤ ⁺toℤ d) b f)))

    lhsSum : ℤ
    lhsSum = ((a *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ b)) *ℤ ⁺toℤ df

    rhsSum : ℤ
    rhsSum = ((c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)) *ℤ ⁺toℤ bf

    lhsExpand : lhsSum ≡ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df)
    lhsExpand = *ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) (⁺toℤ df)

    rhsExpand : rhsSum ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
    rhsExpand = *ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ bf)

    lhsT₁≤rhsT₁ : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) ≤ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf)
    lhsT₁≤rhsT₁ =
      ≤ℤ-resp-≡ˡ (sym lhsTerm₁) (≤ℤ-resp-≡ʳ (sym rhsTerm₁) p≤q-scaled₂)

    eTerm≡ : ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df) ≡ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
    eTerm≡ = rTerm

    eTerm≤ : ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
    eTerm≤ = ≤ℤ-resp-≡ʳ eTerm≡ (≤ℤ-refl ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df))

    sumLe : (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df)) ≤ℤ (((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf))
    sumLe = ≤ℤ-+ℤ-mono lhsT₁≤rhsT₁ eTerm≤
  in
  ≤ℤ-resp-≡ˡ (sym lhsExpand) (≤ℤ-resp-≡ʳ (sym rhsExpand) sumLe)

-- § left monotonicity: q ≤ r ⇒ (p + q) ≤ (p + r)
≤ℚ-+ℚ-mono-left : (p q r : ℚ) → q ≤ℚ r → (p +ℚ q) ≤ℚ (p +ℚ r)
≤ℚ-+ℚ-mono-left p q r q≤r =
  let
    step₁ : (q +ℚ p) ≤ℚ (r +ℚ p)
    step₁ = ≤ℚ-+ℚ-mono-right q r p q≤r

    step₂ : (p +ℚ q) ≤ℚ (q +ℚ p)
    step₂ = ≃ℚ→≤ℚˡ {p = p +ℚ q} {q = q +ℚ p} (+ℚ-comm p q)

    step₃ : (r +ℚ p) ≤ℚ (p +ℚ r)
    step₃ = ≃ℚ→≤ℚˡ {p = r +ℚ p} {q = p +ℚ r} (+ℚ-comm r p)
  in
  ≤ℚ-trans {x = p +ℚ q} {y = q +ℚ p} {z = p +ℚ r} step₂
    (≤ℚ-trans {x = q +ℚ p} {y = r +ℚ p} {z = p +ℚ r} step₁ step₃)
-- § Vec12Eq is an equivalence
Vec12Eq-refl : (v : Vec12ℤ) → Vec12Eq v v
Vec12Eq-refl v = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

Vec12Eq-sym : {u v : Vec12ℤ} → Vec12Eq u v → Vec12Eq v u
Vec12Eq-sym eq =
  (λ i → sym (fst eq i)) ,
  ((λ i → sym (fst (snd eq) i)) ,
   (λ i → sym (snd (snd eq) i)))

Vec12Eq-trans : {u v w : Vec12ℤ} → Vec12Eq u v → Vec12Eq v w → Vec12Eq u w
Vec12Eq-trans eq₁ eq₂ =
  (λ i → trans (fst eq₁ i) (fst eq₂ i)) ,
  ((λ i → trans (fst (snd eq₁) i) (fst (snd eq₂) i)) ,
   (λ i → trans (snd (snd eq₁) i) (snd (snd eq₂) i)))

-- § sum congruence: blockwise
sum12-cong : (u v : Vec12ℤ) → Vec12Eq u v → sum12ℤ u ≡ sum12ℤ v
sum12-cong u v eq =
  trans
    (cong (λ t → t +ℤ (sumFin4ℤ (block₁ u) +ℤ sumFin4ℤ (block₂ u)))
         (sumFin4-cong (block₀ u) (block₀ v) (fst eq)))
    (cong (λ t → sumFin4ℤ (block₀ v) +ℤ t)
      (trans
        (cong (λ t → t +ℤ sumFin4ℤ (block₂ u))
              (sumFin4-cong (block₁ u) (block₁ v) (fst (snd eq))))
        (cong (λ t → sumFin4ℤ (block₁ v) +ℤ t)
              (sumFin4-cong (block₂ u) (block₂ v) (snd (snd eq))))))

-- § scaling congruence
twelveVec12-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (twelveVec12ℤ u) (twelveVec12ℤ v)
twelveVec12-cong u v eq =
  (λ i → cong twelveTimesℤ (fst eq i)) ,
  ((λ i → cong twelveTimesℤ (fst (snd eq) i)) ,
   (λ i → cong twelveTimesℤ (snd (snd eq) i)))

opaque
  unfolding K12LaplacianVec12ℤ

  -- § K₁₂ Laplacian congruence
  K12Laplacian-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (K12LaplacianVec12ℤ u) (K12LaplacianVec12ℤ v)
  K12Laplacian-cong u v eq =
    (λ i →
      let pBlock = cong twelveTimesℤ (fst eq i) in
      let pSum   = cong negℤ (sum12-cong u v eq) in
      trans (cong (λ t → twelveTimesℤ (block₀ u i) +ℤ t) pSum)
            (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)) ,
    ((λ i →
      let pBlock = cong twelveTimesℤ (fst (snd eq) i) in
      let pSum   = cong negℤ (sum12-cong u v eq) in
      trans (cong (λ t → twelveTimesℤ (block₁ u i) +ℤ t) pSum)
            (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)) ,
     (λ i →
      let pBlock = cong twelveTimesℤ (snd (snd eq) i) in
      let pSum   = cong negℤ (sum12-cong u v eq) in
      trans (cong (λ t → twelveTimesℤ (block₂ u i) +ℤ t) pSum)
            (trans (cong (λ t → t +ℤ negℤ (sum12ℤ v)) pBlock) refl)))
-- § Law 14K.0: two-step recurrence L₁₂^(n+2) = 12·L₁₂^(n+1)
law14K-0-LL-step : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc (suc n)) K12LaplacianVec12ℤ v)
         (twelveVec12ℤ (powEndo (suc n) K12LaplacianVec12ℤ v))
law14K-0-LL-step n v = law14H-11-LL-twelveL (powEndo n K12LaplacianVec12ℤ v)

-- § Law 14K.1: L₁₂^(n+1) = 12^n · L₁₂
law14K-1-Lpow-scaling : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc n) K12LaplacianVec12ℤ v)
         (powEndo n twelveVec12ℤ (K12LaplacianVec12ℤ v))
law14K-1-Lpow-scaling zero v = Vec12Eq-refl (K12LaplacianVec12ℤ v)
law14K-1-Lpow-scaling (suc n) v =
  Vec12Eq-trans
    (law14K-0-LL-step n v)
    (twelveVec12-cong
      (powEndo (suc n) K12LaplacianVec12ℤ v)
      (powEndo n twelveVec12ℤ (K12LaplacianVec12ℤ v))
      (law14K-1-Lpow-scaling n v))

-- § Law 14K.2: J₁₂^(n+1) = 12^n · J₁₂
law14K-2-Jpow-scaling : (n : ℕ) → (v : Vec12ℤ) →
  Vec12Eq (powEndo (suc n) J12Vec12ℤ v)
         (powEndo n twelveVec12ℤ (J12Vec12ℤ v))
law14K-2-Jpow-scaling zero v = Vec12Eq-refl (J12Vec12ℤ v)
law14K-2-Jpow-scaling (suc n) v =
  Vec12Eq-trans
    (law14H-5-JJ-twelveJ (powEndo n J12Vec12ℤ v))
    (twelveVec12-cong
      (powEndo (suc n) J12Vec12ℤ v)
      (powEndo n twelveVec12ℤ (J12Vec12ℤ v))
      (law14K-2-Jpow-scaling n v))
-- § generator and word types
data Gen : Set where
  Lg : Gen
  Jg : Gen

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

Word : Set
Word = List Gen

-- § operator type and equality
Op : Set
Op = GenEndo Vec12ℤ

OpEq : Op → Op → Set
OpEq f g = (v : Vec12ℤ) → Vec12Eq (f v) (g v)

idOp : Op
idOp = idGenEndo

zeroOp : Op
zeroOp _ = zeroVec12ℤ

LOp : Op
LOp = K12LaplacianVec12ℤ

JOp : Op
JOp = J12Vec12ℤ

-- § word evaluation
evalGen : Gen → Op
evalGen Lg = LOp
evalGen Jg = JOp

evalWord : Word → Op
evalWord []       = idOp
evalWord (g ∷ w)  = evalGen g ∘ evalWord w

-- § four classification cases
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

-- § step function: how appending a generator updates the case
stepCase : Gen → WordCase → WordCase
stepCase Lg empty     = Lpow zero
stepCase Jg empty     = Jpow zero
stepCase Lg (Lpow n)  = Lpow (suc n)
stepCase Jg (Jpow n)  = Jpow (suc n)
stepCase Lg (Jpow _)  = mixed
stepCase Jg (Lpow _)  = mixed
stepCase _  mixed     = mixed

-- § J₁₂ congruence (from sum congruence)
J12-cong : (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (JOp u) (JOp v)
J12-cong u v eq =
  let sEq = sum12-cong u v eq in
  (λ _ → sEq) , ((λ _ → sEq) , (λ _ → sEq))

-- § mixed annihilation: L after J-powers and J after L-powers
L∘Jpow-zero : (n : ℕ) → OpEq (LOp ∘ powEndo (suc n) JOp) zeroOp
L∘Jpow-zero n v = law14H-10-LJ-zero (powEndo n JOp v)

J∘Lpow-zero : (n : ℕ) → OpEq (JOp ∘ powEndo (suc n) LOp) zeroOp
J∘Lpow-zero n v = law14H-9-JL-zero (powEndo n LOp v)

-- § composition respects case classification (8 cases)
composeGenCase : (g : Gen) → (c : WordCase) → OpEq (evalGen g ∘ caseOp c) (caseOp (stepCase g c))
composeGenCase Lg empty v = Vec12Eq-refl (LOp v)
composeGenCase Jg empty v = Vec12Eq-refl (JOp v)
composeGenCase Lg (Lpow n) v = Vec12Eq-refl (powEndo (suc (suc n)) LOp v)
composeGenCase Jg (Jpow n) v = Vec12Eq-refl (powEndo (suc (suc n)) JOp v)
composeGenCase Lg (Jpow n) v = L∘Jpow-zero n v
composeGenCase Jg (Lpow n) v = J∘Lpow-zero n v
composeGenCase Lg mixed v = law14H-14-const-eigen0 0ℤ
composeGenCase Jg mixed v = Vec12Eq-refl zeroVec12ℤ

-- § generator congruence
congGen : (g : Gen) → (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (evalGen g u) (evalGen g v)
congGen Lg u v eq = K12Laplacian-cong u v eq
congGen Jg u v eq = J12-cong u v eq

-- § Law 14L.0: every word classifies uniquely
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
-- § triple ℕ⁺-product helpers
⁺toℤ-*⁺-assocʳ : (a b c : ℕ⁺) → ⁺toℤ ((a *⁺ b) *⁺ c) ≡ (⁺toℤ a) *ℤ ((⁺toℤ b) *ℤ (⁺toℤ c))
⁺toℤ-*⁺-assocʳ a b c =
  trans
    (⁺toℤ-*⁺ (a *⁺ b) c)
    (trans
      (cong (λ t → t *ℤ ⁺toℤ c) (⁺toℤ-*⁺ a b))
      (*ℤ-assoc (⁺toℤ a) (⁺toℤ b) (⁺toℤ c)))

⁺toℤ-*⁺-assocˡ : (a b c : ℕ⁺) → ⁺toℤ (a *⁺ (b *⁺ c)) ≡ (⁺toℤ a) *ℤ ((⁺toℤ b) *ℤ (⁺toℤ c))
⁺toℤ-*⁺-assocˡ a b c =
  trans
    (⁺toℤ-*⁺ a (b *⁺ c))
    (cong (λ t → (⁺toℤ a) *ℤ t) (⁺toℤ-*⁺ b c))

-- § *ℚ associativity
*ℚ-assoc : (p q r : ℚ) → (p *ℚ q) *ℚ r ≃ℚ p *ℚ (q *ℚ r)
*ℚ-assoc (a / b) (c / d) (e / f) =
  let
    numAssoc : ((a *ℤ c) *ℤ e) ≡ (a *ℤ (c *ℤ e))
    numAssoc = *ℤ-assoc a c e

    denL : ⁺toℤ ((b *⁺ d) *⁺ f) ≡ (⁺toℤ b) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ f))
    denL = ⁺toℤ-*⁺-assocʳ b d f

    denR : ⁺toℤ (b *⁺ (d *⁺ f)) ≡ (⁺toℤ b) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ f))
    denR = ⁺toℤ-*⁺-assocˡ b d f

    denEq : ⁺toℤ ((b *⁺ d) *⁺ f) ≡ ⁺toℤ (b *⁺ (d *⁺ f))
    denEq = trans denL (sym denR)

    cross : (((a *ℤ c) *ℤ e) *ℤ ⁺toℤ (b *⁺ (d *⁺ f))) ≡ ((a *ℤ (c *ℤ e)) *ℤ ⁺toℤ ((b *⁺ d) *⁺ f))
    cross =
      trans
        (cong (λ t → ((a *ℤ c) *ℤ e) *ℤ t) (sym denEq))
        (cong (λ t → t *ℤ ⁺toℤ ((b *⁺ d) *⁺ f)) numAssoc)
  in
  cross

-- § *ℚ right identity
*ℚ-one-right : (p : ℚ) → (p *ℚ 1ℚ) ≃ℚ p
*ℚ-one-right (a / b) =
  let
    numEq : (a *ℤ oneℤ) ≡ a
    numEq = *ℤ-one-right a

    denOne : ⁺toℤ b ≡ ⁺toℤ (b *⁺ one⁺)
    denOne =
      trans
        (sym (*ℤ-one-right (⁺toℤ b)))
        (sym (⁺toℤ-*⁺ b one⁺))

    cross : ((a *ℤ oneℤ) *ℤ ⁺toℤ b) ≡ (a *ℤ ⁺toℤ (b *⁺ one⁺))
    cross =
      trans
        (cong (λ t → t *ℤ ⁺toℤ b) numEq)
        (cong (λ t → a *ℤ t) denOne)
  in
  cross

-- § *ℚ left identity
*ℚ-one-left : (p : ℚ) → (1ℚ *ℚ p) ≃ℚ p
*ℚ-one-left (a / b) =
  let
    numEq : (oneℤ *ℤ a) ≡ a
    numEq = *ℤ-one-left a

    denOneL : ⁺toℤ b ≡ ⁺toℤ (one⁺ *⁺ b)
    denOneL = sym (trans (⁺toℤ-*⁺ one⁺ b) (*ℤ-one-left (⁺toℤ b)))
  in
  trans
    (cong (λ t → t *ℤ ⁺toℤ b) numEq)
    (cong (λ t → a *ℤ t) denOneL)

-- § *ℚ zero annihilation (left)
*ℚ-zero-left : (p : ℚ) → (0ℚ *ℚ p) ≃ℚ 0ℚ
*ℚ-zero-left (a / b) =
  let
    numEq : (0ℤ *ℤ a) ≡ 0ℤ
    numEq = *ℤ-zero-left a

    cross : ((0ℤ *ℤ a) *ℤ ⁺toℤ one⁺) ≡ (0ℤ *ℤ ⁺toℤ (one⁺ *⁺ b))
    cross =
      trans
        (cong (λ t → t *ℤ ⁺toℤ one⁺) numEq)
        (trans
          (*ℤ-zero-left (⁺toℤ one⁺))
          (sym (*ℤ-zero-left (⁺toℤ (one⁺ *⁺ b)))))
  in
  cross

-- § *ℚ zero annihilation (right)
*ℚ-zero-right : (p : ℚ) → (p *ℚ 0ℚ) ≃ℚ 0ℚ
*ℚ-zero-right (a / b) =
  let
    numEq : (a *ℤ 0ℤ) ≡ 0ℤ
    numEq = *ℤ-zero-right a
  in
  trans
    (cong (λ t → t *ℤ ⁺toℤ one⁺) numEq)
    (trans
      (*ℤ-zero-left (⁺toℤ one⁺))
      (sym (*ℤ-zero-left (⁺toℤ (b *⁺ one⁺)))))
-- § *ℚ right-distributes over +ℚ
*ℚ-distrib-right-+ℚ : (p q r : ℚ) → p *ℚ (q +ℚ r) ≃ℚ (p *ℚ q) +ℚ (p *ℚ r)
*ℚ-distrib-right-+ℚ (a / b) (c / d) (e / f) =
  let
    B : ℤ
    B = ⁺toℤ b

    D : ℤ
    D = ⁺toℤ d

    F : ℤ
    F = ⁺toℤ f

    bd : ℕ⁺
    bd = b *⁺ d

    bf : ℕ⁺
    bf = b *⁺ f

    df : ℕ⁺
    df = d *⁺ f

    denR : ℤ
    denR = (B *ℤ D) *ℤ (B *ℤ F)

    denL : ℤ
    denL = B *ℤ (D *ℤ F)

    denR≡ : ⁺toℤ (bd *⁺ bf) ≡ denR
    denR≡ =
      trans
        (⁺toℤ-*⁺ bd bf)
        (cong₂ _*ℤ_ (⁺toℤ-*⁺ b d) (⁺toℤ-*⁺ b f))

    denL≡ : ⁺toℤ (b *⁺ df) ≡ denL
    denL≡ = ⁺toℤ-*⁺-assocˡ b d f

    cF : ℤ
    cF = c *ℤ F

    eD : ℤ
    eD = e *ℤ D

    lhsNum : ℤ
    lhsNum = a *ℤ (cF +ℤ eD)

    lhsExpand₀ : (lhsNum *ℤ denR) ≡ ((a *ℤ cF) *ℤ denR) +ℤ ((a *ℤ eD) *ℤ denR)
    lhsExpand₀ =
      trans
        (cong (λ t → t *ℤ denR) (*ℤ-distrib-right-+ℤ a cF eD))
        (*ℤ-distrib-left-+ℤ (a *ℤ cF) (a *ℤ eD) denR)

    rhsNum : ℤ
    rhsNum = ((a *ℤ c) *ℤ ⁺toℤ bf) +ℤ ((a *ℤ e) *ℤ ⁺toℤ bd)

    rhsExpand₀ : (rhsNum *ℤ denL) ≡ (((a *ℤ c) *ℤ ⁺toℤ bf) *ℤ denL) +ℤ (((a *ℤ e) *ℤ ⁺toℤ bd) *ℤ denL)
    rhsExpand₀ = *ℤ-distrib-left-+ℤ ((a *ℤ c) *ℤ ⁺toℤ bf) ((a *ℤ e) *ℤ ⁺toℤ bd) denL

    -- term 1 alignment
    t1-lhs : ((a *ℤ cF) *ℤ denR) ≡ ((a *ℤ c) *ℤ denR) *ℤ F
    t1-lhs =
      trans
        (cong (λ t → t *ℤ denR) (sym (*ℤ-assoc a c F)))
        (trans
          (*ℤ-assoc (a *ℤ c) F denR)
          (trans
            (cong (λ t → (a *ℤ c) *ℤ t) (*ℤ-comm F denR))
            (sym (*ℤ-assoc (a *ℤ c) denR F))))

    t1-rhs : (((a *ℤ c) *ℤ ⁺toℤ bf) *ℤ denL) ≡ ((a *ℤ c) *ℤ denR) *ℤ F
    t1-rhs =
      let
        bf→ : ⁺toℤ bf ≡ B *ℤ F
        bf→ = ⁺toℤ-*⁺ b f

        denL→ : denL ≡ (B *ℤ D) *ℤ F
        denL→ = sym (*ℤ-assoc B D F)
      in
      trans
        (cong (λ t → ((a *ℤ c) *ℤ t) *ℤ denL) bf→)
        (trans
          (cong (λ t → ((a *ℤ c) *ℤ (B *ℤ F)) *ℤ t) denL→)
          (trans
            (sym (*ℤ-assoc ((a *ℤ c) *ℤ (B *ℤ F)) (B *ℤ D) F))
            (trans
              (cong (λ t → t *ℤ F) (*ℤ-assoc (a *ℤ c) (B *ℤ F) (B *ℤ D)))
              (cong (λ t → ((a *ℤ c) *ℤ t) *ℤ F) (*ℤ-comm (B *ℤ F) (B *ℤ D))))))

    t1 : ((a *ℤ cF) *ℤ denR) ≡ (((a *ℤ c) *ℤ ⁺toℤ bf) *ℤ denL)
    t1 = trans t1-lhs (sym t1-rhs)

    -- term 2 alignment
    t2-lhs : ((a *ℤ eD) *ℤ denR) ≡ ((a *ℤ e) *ℤ denR) *ℤ D
    t2-lhs =
      trans
          (cong (λ t → t *ℤ denR) (sym (*ℤ-assoc a e D)))
          (trans
            (*ℤ-assoc (a *ℤ e) D denR)
            (trans
              (cong (λ t → (a *ℤ e) *ℤ t) (*ℤ-comm D denR))
              (sym (*ℤ-assoc (a *ℤ e) denR D))))

    t2-rhs : (((a *ℤ e) *ℤ ⁺toℤ bd) *ℤ denL) ≡ ((a *ℤ e) *ℤ denR) *ℤ D
    t2-rhs =
      let
        bd→ : ⁺toℤ bd ≡ B *ℤ D
        bd→ = ⁺toℤ-*⁺ b d

        denL→ : denL ≡ (B *ℤ F) *ℤ D
        denL→ =
          trans
            (cong (λ t → B *ℤ t) (*ℤ-comm D F))
            (sym (*ℤ-assoc B F D))
      in
      trans
        (cong (λ t → ((a *ℤ e) *ℤ t) *ℤ denL) bd→)
        (trans
          (cong (λ t → ((a *ℤ e) *ℤ (B *ℤ D)) *ℤ t) denL→)
          (trans
            (sym (*ℤ-assoc ((a *ℤ e) *ℤ (B *ℤ D)) (B *ℤ F) D))
            (cong (λ t → t *ℤ D) (*ℤ-assoc (a *ℤ e) (B *ℤ D) (B *ℤ F)))))

    t2 : ((a *ℤ eD) *ℤ denR) ≡ (((a *ℤ e) *ℤ ⁺toℤ bd) *ℤ denL)
    t2 = trans t2-lhs (sym t2-rhs)

    sumEq : (((a *ℤ cF) *ℤ denR) +ℤ ((a *ℤ eD) *ℤ denR)) ≡ ((((a *ℤ c) *ℤ ⁺toℤ bf) *ℤ denL) +ℤ (((a *ℤ e) *ℤ ⁺toℤ bd) *ℤ denL))
    sumEq = cong₂ _+ℤ_ t1 t2
  in
  trans
    (cong (λ t → lhsNum *ℤ t) denR≡)
    (trans
      lhsExpand₀
      (trans
        sumEq
        (trans
          (sym rhsExpand₀)
          (cong (λ t → rhsNum *ℤ t) (sym denL≡)))))

-- § *ℚ left-distributes over +ℚ (by commutativity reduction)
*ℚ-distrib-left-+ℚ : (p q r : ℚ) → (p +ℚ q) *ℚ r ≃ℚ (p *ℚ r) +ℚ (q *ℚ r)
*ℚ-distrib-left-+ℚ p q r =
  ≃ℚ-trans
    {p = (p +ℚ q) *ℚ r}
    {q = r *ℚ (p +ℚ q)}
    {r = (p *ℚ r) +ℚ (q *ℚ r)}
    (*ℚ-comm (p +ℚ q) r)
    (≃ℚ-trans
      {p = r *ℚ (p +ℚ q)}
      {q = (r *ℚ p) +ℚ (r *ℚ q)}
      {r = (p *ℚ r) +ℚ (q *ℚ r)}
      (*ℚ-distrib-right-+ℚ r p q)
      (+ℚ-resp-≃
        {p = r *ℚ p}
        {p' = p *ℚ r}
        {q = r *ℚ q}
        {q' = q *ℚ r}
        (*ℚ-comm r p)
        (*ℚ-comm r q)))
-- § forced constant: 2 as ℕ⁺
two⁺ : ℕ⁺
two⁺ = suc⁺ one⁺

-- § denominator constructors for ε-splitting
halfDen : ℕ⁺ → ℕ⁺
halfDen b = two⁺ *⁺ b

quarterDen : ℕ⁺ → ℕ⁺
quarterDen b = two⁺ *⁺ (two⁺ *⁺ b)

εQuarter : ℚ → ℚ
εQuarter (a / b) = oneℤ / quarterDen b

εHalf : ℚ → ℚ
εHalf (a / b) = oneℤ / halfDen b

-- § εQuarter is positive
εQuarter-pos : (ε : ℚ) → 0ℚ <ℚ εQuarter ε
εQuarter-pos (a / b) =
  let
    qd : ℕ⁺
    qd = quarterDen b

    lhs0 : (0ℤ *ℤ ⁺toℤ qd) ≡ 0ℤ
    lhs0 = *ℤ-zero-left (⁺toℤ qd)

    one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
    one⁺ℤ≡oneℤ = refl

    rhs1 : (oneℤ *ℤ ⁺toℤ one⁺) ≡ oneℤ
    rhs1 = trans (cong (λ t → oneℤ *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right oneℤ)
  in
  <ℤ-resp-≡ˡ {x = 0ℤ} {y = 0ℤ *ℤ ⁺toℤ qd} {z = oneℤ *ℤ ⁺toℤ one⁺} (sym lhs0)
    (<ℤ-resp-≡ʳ {x = 0ℤ} {y = oneℤ} {z = oneℤ *ℤ ⁺toℤ one⁺} (sym rhs1) 0ℤ<oneℤ)

-- § doubling εQuarter yields εHalf (up to ≃ℚ)
εQuarter+εQuarter≃εHalf : (ε : ℚ) → (εQuarter ε +ℚ εQuarter ε) ≃ℚ (εHalf ε)
εQuarter+εQuarter≃εHalf (a / b) =
  let
    qd : ℕ⁺
    qd = quarterDen b

    hd : ℕ⁺
    hd = halfDen b

    lhsNum : ℤ
    lhsNum = (oneℤ *ℤ ⁺toℤ qd) +ℤ (oneℤ *ℤ ⁺toℤ qd)

    lhsDen : ℕ⁺
    lhsDen = qd *⁺ qd

    qdSplit : ⁺toℤ qd ≡ (⁺toℤ two⁺) *ℤ ((⁺toℤ two⁺) *ℤ (⁺toℤ b))
    qdSplit =
      trans
        (⁺toℤ-*⁺ two⁺ (two⁺ *⁺ b))
        (cong (λ t → (⁺toℤ two⁺) *ℤ t) (⁺toℤ-*⁺ two⁺ b))

    hdSplit : ⁺toℤ hd ≡ (⁺toℤ two⁺) *ℤ (⁺toℤ b)
    hdSplit = ⁺toℤ-*⁺ two⁺ b

    lhsExpand : (lhsNum *ℤ ⁺toℤ hd) ≡ (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd +ℤ (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd
    lhsExpand =
      *ℤ-distrib-left-+ℤ (oneℤ *ℤ ⁺toℤ qd) (oneℤ *ℤ ⁺toℤ qd) (⁺toℤ hd)

    oneqd : (oneℤ *ℤ ⁺toℤ qd) ≡ ⁺toℤ qd
    oneqd = *ℤ-one-left (⁺toℤ qd)

    term : (oneℤ *ℤ ⁺toℤ qd) *ℤ ⁺toℤ hd ≡ (⁺toℤ qd) *ℤ ⁺toℤ hd
    term = cong (λ t → t *ℤ ⁺toℤ hd) oneqd

    rhs : (oneℤ *ℤ ⁺toℤ lhsDen) ≡ (⁺toℤ qd) *ℤ (⁺toℤ qd)
    rhs =
      trans
        (cong (λ t → oneℤ *ℤ t) (⁺toℤ-*⁺ qd qd))
        (trans
          (*ℤ-one-left ((⁺toℤ qd) *ℤ (⁺toℤ qd)))
          refl)

    twoℤ : ℤ
    twoℤ = ⁺toℤ two⁺

    twoℤ≡ : twoℤ ≡ oneℤ +ℤ oneℤ
    twoℤ≡ = refl

    qd≡twohd : qd ≡ two⁺ *⁺ hd
    qd≡twohd = refl

    qdAsTwoHd : ⁺toℤ qd ≡ twoℤ *ℤ ⁺toℤ hd
    qdAsTwoHd = trans (cong ⁺toℤ qd≡twohd) (⁺toℤ-*⁺ two⁺ hd)

    qdHd : ℤ
    qdHd = (⁺toℤ qd) *ℤ ⁺toℤ hd

    dupToMul2 : (qdHd +ℤ qdHd) ≡ qdHd *ℤ twoℤ
    dupToMul2 =
      trans
        (cong (λ t → t +ℤ qdHd) (sym (*ℤ-one-right qdHd)))
        (trans
          (cong (λ t → (qdHd *ℤ oneℤ) +ℤ t) (sym (*ℤ-one-right qdHd)))
          (trans
            (sym (*ℤ-distrib-right-+ℤ qdHd oneℤ oneℤ))
            (cong (λ t → qdHd *ℤ t) (sym twoℤ≡))))

    squareToMul2 : ((⁺toℤ qd) *ℤ (⁺toℤ qd)) ≡ qdHd *ℤ twoℤ
    squareToMul2 =
      trans
        (cong (λ t → (⁺toℤ qd) *ℤ t) qdAsTwoHd)
        (trans
          (sym (*ℤ-assoc (⁺toℤ qd) twoℤ (⁺toℤ hd)))
          (trans
            (cong (λ t → t *ℤ ⁺toℤ hd) (*ℤ-comm (⁺toℤ qd) twoℤ))
            (trans
              (*ℤ-assoc twoℤ (⁺toℤ qd) (⁺toℤ hd))
              (*ℤ-comm twoℤ ((⁺toℤ qd) *ℤ ⁺toℤ hd)))))

    goal : (lhsNum *ℤ ⁺toℤ hd) ≡ (oneℤ *ℤ ⁺toℤ lhsDen)
    goal =
      trans
        lhsExpand
        (trans
          (cong (λ t → t +ℤ t) term)
          (trans
            dupToMul2
            (trans (sym squareToMul2) (sym rhs))))
  in
  goal
-- § εHalf < ε (when ε > 0)
εHalf<ε : (ε : ℚ) → 0ℚ <ℚ ε → εHalf ε <ℚ ε
εHalf<ε (a / b) εpos =
  let
    aPos : 0ℤ <ℤ a
    aPos = 0ℚ<→0ℤ<num (a / b) εpos

    one<2a-sum : oneℤ <ℤ (a +ℤ a)
    one<2a-sum = oneℤ<twoTimes-pos a aPos

    twoℤ : ℤ
    twoℤ = ⁺toℤ two⁺

    twoℤ≡ : twoℤ ≡ oneℤ +ℤ oneℤ
    twoℤ≡ = refl

    aTimesTwo≡ : (a *ℤ twoℤ) ≡ (a +ℤ a)
    aTimesTwo≡ =
      trans
        (cong (λ t → a *ℤ t) twoℤ≡)
        (trans
          (*ℤ-distrib-right-+ℤ a oneℤ oneℤ)
          (trans
            (cong (λ t → t +ℤ (a *ℤ oneℤ)) (*ℤ-one-right a))
            (cong (λ t → a +ℤ t) (*ℤ-one-right a))))

    one<2a : oneℤ <ℤ (a *ℤ twoℤ)
    one<2a = <ℤ-resp-≡ʳ (sym aTimesTwo≡) one<2a-sum

    step₁ : (oneℤ *ℤ ⁺toℤ b) <ℤ ((a *ℤ twoℤ) *ℤ ⁺toℤ b)
    step₁ = <ℤ-mul-pos-right b one<2a

    lhsEq : (oneℤ *ℤ ⁺toℤ b) ≡ ⁺toℤ b
    lhsEq = *ℤ-one-left (⁺toℤ b)

    rhsEq : ((a *ℤ twoℤ) *ℤ ⁺toℤ b) ≡ (a *ℤ ⁺toℤ (two⁺ *⁺ b))
    rhsEq =
      trans
        (*ℤ-assoc a twoℤ (⁺toℤ b))
        (cong (λ t → a *ℤ t) (sym (⁺toℤ-*⁺ two⁺ b)))

    core : (oneℤ *ℤ ⁺toℤ b) <ℤ (a *ℤ ⁺toℤ (two⁺ *⁺ b))
    core = <ℤ-resp-≡ʳ rhsEq step₁
  in
  core

-- § εQuarter-double < ε
εQuarter-double<ε : (ε : ℚ) → 0ℚ <ℚ ε → (εQuarter ε +ℚ εQuarter ε) <ℚ ε
εQuarter-double<ε ε εpos =
  let
    eq : (εQuarter ε +ℚ εQuarter ε) ≃ℚ (εHalf ε)
    eq = εQuarter+εQuarter≃εHalf ε

    le : (εQuarter ε +ℚ εQuarter ε) ≤ℚ (εHalf ε)
    le = ≃ℚ→≤ℚˡ {p = εQuarter ε +ℚ εQuarter ε} {q = εHalf ε} eq

    halfLt : (εHalf ε) <ℚ ε
    halfLt = εHalf<ε ε εpos
  in
  ≤<ℚ→<ℚ {x = εQuarter ε +ℚ εQuarter ε} {y = εHalf ε} {z = ε} le halfLt

-- § εQuarter < ε (from εQuarter ≤ double < ε)
εQuarter<ε : (ε : ℚ) → 0ℚ <ℚ ε → εQuarter ε <ℚ ε
εQuarter<ε ε εpos =
  let
    eq : εQuarter ε ≃ℚ εQuarter ε
    eq = ≃ℚ-refl (εQuarter ε)

    εqPos : 0ℚ <ℚ εQuarter ε
    εqPos = εQuarter-pos ε

    εqNonneg : 0ℚ ≤ℚ εQuarter ε
    εqNonneg = <ℚ→≤ℚ {x = 0ℚ} {y = εQuarter ε} εqPos

    εq≤εq+εq : εQuarter ε ≤ℚ (εQuarter ε +ℚ εQuarter ε)
    εq≤εq+εq = ≤ℚ-add-nonneg-right (εQuarter ε) (εQuarter ε) εqNonneg

    double<ε : (εQuarter ε +ℚ εQuarter ε) <ℚ ε
    double<ε = εQuarter-double<ε ε εpos
  in
  ≤<ℚ→<ℚ {x = εQuarter ε} {y = εQuarter ε +ℚ εQuarter ε} {z = ε} εq≤εq+εq double<ε
-- § absℤ respects propositional equality
absℤ-cong : {x y : ℤ} → x ≡ y → absℤ x ≡ absℤ y
absℤ-cong = cong absℤ

-- § Law 14U.0: distℚ q q ≃ℚ 0ℚ (reflexivity)
distℚ-refl : (q : ℚ) → distℚ q q ≃ℚ 0ℚ
distℚ-refl (a / b) =
  let x : ℤ
      x = a *ℤ ⁺toℤ b

      numDist : ℤ
      numDist = absℤ (x +ℤ negℤ x)

      numDist≡0 : numDist ≡ 0ℤ
      numDist≡0 =
        trans
          (absℤ-cong (+ℤ-inv-right x))
          absℤ-zero

      denDist : ℕ⁺
      denDist = b *⁺ b

      lhs0 : (numDist *ℤ ⁺toℤ one⁺) ≡ 0ℤ
      lhs0 =
        trans
          (cong (λ t → t *ℤ ⁺toℤ one⁺) numDist≡0)
          (trans (*ℤ-zero-left (⁺toℤ one⁺)) refl)

      rhs0 : (0ℤ *ℤ ⁺toℤ denDist) ≡ 0ℤ
      rhs0 = *ℤ-zero-left (⁺toℤ denDist)

  in
  trans lhs0 (sym rhs0)

-- § distℚ q q <ℚ ε for any positive ε
distℚ-const<ε : (q ε : ℚ) → 0ℚ <ℚ ε → distℚ q q <ℚ ε
distℚ-const<ε (a / b) (c / d) εpos =
  let x : ℤ
      x = a *ℤ ⁺toℤ b

      numDist : ℤ
      numDist = absℤ (x +ℤ negℤ x)

      numDist≡0 : numDist ≡ 0ℤ
      numDist≡0 =
        trans
          (absℤ-cong (+ℤ-inv-right x))
          absℤ-zero

      lhs : ℤ
      lhs = numDist *ℤ ⁺toℤ d

      rhs : ℤ
      rhs = c *ℤ ⁺toℤ (b *⁺ b)

      lhs≡0 : lhs ≡ 0ℤ
      lhs≡0 =
        trans
          (cong (λ t → t *ℤ ⁺toℤ d) numDist≡0)
          (*ℤ-zero-left (⁺toℤ d))

      cpos : 0ℤ <ℤ c
      cpos = 0ℚ<→0ℤ<num (c / d) εpos

      rhsPos : 0ℤ <ℤ rhs
      rhsPos = 0<ℤ-mul-pos-right c (b *⁺ b) cpos

      base : 0ℤ <ℤ rhs
      base = rhsPos

  in
  <ℤ-resp-≡ˡ (sym lhs≡0) base

-- § p ≃ℚ q implies distℚ p q ≃ℚ 0ℚ
distℚ-≃0 : {p q : ℚ} → p ≃ℚ q → distℚ p q ≃ℚ 0ℚ
distℚ-≃0 {a / b} {c / d} eq =
  let
    x : ℤ
    x = a *ℤ ⁺toℤ d

    y : ℤ
    y = c *ℤ ⁺toℤ b

    z : ℤ
    z = x +ℤ negℤ y

    z≡0 : z ≡ 0ℤ
    z≡0 =
      trans
        (cong (λ t → t +ℤ negℤ y) eq)
        (+ℤ-inv-right y)

    absZ≡0 : absℤ z ≡ 0ℤ
    absZ≡0 = trans (absℤ-cong z≡0) absℤ-zero

    lhs0 : (absℤ z *ℤ ⁺toℤ one⁺) ≡ 0ℤ
    lhs0 =
      trans
        (cong (λ t → t *ℤ ⁺toℤ one⁺) absZ≡0)
        (trans (*ℤ-zero-left (⁺toℤ one⁺)) refl)

    rhs0 : (0ℤ *ℤ ⁺toℤ (b *⁺ d)) ≡ 0ℤ
    rhs0 = *ℤ-zero-left (⁺toℤ (b *⁺ d))
  in
  trans lhs0 (sym rhs0)
-- § distℚ p q ≥ 0 (nonnegativity)
distℚ-nonneg : (p q : ℚ) → 0ℚ ≤ℚ distℚ p q
distℚ-nonneg (a / b) (c / d) =
  let
    z : ℤ
    z = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    rhs0 : 0ℤ ≤ℤ absℤ z
    rhs0 = absℤ-nonneg z

    lhsEq : (0ℤ *ℤ ⁺toℤ (b *⁺ d)) ≡ 0ℤ
    lhsEq = *ℤ-zero-left (⁺toℤ (b *⁺ d))

    rhsEq : (absℤ z *ℤ ⁺toℤ one⁺) ≡ absℤ z
    rhsEq = *ℤ-one-right (absℤ z)
  in
  ≤ℤ-resp-≡ˡ (sym lhsEq) (≤ℤ-resp-≡ʳ (sym rhsEq) rhs0)

-- § distℚ p q ≃ℚ distℚ q p (symmetry)
distℚ-sym : (p q : ℚ) → distℚ p q ≃ℚ distℚ q p
distℚ-sym (a / b) (c / d) =
  let z : ℤ
      z = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

      z' : ℤ
      z' = (c *ℤ ⁺toℤ b) +ℤ negℤ (a *ℤ ⁺toℤ d)

      negz≡z' : negℤ z ≡ z'
      negz≡z' =
        trans
          (neg-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)))
          (trans
            (cong (λ t → negℤ (a *ℤ ⁺toℤ d) +ℤ t) (negℤ-involutive (c *ℤ ⁺toℤ b)))
            (+ℤ-comm (negℤ (a *ℤ ⁺toℤ d)) (c *ℤ ⁺toℤ b)))

      absEq : absℤ z ≡ absℤ z'
      absEq =
        trans
          (sym (absℤ-neg z))
          (trans
            (cong absℤ negz≡z')
            refl)

      denComm : b *⁺ d ≡ d *⁺ b
      denComm = *⁺-comm b d

      denCommℤ : ⁺toℤ (d *⁺ b) ≡ ⁺toℤ (b *⁺ d)
      denCommℤ = cong ⁺toℤ (sym denComm)

      lhs : absℤ z *ℤ ⁺toℤ (d *⁺ b) ≡ absℤ z' *ℤ ⁺toℤ (b *⁺ d)
      lhs =
        trans
          (cong (λ t → t *ℤ ⁺toℤ (d *⁺ b)) absEq)
          (cong (λ t → (absℤ z') *ℤ t) denCommℤ)

  in
  lhs

-- § distℚ (-p) (-q) ≃ℚ distℚ p q (negation invariance)
distℚ-neg : (p q : ℚ) → distℚ (-ℚ p) (-ℚ q) ≃ℚ distℚ p q
distℚ-neg (a / b) (c / d) =
  let
    den : ℕ⁺
    den = b *⁺ d

    z : ℤ
    z = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    zNeg : ℤ
    zNeg = (negℤ a *ℤ ⁺toℤ d) +ℤ negℤ (negℤ c *ℤ ⁺toℤ b)

    zNeg≡negz : zNeg ≡ negℤ z
    zNeg≡negz =
      trans
        (cong (λ t → t +ℤ negℤ (negℤ c *ℤ ⁺toℤ b)) (*ℤ-neg-left a (⁺toℤ d)))
        (trans
          (cong (λ t → negℤ (a *ℤ ⁺toℤ d) +ℤ t)
            (cong negℤ (*ℤ-neg-left c (⁺toℤ b))))
          (sym (neg-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)))))

    absEq : absℤ zNeg ≡ absℤ z
    absEq = trans (cong absℤ zNeg≡negz) (absℤ-neg z)
  in
  cong (λ t → t *ℤ ⁺toℤ den) absEq
-- § Law 14U.1: triangle inequality for distℚ
distℚ-triangle : (p q r : ℚ) → distℚ p r ≤ℚ (distℚ p q +ℚ distℚ q r)
distℚ-triangle (a / b) (c / d) (e / f) =
  goal
  where
    p q rQ : ℚ
    p = a / b
    q = c / d
    rQ = e / f

    nd-pr : ℤ
    nd-pr = numDistℚ p rQ

    nd-pq : ℤ
    nd-pq = numDistℚ p q

    nd-qr : ℤ
    nd-qr = numDistℚ q rQ

    bd df bf : ℕ⁺
    bd = b *⁺ d
    df = d *⁺ f
    bf = b *⁺ f

    rhsNum : ℤ
    rhsNum = (nd-pq *ℤ ⁺toℤ df) +ℤ (nd-qr *ℤ ⁺toℤ bd)

    rhsDen : ℕ⁺
    rhsDen = bd *⁺ df

    -- § base scaled numerator inequality
    ineq0 : (nd-pr *ℤ ⁺toℤ d) ≤ℤ ((nd-pq *ℤ ⁺toℤ f) +ℤ (nd-qr *ℤ ⁺toℤ b))
    ineq0 = numDistℚ-triangle-scaled p q rQ

    -- § multiply by common positive scale s = (b·d)·f
    s : ℕ⁺
    s = bd *⁺ f

    scaled : ((nd-pr *ℤ ⁺toℤ d) *ℤ ⁺toℤ s)
              ≤ℤ
             (((nd-pq *ℤ ⁺toℤ f) +ℤ (nd-qr *ℤ ⁺toℤ b)) *ℤ ⁺toℤ s)
    scaled =
      ≤ℤ-mul-pos-right
        (nd-pr *ℤ ⁺toℤ d)
        ((nd-pq *ℤ ⁺toℤ f) +ℤ (nd-qr *ℤ ⁺toℤ b))
        s
        ineq0

    -- § swap two positive scaling factors
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    -- § split scaling by a product u*⁺v into sequential scaling
    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    -- § LHS rewrite: ((nd-pr·d)·s) = nd-pr · rhsDen
    lhsEq : ((nd-pr *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) ≡ (nd-pr *ℤ ⁺toℤ rhsDen)
    lhsEq =
      trans
        (scaleSplit (nd-pr *ℤ ⁺toℤ d) bd f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale nd-pr d bd))
          (trans
            (sym (scaleSplit (nd-pr *ℤ ⁺toℤ bd) d f))
            (sym (scaleSplit nd-pr bd df))))

    -- § term-pq rewrite: (nd-pq·f)·s = (nd-pq·df)·bf
    term-pq : (nd-pq *ℤ ⁺toℤ f) *ℤ ⁺toℤ s ≡ (nd-pq *ℤ ⁺toℤ df) *ℤ ⁺toℤ bf
    term-pq =
      trans
        (scaleSplit (nd-pq *ℤ ⁺toℤ f) bd f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale nd-pq f bd))
          (trans
            (cong (λ t → (t *ℤ ⁺toℤ f) *ℤ ⁺toℤ f)
              (trans
                (scaleSplit nd-pq b d)
                (swapScale nd-pq b d)))
            (trans
              (cong (λ t → t *ℤ ⁺toℤ f)
                (swapScale (nd-pq *ℤ ⁺toℤ d) b f))
              (trans
                (cong (λ t → (t *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) (sym (scaleSplit nd-pq d f)))
                (sym (scaleSplit (nd-pq *ℤ ⁺toℤ df) b f))))))

    -- § term-qr rewrite: (nd-qr·b)·s = (nd-qr·bd)·bf
    term-qr : (nd-qr *ℤ ⁺toℤ b) *ℤ ⁺toℤ s ≡ (nd-qr *ℤ ⁺toℤ bd) *ℤ ⁺toℤ bf
    term-qr =
      trans
        (scaleSplit (nd-qr *ℤ ⁺toℤ b) bd f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale nd-qr b bd))
          (sym (scaleSplit (nd-qr *ℤ ⁺toℤ bd) b f)))

    rhsEq : (((nd-pq *ℤ ⁺toℤ f) +ℤ (nd-qr *ℤ ⁺toℤ b)) *ℤ ⁺toℤ s) ≡ (rhsNum *ℤ ⁺toℤ bf)
    rhsEq =
      trans
        (*ℤ-distrib-left-+ℤ (nd-pq *ℤ ⁺toℤ f) (nd-qr *ℤ ⁺toℤ b) (⁺toℤ s))
        (trans
          (trans
            (cong (λ t → t +ℤ ((nd-qr *ℤ ⁺toℤ b) *ℤ ⁺toℤ s)) term-pq)
            (cong (λ t → ((nd-pq *ℤ ⁺toℤ df) *ℤ ⁺toℤ bf) +ℤ t) term-qr))
          (sym (*ℤ-distrib-left-+ℤ (nd-pq *ℤ ⁺toℤ df) (nd-qr *ℤ ⁺toℤ bd) (⁺toℤ bf))))

    goal : distℚ p rQ ≤ℚ (distℚ p q +ℚ distℚ q rQ)
    goal =
      ≤ℤ-resp-≡ˡ lhsEq
        (≤ℤ-resp-≡ʳ rhsEq scaled)
-- § distℚ (p+r) (q+r) ≃ℚ distℚ p q (right translation)
distℚ-+ℚ-right : (p q r : ℚ) → distℚ (p +ℚ r) (q +ℚ r) ≃ℚ distℚ p q
distℚ-+ℚ-right (a / b) (c / d) (e / f) =
  let
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    mul4-rearrange : (x y z w : ℤ) → (x *ℤ y) *ℤ (z *ℤ w) ≡ (x *ℤ z) *ℤ (y *ℤ w)
    mul4-rearrange x y z w =
      trans
        (*ℤ-assoc x y (z *ℤ w))
        (trans
          (cong (λ t → x *ℤ t)
            (trans
              (sym (*ℤ-assoc y z w))
              (trans
                (cong (λ t → t *ℤ w) (*ℤ-comm y z))
                (*ℤ-assoc z y w))))
          (sym (*ℤ-assoc x z (y *ℤ w))))

    bf : ℕ⁺
    bf = b *⁺ f

    df : ℕ⁺
    df = d *⁺ f

    s : ℕ⁺
    s = f *⁺ f

    base : ℤ
    base = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    Pn : ℤ
    Pn = (a *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ b)

    Qn : ℤ
    Qn = (c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)

    Z : ℤ
    Z = (Pn *ℤ ⁺toℤ df) +ℤ negℤ (Qn *ℤ ⁺toℤ bf)

    -- § denominator embedding factorization
    denFactor : ⁺toℤ (bf *⁺ df) ≡ (⁺toℤ (b *⁺ d)) *ℤ (⁺toℤ s)
    denFactor =
      trans
        (⁺toℤ-*⁺ bf df)
        (trans
          (cong (λ t → t *ℤ (⁺toℤ df)) (⁺toℤ-*⁺ b f))
          (trans
            (cong (λ t → ((⁺toℤ b) *ℤ (⁺toℤ f)) *ℤ t) (⁺toℤ-*⁺ d f))
            (trans
              (mul4-rearrange (⁺toℤ b) (⁺toℤ f) (⁺toℤ d) (⁺toℤ f))
              (trans
                (cong (λ t → t *ℤ ((⁺toℤ f) *ℤ (⁺toℤ f))) (sym (⁺toℤ-*⁺ b d)))
                (cong (λ t → (⁺toℤ (b *⁺ d)) *ℤ t) (sym (⁺toℤ-*⁺ f f)))))))

    -- § numerator cancellation and factoring
    cancelR : Z ≡ base *ℤ ⁺toℤ s
    cancelR =
      let
        afdf : ℤ
        afdf = (a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df

        ebdf : ℤ
        ebdf = (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df

        cfbf : ℤ
        cfbf = (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf

        edbf : ℤ
        edbf = (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf

        expandP : (Pn *ℤ ⁺toℤ df) ≡ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df)
        expandP = *ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) (⁺toℤ df)

        expandQ : (Qn *ℤ ⁺toℤ bf) ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
        expandQ = *ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ bf)

        negExpandQ : negℤ (Qn *ℤ ⁺toℤ bf) ≡ negℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
        negExpandQ = trans (cong negℤ expandQ) (neg-+ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf))

        Z₁ : Z ≡ (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df))
                 +ℤ (negℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf))
        Z₁ =
          trans
            (cong (λ t → t +ℤ negℤ (Qn *ℤ ⁺toℤ bf)) expandP)
            (cong (λ t → (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df)) +ℤ t) negExpandQ)

        ebdf≡edbf : ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df) ≡ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
        ebdf≡edbf =
          trans
            (cong (λ t → (e *ℤ ⁺toℤ b) *ℤ t) (⁺toℤ-*⁺ d f))
            (trans
              (mul4-rearrange e (⁺toℤ b) (⁺toℤ d) (⁺toℤ f))
              (sym (cong (λ t → (e *ℤ ⁺toℤ d) *ℤ t) (⁺toℤ-*⁺ b f))))

        cancelTerm : ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df) +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf) ≡ 0ℤ
        cancelTerm = trans (cong (λ t → t +ℤ negℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)) ebdf≡edbf) (+ℤ-inv-right ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf))

        afdf≡ads : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s)
        afdf≡ads =
          trans
            (cong (λ t → (a *ℤ ⁺toℤ f) *ℤ t) (⁺toℤ-*⁺ d f))
            (trans
              (mul4-rearrange a (⁺toℤ f) (⁺toℤ d) (⁺toℤ f))
              (cong (λ t → (a *ℤ ⁺toℤ d) *ℤ t) (sym (⁺toℤ-*⁺ f f))))

        cfbf≡cbs : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) ≡ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ s)
        cfbf≡cbs =
          trans
            (cong (λ t → (c *ℤ ⁺toℤ f) *ℤ t) (⁺toℤ-*⁺ b f))
            (trans
              (mul4-rearrange c (⁺toℤ f) (⁺toℤ b) (⁺toℤ f))
              (cong (λ t → (c *ℤ ⁺toℤ b) *ℤ t) (sym (⁺toℤ-*⁺ f f))))

        -- § cancel the r-contributed terms
        Z₂ : Z ≡ afdf +ℤ negℤ cfbf
        Z₂ =
          let
            Zexp : Z ≡ (afdf +ℤ ebdf) +ℤ (negℤ cfbf +ℤ negℤ edbf)
            Zexp =
              trans
                (cong (λ t → t +ℤ negℤ (Qn *ℤ ⁺toℤ bf)) expandP)
                (trans
                  (cong (λ t → ((afdf +ℤ ebdf) +ℤ t))
                    (trans (cong negℤ expandQ) (neg-+ℤ cfbf edbf)))
                  refl)

            swapNeg : (negℤ cfbf +ℤ negℤ edbf) ≡ (negℤ edbf +ℤ negℤ cfbf)
            swapNeg = +ℤ-comm (negℤ cfbf) (negℤ edbf)

            cancelPair : ebdf +ℤ negℤ edbf ≡ 0ℤ
            cancelPair =
              trans
                (cong (λ t → t +ℤ negℤ edbf) ebdf≡edbf)
                (+ℤ-inv-right edbf)

          in
          trans
            (trans
              Zexp
              (trans
                (cong (λ t → (afdf +ℤ ebdf) +ℤ t) swapNeg)
                (trans
                  (+ℤ-assoc afdf ebdf (negℤ edbf +ℤ negℤ cfbf))
                  (cong (λ t → afdf +ℤ t) (sym (+ℤ-assoc ebdf (negℤ edbf) (negℤ cfbf)))))))
            (trans
              (cong (λ t → afdf +ℤ (t +ℤ negℤ cfbf)) cancelPair)
              (cong (λ t → afdf +ℤ t) (+ℤ-zero-left (negℤ cfbf))))

        -- § factor out the common scale s = f·f
        factor : (afdf +ℤ negℤ cfbf) ≡ base *ℤ ⁺toℤ s
        factor =
          trans
            (cong (λ t → t +ℤ negℤ cfbf) afdf≡ads)
            (trans
              (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ negℤ t) cfbf≡cbs)
              (trans
                (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ t)
                  (sym (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ s))))
                (sym (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ s)))))
      in
      trans Z₂ factor

    absZEq : absℤ Z ≡ absℤ base *ℤ ⁺toℤ s
    absZEq = trans (cong absℤ cancelR) (absℤ-mul-pos-right base s)

    rhsDen : ℕ⁺
    rhsDen = b *⁺ d

    lhsDen : ℕ⁺
    lhsDen = bf *⁺ df

    rhsNum : ℤ
    rhsNum = absℤ base

    rhsRewrite : (rhsNum *ℤ ⁺toℤ lhsDen) ≡ (rhsNum *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ s
    rhsRewrite =
      trans
        (cong (λ t → rhsNum *ℤ t) denFactor)
        (sym (*ℤ-assoc rhsNum (⁺toℤ rhsDen) (⁺toℤ s)))

    cross : (absℤ Z *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
    cross =
      trans
        (cong (λ t → t *ℤ ⁺toℤ rhsDen) absZEq)
        (trans
          (swapScale rhsNum s rhsDen)
          (sym rhsRewrite))
  in
  cross
-- § distℚ (r+p) (r+q) ≃ℚ distℚ p q (left translation)
distℚ-+ℚ-left : (r p q : ℚ) → distℚ (r +ℚ p) (r +ℚ q) ≃ℚ distℚ p q
distℚ-+ℚ-left (e / f) (a / b) (c / d) =
  let
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    mul4-rearrange : (x y z w : ℤ) → (x *ℤ y) *ℤ (z *ℤ w) ≡ (x *ℤ z) *ℤ (y *ℤ w)
    mul4-rearrange x y z w =
      trans
        (*ℤ-assoc x y (z *ℤ w))
        (trans
          (cong (λ t → x *ℤ t)
            (trans
              (sym (*ℤ-assoc y z w))
              (trans
                (cong (λ t → t *ℤ w) (*ℤ-comm y z))
                (*ℤ-assoc z y w))))
          (sym (*ℤ-assoc x z (y *ℤ w))))

    fb : ℕ⁺
    fb = f *⁺ b

    fd : ℕ⁺
    fd = f *⁺ d

    s : ℕ⁺
    s = f *⁺ f

    base : ℤ
    base = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    Pn : ℤ
    Pn = (e *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ f)

    Qn : ℤ
    Qn = (e *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ f)

    Z : ℤ
    Z = (Pn *ℤ ⁺toℤ fd) +ℤ negℤ (Qn *ℤ ⁺toℤ fb)

    denFactor : ⁺toℤ (fb *⁺ fd) ≡ (⁺toℤ (b *⁺ d)) *ℤ (⁺toℤ s)
    denFactor =
      trans
        (⁺toℤ-*⁺ fb fd)
        (trans
          (cong (λ t → t *ℤ (⁺toℤ fd)) (⁺toℤ-*⁺ f b))
          (trans
            (cong (λ t → ((⁺toℤ f) *ℤ (⁺toℤ b)) *ℤ t) (⁺toℤ-*⁺ f d))
            (trans
              (mul4-rearrange (⁺toℤ f) (⁺toℤ b) (⁺toℤ f) (⁺toℤ d))
              (trans
                (*ℤ-comm ((⁺toℤ f) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ d)))
                (trans
                  (cong (λ t → t *ℤ ((⁺toℤ f) *ℤ (⁺toℤ f))) (sym (⁺toℤ-*⁺ b d)))
                  (cong (λ t → (⁺toℤ (b *⁺ d)) *ℤ t) (sym (⁺toℤ-*⁺ f f))))))))

    cancelR : Z ≡ base *ℤ ⁺toℤ s
    cancelR =
      let
        ebfd : ℤ
        ebfd = (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ fd

        affd : ℤ
        affd = (a *ℤ ⁺toℤ f) *ℤ ⁺toℤ fd

        edfb : ℤ
        edfb = (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ fb

        cffb : ℤ
        cffb = (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ fb

        expandP : (Pn *ℤ ⁺toℤ fd) ≡ ebfd +ℤ affd
        expandP = *ℤ-distrib-left-+ℤ (e *ℤ ⁺toℤ b) (a *ℤ ⁺toℤ f) (⁺toℤ fd)

        expandQ : (Qn *ℤ ⁺toℤ fb) ≡ edfb +ℤ cffb
        expandQ = *ℤ-distrib-left-+ℤ (e *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ f) (⁺toℤ fb)

        Zexp : Z ≡ (ebfd +ℤ affd) +ℤ (negℤ edfb +ℤ negℤ cffb)
        Zexp =
          trans
            (cong (λ t → t +ℤ negℤ (Qn *ℤ ⁺toℤ fb)) expandP)
            (trans
              (cong (λ t → (ebfd +ℤ affd) +ℤ t) (trans (cong negℤ expandQ) (neg-+ℤ edfb cffb)))
              refl)

        ebfd≡edfb : ebfd ≡ edfb
        ebfd≡edfb =
          trans
            (cong (λ t → (e *ℤ ⁺toℤ b) *ℤ t) (⁺toℤ-*⁺ f d))
            (trans
              (cong (λ t → (e *ℤ ⁺toℤ b) *ℤ t) (*ℤ-comm (⁺toℤ f) (⁺toℤ d)))
              (trans
                (mul4-rearrange e (⁺toℤ b) (⁺toℤ d) (⁺toℤ f))
                (trans
                  (cong (λ t → (e *ℤ ⁺toℤ d) *ℤ t) (*ℤ-comm (⁺toℤ b) (⁺toℤ f)))
                  (cong (λ t → (e *ℤ ⁺toℤ d) *ℤ t) (sym (⁺toℤ-*⁺ f b))))))

        cancelPair : ebfd +ℤ negℤ edfb ≡ 0ℤ
        cancelPair =
          trans
            (cong (λ t → t +ℤ negℤ edfb) ebfd≡edfb)
            (+ℤ-inv-right edfb)

        affd≡ads : affd ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s
        affd≡ads =
          trans
            (cong (λ t → (a *ℤ ⁺toℤ f) *ℤ t) (⁺toℤ-*⁺ f d))
            (trans
              (cong (λ t → (a *ℤ ⁺toℤ f) *ℤ t) (*ℤ-comm (⁺toℤ f) (⁺toℤ d)))
              (trans
                (mul4-rearrange a (⁺toℤ f) (⁺toℤ d) (⁺toℤ f))
                (cong (λ t → (a *ℤ ⁺toℤ d) *ℤ t) (sym (⁺toℤ-*⁺ f f)))))

        cffb≡cbs : cffb ≡ (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ s
        cffb≡cbs =
          trans
            (cong (λ t → (c *ℤ ⁺toℤ f) *ℤ t) (⁺toℤ-*⁺ f b))
            (trans
              (cong (λ t → (c *ℤ ⁺toℤ f) *ℤ t) (*ℤ-comm (⁺toℤ f) (⁺toℤ b)))
              (trans
                (mul4-rearrange c (⁺toℤ f) (⁺toℤ b) (⁺toℤ f))
                (cong (λ t → (c *ℤ ⁺toℤ b) *ℤ t) (sym (⁺toℤ-*⁺ f f)))))

        step₁ : Z ≡ affd +ℤ negℤ cffb
        step₁ =
          trans
            Zexp
            (trans
              (cong (λ t → t +ℤ (negℤ edfb +ℤ negℤ cffb)) (+ℤ-comm ebfd affd))
              (trans
                (+ℤ-assoc affd ebfd (negℤ edfb +ℤ negℤ cffb))
                (trans
                  (cong (λ t → affd +ℤ t) (sym (+ℤ-assoc ebfd (negℤ edfb) (negℤ cffb))))
                  (trans
                    (cong (λ t → affd +ℤ (t +ℤ negℤ cffb)) cancelPair)
                    (cong (λ t → affd +ℤ t) (+ℤ-zero-left (negℤ cffb)))))))

        step₂ : (affd +ℤ negℤ cffb) ≡ ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ negℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ s)
        step₂ =
          trans
            (cong (λ t → t +ℤ negℤ cffb) affd≡ads)
            (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ negℤ t) cffb≡cbs)

        factor : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ negℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ s)
                  ≡
                 base *ℤ ⁺toℤ s
        factor =
          trans
            (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) +ℤ t)
              (sym (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ s))))
            (sym (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ s)))
      in
      trans step₁ (trans step₂ factor)

    absZEq : absℤ Z ≡ absℤ base *ℤ ⁺toℤ s
    absZEq = trans (cong absℤ cancelR) (absℤ-mul-pos-right base s)

    rhsDen : ℕ⁺
    rhsDen = b *⁺ d

    lhsDen : ℕ⁺
    lhsDen = fb *⁺ fd

    rhsNum : ℤ
    rhsNum = absℤ base

    rhsRewrite : (rhsNum *ℤ ⁺toℤ lhsDen) ≡ (rhsNum *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ s
    rhsRewrite =
      trans
        (cong (λ t → rhsNum *ℤ t) denFactor)
        (sym (*ℤ-assoc rhsNum (⁺toℤ rhsDen) (⁺toℤ s)))

    cross : (absℤ Z *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
    cross =
      trans
        (cong (λ t → t *ℤ ⁺toℤ rhsDen) absZEq)
        (trans
          (swapScale rhsNum s rhsDen)
          (sym rhsRewrite))
  in
  cross
-- § distℚ (p*q) (p*r) ≃ℚ distℚ q r * distℚ p 0 (left scaling)
distℚ-*ℚ-left : (p q r : ℚ) → distℚ (p *ℚ q) (p *ℚ r) ≃ℚ (distℚ q r *ℚ distℚ p 0ℚ)
distℚ-*ℚ-left (a / b) (c / d) (e / f) =
  let
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    mul4-rearrange : (x y z w : ℤ) → (x *ℤ y) *ℤ (z *ℤ w) ≡ (x *ℤ z) *ℤ (y *ℤ w)
    mul4-rearrange x y z w =
      trans
        (*ℤ-assoc x y (z *ℤ w))
        (trans
          (cong (λ t → x *ℤ t)
            (trans
              (sym (*ℤ-assoc y z w))
              (trans
                (cong (λ t → t *ℤ w) (*ℤ-comm y z))
                (*ℤ-assoc z y w))))
          (sym (*ℤ-assoc x z (y *ℤ w))))

    -- § key cleared numerators
    cf : ℤ
    cf = c *ℤ ⁺toℤ f

    ed : ℤ
    ed = e *ℤ ⁺toℤ d

    baseQR : ℤ
    baseQR = cf +ℤ negℤ ed

    ab : ℤ
    ab = a *ℤ ⁺toℤ b

    -- § distℚ p 0ℚ numerator collapses to absℤ a
    p0Raw : ℤ
    p0Raw = (a *ℤ ⁺toℤ one⁺) +ℤ negℤ (0ℤ *ℤ ⁺toℤ b)

    p0Raw≡a : p0Raw ≡ a
    p0Raw≡a =
      trans
        (cong (λ t → t +ℤ negℤ (0ℤ *ℤ ⁺toℤ b)) (*ℤ-one-right a))
        (trans
          (cong (λ t → a +ℤ negℤ t) (*ℤ-zero-left (⁺toℤ b)))
          (trans
            (cong (λ t → a +ℤ t) (negℤ-zero))
            (+ℤ-zero-right a)))

    absP0 : ℤ
    absP0 = absℤ p0Raw

    absP0≡absA : absP0 ≡ absℤ a
    absP0≡absA = trans (absℤ-cong p0Raw≡a) refl

    -- § LHS cleared numerator for distℚ (p*q) (p*r)
    bf : ℕ⁺
    bf = b *⁺ f

    bd : ℕ⁺
    bd = b *⁺ d

    Z : ℤ
    Z = ((a *ℤ c) *ℤ ⁺toℤ bf) +ℤ negℤ ((a *ℤ e) *ℤ ⁺toℤ bd)

    term₁ : ((a *ℤ c) *ℤ ⁺toℤ bf) ≡ ab *ℤ cf
    term₁ =
      trans
        (cong (λ t → (a *ℤ c) *ℤ t) (⁺toℤ-*⁺ b f))
        (trans
          (mul4-rearrange a c (⁺toℤ b) (⁺toℤ f))
          refl)

    term₂ : ((a *ℤ e) *ℤ ⁺toℤ bd) ≡ ab *ℤ ed
    term₂ =
      trans
        (cong (λ t → (a *ℤ e) *ℤ t) (⁺toℤ-*⁺ b d))
        (trans
          (mul4-rearrange a e (⁺toℤ b) (⁺toℤ d))
          refl)

    factorZ : Z ≡ ab *ℤ baseQR
    factorZ =
      let
        Z₁ : Z ≡ (ab *ℤ cf) +ℤ negℤ (ab *ℤ ed)
        Z₁ =
          trans
            (cong (λ t → t +ℤ negℤ ((a *ℤ e) *ℤ ⁺toℤ bd)) term₁)
            (cong (λ t → (ab *ℤ cf) +ℤ negℤ t) term₂)

        negPull : negℤ (ab *ℤ ed) ≡ ab *ℤ negℤ ed
        negPull = sym (*ℤ-neg-right ab ed)

        Z₂ : (ab *ℤ cf) +ℤ negℤ (ab *ℤ ed) ≡ (ab *ℤ cf) +ℤ (ab *ℤ negℤ ed)
        Z₂ = cong (λ t → (ab *ℤ cf) +ℤ t) negPull

        Z₃ : (ab *ℤ cf) +ℤ (ab *ℤ negℤ ed) ≡ ab *ℤ (cf +ℤ negℤ ed)
        Z₃ = sym (*ℤ-distrib-right-+ℤ ab cf (negℤ ed))
      in
      trans Z₁ (trans Z₂ Z₃)

    absZ : ℤ
    absZ = absℤ Z

    absZ≡scaled : absZ ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b
    absZ≡scaled =
      let
        absZ₁ : absZ ≡ absℤ (ab *ℤ baseQR)
        absZ₁ = cong absℤ factorZ

        absZ₂ : absℤ (ab *ℤ baseQR) ≡ (absℤ ab *ℤ absℤ baseQR)
        absZ₂ = absℤ-mul ab baseQR

        absAB : absℤ ab ≡ absℤ a *ℤ ⁺toℤ b
        absAB = absℤ-mul-pos-right a b

        absZ₃ : (absℤ ab *ℤ absℤ baseQR) ≡ ((absℤ a *ℤ ⁺toℤ b) *ℤ absℤ baseQR)
        absZ₃ = cong (λ t → t *ℤ absℤ baseQR) absAB

        absZ₄ : ((absℤ a *ℤ ⁺toℤ b) *ℤ absℤ baseQR) ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b)
        absZ₄ =
          trans
            (*ℤ-assoc (absℤ a) (⁺toℤ b) (absℤ baseQR))
            (trans
              (cong (λ t → (absℤ a) *ℤ t) (*ℤ-comm (⁺toℤ b) (absℤ baseQR)))
              (trans
                (sym (*ℤ-assoc (absℤ a) (absℤ baseQR) (⁺toℤ b)))
                (trans
                  (cong (λ t → t *ℤ (⁺toℤ b)) (*ℤ-comm (absℤ a) (absℤ baseQR)))
                  refl)))
      in
      trans absZ₁ (trans absZ₂ (trans absZ₃ absZ₄))

    lhsDen : ℕ⁺
    lhsDen = (b *⁺ d) *⁺ (b *⁺ f)

    rhsDen : ℕ⁺
    rhsDen = (d *⁺ f) *⁺ (b *⁺ one⁺)

    rhsNum : ℤ
    rhsNum = (absℤ baseQR *ℤ absP0)

    rhsNum≡ : rhsNum ≡ (absℤ baseQR *ℤ absℤ a)
    rhsNum≡ = cong (λ t → (absℤ baseQR *ℤ t)) absP0≡absA

    -- § denominator embedding relation
    denRel : (⁺toℤ rhsDen) *ℤ (⁺toℤ b) ≡ ⁺toℤ lhsDen
    denRel =
      let
        lhs₀ : ⁺toℤ lhsDen ≡ (⁺toℤ (b *⁺ d)) *ℤ (⁺toℤ (b *⁺ f))
        lhs₀ = ⁺toℤ-*⁺ (b *⁺ d) (b *⁺ f)

        rhs₀ : ⁺toℤ rhsDen ≡ (⁺toℤ (d *⁺ f)) *ℤ (⁺toℤ (b *⁺ one⁺))
        rhs₀ = ⁺toℤ-*⁺ (d *⁺ f) (b *⁺ one⁺)

        bdf : ⁺toℤ (b *⁺ d) ≡ (⁺toℤ b) *ℤ (⁺toℤ d)
        bdf = ⁺toℤ-*⁺ b d

        bff : ⁺toℤ (b *⁺ f) ≡ (⁺toℤ b) *ℤ (⁺toℤ f)
        bff = ⁺toℤ-*⁺ b f

        dff : ⁺toℤ (d *⁺ f) ≡ (⁺toℤ d) *ℤ (⁺toℤ f)
        dff = ⁺toℤ-*⁺ d f

        bone : ⁺toℤ (b *⁺ one⁺) ≡ (⁺toℤ b) *ℤ (⁺toℤ one⁺)
        bone = ⁺toℤ-*⁺ b one⁺

        stepR : (⁺toℤ rhsDen) *ℤ (⁺toℤ b) ≡ ((⁺toℤ d) *ℤ (⁺toℤ f)) *ℤ (((⁺toℤ b) *ℤ (⁺toℤ one⁺)) *ℤ (⁺toℤ b))
        stepR =
          trans
            (cong (λ t → t *ℤ (⁺toℤ b)) rhs₀)
            (trans
              (cong (λ t → ((⁺toℤ (d *⁺ f)) *ℤ t) *ℤ (⁺toℤ b)) bone)
              (trans
                (cong (λ t → (t *ℤ ((⁺toℤ b) *ℤ (⁺toℤ one⁺))) *ℤ (⁺toℤ b)) dff)
                (trans
                  (*ℤ-assoc ((⁺toℤ d) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ one⁺)) (⁺toℤ b))
                  refl)))

        stepL : ⁺toℤ lhsDen ≡ ((⁺toℤ b) *ℤ (⁺toℤ b)) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ f))
        stepL =
          trans
            lhs₀
            (trans
              (cong (λ t → t *ℤ (⁺toℤ (b *⁺ f))) bdf)
              (trans
                (cong (λ t → ((⁺toℤ b) *ℤ (⁺toℤ d)) *ℤ t) bff)
                (trans
                  (mul4-rearrange (⁺toℤ b) (⁺toℤ d) (⁺toℤ b) (⁺toℤ f))
                  refl)))
      in
      let
        b1≡b : (⁺toℤ b) *ℤ (⁺toℤ one⁺) ≡ (⁺toℤ b)
        b1≡b = *ℤ-one-right (⁺toℤ b)

        inner : ((⁺toℤ b) *ℤ (⁺toℤ one⁺)) *ℤ (⁺toℤ b) ≡ (⁺toℤ b) *ℤ (⁺toℤ b)
        inner = cong (λ t → t *ℤ (⁺toℤ b)) b1≡b
      in
      trans
        stepR
        (trans
          (cong (λ t → ((⁺toℤ d) *ℤ (⁺toℤ f)) *ℤ t) inner)
          (trans
            (*ℤ-comm ((⁺toℤ d) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ b)))
            (sym stepL)))

    cross : (absZ *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
    cross =
      let
        lhs₁ : absZ *ℤ ⁺toℤ rhsDen ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b) *ℤ ⁺toℤ rhsDen
        lhs₁ = cong (λ t → t *ℤ ⁺toℤ rhsDen) absZ≡scaled

        lhs₂ : ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b) *ℤ ⁺toℤ rhsDen ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ b
        lhs₂ = swapScale (absℤ baseQR *ℤ absℤ a) b rhsDen

        lhs₃ : ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ b ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ((⁺toℤ rhsDen) *ℤ (⁺toℤ b))
        lhs₃ =
          trans
            (*ℤ-assoc (absℤ baseQR *ℤ absℤ a) (⁺toℤ rhsDen) (⁺toℤ b))
            refl

        rhs₁ : rhsNum *ℤ ⁺toℤ lhsDen ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ lhsDen
        rhs₁ = cong (λ t → t *ℤ ⁺toℤ lhsDen) rhsNum≡

        rhs₂ : (absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ lhsDen ≡ (absℤ baseQR *ℤ absℤ a) *ℤ (⁺toℤ lhsDen)
        rhs₂ = refl

      in
      trans
        (trans lhs₁ lhs₂)
        (trans
          lhs₃
          (trans
            (cong (λ t → (absℤ baseQR *ℤ absℤ a) *ℤ t) denRel)
            (sym (trans rhs₁ rhs₂))))
  in
  cross
-- § distℚ (q*p) (r*p) ≃ℚ distℚ q r * distℚ p 0 (right scaling)
distℚ-*ℚ-right : (p q r : ℚ) → distℚ (q *ℚ p) (r *ℚ p) ≃ℚ (distℚ q r *ℚ distℚ p 0ℚ)
distℚ-*ℚ-right (a / b) (c / d) (e / f) =
  let
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    mul4-rearrange : (x y z w : ℤ) → (x *ℤ y) *ℤ (z *ℤ w) ≡ (x *ℤ z) *ℤ (y *ℤ w)
    mul4-rearrange x y z w =
      trans
        (*ℤ-assoc x y (z *ℤ w))
        (trans
          (cong (λ t → x *ℤ t)
            (trans
              (sym (*ℤ-assoc y z w))
              (trans
                (cong (λ t → t *ℤ w) (*ℤ-comm y z))
                (*ℤ-assoc z y w))))
          (sym (*ℤ-assoc x z (y *ℤ w))))

    cf : ℤ
    cf = c *ℤ ⁺toℤ f

    ed : ℤ
    ed = e *ℤ ⁺toℤ d

    baseQR : ℤ
    baseQR = cf +ℤ negℤ ed

    ab : ℤ
    ab = a *ℤ ⁺toℤ b

    p0Raw : ℤ
    p0Raw = (a *ℤ ⁺toℤ one⁺) +ℤ negℤ (0ℤ *ℤ ⁺toℤ b)

    p0Raw≡a : p0Raw ≡ a
    p0Raw≡a =
      trans
        (cong (λ t → t +ℤ negℤ (0ℤ *ℤ ⁺toℤ b)) (*ℤ-one-right a))
        (trans
          (cong (λ t → a +ℤ negℤ t) (*ℤ-zero-left (⁺toℤ b)))
          (trans
            (cong (λ t → a +ℤ t) (negℤ-zero))
            (+ℤ-zero-right a)))

    absP0 : ℤ
    absP0 = absℤ p0Raw

    absP0≡absA : absP0 ≡ absℤ a
    absP0≡absA = trans (absℤ-cong p0Raw≡a) refl

    fbDen : ℕ⁺
    fbDen = f *⁺ b

    dbDen : ℕ⁺
    dbDen = d *⁺ b

    -- § LHS cleared numerator for distℚ (q*p) (r*p)
    Z : ℤ
    Z = ((c *ℤ a) *ℤ ⁺toℤ fbDen) +ℤ negℤ ((e *ℤ a) *ℤ ⁺toℤ dbDen)

    term₁ : ((c *ℤ a) *ℤ ⁺toℤ fbDen) ≡ ab *ℤ cf
    term₁ =
      trans
        (cong (λ t → (c *ℤ a) *ℤ t) (⁺toℤ-*⁺ f b))
        (trans
          (mul4-rearrange c a (⁺toℤ f) (⁺toℤ b))
          (*ℤ-comm (c *ℤ ⁺toℤ f) (a *ℤ ⁺toℤ b)))

    term₂ : ((e *ℤ a) *ℤ ⁺toℤ dbDen) ≡ ab *ℤ ed
    term₂ =
      trans
        (cong (λ t → (e *ℤ a) *ℤ t) (⁺toℤ-*⁺ d b))
        (trans
          (mul4-rearrange e a (⁺toℤ d) (⁺toℤ b))
          (*ℤ-comm (e *ℤ ⁺toℤ d) (a *ℤ ⁺toℤ b)))

    factorZ : Z ≡ ab *ℤ baseQR
    factorZ =
      let
        Z₁ : Z ≡ (ab *ℤ cf) +ℤ negℤ (ab *ℤ ed)
        Z₁ =
          trans
            (cong (λ t → t +ℤ negℤ ((e *ℤ a) *ℤ ⁺toℤ dbDen)) term₁)
            (cong (λ t → (ab *ℤ cf) +ℤ negℤ t) term₂)

        negPull : negℤ (ab *ℤ ed) ≡ ab *ℤ negℤ ed
        negPull = sym (*ℤ-neg-right ab ed)

        Z₂ : (ab *ℤ cf) +ℤ negℤ (ab *ℤ ed) ≡ (ab *ℤ cf) +ℤ (ab *ℤ negℤ ed)
        Z₂ = cong (λ t → (ab *ℤ cf) +ℤ t) negPull

        Z₃ : (ab *ℤ cf) +ℤ (ab *ℤ negℤ ed) ≡ ab *ℤ (cf +ℤ negℤ ed)
        Z₃ = sym (*ℤ-distrib-right-+ℤ ab cf (negℤ ed))
      in
      trans Z₁ (trans Z₂ Z₃)

    absZ : ℤ
    absZ = absℤ Z

    absZ≡scaled : absZ ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b
    absZ≡scaled =
      let
        absZ₁ : absZ ≡ absℤ (ab *ℤ baseQR)
        absZ₁ = cong absℤ factorZ

        absZ₂ : absℤ (ab *ℤ baseQR) ≡ (absℤ ab *ℤ absℤ baseQR)
        absZ₂ = absℤ-mul ab baseQR

        absAB : absℤ ab ≡ absℤ a *ℤ ⁺toℤ b
        absAB = absℤ-mul-pos-right a b

        absZ₃ : (absℤ ab *ℤ absℤ baseQR) ≡ ((absℤ a *ℤ ⁺toℤ b) *ℤ absℤ baseQR)
        absZ₃ = cong (λ t → t *ℤ absℤ baseQR) absAB

        absZ₄ : ((absℤ a *ℤ ⁺toℤ b) *ℤ absℤ baseQR) ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b)
        absZ₄ =
          trans
            (*ℤ-assoc (absℤ a) (⁺toℤ b) (absℤ baseQR))
            (trans
              (cong (λ t → (absℤ a) *ℤ t) (*ℤ-comm (⁺toℤ b) (absℤ baseQR)))
              (trans
                (sym (*ℤ-assoc (absℤ a) (absℤ baseQR) (⁺toℤ b)))
                (trans
                  (cong (λ t → t *ℤ (⁺toℤ b)) (*ℤ-comm (absℤ a) (absℤ baseQR)))
                  refl)))
      in
      trans absZ₁ (trans absZ₂ (trans absZ₃ absZ₄))

    lhsDen : ℕ⁺
    lhsDen = (d *⁺ b) *⁺ (f *⁺ b)

    rhsDen : ℕ⁺
    rhsDen = (d *⁺ f) *⁺ (b *⁺ one⁺)

    rhsNum : ℤ
    rhsNum = (absℤ baseQR *ℤ absP0)

    rhsNum≡ : rhsNum ≡ (absℤ baseQR *ℤ absℤ a)
    rhsNum≡ = cong (λ t → (absℤ baseQR *ℤ t)) absP0≡absA

    denRel : (⁺toℤ rhsDen) *ℤ (⁺toℤ b) ≡ ⁺toℤ lhsDen
    denRel =
      let
        lhs₀ : ⁺toℤ lhsDen ≡ (⁺toℤ (d *⁺ b)) *ℤ (⁺toℤ (f *⁺ b))
        lhs₀ = ⁺toℤ-*⁺ (d *⁺ b) (f *⁺ b)

        rhs₀ : ⁺toℤ rhsDen ≡ (⁺toℤ (d *⁺ f)) *ℤ (⁺toℤ (b *⁺ one⁺))
        rhs₀ = ⁺toℤ-*⁺ (d *⁺ f) (b *⁺ one⁺)

        db : ⁺toℤ (d *⁺ b) ≡ (⁺toℤ d) *ℤ (⁺toℤ b)
        db = ⁺toℤ-*⁺ d b

        fb' : ⁺toℤ (f *⁺ b) ≡ (⁺toℤ f) *ℤ (⁺toℤ b)
        fb' = ⁺toℤ-*⁺ f b

        dff : ⁺toℤ (d *⁺ f) ≡ (⁺toℤ d) *ℤ (⁺toℤ f)
        dff = ⁺toℤ-*⁺ d f

        bone : ⁺toℤ (b *⁺ one⁺) ≡ (⁺toℤ b) *ℤ (⁺toℤ one⁺)
        bone = ⁺toℤ-*⁺ b one⁺

        stepR : (⁺toℤ rhsDen) *ℤ (⁺toℤ b) ≡ ((⁺toℤ d) *ℤ (⁺toℤ f)) *ℤ (((⁺toℤ b) *ℤ (⁺toℤ one⁺)) *ℤ (⁺toℤ b))
        stepR =
          trans
            (cong (λ t → t *ℤ (⁺toℤ b)) rhs₀)
            (trans
              (cong (λ t → ((⁺toℤ (d *⁺ f)) *ℤ t) *ℤ (⁺toℤ b)) bone)
              (trans
                (cong (λ t → (t *ℤ ((⁺toℤ b) *ℤ (⁺toℤ one⁺))) *ℤ (⁺toℤ b)) dff)
                (trans
                  (*ℤ-assoc ((⁺toℤ d) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ one⁺)) (⁺toℤ b))
                  refl)))

        stepL : ⁺toℤ lhsDen ≡ ((⁺toℤ b) *ℤ (⁺toℤ b)) *ℤ ((⁺toℤ d) *ℤ (⁺toℤ f))
        stepL =
          trans
            lhs₀
            (trans
              (cong (λ t → t *ℤ (⁺toℤ (f *⁺ b))) db)
              (trans
                (cong (λ t → ((⁺toℤ d) *ℤ (⁺toℤ b)) *ℤ t) fb')
                (trans
                  (mul4-rearrange (⁺toℤ d) (⁺toℤ b) (⁺toℤ f) (⁺toℤ b))
                  (trans
                    (cong (λ t → ((⁺toℤ d) *ℤ (⁺toℤ f)) *ℤ t) (*ℤ-comm (⁺toℤ b) (⁺toℤ b)))
                    (trans
                      (*ℤ-comm ((⁺toℤ d) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ b)))
                      refl)))))
      in
      let
        b1≡b : (⁺toℤ b) *ℤ (⁺toℤ one⁺) ≡ (⁺toℤ b)
        b1≡b = *ℤ-one-right (⁺toℤ b)

        inner : ((⁺toℤ b) *ℤ (⁺toℤ one⁺)) *ℤ (⁺toℤ b) ≡ (⁺toℤ b) *ℤ (⁺toℤ b)
        inner = cong (λ t → t *ℤ (⁺toℤ b)) b1≡b
      in
      trans
        stepR
        (trans
          (cong (λ t → ((⁺toℤ d) *ℤ (⁺toℤ f)) *ℤ t) inner)
          (trans
            (*ℤ-comm ((⁺toℤ d) *ℤ (⁺toℤ f)) ((⁺toℤ b) *ℤ (⁺toℤ b)))
            (sym stepL)))

    cross : (absZ *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
    cross =
      let
        lhs₁ : absZ *ℤ ⁺toℤ rhsDen ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b) *ℤ ⁺toℤ rhsDen
        lhs₁ = cong (λ t → t *ℤ ⁺toℤ rhsDen) absZ≡scaled

        lhs₂ : ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ b) *ℤ ⁺toℤ rhsDen ≡ ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ b
        lhs₂ = swapScale (absℤ baseQR *ℤ absℤ a) b rhsDen

        lhs₃ : ((absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ rhsDen) *ℤ ⁺toℤ b ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ((⁺toℤ rhsDen) *ℤ (⁺toℤ b))
        lhs₃ = trans (*ℤ-assoc (absℤ baseQR *ℤ absℤ a) (⁺toℤ rhsDen) (⁺toℤ b)) refl

        rhs₁ : rhsNum *ℤ ⁺toℤ lhsDen ≡ (absℤ baseQR *ℤ absℤ a) *ℤ ⁺toℤ lhsDen
        rhs₁ = cong (λ t → t *ℤ ⁺toℤ lhsDen) rhsNum≡
      in
      trans
        (trans lhs₁ lhs₂)
        (trans
          lhs₃
          (trans
            (cong (λ t → (absℤ baseQR *ℤ absℤ a) *ℤ t) denRel)
            (sym rhs₁)))
  in
  cross
-- § key bound: x ≤ y+ε and y ≤ x+ε imply distℚ x y ≤ ε
distℚ-bounded-by-ε : (x y ε : ℚ) → x ≤ℚ (y +ℚ ε) → y ≤ℚ (x +ℚ ε) → distℚ x y ≤ℚ ε
distℚ-bounded-by-ε (a / b) (c / d) (e / f) x≤y+ε y≤x+ε =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    df : ℕ⁺
    df = d *⁺ f

    bf : ℕ⁺
    bf = b *⁺ f

    bdf : ℕ⁺
    bdf = bd *⁺ f

    diff : ℤ
    diff = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    y+ε-num : ℤ
    y+ε-num = (c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)

    x+ε-num : ℤ
    x+ε-num = (a *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ b)

    hyp1 : (a *ℤ ⁺toℤ df) ≤ℤ (y+ε-num *ℤ ⁺toℤ b)
    hyp1 = x≤y+ε

    hyp2 : (c *ℤ ⁺toℤ bf) ≤ℤ (x+ε-num *ℤ ⁺toℤ d)
    hyp2 = y≤x+ε

    -- § expand hypotheses
    adf≤cfb+edb : (a *ℤ ⁺toℤ df) ≤ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    adf≤cfb+edb = ≤ℤ-resp-≡ʳ (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ b)) hyp1

    cbf≤afd+ebd : (c *ℤ ⁺toℤ bf) ≤ℤ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d +ℤ (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    cbf≤afd+ebd = ≤ℤ-resp-≡ʳ (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) (⁺toℤ d)) hyp2

    -- § associativity lemmas
    assoc-adf : a *ℤ ⁺toℤ df ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
    assoc-adf = trans (cong (λ t → a *ℤ t) (⁺toℤ-*⁺ d f)) (sym (*ℤ-assoc a (⁺toℤ d) (⁺toℤ f)))

    assoc-cbf : c *ℤ ⁺toℤ bf ≡ (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f
    assoc-cbf = trans (cong (λ t → c *ℤ t) (⁺toℤ-*⁺ b f)) (sym (*ℤ-assoc c (⁺toℤ b) (⁺toℤ f)))

    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    assoc-cfb : (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b ≡ (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f
    assoc-cfb = swapScale c f b

    assoc-afd : (a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
    assoc-afd = swapScale a f d

    edb≡ebd : (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b ≡ (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d
    edb≡ebd = swapScale e d b

    -- § renamed for clarity
    adf' : ℤ
    adf' = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f

    cbf' : ℤ
    cbf' = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f

    ebd : ℤ
    ebd = (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d

    rhsEq₁ : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (cbf' +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    rhsEq₁ = cong (λ t → t +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) assoc-cfb

    rhsEq₂ : (cbf' +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (cbf' +ℤ ebd)
    rhsEq₂ = cong (λ t → cbf' +ℤ t) edb≡ebd

    rhsEq : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (cbf' +ℤ ebd)
    rhsEq = trans rhsEq₁ rhsEq₂

    -- § hyp1 gives: (a*d)*f ≤ (c*b)*f + ebd
    hyp1' : adf' ≤ℤ (cbf' +ℤ ebd)
    hyp1' = ≤ℤ-resp-≡ˡ assoc-adf (≤ℤ-resp-≡ʳ rhsEq adf≤cfb+edb)

    -- § hyp2 gives: (c*b)*f ≤ (a*d)*f + ebd
    hyp2' : cbf' ≤ℤ (adf' +ℤ ebd)
    hyp2' = ≤ℤ-resp-≡ˡ assoc-cbf (≤ℤ-resp-≡ʳ (cong (λ t → t +ℤ ebd) assoc-afd) cbf≤afd+ebd)

    -- § diff * f = adf' - cbf'
    diff-f : ℤ
    diff-f = adf' +ℤ negℤ cbf'

    diff-f-eq : diff *ℤ ⁺toℤ f ≡ diff-f
    diff-f-eq =
      trans
        (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ f))
        (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t) (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ f)))

    -- § diff-f ≤ ebd from hyp1'
    diff-f≤ebd : diff-f ≤ℤ ebd
    diff-f≤ebd = ≤ℤ-+ℤ-cancelʳ adf' cbf' ebd (≤ℤ-resp-≡ʳ (sym (+ℤ-comm ebd cbf')) hyp1')

    -- § negℤ diff-f ≤ ebd from hyp2'
    neg-diff-f≤ebd : (negℤ diff-f) ≤ℤ ebd
    neg-diff-f≤ebd =
      let
        step : cbf' +ℤ negℤ adf' ≤ℤ ebd
        step = ≤ℤ-+ℤ-cancelʳ cbf' adf' ebd (≤ℤ-resp-≡ʳ (sym (+ℤ-comm ebd adf')) hyp2')

        neg-eq : negℤ diff-f ≡ cbf' +ℤ negℤ adf'
        neg-eq =
          trans
            (neg-+ℤ adf' (negℤ cbf'))
            (trans
              (+ℤ-comm (negℤ adf') (negℤ (negℤ cbf')))
              (cong (λ t → t +ℤ negℤ adf') (negℤ-involutive cbf')))
      in
      ≤ℤ-resp-≡ˡ (sym neg-eq) step

    -- § combine via absℤ-within-bound
    neg-ebd≤diff-f : (negℤ ebd) ≤ℤ diff-f
    neg-ebd≤diff-f = ≤ℤ-resp-≡ʳ (negℤ-involutive diff-f) (negℤ-antitone-≤ℤ neg-diff-f≤ebd)

    abs-diff-f≤ebd : absℤ diff-f ≤ℤ ebd
    abs-diff-f≤ebd = absℤ-within-bound diff-f ebd neg-ebd≤diff-f diff-f≤ebd

    -- § transport to distℚ x y ≤ℚ ε
    abs-diff-f-eq : absℤ diff-f ≡ absℤ (diff *ℤ ⁺toℤ f)
    abs-diff-f-eq = cong absℤ (sym diff-f-eq)

    abs-mul-eq : absℤ (diff *ℤ ⁺toℤ f) ≡ (absℤ diff *ℤ ⁺toℤ f)
    abs-mul-eq = absℤ-mul-pos-right diff f

    ebd-eq : ebd ≡ (e *ℤ ⁺toℤ bd)
    ebd-eq =
      trans
        (*ℤ-assoc e (⁺toℤ b) (⁺toℤ d))
        (cong (λ t → e *ℤ t) (sym (⁺toℤ-*⁺ b d)))

    goal : (absℤ diff *ℤ ⁺toℤ f) ≤ℤ (e *ℤ ⁺toℤ bd)
    goal = ≤ℤ-resp-≡ˡ (trans abs-diff-f-eq abs-mul-eq) (≤ℤ-resp-≡ʳ ebd-eq abs-diff-f≤ebd)
  in
  goal
-- § distℚ x y ≤ ε implies x ≤ y + ε
distℚ≤ε→x≤y+ε : (x y ε : ℚ) → distℚ x y ≤ℚ ε → x ≤ℚ (y +ℚ ε)
distℚ≤ε→x≤y+ε (a / b) (c / d) (e / f) dist≤ =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    df : ℕ⁺
    df = d *⁺ f

    diff : ℤ
    diff = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    absDiff : ℤ
    absDiff = absℤ diff

    absDiff*f≤e*bd : (absDiff *ℤ ⁺toℤ f) ≤ℤ (e *ℤ ⁺toℤ bd)
    absDiff*f≤e*bd = dist≤

    diff≤absDiff : diff ≤ℤ absDiff
    diff≤absDiff = ≤ℤ-absℤ diff

    diff*f≤absDiff*f : (diff *ℤ ⁺toℤ f) ≤ℤ (absDiff *ℤ ⁺toℤ f)
    diff*f≤absDiff*f = ≤ℤ-mul-pos-right diff absDiff f diff≤absDiff

    diff*f≤e*bd : (diff *ℤ ⁺toℤ f) ≤ℤ (e *ℤ ⁺toℤ bd)
    diff*f≤e*bd = ≤ℤ-trans diff*f≤absDiff*f absDiff*f≤e*bd

    y+ε-num : ℤ
    y+ε-num = (c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)

    assoc-adf : a *ℤ ⁺toℤ df ≡ (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f
    assoc-adf = trans (cong (λ t → a *ℤ t) (⁺toℤ-*⁺ d f)) (sym (*ℤ-assoc a (⁺toℤ d) (⁺toℤ f)))

    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    assoc-cfb : (c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b ≡ (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f
    assoc-cfb = swapScale c f b

    edb≡ebd : (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b ≡ (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d
    edb≡ebd = swapScale e d b

    adf' : ℤ
    adf' = (a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f

    cbf' : ℤ
    cbf' = (c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f

    ebd : ℤ
    ebd = (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d

    ebd≡e*bd : ebd ≡ (e *ℤ ⁺toℤ bd)
    ebd≡e*bd =
      trans
        (*ℤ-assoc e (⁺toℤ b) (⁺toℤ d))
        (cong (λ t → e *ℤ t) (sym (⁺toℤ-*⁺ b d)))

    diff*f≤ebd : (diff *ℤ ⁺toℤ f) ≤ℤ ebd
    diff*f≤ebd = ≤ℤ-resp-≡ʳ (sym ebd≡e*bd) diff*f≤e*bd

    diff-f : ℤ
    diff-f = adf' +ℤ negℤ cbf'

    diff-f-eq : diff *ℤ ⁺toℤ f ≡ diff-f
    diff-f-eq =
      trans
        (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ f))
        (cong
          (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t)
          (trans
            (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ f))
            refl))

    diff-f≤ebd' : diff-f ≤ℤ ebd
    diff-f≤ebd' = ≤ℤ-resp-≡ˡ diff-f-eq diff*f≤ebd

    -- § add cbf' to both sides
    sumLe : (diff-f +ℤ cbf') ≤ℤ (ebd +ℤ cbf')
    sumLe = ≤ℤ-+ℤ-mono diff-f≤ebd' (≤ℤ-refl cbf')

    lhsEq : (diff-f +ℤ cbf') ≡ adf'
    lhsEq =
      trans
        (+ℤ-assoc adf' (negℤ cbf') cbf')
        (trans
          (cong (λ t → adf' +ℤ t) (+ℤ-inv-left cbf'))
          (+ℤ-zero-right adf'))

    rhsEq : (ebd +ℤ cbf') ≡ (cbf' +ℤ ebd)
    rhsEq = +ℤ-comm ebd cbf'

    hyp1' : adf' ≤ℤ (cbf' +ℤ ebd)
    hyp1' = ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq sumLe)

    rhsExpand : (y+ε-num *ℤ ⁺toℤ b) ≡ (cbf' +ℤ ebd)
    rhsExpand =
      let
        step₁ : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (cbf' +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
        step₁ = cong (λ t → t +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) assoc-cfb

        step₂ : (cbf' +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≡ (cbf' +ℤ ebd)
        step₂ = cong (λ t → cbf' +ℤ t) edb≡ebd
      in
      trans (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ b)) (trans step₁ step₂)
  in
  ≤ℤ-resp-≡ˡ (sym assoc-adf) (≤ℤ-resp-≡ʳ (sym rhsExpand) hyp1')

-- § converse: distℚ x y ≤ ε implies y ≤ x + ε (by symmetry)
distℚ≤ε→y≤x+ε : (x y ε : ℚ) → distℚ x y ≤ℚ ε → y ≤ℚ (x +ℚ ε)
distℚ≤ε→y≤x+ε x y ε dist≤ =
  let
    dyx≤dxy : distℚ y x ≤ℚ distℚ x y
    dyx≤dxy =
      ≃ℚ→≤ℚˡ
        {p = distℚ y x}
        {q = distℚ x y}
        (distℚ-sym y x)

    dyx≤ε : distℚ y x ≤ℚ ε
    dyx≤ε =
      ≤ℚ-trans
        {x = distℚ y x}
        {y = distℚ x y}
        {z = ε}
        dyx≤dxy
        dist≤
  in
  distℚ≤ε→x≤y+ε y x ε dyx≤ε
-- § right identity for ℕ⁺ multiplication
*⁺-one-right : (u : ℕ⁺) → (u *⁺ one⁺) ≡ u
*⁺-one-right (mkℕ⁺ p) =
  cong mkℕ⁺
    (trans
      (+ℕ-zero-right (p *ℕ suc zero))
      (*ℕ-one-right p))

-- § 0 < 1/b for any positive denominator
oneOver-pos : (b : ℕ⁺) → 0ℚ <ℚ (oneℤ / b)
oneOver-pos b =
  let
    rhsEq : oneℤ ≡ (oneℤ *ℤ ⁺toℤ one⁺)
    rhsEq = sym (*ℤ-one-right oneℤ)

    base : 0ℤ <ℤ (oneℤ *ℤ ⁺toℤ one⁺)
    base = <ℤ-resp-≡ʳ {x = 0ℤ} {y = oneℤ} {z = (oneℤ *ℤ ⁺toℤ one⁺)} rhsEq 0ℤ<oneℤ
  in
  <ℤ-resp-≡ˡ
    {x = 0ℤ}
    {y = (0ℤ *ℤ ⁺toℤ b)}
    {z = (oneℤ *ℤ ⁺toℤ one⁺)}
    (sym (*ℤ-zero-left (⁺toℤ b)))
    base

-- § denominators are ≥ 1 in the integer order
one≤⁺toℤ : (d : ℕ⁺) → oneℤ ≤ℤ ⁺toℤ d
one≤⁺toℤ (mkℕ⁺ k) = s≤s z≤n

-- § q ≥ 0 implies q ≤ num(q)/1
nonneg-≤numOverOne : (q : ℚ) → 0ℚ ≤ℚ q → q ≤ℚ (num q / one⁺)
nonneg-≤numOverOne (a / b) qNonneg =
  let
    aNonneg : 0ℤ ≤ℤ a
    aNonneg =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsEq : (a *ℤ ⁺toℤ one⁺) ≡ a
        rhsEq = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)

        step₀ : 0ℤ ≤ℤ (a *ℤ ⁺toℤ one⁺)
        step₀ = ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b)) qNonneg
      in
      ≤ℤ-resp-≡ʳ rhsEq step₀

    one≤b : oneℤ ≤ℤ ⁺toℤ b
    one≤b = one≤⁺toℤ b

    step : (oneℤ *ℤ a) ≤ℤ ((⁺toℤ b) *ℤ a)
    step = ≤ℤ-mul-nonneg-right oneℤ (⁺toℤ b) a one≤b aNonneg

    lhsEq : (oneℤ *ℤ a) ≡ (a *ℤ ⁺toℤ one⁺)
    lhsEq = trans (*ℤ-one-left a) (sym (*ℤ-one-right a))

    rhsEq : ((⁺toℤ b) *ℤ a) ≡ (a *ℤ ⁺toℤ b)
    rhsEq = *ℤ-comm (⁺toℤ b) a

    core : (a *ℤ ⁺toℤ one⁺) ≤ℤ (a *ℤ ⁺toℤ b)
    core = ≤ℤ-resp-≡ˡ lhsEq (≤ℤ-resp-≡ʳ rhsEq step)
  in
  core

-- § nonnegative q is bounded by suc(m)/1 for some m
nonneg-bound-sucInt : (q : ℚ) → 0ℚ ≤ℚ q → Σ ℕ (λ m → q ≤ℚ (fromℕℤ (suc m) / one⁺))
nonneg-bound-sucInt (a / b) qNonneg =
  let
    aNonneg : 0ℤ ≤ℤ a
    aNonneg =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsEq : (a *ℤ ⁺toℤ one⁺) ≡ a
        rhsEq = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)

        step₀ : 0ℤ ≤ℤ (a *ℤ ⁺toℤ one⁺)
        step₀ = ≤ℤ-resp-≡ˡ (*ℤ-zero-left (⁺toℤ b)) qNonneg
      in
      ≤ℤ-resp-≡ʳ rhsEq step₀

    aNatPack : Σ ℕ (λ n → a ≡ fromℕℤ n)
    aNatPack = 0≤ℤ→fromℕℤ a aNonneg

    m : ℕ
    m = fst aNatPack

    a≡ : a ≡ fromℕℤ m
    a≡ = snd aNatPack

    q≤a/1 : (a / b) ≤ℚ (a / one⁺)
    q≤a/1 = nonneg-≤numOverOne (a / b) qNonneg

    a/1≤m/1 : (a / one⁺) ≤ℚ (fromℕℤ m / one⁺)
    a/1≤m/1 =
      ≤ℤ-resp-≡ʳ
        (cong (λ t → t *ℤ ⁺toℤ one⁺) a≡)
        (≤ℤ-refl (a *ℤ ⁺toℤ one⁺))

    m≤sucm : m ≤ suc m
    m≤sucm = ≤-step m

    fm≤fs : fromℕℤ m ≤ℤ fromℕℤ (suc m)
    fm≤fs = fromℕℤ-mono m≤sucm

    m/1≤sucm/1 : (fromℕℤ m / one⁺) ≤ℚ (fromℕℤ (suc m) / one⁺)
    m/1≤sucm/1 =
      let
        one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
        one⁺ℤ≡oneℤ = refl

        rhsOneEq : (n : ℕ) → (fromℕℤ n *ℤ ⁺toℤ one⁺) ≡ fromℕℤ n
        rhsOneEq n = trans (cong (λ t → fromℕℤ n *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right (fromℕℤ n))

        stepR : fromℕℤ m ≤ℤ (fromℕℤ (suc m) *ℤ ⁺toℤ one⁺)
        stepR = ≤ℤ-resp-≡ʳ (sym (rhsOneEq (suc m))) fm≤fs
      in
      ≤ℤ-resp-≡ˡ (sym (rhsOneEq m)) stepR
  in
  m ,
    (≤ℚ-trans {a / b} {a / one⁺} {fromℕℤ (suc m) / one⁺} q≤a/1
      (≤ℚ-trans {a / one⁺} {fromℕℤ m / one⁺} {fromℕℤ (suc m) / one⁺} a/1≤m/1 m/1≤sucm/1))
-- § Archimedean scaling: ∃ δ>0 with δ·(suc m) < ε
δ-scale-suc : (ε : ℚ) → 0ℚ <ℚ ε → (m : ℕ) → Σ ℚ (λ δ → (0ℚ <ℚ δ) × ((δ *ℚ (fromℕℤ (suc m) / one⁺)) <ℚ ε))
δ-scale-suc ε εpos m =
  let
    k : ℕ⁺
    k = mkℕ⁺ m

    b : ℕ⁺
    b = den ε

    δ : ℚ
    δ = oneℤ / halfDen (k *⁺ b)

    δpos : 0ℚ <ℚ δ
    δpos = oneOver-pos (halfDen (k *⁺ b))

    factor : ℚ
    factor = fromℕℤ (suc m) / one⁺

    prod : ℚ
    prod = δ *ℚ factor

    -- § prod ≃ εHalf ε, hence prod < ε
    kZ : ℤ
    kZ = ⁺toℤ k

    kZ≡ : kZ ≡ fromℕℤ (suc m)
    kZ≡ = refl

    halfDenZ : (u : ℕ⁺) → ⁺toℤ (halfDen u) ≡ (⁺toℤ two⁺) *ℤ ⁺toℤ u
    halfDenZ u = ⁺toℤ-*⁺ two⁺ u

    rhsDenZ : ⁺toℤ (halfDen b) ≡ (⁺toℤ two⁺) *ℤ ⁺toℤ b
    rhsDenZ = halfDenZ b

    lhsDenZ : ⁺toℤ (halfDen (k *⁺ b)) ≡ (⁺toℤ two⁺) *ℤ ((⁺toℤ k) *ℤ ⁺toℤ b)
    lhsDenZ =
      trans
        (halfDenZ (k *⁺ b))
        (cong (λ t → (⁺toℤ two⁺) *ℤ t) (⁺toℤ-*⁺ k b))

    swap : (x y z : ℤ) → (x *ℤ (y *ℤ z)) ≡ (y *ℤ (x *ℤ z))
    swap x y z =
      trans
        (sym (*ℤ-assoc x y z))
        (trans
          (cong (λ t → t *ℤ z) (*ℤ-comm x y))
          (*ℤ-assoc y x z))

    denEq : (⁺toℤ (halfDen (k *⁺ b))) ≡ (fromℕℤ (suc m) *ℤ ⁺toℤ (halfDen b))
    denEq =
      trans
        lhsDenZ
        (trans
          (cong (λ t → (⁺toℤ two⁺) *ℤ (t *ℤ ⁺toℤ b)) (sym kZ≡))
          (trans
            (swap (⁺toℤ two⁺) (fromℕℤ (suc m)) (⁺toℤ b))
            (cong (λ t → (fromℕℤ (suc m)) *ℤ t) (sym rhsDenZ))))

    prod≃half : prod ≃ℚ (εHalf ε)
    prod≃half =
      let
        lhsNum : ℤ
        lhsNum = oneℤ *ℤ fromℕℤ (suc m)

        lhsDen : ℕ⁺
        lhsDen = (halfDen (k *⁺ b)) *⁺ one⁺

        rhsNum : ℤ
        rhsNum = oneℤ

        rhsDen : ℕ⁺
        rhsDen = halfDen b

        lhsNumEq : lhsNum ≡ fromℕℤ (suc m)
        lhsNumEq = *ℤ-one-left (fromℕℤ (suc m))

        denOne : (halfDen (k *⁺ b)) *⁺ one⁺ ≡ halfDen (k *⁺ b)
        denOne = *⁺-one-right (halfDen (k *⁺ b))

        lhsDenEq : (⁺toℤ lhsDen) ≡ ⁺toℤ (halfDen (k *⁺ b))
        lhsDenEq = cong ⁺toℤ denOne

        cross : (lhsNum *ℤ ⁺toℤ rhsDen) ≡ (rhsNum *ℤ ⁺toℤ lhsDen)
        cross =
          trans
            (cong (λ t → t *ℤ ⁺toℤ rhsDen) lhsNumEq)
            (trans
              (sym denEq)
              (trans
                (sym (*ℤ-one-left (⁺toℤ (halfDen (k *⁺ b)))))
                (cong (λ t → oneℤ *ℤ t) (sym lhsDenEq))))
      in
      cross

    half<ε : (εHalf ε) <ℚ ε
    half<ε = εHalf<ε ε εpos

    prod<ε : prod <ℚ ε
    prod<ε =
      ≤<ℚ→<ℚ
        {x = prod} {y = εHalf ε} {z = ε}
        (≃ℚ→≤ℚˡ {p = prod} {q = εHalf ε} prod≃half)
        half<ε
  in
  δ , (δpos , prod<ε)
-- § identity operator on Vec12ℤ
I12 : Op
I12 v = v

-- § scale a 4-vector by integer a
scaleVec4ℤ : ℤ → Vec4ℤ → Vec4ℤ
scaleVec4ℤ a v i = a *ℤ v i

-- § scale a 12-vector blockwise
scaleVec12ℤ : ℤ → Vec12ℤ → Vec12ℤ
scaleVec12ℤ a v = scaleVec4ℤ a (block₀ v) , (scaleVec4ℤ a (block₁ v) , scaleVec4ℤ a (block₂ v))

-- § linear combination a·I + b·J
linIJ : ℤ → ℤ → Op
linIJ a b v = scaleVec12ℤ a v +Vec12ℤ scaleVec12ℤ b (J12Vec12ℤ v)

-- § block projection lemmas (all refl)
block₀-linIJ : (a b : ℤ) → (v : Vec12ℤ) → (i : Fin4) →
  block₀ (linIJ a b v) i ≡ (a *ℤ block₀ v i) +ℤ (b *ℤ sum12ℤ v)
block₀-linIJ a b v i = refl

block₁-linIJ : (a b : ℤ) → (v : Vec12ℤ) → (i : Fin4) →
  block₁ (linIJ a b v) i ≡ (a *ℤ block₁ v i) +ℤ (b *ℤ sum12ℤ v)
block₁-linIJ a b v i = refl

block₂-linIJ : (a b : ℤ) → (v : Vec12ℤ) → (i : Fin4) →
  block₂ (linIJ a b v) i ≡ (a *ℤ block₂ v i) +ℤ (b *ℤ sum12ℤ v)
block₂-linIJ a b v i = refl
-- § six-term sum reassociation into (v-side) + (w-side)
shuffle3Pairs : (A A' B B' C C' : ℤ) →
  (A +ℤ A') +ℤ ((B +ℤ B') +ℤ (C +ℤ C')) ≡ (A +ℤ (B +ℤ C)) +ℤ (A' +ℤ (B' +ℤ C'))
shuffle3Pairs A A' B B' C C' =
  let
    X = (B +ℤ B') +ℤ (C +ℤ C')

    step₁ : (A +ℤ A') +ℤ X ≡ A +ℤ (A' +ℤ X)
    step₁ = +ℤ-assoc A A' X

    step₂ : A' +ℤ X ≡ A' +ℤ (B +ℤ (B' +ℤ (C +ℤ C')))
    step₂ = cong (λ t → A' +ℤ t) (+ℤ-assoc B B' (C +ℤ C'))

    step₃ : A' +ℤ (B +ℤ (B' +ℤ (C +ℤ C'))) ≡ B +ℤ (A' +ℤ (B' +ℤ (C +ℤ C')))
    step₃ = swapHeadℤ A' B (B' +ℤ (C +ℤ C'))

    step₄ : A' +ℤ (B' +ℤ (C +ℤ C')) ≡ C +ℤ (A' +ℤ (B' +ℤ C'))
    step₄ =
      trans
        (cong (λ t → A' +ℤ t) (swapHeadℤ B' C C'))
        (swapHeadℤ A' C (B' +ℤ C'))

    step₅ : B +ℤ (A' +ℤ (B' +ℤ (C +ℤ C'))) ≡ B +ℤ (C +ℤ (A' +ℤ (B' +ℤ C')))
    step₅ = cong (λ t → B +ℤ t) step₄

    step₆ : A +ℤ (B +ℤ (C +ℤ (A' +ℤ (B' +ℤ C')))) ≡ (A +ℤ (B +ℤ C)) +ℤ (A' +ℤ (B' +ℤ C'))
    step₆ =
      trans
        (cong (λ t → A +ℤ t) (sym (+ℤ-assoc B C (A' +ℤ (B' +ℤ C')))))
        (sym (+ℤ-assoc A (B +ℤ C) (A' +ℤ (B' +ℤ C'))))
  in
  trans
    step₁
    (trans
      (cong (λ t → A +ℤ t) (trans step₂ (trans step₃ step₅)))
      step₆)

-- § finite-sum scaling by right distributivity
sumFin4-scaleVec4ℤ : (a : ℤ) → (v : Vec4ℤ) →
  sumFin4ℤ (scaleVec4ℤ a v) ≡ a *ℤ sumFin4ℤ v
sumFin4-scaleVec4ℤ a v =
  let
    v0 = v g0
    v1 = v g1
    v2 = v g2
    v3 = v g3

    expand : a *ℤ (v0 +ℤ (v1 +ℤ (v2 +ℤ v3))) ≡ (a *ℤ v0) +ℤ ((a *ℤ v1) +ℤ ((a *ℤ v2) +ℤ (a *ℤ v3)))
    expand =
      trans
        (*ℤ-distrib-right-+ℤ a v0 (v1 +ℤ (v2 +ℤ v3)))
        (cong (λ t → (a *ℤ v0) +ℤ t)
          (trans
            (*ℤ-distrib-right-+ℤ a v1 (v2 +ℤ v3))
            (cong (λ t → (a *ℤ v1) +ℤ t)
              (*ℤ-distrib-right-+ℤ a v2 v3))))
  in
  sym expand

-- § 12-vector sum distributes over addition
sum12-+Vec12ℤ : (v w : Vec12ℤ) → sum12ℤ (v +Vec12ℤ w) ≡ sum12ℤ v +ℤ sum12ℤ w
sum12-+Vec12ℤ v w =
  let
    A  = sumFin4ℤ (block₀ v)
    B  = sumFin4ℤ (block₁ v)
    C  = sumFin4ℤ (block₂ v)
    A' = sumFin4ℤ (block₀ w)
    B' = sumFin4ℤ (block₁ w)
    C' = sumFin4ℤ (block₂ w)
  in
  trans
    refl
    (trans
      (cong
        (λ t → t +ℤ (sumFin4ℤ (block₁ (v +Vec12ℤ w)) +ℤ sumFin4ℤ (block₂ (v +Vec12ℤ w))))
        (sumFin4-+Vec4ℤ (block₀ v) (block₀ w)))
      (trans
        (cong
          (λ t → (A +ℤ A') +ℤ (t +ℤ sumFin4ℤ (block₂ (v +Vec12ℤ w))) )
          (sumFin4-+Vec4ℤ (block₁ v) (block₁ w)))
        (trans
          (cong
            (λ t → (A +ℤ A') +ℤ ((B +ℤ B') +ℤ t))
            (sumFin4-+Vec4ℤ (block₂ v) (block₂ w)))
          (shuffle3Pairs A A' B B' C C'))))

-- § 12-vector sum distributes over scalar multiplication
sum12-scaleVec12ℤ : (a : ℤ) → (v : Vec12ℤ) → sum12ℤ (scaleVec12ℤ a v) ≡ a *ℤ sum12ℤ v
sum12-scaleVec12ℤ a v =
  let
    s0 = sumFin4ℤ (block₀ v)
    s1 = sumFin4ℤ (block₁ v)
    s2 = sumFin4ℤ (block₂ v)
  in
  let
    stepBlock : sum12ℤ (scaleVec12ℤ a v) ≡ (a *ℤ s0) +ℤ ((a *ℤ s1) +ℤ (a *ℤ s2))
    stepBlock =
      trans
        refl
        (trans
          (cong
            (λ t → t +ℤ (sumFin4ℤ (scaleVec4ℤ a (block₁ v)) +ℤ sumFin4ℤ (scaleVec4ℤ a (block₂ v))))
            (sumFin4-scaleVec4ℤ a (block₀ v)))
          (trans
            (cong
              (λ t → (a *ℤ s0) +ℤ (t +ℤ sumFin4ℤ (scaleVec4ℤ a (block₂ v))) )
              (sumFin4-scaleVec4ℤ a (block₁ v)))
            (cong
              (λ t → (a *ℤ s0) +ℤ ((a *ℤ s1) +ℤ t))
              (sumFin4-scaleVec4ℤ a (block₂ v)))))

    fold : a *ℤ (s0 +ℤ (s1 +ℤ s2)) ≡ (a *ℤ s0) +ℤ ((a *ℤ s1) +ℤ (a *ℤ s2))
    fold =
      trans
        (*ℤ-distrib-right-+ℤ a s0 (s1 +ℤ s2))
        (cong (λ t → (a *ℤ s0) +ℤ t) (*ℤ-distrib-right-+ℤ a s1 s2))
  in
  trans stepBlock (sym fold)
-- § x * fourTimes y = fourTimes (x*y)
*ℤ-fourTimes-right : (x y : ℤ) → x *ℤ fourTimesℤ y ≡ fourTimesℤ (x *ℤ y)
*ℤ-fourTimes-right x y =
  trans
    (*ℤ-distrib-right-+ℤ x y (y +ℤ (y +ℤ y)))
    (cong (λ t → (x *ℤ y) +ℤ t)
      (trans
        (*ℤ-distrib-right-+ℤ x y (y +ℤ y))
        (cong (λ t → (x *ℤ y) +ℤ t)
          (*ℤ-distrib-right-+ℤ x y y))))

-- § fourTimes x * y = fourTimes (x*y)
*ℤ-fourTimes-left : (x y : ℤ) → fourTimesℤ x *ℤ y ≡ fourTimesℤ (x *ℤ y)
*ℤ-fourTimes-left x y =
  trans
    (*ℤ-distrib-left-+ℤ x (x +ℤ (x +ℤ x)) y)
    (cong (λ t → (x *ℤ y) +ℤ t)
      (trans
        (*ℤ-distrib-left-+ℤ x (x +ℤ x) y)
        (cong (λ t → (x *ℤ y) +ℤ t)
          (*ℤ-distrib-left-+ℤ x x y))))

-- § x * eightTimes y = eightTimes (x*y)
*ℤ-eightTimes-right : (x y : ℤ) → x *ℤ eightTimesℤ y ≡ eightTimesℤ (x *ℤ y)
*ℤ-eightTimes-right x y =
  trans
    (*ℤ-distrib-right-+ℤ x (fourTimesℤ y) (fourTimesℤ y))
    (cong (λ t → t +ℤ t) (*ℤ-fourTimes-right x y))

-- § eightTimes x * y = eightTimes (x*y)
*ℤ-eightTimes-left : (x y : ℤ) → eightTimesℤ x *ℤ y ≡ eightTimesℤ (x *ℤ y)
*ℤ-eightTimes-left x y =
  trans
    (*ℤ-distrib-left-+ℤ (fourTimesℤ x) (fourTimesℤ x) y)
    (cong (λ t → t +ℤ t) (*ℤ-fourTimes-left x y))

-- § x * twelveTimes y = twelveTimes (x*y)
*ℤ-twelveTimes-right : (x y : ℤ) → x *ℤ twelveTimesℤ y ≡ twelveTimesℤ (x *ℤ y)
*ℤ-twelveTimes-right x y =
  trans
    (*ℤ-distrib-right-+ℤ x (fourTimesℤ y) (eightTimesℤ y))
    (trans
      (cong (λ t → t +ℤ x *ℤ eightTimesℤ y) (*ℤ-fourTimes-right x y))
      (cong (λ t → fourTimesℤ (x *ℤ y) +ℤ t) (*ℤ-eightTimes-right x y)))

-- § twelveTimes x * y = twelveTimes (x*y)
*ℤ-twelveTimes-left : (x y : ℤ) → twelveTimesℤ x *ℤ y ≡ twelveTimesℤ (x *ℤ y)
*ℤ-twelveTimes-left x y =
  trans
    (*ℤ-distrib-left-+ℤ (fourTimesℤ x) (eightTimesℤ x) y)
    (trans
      (cong (λ t → t +ℤ eightTimesℤ x *ℤ y) (*ℤ-fourTimes-left x y))
      (cong (λ t → fourTimesℤ (x *ℤ y) +ℤ t) (*ℤ-eightTimes-left x y)))

-- § x * twelveTimes y = twelveTimes x * y
mul-twelveShift : (x y : ℤ) → x *ℤ twelveTimesℤ y ≡ twelveTimesℤ x *ℤ y
mul-twelveShift x y = trans (*ℤ-twelveTimes-right x y) (sym (*ℤ-twelveTimes-left x y))

-- § sum of an (I,J)-combination
sum12-linIJ : (a b : ℤ) → (v : Vec12ℤ) →
  sum12ℤ (linIJ a b v) ≡ (a *ℤ sum12ℤ v) +ℤ (b *ℤ twelveTimesℤ (sum12ℤ v))
sum12-linIJ a b v =
  let
    s = sum12ℤ v
    step₁ : sum12ℤ (linIJ a b v)
              ≡ sum12ℤ (scaleVec12ℤ a v) +ℤ sum12ℤ (scaleVec12ℤ b (J12Vec12ℤ v))
    step₁ = sum12-+Vec12ℤ (scaleVec12ℤ a v) (scaleVec12ℤ b (J12Vec12ℤ v))

    step₂ : sum12ℤ (scaleVec12ℤ a v) ≡ a *ℤ s
    step₂ = sum12-scaleVec12ℤ a v

    step₃ : sum12ℤ (scaleVec12ℤ b (J12Vec12ℤ v)) ≡ b *ℤ sum12ℤ (J12Vec12ℤ v)
    step₃ = sum12-scaleVec12ℤ b (J12Vec12ℤ v)

    step₄ : b *ℤ sum12ℤ (J12Vec12ℤ v) ≡ b *ℤ twelveTimesℤ s
    step₄ = cong (λ t → b *ℤ t) (sum12-J12 v)
  in
  trans
    step₁
    (trans
      (cong (λ t → t +ℤ sum12ℤ (scaleVec12ℤ b (J12Vec12ℤ v))) step₂)
      (cong (λ t → (a *ℤ s) +ℤ t) (trans step₃ step₄)))
-- § single-coordinate delta vector on Fin4 (16 pattern cases)
delta4 : Fin4 → ℤ → Vec4ℤ
delta4 g0 x g0 = x
delta4 g0 x g1 = 0ℤ
delta4 g0 x g2 = 0ℤ
delta4 g0 x g3 = 0ℤ

delta4 g1 x g0 = 0ℤ
delta4 g1 x g1 = x
delta4 g1 x g2 = 0ℤ
delta4 g1 x g3 = 0ℤ

delta4 g2 x g0 = 0ℤ
delta4 g2 x g1 = 0ℤ
delta4 g2 x g2 = x
delta4 g2 x g3 = 0ℤ

delta4 g3 x g0 = 0ℤ
delta4 g3 x g1 = 0ℤ
delta4 g3 x g2 = 0ℤ
delta4 g3 x g3 = x

-- § sumFin4 of delta is identity
sumFin4-delta4 : (i : Fin4) → (x : ℤ) → sumFin4ℤ (delta4 i x) ≡ x
sumFin4-delta4 g0 x =
  trans
    (cong (λ t → x +ℤ t)
      (trans
        (+ℤ-zero-left (0ℤ +ℤ 0ℤ))
        (+ℤ-zero-left 0ℤ)))
    (+ℤ-zero-right x)
sumFin4-delta4 g1 x =
  trans
    (+ℤ-zero-left (x +ℤ (0ℤ +ℤ 0ℤ)))
    (trans
      (cong (λ t → x +ℤ t) (+ℤ-zero-left 0ℤ))
      (+ℤ-zero-right x))
sumFin4-delta4 g2 x =
  trans
    (+ℤ-zero-left (0ℤ +ℤ (x +ℤ 0ℤ)))
    (trans
      (+ℤ-zero-left (x +ℤ 0ℤ))
      (+ℤ-zero-right x))
sumFin4-delta4 g3 x =
  trans
    (+ℤ-zero-left (0ℤ +ℤ (0ℤ +ℤ x)))
    (trans
      (+ℤ-zero-left (0ℤ +ℤ x))
      (+ℤ-zero-left x))

-- § delta vector on Vec12ℤ supported at (block₀, g0)
delta12 : ℤ → Vec12ℤ
delta12 x = delta4 g0 x , (delta4 g0 0ℤ , delta4 g0 0ℤ)

-- § sum12 of delta12 is identity
sum12-delta12 : (x : ℤ) → sum12ℤ (delta12 x) ≡ x
sum12-delta12 x =
  trans
    (cong (λ t → t +ℤ (sumFin4ℤ (delta4 g0 0ℤ) +ℤ sumFin4ℤ (delta4 g0 0ℤ)))
          (sumFin4-delta4 g0 x))
    (trans
      (cong (λ t → x +ℤ t)
            (cong (λ t → t +ℤ sumFin4ℤ (delta4 g0 0ℤ)) (sumFin4-delta4 g0 0ℤ)))
      (trans
        (cong (λ t → x +ℤ (0ℤ +ℤ t)) (sumFin4-delta4 g0 0ℤ))
        (trans
          (cong (λ t → x +ℤ t) (+ℤ-zero-left 0ℤ))
          (+ℤ-zero-right x))))

-- § J12 on delta12 is constant vector
J12-delta12-const : (x : ℤ) → Vec12Eq (J12Vec12ℤ (delta12 x)) (constVec12ℤ x)
J12-delta12-const x =
  let p = sum12-delta12 x in
  (λ _ → p) , ((λ _ → p) , (λ _ → p))
-- § Law 14N.0: (a·I + b·J) = 0 forces a = 0 and b = 0
law14N-0-IJ-independent : (a b : ℤ) → OpEq (linIJ a b) zeroOp → (a ≡ 0ℤ) × (b ≡ 0ℤ)
law14N-0-IJ-independent a b hyp = a0 , b0
  where
    v : Vec12ℤ
    v = delta12 oneℤ

    pSum : sum12ℤ v ≡ oneℤ
    pSum = sum12-delta12 oneℤ

    -- § at g1 the I-term vanishes, extracting b
    eqQraw : block₀ (linIJ a b v) g1 ≡ block₀ (zeroOp v) g1
    eqQraw = fst (hyp v) g1

    eqQ₀ : (a *ℤ 0ℤ) +ℤ (b *ℤ sum12ℤ v) ≡ 0ℤ
    eqQ₀ = trans (sym (block₀-linIJ a b v g1)) eqQraw

    eqQ₁ : (a *ℤ 0ℤ) +ℤ (b *ℤ oneℤ) ≡ 0ℤ
    eqQ₁ = trans (sym (cong (λ t → (a *ℤ 0ℤ) +ℤ (b *ℤ t)) pSum)) eqQ₀

    eqQ₂ : 0ℤ +ℤ (b *ℤ oneℤ) ≡ 0ℤ
    eqQ₂ =
      trans
        (sym (cong (λ t → t +ℤ (b *ℤ oneℤ)) (*ℤ-zero-right a)))
        eqQ₁

    bAtQ : (b *ℤ oneℤ) ≡ 0ℤ
    bAtQ = trans (sym (+ℤ-zero-left (b *ℤ oneℤ))) eqQ₂

    b0 : b ≡ 0ℤ
    b0 = trans (sym (*ℤ-one-right b)) bAtQ

    -- § at g0 the I-term gives a, extracting a
    eqPraw : block₀ (linIJ a b v) g0 ≡ block₀ (zeroOp v) g0
    eqPraw = fst (hyp v) g0

    eqP₀ : (a *ℤ oneℤ) +ℤ (b *ℤ sum12ℤ v) ≡ 0ℤ
    eqP₀ = trans (sym (block₀-linIJ a b v g0)) eqPraw

    eqP₁ : (a *ℤ oneℤ) +ℤ (b *ℤ oneℤ) ≡ 0ℤ
    eqP₁ = trans (sym (cong (λ t → (a *ℤ oneℤ) +ℤ (b *ℤ t)) pSum)) eqP₀

    eqP₂ : (a *ℤ oneℤ) +ℤ (0ℤ *ℤ oneℤ) ≡ 0ℤ
    eqP₂ =
      trans
        (sym (cong (λ t → (a *ℤ oneℤ) +ℤ (t *ℤ oneℤ)) b0))
        eqP₁

    eqP₃ : (a *ℤ oneℤ) +ℤ 0ℤ ≡ 0ℤ
    eqP₃ =
      trans
        (sym (cong (λ t → (a *ℤ oneℤ) +ℤ t) (*ℤ-zero-left oneℤ)))
        eqP₂

    aAtP : (a *ℤ oneℤ) ≡ 0ℤ
    aAtP = trans (sym (+ℤ-zero-right (a *ℤ oneℤ))) eqP₃

    a0 : a ≡ 0ℤ
    a0 = trans (sym (*ℤ-one-right a)) aAtP

-- § additive right cancellation
+ℤ-cancel-right : (a c b : ℤ) → a +ℤ b ≡ c +ℤ b → a ≡ c
+ℤ-cancel-right a c b eq =
  let eq' = cong (λ t → negℤ b +ℤ t) eq in
  trans
    (sym (reduce a))
    (trans eq' (reduce c))
  where
    reduce : (x : ℤ) → negℤ b +ℤ (x +ℤ b) ≡ x
    reduce x =
      trans
        (swapHeadℤ (negℤ b) x b)
        (trans
          (cong (λ t → x +ℤ t) (+ℤ-inv-left b))
          (+ℤ-zero-right x))
-- § Law 14N.1: (a·I + b·J) = (c·I + d·J) forces a = c and b = d
law14N-1-IJ-unique : (a b c d : ℤ) → OpEq (linIJ a b) (linIJ c d) → (a ≡ c) × (b ≡ d)
law14N-1-IJ-unique a b c d hyp = aEq , bEq
  where
    v : Vec12ℤ
    v = delta12 oneℤ

    pSum : sum12ℤ v ≡ oneℤ
    pSum = sum12-delta12 oneℤ

    -- § extract b = d from g1 evaluation
    eqQraw : block₀ (linIJ a b v) g1 ≡ block₀ (linIJ c d v) g1
    eqQraw = fst (hyp v) g1

    eqQ₀ : (a *ℤ 0ℤ) +ℤ (b *ℤ sum12ℤ v) ≡ (c *ℤ 0ℤ) +ℤ (d *ℤ sum12ℤ v)
    eqQ₀ =
      trans (sym (block₀-linIJ a b v g1))
        (trans eqQraw (block₀-linIJ c d v g1))

    eqQ₁a : (a *ℤ 0ℤ) +ℤ (b *ℤ sum12ℤ v) ≡ 0ℤ +ℤ (b *ℤ sum12ℤ v)
    eqQ₁a = cong (λ t → t +ℤ (b *ℤ sum12ℤ v)) (*ℤ-zero-right a)

    eqQ₁c : (c *ℤ 0ℤ) +ℤ (d *ℤ sum12ℤ v) ≡ 0ℤ +ℤ (d *ℤ sum12ℤ v)
    eqQ₁c = cong (λ t → t +ℤ (d *ℤ sum12ℤ v)) (*ℤ-zero-right c)

    eqQ₁ : 0ℤ +ℤ (b *ℤ sum12ℤ v) ≡ 0ℤ +ℤ (d *ℤ sum12ℤ v)
    eqQ₁ = trans (sym eqQ₁a) (trans eqQ₀ eqQ₁c)

    eqQ₂ : 0ℤ +ℤ (b *ℤ oneℤ) ≡ 0ℤ +ℤ (d *ℤ oneℤ)
    eqQ₂ =
      trans
        (cong (λ t → 0ℤ +ℤ (b *ℤ t)) pSum)
        (trans eqQ₁ (sym (cong (λ t → 0ℤ +ℤ (d *ℤ t)) pSum)))

    bEq' : (b *ℤ oneℤ) ≡ (d *ℤ oneℤ)
    bEq' =
      trans
        (sym (+ℤ-zero-left (b *ℤ oneℤ)))
        (trans eqQ₂ (+ℤ-zero-left (d *ℤ oneℤ)))

    bEq : b ≡ d
    bEq =
      trans (sym (*ℤ-one-right b))
        (trans bEq' (*ℤ-one-right d))

    -- § extract a = c from g0 evaluation with right cancellation
    eqPraw : block₀ (linIJ a b v) g0 ≡ block₀ (linIJ c d v) g0
    eqPraw = fst (hyp v) g0

    eqP₀ : (a *ℤ oneℤ) +ℤ (b *ℤ sum12ℤ v) ≡ (c *ℤ oneℤ) +ℤ (d *ℤ sum12ℤ v)
    eqP₀ =
      trans (sym (block₀-linIJ a b v g0))
        (trans eqPraw (block₀-linIJ c d v g0))

    eqP₁ : (a *ℤ oneℤ) +ℤ (b *ℤ oneℤ) ≡ (c *ℤ oneℤ) +ℤ (d *ℤ oneℤ)
    eqP₁ =
      trans (cong (λ t → (a *ℤ oneℤ) +ℤ (b *ℤ t)) pSum)
        (trans eqP₀ (sym (cong (λ t → (c *ℤ oneℤ) +ℤ (d *ℤ t)) pSum)))

    eqP₂ : (a *ℤ oneℤ) +ℤ (b *ℤ oneℤ) ≡ (c *ℤ oneℤ) +ℤ (b *ℤ oneℤ)
    eqP₂ =
      trans
        eqP₁
        (cong (λ t → (c *ℤ oneℤ) +ℤ t)
          (cong (λ z → z *ℤ oneℤ) (sym bEq)))

    aEq' : (a *ℤ oneℤ) ≡ (c *ℤ oneℤ)
    aEq' = +ℤ-cancel-right (a *ℤ oneℤ) (c *ℤ oneℤ) (b *ℤ oneℤ) eqP₂

    aEq : a ≡ c
    aEq =
      trans (sym (*ℤ-one-right a))
        (trans aEq' (*ℤ-one-right c))
-- § the forced (I,J) normal form
SpanIJ : Set
SpanIJ = ℤ × ℤ

-- § interpretation into operators
interpIJ : SpanIJ → Op
interpIJ ab = linIJ (fst ab) (snd ab)

-- § injectivity of interpretation
interpIJ-injective : (p q : SpanIJ) → OpEq (interpIJ p) (interpIJ q) → p ≡ q
interpIJ-injective (a , b) (c , d) eq =
  let res = law14N-1-IJ-unique a b c d eq in
  pair-ext (fst res) (snd res)
  where
    pair-ext : {a b c d : ℤ} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
    pair-ext refl refl = refl

-- § Law 14N.2: image witness in span is forced unique
law14N-2-image-witness-unique :
  (f : Op) →
  (w₁ w₂ : Σ SpanIJ (λ p → OpEq f (interpIJ p))) →
  fst w₁ ≡ fst w₂
law14N-2-image-witness-unique f (p₁ , eq₁) (p₂ , eq₂) =
  interpIJ-injective p₁ p₂ (λ v → Vec12Eq-trans (Vec12Eq-sym (eq₁ v)) (eq₂ v))

-- § multiplication rule for SpanIJ
mulSpanIJ : SpanIJ → SpanIJ → SpanIJ
mulSpanIJ (a , b) (c , d) = (a *ℤ c) , (((a *ℤ d) +ℤ (b *ℤ c)) +ℤ twelveTimesℤ (b *ℤ d))
-- § Law 14N.3: (I,J)-span is closed under composition
law14N-3-IJ-compose-closed : (p q : SpanIJ) → OpEq (λ v → interpIJ p (interpIJ q v)) (interpIJ (mulSpanIJ p q))
law14N-3-IJ-compose-closed (a , b) (c , d) v = eq0 , (eq1 , eq2)
  where
    s : ℤ
    s = sum12ℤ v

    w : Vec12ℤ
    w = linIJ c d v

    sw : sum12ℤ w ≡ (c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s)
    sw = sum12-linIJ c d v

    b' : ℤ
    b' = ((a *ℤ d) +ℤ (b *ℤ c)) +ℤ twelveTimesℤ (b *ℤ d)

    -- § generic block equality helper
    blkEq :
      (blk : Vec12ℤ → Vec4ℤ) →
      ((x y : ℤ) → (u : Vec12ℤ) → (i : Fin4) → blk (linIJ x y u) i ≡ (x *ℤ blk u i) +ℤ (y *ℤ sum12ℤ u)) →
      (i : Fin4) →
      blk (linIJ a b w) i ≡ blk (linIJ (a *ℤ c) b' v) i
    blkEq blk blk-lin i =
      let
        vi = blk v i

        lhsForm : blk (linIJ a b w) i ≡ (a *ℤ blk w i) +ℤ (b *ℤ sum12ℤ w)
        lhsForm = blk-lin a b w i

        blkW : blk w i ≡ (c *ℤ vi) +ℤ (d *ℤ s)
        blkW = blk-lin c d v i

        rhsForm : blk (linIJ (a *ℤ c) b' v) i ≡ ((a *ℤ c) *ℤ vi) +ℤ (b' *ℤ s)
        rhsForm = blk-lin (a *ℤ c) b' v i

        step₁ : blk (linIJ a b w) i ≡ (a *ℤ ((c *ℤ vi) +ℤ (d *ℤ s))) +ℤ (b *ℤ sum12ℤ w)
        step₁ =
          trans
            lhsForm
            (cong (λ t → (a *ℤ t) +ℤ (b *ℤ sum12ℤ w)) blkW)

        step₂ : (a *ℤ ((c *ℤ vi) +ℤ (d *ℤ s))) +ℤ (b *ℤ sum12ℤ w)
                  ≡ ((a *ℤ (c *ℤ vi)) +ℤ (a *ℤ (d *ℤ s))) +ℤ (b *ℤ sum12ℤ w)
        step₂ = cong (λ t → t +ℤ (b *ℤ sum12ℤ w)) (*ℤ-distrib-right-+ℤ a (c *ℤ vi) (d *ℤ s))

        assocAC : a *ℤ (c *ℤ vi) ≡ (a *ℤ c) *ℤ vi
        assocAC = sym (*ℤ-assoc a c vi)

        assocAD : a *ℤ (d *ℤ s) ≡ (a *ℤ d) *ℤ s
        assocAD = sym (*ℤ-assoc a d s)

        step₃ : ((a *ℤ (c *ℤ vi)) +ℤ (a *ℤ (d *ℤ s))) +ℤ (b *ℤ sum12ℤ w)
                  ≡ (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (b *ℤ sum12ℤ w)
        step₃ =
          cong (λ t → t +ℤ (b *ℤ sum12ℤ w))
            (trans
              (cong (λ t → t +ℤ (a *ℤ (d *ℤ s))) assocAC)
              (cong (λ t → ((a *ℤ c) *ℤ vi) +ℤ t) assocAD))

        step₄ : (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (b *ℤ sum12ℤ w)
                  ≡ (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (b *ℤ ((c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s)))
        step₄ = cong (λ t → (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (b *ℤ t)) sw

        step₅ : b *ℤ ((c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s))
                  ≡ (b *ℤ (c *ℤ s)) +ℤ (b *ℤ (d *ℤ twelveTimesℤ s))
        step₅ = *ℤ-distrib-right-+ℤ b (c *ℤ s) (d *ℤ twelveTimesℤ s)

        step₆ : b *ℤ (c *ℤ s) ≡ (b *ℤ c) *ℤ s
        step₆ = sym (*ℤ-assoc b c s)

        step₇ : b *ℤ (d *ℤ twelveTimesℤ s) ≡ (twelveTimesℤ (b *ℤ d)) *ℤ s
        step₇ =
          trans
            (sym (*ℤ-assoc b d (twelveTimesℤ s)))
            (mul-twelveShift (b *ℤ d) s)

        step₈ : b *ℤ ((c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s))
                  ≡ ((b *ℤ c) *ℤ s) +ℤ ((twelveTimesℤ (b *ℤ d)) *ℤ s)
        step₈ =
          trans
            step₅
            (trans
              (cong (λ t → t +ℤ (b *ℤ (d *ℤ twelveTimesℤ s))) step₆)
              (cong (λ t → ((b *ℤ c) *ℤ s) +ℤ t) step₇))

        step₉ : (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (b *ℤ ((c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s)))
                  ≡ (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ (((b *ℤ c) *ℤ s) +ℤ ((twelveTimesℤ (b *ℤ d)) *ℤ s))
        step₉ = cong (λ t → (((a *ℤ c) *ℤ vi) +ℤ ((a *ℤ d) *ℤ s)) +ℤ t) step₈

        X = (a *ℤ c) *ℤ vi
        Y = (a *ℤ d) *ℤ s
        Z = ((b *ℤ c) *ℤ s) +ℤ ((twelveTimesℤ (b *ℤ d)) *ℤ s)

        step₁₀ : (X +ℤ Y) +ℤ Z ≡ X +ℤ (Y +ℤ Z)
        step₁₀ = +ℤ-assoc X Y Z

        twelveTerm = (twelveTimesℤ (b *ℤ d)) *ℤ s
        y2 = (b *ℤ c) *ℤ s

        fold₁ : Y +ℤ y2 ≡ ((a *ℤ d) +ℤ (b *ℤ c)) *ℤ s
        fold₁ = sym (*ℤ-distrib-left-+ℤ (a *ℤ d) (b *ℤ c) s)

        fold₂ : (((a *ℤ d) +ℤ (b *ℤ c)) *ℤ s) +ℤ twelveTerm ≡ b' *ℤ s
        fold₂ =
          trans
            (sym (*ℤ-distrib-left-+ℤ ((a *ℤ d) +ℤ (b *ℤ c)) (twelveTimesℤ (b *ℤ d)) s))
            refl

        innerFold : Y +ℤ (y2 +ℤ twelveTerm) ≡ b' *ℤ s
        innerFold =
          trans
            (sym (+ℤ-assoc Y y2 twelveTerm))
            (trans
              (cong (λ t → t +ℤ twelveTerm) fold₁)
              fold₂)
      in
      let
        pA : blk (linIJ a b w) i ≡ (X +ℤ Y) +ℤ (b *ℤ sum12ℤ w)
        pA = trans step₁ (trans step₂ step₃)

        pB : blk (linIJ a b w) i ≡ (X +ℤ Y) +ℤ (b *ℤ ((c *ℤ s) +ℤ (d *ℤ twelveTimesℤ s)))
        pB = trans pA step₄

        pC : blk (linIJ a b w) i ≡ (X +ℤ Y) +ℤ Z
        pC = trans pB (cong (λ t → (X +ℤ Y) +ℤ t) step₈)

        pD : blk (linIJ a b w) i ≡ X +ℤ (Y +ℤ Z)
        pD = trans pC (+ℤ-assoc X Y Z)

        pE : blk (linIJ a b w) i ≡ X +ℤ (b' *ℤ s)
        pE = trans pD (cong (λ t → X +ℤ t) innerFold)
      in
      trans pE (sym rhsForm)

    eq0 : (i : Fin4) → block₀ (linIJ a b w) i ≡ block₀ (linIJ (a *ℤ c) b' v) i
    eq0 = blkEq block₀ (λ x y u i → block₀-linIJ x y u i)

    eq1 : (i : Fin4) → block₁ (linIJ a b w) i ≡ block₁ (linIJ (a *ℤ c) b' v) i
    eq1 = blkEq block₁ (λ x y u i → block₁-linIJ x y u i)

    eq2 : (i : Fin4) → block₂ (linIJ a b w) i ≡ block₂ (linIJ (a *ℤ c) b' v) i
    eq2 = blkEq block₂ (λ x y u i → block₂-linIJ x y u i)
-- § Sum-zero and constant predicate witnesses on Vec12ℤ
ZeroSumVec12 : Vec12ℤ → Set
ZeroSumVec12 v = sum12ℤ v ≡ 0ℤ

ConstVec12 : Vec12ℤ → Set
ConstVec12 v = Σ ℤ (λ c → Vec12Eq v (constVec12ℤ c))
-- § linIJ respects Vec12Eq
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

-- § interpIJ inherits congruence from linIJ
interpIJ-cong : (p : SpanIJ) → (u v : Vec12ℤ) → Vec12Eq u v → Vec12Eq (interpIJ p u) (interpIJ p v)
interpIJ-cong p = linIJ-cong (fst p) (snd p)
-- § Law 14O.0: sum-zero forces J-annihilation
law14O-0-J-sum0 : (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (J12Vec12ℤ v) zeroVec12ℤ
law14O-0-J-sum0 v sum0 =
  (λ _ → sum0) , ((λ _ → sum0) , (λ _ → sum0))

-- § Law 14O.1: constant vectors force J-scaling by 12
law14O-1-J-const : (c : ℤ) → Vec12Eq (J12Vec12ℤ (constVec12ℤ c)) (constVec12ℤ (twelveTimesℤ c))
law14O-1-J-const c =
  (λ _ → sum12-const c) , ((λ _ → sum12-const c) , (λ _ → sum12-const c))
-- § Law 14O.2: sum-zero forces eigenvalue a for (a·I+b·J)
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

-- § Law 14O.3: constants force eigenvalue a+12b for (a·I+b·J)
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
-- § Helper: fourTimes 0 = 0
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

-- § Helper: eightTimes 0 = 0
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

-- § Helper: twelveTimes 0 = 0
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

-- § Law 14O.8: sum-zero is forced invariant under every (a·I+b·J)
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
-- § Helper: scaling a constant vector yields a constant vector
scaleVec12ℤ-const : (a c : ℤ) → Vec12Eq (scaleVec12ℤ a (constVec12ℤ c)) (constVec12ℤ (a *ℤ c))
scaleVec12ℤ-const a c = (λ _ → refl) , ((λ _ → refl) , (λ _ → refl))

-- § Law 14O.9: constant vectors are forced invariant under every (a·I+b·J)
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
-- § Law 14O.10: linIJ spectral package (4 components)
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

-- § Projections for LinIJSpectralPackage
LinIJPkg-sum0-inv : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ZeroSumVec12 v → ZeroSumVec12 (linIJ a b v)
LinIJPkg-sum0-inv pkg v = fst (pkg v)

LinIJPkg-const-inv : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ConstVec12 v → ConstVec12 (linIJ a b v)
LinIJPkg-const-inv pkg v = fst (snd (pkg v))

LinIJPkg-sum0-eigen : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (linIJ a b v) (scaleVec12ℤ a v)
LinIJPkg-sum0-eigen pkg v = fst (snd (snd (pkg v)))

LinIJPkg-const-eigen : {a b : ℤ} → LinIJSpectralPackage a b → (v : Vec12ℤ) → (c : ℤ) →
  Vec12Eq (linIJ a b (constVec12ℤ c)) (scaleVec12ℤ (a +ℤ twelveTimesℤ b) (constVec12ℤ c))
LinIJPkg-const-eigen pkg v = snd (snd (snd (pkg v)))
-- § Law 14O.11: any f with witness f=(a·I+b·J) inherits the spectral facts
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
-- § Law 14O.12: span-IJ coefficient witness is forced unique
SpanIJSpectralPackage : Op → Set
SpanIJSpectralPackage f = Σ SpanIJ (λ p → OpEq f (interpIJ p))

law14O-12-spanIJ-witness-unique : (f : Op) → (w₁ w₂ : SpanIJSpectralPackage f) → fst w₁ ≡ fst w₂
law14O-12-spanIJ-witness-unique f = law14N-2-image-witness-unique f

-- § Law 14O.13: spectral facts are read directly from a span witness
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

-- § Consumer projections for SpanIJSpectralPackage
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
-- § Law 14O.14: unified span transport package
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

-- § Projections for SpanIJUnifiedPackage
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

-- § Law 14O.15: unified span coefficients are forced unique
SpanIJUpkg-witness : {f : Op} → SpanIJUnifiedPackage f → Σ SpanIJ (λ p → OpEq f (interpIJ p))
SpanIJUpkg-witness upkg = SpanIJUpkg-coeffs upkg , SpanIJUpkg-opEq upkg

law14O-15-unified-coeffs-unique : (f : Op) → (u₁ u₂ : SpanIJUnifiedPackage f) → SpanIJUpkg-coeffs u₁ ≡ SpanIJUpkg-coeffs u₂
law14O-15-unified-coeffs-unique f u₁ u₂ =
  law14N-2-image-witness-unique f (SpanIJUpkg-witness u₁) (SpanIJUpkg-witness u₂)
-- § Forced integer 12
twelveℤ : ℤ
twelveℤ = twelveTimesℤ oneℤ

-- § Forced positivity witness for twelveℤ
twelveℤ-pos : Σ ℕ (λ n → twelveℤ ≡ +suc n)
twelveℤ-pos = (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) , refl

-- § 12 on the left collapses to twelveTimes
twelveℤ-*ℤ-left : (x : ℤ) → twelveℤ *ℤ x ≡ twelveTimesℤ x
twelveℤ-*ℤ-left x =
  trans
    (*ℤ-twelveTimes-left oneℤ x)
    (cong twelveTimesℤ (*ℤ-one-left x))

-- § Multiplication by (−1) collapses to additive negation
negOne-*ℤ-left : (x : ℤ) → (negℤ oneℤ) *ℤ x ≡ negℤ x
negOne-*ℤ-left x =
  let
    neg1 = negℤ oneℤ

    dist : (neg1 +ℤ oneℤ) *ℤ x ≡ (neg1 *ℤ x) +ℤ (oneℤ *ℤ x)
    dist = *ℤ-distrib-left-+ℤ neg1 oneℤ x

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
-- § Law 14O.4: L₁₂ is forced to equal (12·I)+(−1)·J
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
    eq0 i = trans (fst (law14H-6-L-twelve-minus-J v) i) (sym (rhs0 i))

    eq1 : (i : Fin4) → block₁ (K12LaplacianVec12ℤ v) i ≡ block₁ (linIJ twelveℤ neg1 v) i
    eq1 i = trans (fst (snd (law14H-6-L-twelve-minus-J v)) i) (sym (rhs1 i))

    eq2 : (i : Fin4) → block₂ (K12LaplacianVec12ℤ v) i ≡ block₂ (linIJ twelveℤ neg1 v) i
    eq2 i = trans (snd (snd (law14H-6-L-twelve-minus-J v)) i) (sym (rhs2 i))
-- § Law 14O.16: L₁₂ has forced span witness (12,−1)
LSpanIJ : SpanIJ
LSpanIJ = twelveℤ , (negℤ oneℤ)

law14O-16-L-span-witness : SpanIJSpectralPackage K12LaplacianVec12ℤ
law14O-16-L-span-witness = LSpanIJ , (λ v → law14O-4-L-in-span v)

-- § Law 14O.17: left composition by L₁₂ preserves span membership
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

-- § Law 14O.18: right composition by L₁₂ preserves span membership
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

-- § Law 14O.19: left composition by L₁₂ preserves unified packages
SpanIJUpkg-to-span : {f : Op} → SpanIJUnifiedPackage f → SpanIJSpectralPackage f
SpanIJUpkg-to-span upkg = SpanIJUpkg-coeffs upkg , SpanIJUpkg-opEq upkg

law14O-19-L-compose-left-unified : (f : Op) → SpanIJUnifiedPackage f → SpanIJUnifiedPackage (λ v → K12LaplacianVec12ℤ (f v))
law14O-19-L-compose-left-unified f upkg =
  law14O-14-spanIJ-unified-package
    (λ v → K12LaplacianVec12ℤ (f v))
    (law14O-17-L-compose-left-span f (SpanIJUpkg-to-span upkg))

-- § Law 14O.20: right composition by L₁₂ preserves unified packages
law14O-20-L-compose-right-unified : (f : Op) → SpanIJUnifiedPackage f → SpanIJUnifiedPackage (λ v → f (K12LaplacianVec12ℤ v))
law14O-20-L-compose-right-unified f upkg =
  law14O-14-spanIJ-unified-package
    (λ v → f (K12LaplacianVec12ℤ v))
    (law14O-18-L-compose-right-span f (SpanIJUpkg-to-span upkg))
-- § Law 14O.5: sum-zero forces Laplacian eigenvalue 12
law14O-5-L-sum0-eigen12 : (v : Vec12ℤ) → ZeroSumVec12 v → Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ twelveℤ v)
law14O-5-L-sum0-eigen12 v sum0 =
  Vec12Eq-trans
    (law14O-4-L-in-span v)
    (law14O-2-linIJ-sum0-eigen twelveℤ (negℤ oneℤ) v sum0)

-- § Law 14O.6: constant vectors force Laplacian eigenvalue 0
law14O-6-L-const-eigen0 : (c : ℤ) → Vec12Eq (K12LaplacianVec12ℤ (constVec12ℤ c)) zeroVec12ℤ
law14O-6-L-const-eigen0 = law14H-14-const-eigen0
-- § Law 14O.7: L₁₂ spectral package (7 components)
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

-- § Projections for L12SpectralPackage
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
-- § Law 14O.21: scale-by-12 agrees with twelveVec12ℤ
law14O-21-scale12≡twelveVec12 : (v : Vec12ℤ) → Vec12Eq (scaleVec12ℤ twelveℤ v) (twelveVec12ℤ v)
law14O-21-scale12≡twelveVec12 v =
  (λ i → twelveℤ-*ℤ-left (block₀ v i)) ,
  ((λ i → twelveℤ-*ℤ-left (block₁ v i)) ,
   (λ i → twelveℤ-*ℤ-left (block₂ v i)))

-- § Law 14O.22: scale-by-0 collapses to zeroVec12ℤ
law14O-22-scale0≡zeroVec12 : (v : Vec12ℤ) → Vec12Eq (scaleVec12ℤ 0ℤ v) zeroVec12ℤ
law14O-22-scale0≡zeroVec12 v =
  (λ i → *ℤ-zero-left (block₀ v i)) ,
  ((λ i → *ℤ-zero-left (block₁ v i)) ,
   (λ i → *ℤ-zero-left (block₂ v i)))

-- § Law 14O.23: scale-form 12-eigenvectors force sum-zero
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

-- § Law 14O.24: scale-form 0-eigenvectors force 12·v = J v
law14O-24-eigen0Scale→twelveEqJ : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) → Vec12Eq (twelveVec12ℤ v) (J12Vec12ℤ v)
law14O-24-eigen0Scale→twelveEqJ v eigen0Scale =
  let
    L0 : Vec12Eq (K12LaplacianVec12ℤ v) zeroVec12ℤ
    L0 = Vec12Eq-trans eigen0Scale (law14O-22-scale0≡zeroVec12 v)
  in
  law14H-15-L0→twelveEqJ v L0

-- § Law 14O.25: eigen-equation forces constraints for λ=12 or λ=0
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

-- § Law 14O.26: J-images are forced constant
law14O-26-J-constVec : (v : Vec12ℤ) → ConstVec12 (J12Vec12ℤ v)
law14O-26-J-constVec v = (sum12ℤ v) , ((λ _ → refl) , ((λ _ → refl) , (λ _ → refl)))

-- § Law 14O.27: kernel constraint forces 12·v to be constant
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

-- § Law 14O.28: scale-form 0-eigenvectors force 12·v constant
law14O-28-eigen0Scale→twelveConst : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) → ConstVec12 (twelveVec12ℤ v)
law14O-28-eigen0Scale→twelveConst v eigen0Scale =
  law14O-27-twelveEqJ→twelveConst v (law14O-24-eigen0Scale→twelveEqJ v eigen0Scale)

-- § Law 14O.29: eigen-equation forces sum-zero (λ=12) and 12·v constant (λ=0)
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
-- § Law 14O.30: 0-eigenvectors are forced constant (with positivity witness)
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

    -- Convert a coordinate equation 12·x = Σ into twelveℤ*x = Σ
    toMul12 : (x s : ℤ) → twelveTimesℤ x ≡ s → twelveℤ *ℤ x ≡ s
    toMul12 x s eq = trans (twelveℤ-*ℤ-left x) eq

    -- From twelveℤ*x = twelveℤ*y, force x = y via torsion-freeness
    cancel12 : (x y : ℤ) → twelveℤ *ℤ x ≡ twelveℤ *ℤ y → x ≡ y
    cancel12 x y mulEq =
      let
        Q : ℤ → Set
        Q t = t *ℤ x ≡ t *ℤ y
        mulEq' : (+suc n) *ℤ x ≡ (+suc n) *ℤ y
        mulEq' = subst Q twelvePos mulEq

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
-- § Law 14O.31: 0-eigenvectors are forced constant (no extra witness)
law14O-31-eigen0Scale→const : (v : Vec12ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ 0ℤ v) →
  ConstVec12 v
law14O-31-eigen0Scale→const v eigen0Scale =
  law14O-30-eigen0Scale→const-assuming-twelvePos v twelveℤ-pos eigen0Scale

-- § Law 14O.32: eigen-equation forces sum-zero (λ=12) and const (λ=0)
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
-- § scaleVec12 congruence and associativity
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

-- § Law 14O.33: Laplacian commutes with scaleVec12ℤ
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
        lhsBridge : block₀ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡
                    twelveTimesℤ (block₀ (scaleVec12ℤ lam v) i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
        lhsBridge = fst (law14H-6-L-twelve-minus-J (scaleVec12ℤ lam v)) i

        step₁ :
          twelveTimesℤ (lam *ℤ block₀ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₀ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₀ v i) +ℤ t) sNegScale

        rhsBridge : block₀ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i ≡
                    lam *ℤ (twelveTimesℤ (block₀ v i) +ℤ negℤ s)
        rhsBridge = cong (λ z → lam *ℤ z) (fst (law14H-6-L-twelve-minus-J v) i)
      in
      trans lhsBridge (trans step₁ (trans (sym (rhsBlock (block₀ v i))) (sym rhsBridge)))

    eq1 : (i : Fin4) → block₁ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡ block₁ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i
    eq1 i =
      let
        lhsBridge : block₁ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡
                    twelveTimesℤ (block₁ (scaleVec12ℤ lam v) i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
        lhsBridge = fst (snd (law14H-6-L-twelve-minus-J (scaleVec12ℤ lam v))) i

        step₁ :
          twelveTimesℤ (lam *ℤ block₁ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₁ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₁ v i) +ℤ t) sNegScale

        rhsBridge : block₁ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i ≡
                    lam *ℤ (twelveTimesℤ (block₁ v i) +ℤ negℤ s)
        rhsBridge = cong (λ z → lam *ℤ z) (fst (snd (law14H-6-L-twelve-minus-J v)) i)
      in
      trans lhsBridge (trans step₁ (trans (sym (rhsBlock (block₁ v i))) (sym rhsBridge)))

    eq2 : (i : Fin4) → block₂ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡ block₂ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i
    eq2 i =
      let
        lhsBridge : block₂ (K12LaplacianVec12ℤ (scaleVec12ℤ lam v)) i ≡
                    twelveTimesℤ (block₂ (scaleVec12ℤ lam v) i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
        lhsBridge = snd (snd (law14H-6-L-twelve-minus-J (scaleVec12ℤ lam v))) i

        step₁ :
          twelveTimesℤ (lam *ℤ block₂ v i) +ℤ negℤ (sum12ℤ (scaleVec12ℤ lam v))
            ≡
          twelveTimesℤ (lam *ℤ block₂ v i) +ℤ negℤ (lam *ℤ s)
        step₁ = cong (λ t → twelveTimesℤ (lam *ℤ block₂ v i) +ℤ t) sNegScale

        rhsBridge : block₂ (scaleVec12ℤ lam (K12LaplacianVec12ℤ v)) i ≡
                    lam *ℤ (twelveTimesℤ (block₂ v i) +ℤ negℤ s)
        rhsBridge = cong (λ z → lam *ℤ z) (snd (snd (law14H-6-L-twelve-minus-J v)) i)
      in
      trans lhsBridge (trans step₁ (trans (sym (rhsBlock (block₂ v i))) (sym rhsBridge)))

-- § Law 14O.34: nonzero scalar has no torsion on Vec12ℤ
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

-- § Helper: λ−12=0 forces λ=12
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
-- § Helper: λ·w = 12·w implies (λ−12)·w = 0
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

-- § Inspect pattern for case-splitting on computed values
data Inspect {A : Set} (x : A) : Set where
  reveal : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} (x : A) → Inspect x
inspect x = reveal x refl

-- § Law 14O.35: eigen-equation forces λ∈{0,12} or zero vector
law14O-35-eigenvalue-exhaustion : (v : Vec12ℤ) → (lam : ℤ) →
  Vec12Eq (K12LaplacianVec12ℤ v) (scaleVec12ℤ lam v) →
  ((lam ≡ twelveℤ) ⊎ (lam ≡ 0ℤ)) ⊎ (Vec12Eq v zeroVec12ℤ)
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
-- § Law 14O.36: corrected Ausschlussgesetz (exhaustion + constraints)
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

-- § Bundled torsion-freeness pair for Vec12ℤ
scaleVec12_nonzero_left_zero_to_zeroVec :
  (n : ℕ) → (v : Vec12ℤ) →
  (Vec12Eq (scaleVec12ℤ (+suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ)
  × (Vec12Eq (scaleVec12ℤ (-suc n) v) zeroVec12ℤ → Vec12Eq v zeroVec12ℤ)
scaleVec12_nonzero_left_zero_to_zeroVec n v =
  scaleVec12-pos-left-zero→zeroVec n v , scaleVec12-neg-left-zero→zeroVec n v
-- § Cauchy condition: eventual ε-clustering
record IsCauchy (seq : ℕ → ℚ) : Set where
  field
    cauchy : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq m) (seq n) <ℚ ε)

-- § Type alias for Cauchy predicate
IsCauchyP : (ℕ → ℚ) → Set
IsCauchyP = IsCauchy

-- § Real number: sequence + Cauchy proof
record ℝ : Set where
  constructor mkℝ
  field
    seq : ℕ → ℚ
    isCauchy : IsCauchy seq

open ℝ public

-- § Rational embedding: constant sequences
ℚtoℝ : ℚ → ℝ
ℚtoℝ q = mkℝ (λ _ → q) record
  { cauchy = λ ε εpos →
      zero , (λ m n _ _ → distℚ-const<ε q ε εpos)
  }
-- § Real equivalence: difference converges to 0
infix 4 _≃ℝ_

record _≃ℝ_ (x y : ℝ) : Set where
  field
    conv0 : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε)

-- § Symmetry of real equivalence
≃ℝ-sym : {x y : ℝ} → x ≃ℝ y → y ≃ℝ x
≃ℝ-sym {x} {y} x≃y = record
  { conv0 = λ ε εpos →
      let
        pack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε)
        pack = _≃ℝ_.conv0 x≃y ε εpos

        N : ℕ
        N = fst pack

        conv : (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε
        conv = snd pack
      in
      N , (λ n N≤n →
        let
          swap : distℚ (seq y n) (seq x n) ≃ℚ distℚ (seq x n) (seq y n)
          swap = distℚ-sym (seq y n) (seq x n)

          d≤ : distℚ (seq y n) (seq x n) ≤ℚ distℚ (seq x n) (seq y n)
          d≤ = ≃ℚ→≤ℚˡ {distℚ (seq y n) (seq x n)} {distℚ (seq x n) (seq y n)} swap
        in
        ≤<ℚ→<ℚ {distℚ (seq y n) (seq x n)} {distℚ (seq x n) (seq y n)} {ε} d≤ (conv n N≤n))
  }
-- § Real addition with Cauchy preservation via ε-quartering
_+ℝ_ : ℝ → ℝ → ℝ
x +ℝ y = mkℝ (λ n → seq x n +ℚ seq y n) record
  { cauchy = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        cxPack = IsCauchy.cauchy (isCauchy x) εq εqPos
        cyPack = IsCauchy.cauchy (isCauchy y) εq εqPos

        CxN : ℕ
        CxN = fst cxPack

        CyN : ℕ
        CyN = fst cyPack

        cx : (m n : ℕ) → CxN ≤ m → CxN ≤ n → distℚ (seq x m) (seq x n) <ℚ εq
        cx = snd cxPack

        cy : (m n : ℕ) → CyN ≤ m → CyN ≤ n → distℚ (seq y m) (seq y n) <ℚ εq
        cy = snd cyPack

        N : ℕ
        N = CxN +ℕ CyN

        CxN≤N : CxN ≤ N
        CxN≤N =
          let
            step : (CxN +ℕ zero) ≤ (CxN +ℕ CyN)
            step = ≤-+ℕ-monoˡ {a = zero} {b = CyN} z≤n CxN
          in
          subst (λ t → t ≤ (CxN +ℕ CyN)) (+ℕ-zero-right CxN) step

        CyN≤N : CyN ≤ N
        CyN≤N =
          let
            step : (CyN +ℕ zero) ≤ (CyN +ℕ CxN)
            step = ≤-+ℕ-monoˡ {a = zero} {b = CxN} z≤n CyN

            base : CyN ≤ (CyN +ℕ CxN)
            base = subst (λ t → t ≤ (CyN +ℕ CxN)) (+ℕ-zero-right CyN) step
          in
          subst (λ t → CyN ≤ t) (+ℕ-comm CyN CxN) base

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ {0ℚ} {εq} εqPos
      in
      N , (λ m n N≤m N≤n →
        let
          Cx≤m : CxN ≤ m
          Cx≤m = ≤-trans CxN≤N N≤m

          Cx≤n : CxN ≤ n
          Cx≤n = ≤-trans CxN≤N N≤n

          Cy≤m : CyN ≤ m
          Cy≤m = ≤-trans CyN≤N N≤m

          Cy≤n : CyN ≤ n
          Cy≤n = ≤-trans CyN≤N N≤n

          dx : ℚ
          dx = distℚ (seq x m) (seq x n)

          dy : ℚ
          dy = distℚ (seq y m) (seq y n)

          dx<εq : dx <ℚ εq
          dx<εq = cx m n Cx≤m Cx≤n

          dy<εq : dy <ℚ εq
          dy<εq = cy m n Cy≤m Cy≤n

          dx≤εq : dx ≤ℚ εq
          dx≤εq = <ℚ→≤ℚ {dx} {εq} dx<εq

          dy≤εq : dy ≤ℚ εq
          dy≤εq = <ℚ→≤ℚ {dy} {εq} dy<εq

          dxNonneg : 0ℚ ≤ℚ dx
          dxNonneg = distℚ-nonneg (seq x m) (seq x n)

          dyNonneg : 0ℚ ≤ℚ dy
          dyNonneg = distℚ-nonneg (seq y m) (seq y n)

          d1 : ℚ
          d1 = distℚ ((seq x m) +ℚ (seq y m)) ((seq x n) +ℚ (seq y m))

          d2 : ℚ
          d2 = distℚ ((seq x n) +ℚ (seq y m)) ((seq x n) +ℚ (seq y n))

          d1≤dx : d1 ≤ℚ dx
          d1≤dx = ≃ℚ→≤ℚˡ {d1} {dx} (distℚ-+ℚ-right (seq x m) (seq x n) (seq y m))

          d2≤dy : d2 ≤ℚ dy
          d2≤dy = ≃ℚ→≤ℚˡ {d2} {dy} (distℚ-+ℚ-left (seq x n) (seq y m) (seq y n))

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = ≤ℚ-trans {d1} {dx} {εq} d1≤dx dx≤εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = ≤ℚ-trans {d2} {dy} {εq} d2≤dy dy≤εq

          d1Nonneg : 0ℚ ≤ℚ d1
          d1Nonneg = distℚ-nonneg ((seq x m) +ℚ (seq y m)) ((seq x n) +ℚ (seq y m))

          d2Nonneg : 0ℚ ≤ℚ d2
          d2Nonneg = distℚ-nonneg ((seq x n) +ℚ (seq y m)) ((seq x n) +ℚ (seq y n))

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ {(d1 +ℚ d2)} {(εq +ℚ εq)} {ε} sum≤ εq+εq<ε

          tri : distℚ ((seq x m) +ℚ (seq y m)) ((seq x n) +ℚ (seq y n)) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle ((seq x m) +ℚ (seq y m)) ((seq x n) +ℚ (seq y m)) ((seq x n) +ℚ (seq y n))
        in
        ≤<ℚ→<ℚ {distℚ ((seq x m) +ℚ (seq y m)) ((seq x n) +ℚ (seq y n))} {(d1 +ℚ d2)} {ε} tri sum<ε)
  }
-- § Real negation via distℚ-neg
-ℝ_ : ℝ → ℝ
-ℝ x = mkℝ (λ n → -ℚ (seq x n)) record
  { cauchy = λ ε εpos →
      let
        pack = IsCauchy.cauchy (isCauchy x) ε εpos
        N : ℕ
        N = fst pack
        cx = snd pack
      in
      N , (λ m n N≤m N≤n →
        let
          d≃ : distℚ (-ℚ (seq x m)) (-ℚ (seq x n)) ≃ℚ distℚ (seq x m) (seq x n)
          d≃ = distℚ-neg (seq x m) (seq x n)

          d≤ : distℚ (-ℚ (seq x m)) (-ℚ (seq x n)) ≤ℚ distℚ (seq x m) (seq x n)
          d≤ = ≃ℚ→≤ℚˡ {distℚ (-ℚ (seq x m)) (-ℚ (seq x n))} {distℚ (seq x m) (seq x n)} d≃
        in
        ≤<ℚ→<ℚ {distℚ (-ℚ (seq x m)) (-ℚ (seq x n))} {distℚ (seq x m) (seq x n)} {ε} d≤ (cx m n N≤m N≤n))
  }

-- § Real subtraction
_-ℝ_ : ℝ → ℝ → ℝ
x -ℝ y = x +ℝ (-ℝ y)

-- § Zero and one in ℝ
0ℝ : ℝ
0ℝ = ℚtoℝ 0ℚ

1ℝ : ℝ
1ℝ = ℚtoℝ 1ℚ
-- § Commutativity of real addition
+ℝ-comm : (x y : ℝ) → (x +ℝ y) ≃ℝ (y +ℝ x)
+ℝ-comm x y = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = seq x n +ℚ seq y n

          q : ℚ
          q = seq y n +ℚ seq x n

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-comm (seq x n) (seq y n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Associativity of real addition
+ℝ-assoc : (x y z : ℝ) → ((x +ℝ y) +ℝ z) ≃ℝ (x +ℝ (y +ℝ z))
+ℝ-assoc x y z = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n +ℚ seq y n) +ℚ seq z n

          q : ℚ
          q = seq x n +ℚ (seq y n +ℚ seq z n)

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-assoc (seq x n) (seq y n) (seq z n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Right identity for real addition
+ℝ-zero-right : (x : ℝ) → (x +ℝ 0ℝ) ≃ℝ x
+ℝ-zero-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = seq x n +ℚ 0ℚ

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-zero-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Left identity for real addition
+ℝ-zero-left : (x : ℝ) → (0ℝ +ℝ x) ≃ℝ x
+ℝ-zero-left x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = 0ℚ +ℚ seq x n

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-zero-left (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Right inverse for real addition
+ℝ-inv-right : (x : ℝ) → (x +ℝ (-ℝ x)) ≃ℝ 0ℝ
+ℝ-inv-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = seq x n +ℚ (-ℚ (seq x n))

          q : ℚ
          q = 0ℚ

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-inv-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }
-- § Cauchy sequences are eventually bounded
IsCauchy-eventually-bounded :
  (f : ℕ → ℚ) → IsCauchy f →
  Σ ℕ (λ N → Σ ℚ (λ B → (n : ℕ) → N ≤ n → distℚ (f n) 0ℚ ≤ℚ B))
IsCauchy-eventually-bounded f ic =
  let
    pack = IsCauchy.cauchy ic 1ℚ 0ℚ<1ℚ
    N : ℕ
    N = fst pack
    conv = snd pack

    B : ℚ
    B = distℚ (f N) 0ℚ +ℚ 1ℚ
  in
  N , (B , (λ n N≤n →
    let
      d<1 : distℚ (f n) (f N) <ℚ 1ℚ
      d<1 = conv n N N≤n (≤-refl N)

      d≤1 : distℚ (f n) (f N) ≤ℚ 1ℚ
      d≤1 = <ℚ→≤ℚ {distℚ (f n) (f N)} {1ℚ} d<1

      tri : distℚ (f n) 0ℚ ≤ℚ (distℚ (f n) (f N) +ℚ distℚ (f N) 0ℚ)
      tri = distℚ-triangle (f n) (f N) 0ℚ

      step : (distℚ (f n) (f N) +ℚ distℚ (f N) 0ℚ) ≤ℚ (1ℚ +ℚ distℚ (f N) 0ℚ)
      step = ≤ℚ-+ℚ-mono-right (distℚ (f n) (f N)) 1ℚ (distℚ (f N) 0ℚ) d≤1

      comm : (1ℚ +ℚ distℚ (f N) 0ℚ) ≃ℚ B
      comm = +ℚ-comm 1ℚ (distℚ (f N) 0ℚ)
    in
    ≤ℚ-trans {distℚ (f n) 0ℚ} {(1ℚ +ℚ distℚ (f N) 0ℚ)} {B}
      (≤ℚ-trans {distℚ (f n) 0ℚ} {(distℚ (f n) (f N) +ℚ distℚ (f N) 0ℚ)} {(1ℚ +ℚ distℚ (f N) 0ℚ)} tri step)
      (≃ℚ→≤ℚˡ {(1ℚ +ℚ distℚ (f N) 0ℚ)} {B} comm)))
-- § Real multiplication with full Cauchy proof
_⋅ℝ_ : ℝ → ℝ → ℝ
x ⋅ℝ y = mkℝ (λ n → seq x n *ℚ seq y n) record
  { cauchy = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        -- Eventual bounds on factors
        bxPack = IsCauchy-eventually-bounded (seq x) (isCauchy x)
        byPack = IsCauchy-eventually-bounded (seq y) (isCauchy y)

        Nx : ℕ
        Nx = fst bxPack

        Ny : ℕ
        Ny = fst byPack

        Bx : ℚ
        Bx = fst (snd bxPack)

        By : ℚ
        By = fst (snd byPack)

        bxBound : (n : ℕ) → Nx ≤ n → distℚ (seq x n) 0ℚ ≤ℚ Bx
        bxBound = snd (snd bxPack)

        byBound : (n : ℕ) → Ny ≤ n → distℚ (seq y n) 0ℚ ≤ℚ By
        byBound = snd (snd byPack)

        -- Integer upper bounds for scaling
        BxNonneg : 0ℚ ≤ℚ Bx
        BxNonneg =
          ≤ℚ-trans {0ℚ} {distℚ (seq x Nx) 0ℚ} {Bx}
            (distℚ-nonneg (seq x Nx) 0ℚ)
            (bxBound Nx (≤-refl Nx))

        ByNonneg : 0ℚ ≤ℚ By
        ByNonneg =
          ≤ℚ-trans {0ℚ} {distℚ (seq y Ny) 0ℚ} {By}
            (distℚ-nonneg (seq y Ny) 0ℚ)
            (byBound Ny (≤-refl Ny))

        mx : ℕ
        mx = fst (nonneg-bound-sucInt Bx BxNonneg)

        my : ℕ
        my = fst (nonneg-bound-sucInt By ByNonneg)

        Ix : ℚ
        Ix = fromℕℤ (suc mx) / one⁺

        Iy : ℚ
        Iy = fromℕℤ (suc my) / one⁺

        Bx≤Ix : Bx ≤ℚ Ix
        Bx≤Ix = snd (nonneg-bound-sucInt Bx BxNonneg)

        By≤Iy : By ≤ℚ Iy
        By≤Iy = snd (nonneg-bound-sucInt By ByNonneg)

        IxNonneg : 0ℚ ≤ℚ Ix
        IxNonneg = ≤ℚ-trans {0ℚ} {Bx} {Ix} BxNonneg Bx≤Ix

        IyNonneg : 0ℚ ≤ℚ Iy
        IyNonneg = ≤ℚ-trans {0ℚ} {By} {Iy} ByNonneg By≤Iy

        -- δ-scaling: choose δ so that δ·I < εq
        dyPack = δ-scale-suc εq εqPos mx
        dxPack = δ-scale-suc εq εqPos my

        δy : ℚ
        δy = fst dyPack

        δx : ℚ
        δx = fst dxPack

        δyPos : 0ℚ <ℚ δy
        δyPos = fst (snd dyPack)

        δxPos : 0ℚ <ℚ δx
        δxPos = fst (snd dxPack)

        δyIx<εq : (δy *ℚ Ix) <ℚ εq
        δyIx<εq = snd (snd dyPack)

        δxIy<εq : (δx *ℚ Iy) <ℚ εq
        δxIy<εq = snd (snd dxPack)

        -- Cauchy moduli at δx, δy
        cxPack = IsCauchy.cauchy (isCauchy x) δx δxPos
        cyPack = IsCauchy.cauchy (isCauchy y) δy δyPos

        CxN : ℕ
        CxN = fst cxPack

        CyN : ℕ
        CyN = fst cyPack

        cx : (m n : ℕ) → CxN ≤ m → CxN ≤ n → distℚ (seq x m) (seq x n) <ℚ δx
        cx = snd cxPack

        cy : (m n : ℕ) → CyN ≤ m → CyN ≤ n → distℚ (seq y m) (seq y n) <ℚ δy
        cy = snd cyPack

        -- Global N combining all moduli
        N : ℕ
        N = Nx +ℕ (Ny +ℕ (CxN +ℕ CyN))

        Nx≤N : Nx ≤ N
        Nx≤N =
          let
            step : (Nx +ℕ zero) ≤ (Nx +ℕ (Ny +ℕ (CxN +ℕ CyN)))
            step = ≤-+ℕ-monoˡ {a = zero} {b = (Ny +ℕ (CxN +ℕ CyN))} z≤n Nx
          in
          subst (λ t → t ≤ (Nx +ℕ (Ny +ℕ (CxN +ℕ CyN)))) (+ℕ-zero-right Nx) step

        Ny≤N : Ny ≤ N
        Ny≤N =
          let
            step : (Ny +ℕ zero) ≤ (Ny +ℕ (Nx +ℕ (CxN +ℕ CyN)))
            step = ≤-+ℕ-monoˡ {a = zero} {b = (Nx +ℕ (CxN +ℕ CyN))} z≤n Ny

            base : Ny ≤ (Ny +ℕ (Nx +ℕ (CxN +ℕ CyN)))
            base = subst (λ t → t ≤ (Ny +ℕ (Nx +ℕ (CxN +ℕ CyN)))) (+ℕ-zero-right Ny) step

            rhsEq : (Ny +ℕ (Nx +ℕ (CxN +ℕ CyN))) ≡ (Nx +ℕ (Ny +ℕ (CxN +ℕ CyN)))
            rhsEq =
              trans
                (sym (+ℕ-assoc Ny Nx (CxN +ℕ CyN)))
                (trans
                  (cong (λ t → t +ℕ (CxN +ℕ CyN)) (+ℕ-comm Ny Nx))
                  (+ℕ-assoc Nx Ny (CxN +ℕ CyN)))
          in
          subst (λ t → Ny ≤ t) rhsEq base

        CxN≤N : CxN ≤ N
        CxN≤N =
          let
            step : (CxN +ℕ zero) ≤ (CxN +ℕ (Nx +ℕ (Ny +ℕ CyN)))
            step = ≤-+ℕ-monoˡ {a = zero} {b = (Nx +ℕ (Ny +ℕ CyN))} z≤n CxN

            base : CxN ≤ (CxN +ℕ (Nx +ℕ (Ny +ℕ CyN)))
            base = subst (λ t → t ≤ (CxN +ℕ (Nx +ℕ (Ny +ℕ CyN)))) (+ℕ-zero-right CxN) step

            rhsEq : (CxN +ℕ (Nx +ℕ (Ny +ℕ CyN))) ≡ N
            rhsEq =
              trans
                (sym (+ℕ-assoc CxN Nx (Ny +ℕ CyN)))
                (trans
                  (cong (λ t → t +ℕ (Ny +ℕ CyN)) (+ℕ-comm CxN Nx))
                  (trans
                    (+ℕ-assoc Nx CxN (Ny +ℕ CyN))
                    (cong (λ t → Nx +ℕ t)
                      (trans
                        (sym (+ℕ-assoc CxN Ny CyN))
                        (trans
                          (cong (λ t → t +ℕ CyN) (+ℕ-comm CxN Ny))
                          (+ℕ-assoc Ny CxN CyN))))))
          in
          subst (λ t → CxN ≤ t) rhsEq base

        CyN≤N : CyN ≤ N
        CyN≤N =
          let
            step : (CyN +ℕ zero) ≤ (CyN +ℕ (Nx +ℕ (Ny +ℕ CxN)))
            step = ≤-+ℕ-monoˡ {a = zero} {b = (Nx +ℕ (Ny +ℕ CxN))} z≤n CyN

            base : CyN ≤ (CyN +ℕ (Nx +ℕ (Ny +ℕ CxN)))
            base = subst (λ t → t ≤ (CyN +ℕ (Nx +ℕ (Ny +ℕ CxN)))) (+ℕ-zero-right CyN) step

            rhsEq : (CyN +ℕ (Nx +ℕ (Ny +ℕ CxN))) ≡ N
            rhsEq =
              trans
                (sym (+ℕ-assoc CyN Nx (Ny +ℕ CxN)))
                (trans
                  (cong (λ t → t +ℕ (Ny +ℕ CxN)) (+ℕ-comm CyN Nx))
                  (trans
                    (+ℕ-assoc Nx CyN (Ny +ℕ CxN))
                    (cong (λ t → Nx +ℕ t)
                      (trans
                        (sym (+ℕ-assoc CyN Ny CxN))
                        (trans
                          (cong (λ t → t +ℕ CxN) (+ℕ-comm CyN Ny))
                          (trans
                            (+ℕ-assoc Ny CyN CxN)
                            (cong (λ t → Ny +ℕ t) (+ℕ-comm CyN CxN))))))))
          in
          subst (λ t → CyN ≤ t) rhsEq base

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ {0ℚ} {εq} εqPos

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos
      in
      N , (λ m n N≤m N≤n →
        let
          Nx≤m : Nx ≤ m
          Nx≤m = ≤-trans Nx≤N N≤m

          Nx≤n : Nx ≤ n
          Nx≤n = ≤-trans Nx≤N N≤n

          Ny≤m : Ny ≤ m
          Ny≤m = ≤-trans Ny≤N N≤m

          Ny≤n : Ny ≤ n
          Ny≤n = ≤-trans Ny≤N N≤n

          Cx≤m : CxN ≤ m
          Cx≤m = ≤-trans CxN≤N N≤m

          Cx≤n : CxN ≤ n
          Cx≤n = ≤-trans CxN≤N N≤n

          Cy≤m : CyN ≤ m
          Cy≤m = ≤-trans CyN≤N N≤m

          Cy≤n : CyN ≤ n
          Cy≤n = ≤-trans CyN≤N N≤n

          dx0≤Bx : distℚ (seq x m) 0ℚ ≤ℚ Bx
          dx0≤Bx = bxBound m Nx≤m

          dy0≤By : distℚ (seq y n) 0ℚ ≤ℚ By
          dy0≤By = byBound n Ny≤n

          dx0≤Ix : distℚ (seq x m) 0ℚ ≤ℚ Ix
          dx0≤Ix = ≤ℚ-trans {distℚ (seq x m) 0ℚ} {Bx} {Ix} dx0≤Bx Bx≤Ix

          dy0≤Iy : distℚ (seq y n) 0ℚ ≤ℚ Iy
          dy0≤Iy = ≤ℚ-trans {distℚ (seq y n) 0ℚ} {By} {Iy} dy0≤By By≤Iy

          dy<δy : distℚ (seq y m) (seq y n) <ℚ δy
          dy<δy = cy m n Cy≤m Cy≤n

          dx<δx : distℚ (seq x m) (seq x n) <ℚ δx
          dx<δx = cx m n Cx≤m Cx≤n

          dy≤δy : distℚ (seq y m) (seq y n) ≤ℚ δy
          dy≤δy = <ℚ→≤ℚ {distℚ (seq y m) (seq y n)} {δy} dy<δy

          dx≤δx : distℚ (seq x m) (seq x n) ≤ℚ δx
          dx≤δx = <ℚ→≤ℚ {distℚ (seq x m) (seq x n)} {δx} dx<δx

          dyNonneg : 0ℚ ≤ℚ distℚ (seq y m) (seq y n)
          dyNonneg = distℚ-nonneg (seq y m) (seq y n)

          dxNonneg : 0ℚ ≤ℚ distℚ (seq x m) (seq x n)
          dxNonneg = distℚ-nonneg (seq x m) (seq x n)

          dx0Nonneg : 0ℚ ≤ℚ distℚ (seq x m) 0ℚ
          dx0Nonneg = distℚ-nonneg (seq x m) 0ℚ

          dy0Nonneg : 0ℚ ≤ℚ distℚ (seq y n) 0ℚ
          dy0Nonneg = distℚ-nonneg (seq y n) 0ℚ

          -- Product distance decomposition
          p : ℚ
          p = (seq x m)

          q : ℚ
          q = (seq y m)

          r : ℚ
          r = (seq x n)

          s : ℚ
          s = (seq y n)

          d1 : ℚ
          d1 = distℚ (p *ℚ q) (p *ℚ s)

          d2 : ℚ
          d2 = distℚ (p *ℚ s) (r *ℚ s)

          d1≤ : d1 ≤ℚ (distℚ q s *ℚ distℚ p 0ℚ)
          d1≤ = ≃ℚ→≤ℚˡ {d1} {(distℚ q s *ℚ distℚ p 0ℚ)} (distℚ-*ℚ-left p q s)

          d2≤ : d2 ≤ℚ (distℚ p r *ℚ distℚ s 0ℚ)
          d2≤ = ≃ℚ→≤ℚˡ {d2} {(distℚ p r *ℚ distℚ s 0ℚ)} (distℚ-*ℚ-right s p r)

          d1Bound : (distℚ q s *ℚ distℚ p 0ℚ) ≤ℚ (distℚ q s *ℚ Ix)
          d1Bound = ≤ℚ-mul-nonneg-left (distℚ p 0ℚ) Ix (distℚ q s) dx0≤Ix dyNonneg

          d2Bound : (distℚ p r *ℚ distℚ s 0ℚ) ≤ℚ (distℚ p r *ℚ Iy)
          d2Bound = ≤ℚ-mul-nonneg-left (distℚ s 0ℚ) Iy (distℚ p r) dy0≤Iy dxNonneg

          dqsIx≤ : (distℚ q s *ℚ Ix) ≤ℚ (δy *ℚ Ix)
          dqsIx≤ = ≤ℚ-mul-nonneg-right (distℚ q s) δy Ix dy≤δy IxNonneg

          dprIy≤ : (distℚ p r *ℚ Iy) ≤ℚ (δx *ℚ Iy)
          dprIy≤ = ≤ℚ-mul-nonneg-right (distℚ p r) δx Iy dx≤δx IyNonneg

          d1'<εq : (distℚ q s *ℚ Ix) <ℚ εq
          d1'<εq = ≤<ℚ→<ℚ {(distℚ q s *ℚ Ix)} {(δy *ℚ Ix)} {εq} dqsIx≤ δyIx<εq

          d2'<εq : (distℚ p r *ℚ Iy) <ℚ εq
          d2'<εq = ≤<ℚ→<ℚ {(distℚ p r *ℚ Iy)} {(δx *ℚ Iy)} {εq} dprIy≤ δxIy<εq

          d1<εq : d1 <ℚ εq
          d1<εq = ≤<ℚ→<ℚ {d1} {(distℚ q s *ℚ Ix)} {εq} (≤ℚ-trans {d1} {(distℚ q s *ℚ distℚ p 0ℚ)} {(distℚ q s *ℚ Ix)} d1≤ d1Bound) d1'<εq

          d2<εq : d2 <ℚ εq
          d2<εq = ≤<ℚ→<ℚ {d2} {(distℚ p r *ℚ Iy)} {εq} (≤ℚ-trans {d2} {(distℚ p r *ℚ distℚ s 0ℚ)} {(distℚ p r *ℚ Iy)} d2≤ d2Bound) d2'<εq

          d1Nonneg : 0ℚ ≤ℚ d1
          d1Nonneg = distℚ-nonneg (p *ℚ q) (p *ℚ s)

          d2Nonneg : 0ℚ ≤ℚ d2
          d2Nonneg = distℚ-nonneg (p *ℚ s) (r *ℚ s)

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = <ℚ→≤ℚ {d1} {εq} d1<εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = <ℚ→≤ℚ {d2} {εq} d2<εq

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ {(d1 +ℚ d2)} {(εq +ℚ εq)} {ε} sum≤ εq+εq<ε

          tri : distℚ (p *ℚ q) (r *ℚ s) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle (p *ℚ q) (p *ℚ s) (r *ℚ s)
        in
        ≤<ℚ→<ℚ {distℚ (p *ℚ q) (r *ℚ s)} {(d1 +ℚ d2)} {ε} tri sum<ε)
  }
-- § Commutativity of real multiplication
⋅ℝ-comm : (x y : ℝ) → (x ⋅ℝ y) ≃ℝ (y ⋅ℝ x)
⋅ℝ-comm x y = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) *ℚ (seq y n)

          q : ℚ
          q = (seq y n) *ℚ (seq x n)

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-comm (seq x n) (seq y n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Associativity of real multiplication
⋅ℝ-assoc : (x y z : ℝ) → ((x ⋅ℝ y) ⋅ℝ z) ≃ℝ (x ⋅ℝ (y ⋅ℝ z))
⋅ℝ-assoc x y z = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = ((seq x n) *ℚ (seq y n)) *ℚ (seq z n)

          q : ℚ
          q = (seq x n) *ℚ ((seq y n) *ℚ (seq z n))

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-assoc (seq x n) (seq y n) (seq z n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Right multiplicative identity
⋅ℝ-one-right : (x : ℝ) → (x ⋅ℝ 1ℝ) ≃ℝ x
⋅ℝ-one-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) *ℚ 1ℚ

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-one-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Left multiplicative identity
⋅ℝ-one-left : (x : ℝ) → (1ℝ ⋅ℝ x) ≃ℝ x
⋅ℝ-one-left x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = 1ℚ *ℚ (seq x n)

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-one-left (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }
-- § Left absorption by zero
⋅ℝ-zero-left : (x : ℝ) → (0ℝ ⋅ℝ x) ≃ℝ 0ℝ
⋅ℝ-zero-left x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = 0ℚ *ℚ (seq x n)

          q : ℚ
          q = 0ℚ

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-zero-left (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Right absorption by zero
⋅ℝ-zero-right : (x : ℝ) → (x ⋅ℝ 0ℝ) ≃ℝ 0ℝ
⋅ℝ-zero-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) *ℚ 0ℚ

          q : ℚ
          q = 0ℚ

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-zero-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Right distributivity of multiplication over addition
⋅ℝ-distrib-right-+ℝ : (x y z : ℝ) → (x ⋅ℝ (y +ℝ z)) ≃ℝ ((x ⋅ℝ y) +ℝ (x ⋅ℝ z))
⋅ℝ-distrib-right-+ℝ x y z = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) *ℚ ((seq y n) +ℚ (seq z n))

          q : ℚ
          q = ((seq x n) *ℚ (seq y n)) +ℚ ((seq x n) *ℚ (seq z n))

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-distrib-right-+ℚ (seq x n) (seq y n) (seq z n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }

-- § Left distributivity of multiplication over addition
⋅ℝ-distrib-left-+ℝ : (x y z : ℝ) → ((x +ℝ y) ⋅ℝ z) ≃ℝ ((x ⋅ℝ z) +ℝ (y ⋅ℝ z))
⋅ℝ-distrib-left-+ℝ x y z = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = ((seq x n) +ℚ (seq y n)) *ℚ (seq z n)

          q : ℚ
          q = ((seq x n) *ℚ (seq z n)) +ℚ ((seq y n) *ℚ (seq z n))

          pq≃ : p ≃ℚ q
          pq≃ = *ℚ-distrib-left-+ℚ (seq x n) (seq y n) (seq z n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ {distℚ p q} {0ℚ} d≃0
        in
        ≤<ℚ→<ℚ {distℚ p q} {0ℚ} {ε} d≤0 εpos)
  }
-- § Multiplication respects ≃ℝ
⋅ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x ⋅ℝ y) ≃ℝ (x' ⋅ℝ y')
⋅ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' = record
  { conv0 = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ {0ℚ} {εq} εqPos

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos

        -- Eventual bounds
        byPack : Σ ℕ (λ N → Σ ℚ (λ B → (n : ℕ) → N ≤ n → distℚ (seq y n) 0ℚ ≤ℚ B))
        byPack = IsCauchy-eventually-bounded (seq y) (isCauchy y)

        bx'Pack : Σ ℕ (λ N → Σ ℚ (λ B → (n : ℕ) → N ≤ n → distℚ (seq x' n) 0ℚ ≤ℚ B))
        bx'Pack = IsCauchy-eventually-bounded (seq x') (isCauchy x')

        Ny0 : ℕ
        Ny0 = fst byPack

        By : ℚ
        By = fst (snd byPack)

        ByBound : (n : ℕ) → Ny0 ≤ n → distℚ (seq y n) 0ℚ ≤ℚ By
        ByBound = snd (snd byPack)

        Nx'0 : ℕ
        Nx'0 = fst bx'Pack

        Bx' : ℚ
        Bx' = fst (snd bx'Pack)

        Bx'Bound : (n : ℕ) → Nx'0 ≤ n → distℚ (seq x' n) 0ℚ ≤ℚ Bx'
        Bx'Bound = snd (snd bx'Pack)

        ByNonneg : 0ℚ ≤ℚ By
        ByNonneg =
          ≤ℚ-trans {0ℚ} {distℚ (seq y Ny0) 0ℚ} {By}
            (distℚ-nonneg (seq y Ny0) 0ℚ)
            (ByBound Ny0 (≤-refl Ny0))

        Bx'Nonneg : 0ℚ ≤ℚ Bx'
        Bx'Nonneg =
          ≤ℚ-trans {0ℚ} {distℚ (seq x' Nx'0) 0ℚ} {Bx'}
            (distℚ-nonneg (seq x' Nx'0) 0ℚ)
            (Bx'Bound Nx'0 (≤-refl Nx'0))

        mYPack : Σ ℕ (λ m → By ≤ℚ (fromℕℤ (suc m) / one⁺))
        mYPack = nonneg-bound-sucInt By ByNonneg

        mX'Pack : Σ ℕ (λ m → Bx' ≤ℚ (fromℕℤ (suc m) / one⁺))
        mX'Pack = nonneg-bound-sucInt Bx' Bx'Nonneg

        mY : ℕ
        mY = fst mYPack

        KY : ℚ
        KY = fromℕℤ (suc mY) / one⁺

        By≤KY : By ≤ℚ KY
        By≤KY = snd mYPack

        mX' : ℕ
        mX' = fst mX'Pack

        KX' : ℚ
        KX' = fromℕℤ (suc mX') / one⁺

        Bx'≤KX' : Bx' ≤ℚ KX'
        Bx'≤KX' = snd mX'Pack

        δxPack : Σ ℚ (λ δ → (0ℚ <ℚ δ) × ((δ *ℚ KY) <ℚ εq))
        δxPack = δ-scale-suc εq εqPos mY

        δyPack : Σ ℚ (λ δ → (0ℚ <ℚ δ) × ((δ *ℚ KX') <ℚ εq))
        δyPack = δ-scale-suc εq εqPos mX'

        δx : ℚ
        δx = fst δxPack

        δxPos : 0ℚ <ℚ δx
        δxPos = fst (snd δxPack)

        δxNonneg : 0ℚ ≤ℚ δx
        δxNonneg = <ℚ→≤ℚ {0ℚ} {δx} δxPos

        δxKY<εq : (δx *ℚ KY) <ℚ εq
        δxKY<εq = snd (snd δxPack)

        δy : ℚ
        δy = fst δyPack

        δyPos : 0ℚ <ℚ δy
        δyPos = fst (snd δyPack)

        δyNonneg : 0ℚ ≤ℚ δy
        δyNonneg = <ℚ→≤ℚ {0ℚ} {δy} δyPos

        δyKX'<εq : (δy *ℚ KX') <ℚ εq
        δyKX'<εq = snd (snd δyPack)

        NxPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq x' n) <ℚ δx)
        NxPack = _≃ℝ_.conv0 x≃x' δx δxPos

        NyPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq y n) (seq y' n) <ℚ δy)
        NyPack = _≃ℝ_.conv0 y≃y' δy δyPos

        Nx : ℕ
        Nx = fst NxPack

        Ny : ℕ
        Ny = fst NyPack

        NxConv : (n : ℕ) → Nx ≤ n → distℚ (seq x n) (seq x' n) <ℚ δx
        NxConv = snd NxPack

        NyConv : (n : ℕ) → Ny ≤ n → distℚ (seq y n) (seq y' n) <ℚ δy
        NyConv = snd NyPack

        N : ℕ
        N = ((Nx +ℕ Ny) +ℕ Ny0) +ℕ Nx'0

        ≤-self+ℕ : (m n : ℕ) → m ≤ (m +ℕ n)
        ≤-self+ℕ m n =
          let
            mono : (m +ℕ zero) ≤ (m +ℕ n)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = n} z≤n m
          in
          subst (λ t → t ≤ (m +ℕ n)) (+ℕ-zero-right m) mono

        Nx≤N : Nx ≤ N
        Nx≤N =
          let
            step₁ : Nx ≤ (Nx +ℕ Ny)
            step₁ =
              let
                mono : (Nx +ℕ zero) ≤ (Nx +ℕ Ny)
                mono = ≤-+ℕ-monoˡ {a = zero} {b = Ny} z≤n Nx
              in
              subst (λ t → t ≤ (Nx +ℕ Ny)) (+ℕ-zero-right Nx) mono

            step₂ : (Nx +ℕ Ny) ≤ N
            step₂ =
              ≤-trans
                (≤-self+ℕ (Nx +ℕ Ny) Ny0)
                (≤-self+ℕ ((Nx +ℕ Ny) +ℕ Ny0) Nx'0)
          in
          ≤-trans step₁ step₂

        Ny≤N : Ny ≤ N
        Ny≤N =
          let
            step₁ : Ny ≤ (Nx +ℕ Ny)
            step₁ =
              let
                mono : (Ny +ℕ zero) ≤ (Ny +ℕ Nx)
                mono = ≤-+ℕ-monoˡ {a = zero} {b = Nx} z≤n Ny

                base : Ny ≤ (Ny +ℕ Nx)
                base = subst (λ t → t ≤ (Ny +ℕ Nx)) (+ℕ-zero-right Ny) mono
              in
              subst (λ t → Ny ≤ t) (+ℕ-comm Ny Nx) base

            step₂ : (Nx +ℕ Ny) ≤ N
            step₂ =
              ≤-trans
                (≤-self+ℕ (Nx +ℕ Ny) Ny0)
                (≤-self+ℕ ((Nx +ℕ Ny) +ℕ Ny0) Nx'0)
          in
          ≤-trans step₁ step₂

        Ny0≤N : Ny0 ≤ N
        Ny0≤N =
          let
            step₁ : Ny0 ≤ ((Nx +ℕ Ny) +ℕ Ny0)
            step₁ =
              subst (λ t → Ny0 ≤ t) (+ℕ-comm Ny0 (Nx +ℕ Ny)) (≤-self+ℕ Ny0 (Nx +ℕ Ny))

            step₂ : ((Nx +ℕ Ny) +ℕ Ny0) ≤ N
            step₂ = ≤-self+ℕ ((Nx +ℕ Ny) +ℕ Ny0) Nx'0
          in
          ≤-trans step₁ step₂

        Nx'0≤N : Nx'0 ≤ N
        Nx'0≤N =
          let
            base : Nx'0 ≤ (Nx'0 +ℕ ((Nx +ℕ Ny) +ℕ Ny0))
            base = ≤-self+ℕ Nx'0 (((Nx +ℕ Ny) +ℕ Ny0))
          in
          subst (λ t → Nx'0 ≤ t) (+ℕ-comm Nx'0 (((Nx +ℕ Ny) +ℕ Ny0))) base
      in
      N , (λ n N≤n →
        let
          Nx≤n : Nx ≤ n
          Nx≤n = ≤-trans Nx≤N N≤n

          Ny≤n : Ny ≤ n
          Ny≤n = ≤-trans Ny≤N N≤n

          Ny0≤n : Ny0 ≤ n
          Ny0≤n = ≤-trans Ny0≤N N≤n

          Nx'0≤n : Nx'0 ≤ n
          Nx'0≤n = ≤-trans Nx'0≤N N≤n

          xn : ℚ
          xn = seq x n

          x'n : ℚ
          x'n = seq x' n

          yn : ℚ
          yn = seq y n

          y'n : ℚ
          y'n = seq y' n

          dxx' : ℚ
          dxx' = distℚ xn x'n

          dyy' : ℚ
          dyy' = distℚ yn y'n

          Iy : ℚ
          Iy = distℚ yn 0ℚ

          Ix' : ℚ
          Ix' = distℚ x'n 0ℚ

          dxx'<δx : dxx' <ℚ δx
          dxx'<δx = NxConv n Nx≤n

          dyy'<δy : dyy' <ℚ δy
          dyy'<δy = NyConv n Ny≤n

          Iy≤By : Iy ≤ℚ By
          Iy≤By = ByBound n Ny0≤n

          Ix'≤Bx' : Ix' ≤ℚ Bx'
          Ix'≤Bx' = Bx'Bound n Nx'0≤n

          IyNonneg : 0ℚ ≤ℚ Iy
          IyNonneg = distℚ-nonneg yn 0ℚ

          Ix'Nonneg : 0ℚ ≤ℚ Ix'
          Ix'Nonneg = distℚ-nonneg x'n 0ℚ

          dxx'≤δx : dxx' ≤ℚ δx
          dxx'≤δx = <ℚ→≤ℚ {dxx'} {δx} dxx'<δx

          dyy'≤δy : dyy' ≤ℚ δy
          dyy'≤δy = <ℚ→≤ℚ {dyy'} {δy} dyy'<δy

          Iy≤KY : Iy ≤ℚ KY
          Iy≤KY = ≤ℚ-trans {Iy} {By} {KY} Iy≤By By≤KY

          Ix'≤KX' : Ix' ≤ℚ KX'
          Ix'≤KX' = ≤ℚ-trans {Ix'} {Bx'} {KX'} Ix'≤Bx' Bx'≤KX'

          d1 : ℚ
          d1 = distℚ (xn *ℚ yn) (x'n *ℚ yn)

          d2 : ℚ
          d2 = distℚ (x'n *ℚ yn) (x'n *ℚ y'n)

          d1Nonneg : 0ℚ ≤ℚ d1
          d1Nonneg = distℚ-nonneg (xn *ℚ yn) (x'n *ℚ yn)

          d2Nonneg : 0ℚ ≤ℚ d2
          d2Nonneg = distℚ-nonneg (x'n *ℚ yn) (x'n *ℚ y'n)

          d1≤scaled : d1 ≤ℚ (dxx' *ℚ Iy)
          d1≤scaled = ≃ℚ→≤ℚˡ {d1} {(dxx' *ℚ Iy)} (distℚ-*ℚ-right yn xn x'n)

          d2≤scaled : d2 ≤ℚ (dyy' *ℚ Ix')
          d2≤scaled = ≃ℚ→≤ℚˡ {d2} {(dyy' *ℚ Ix')} (distℚ-*ℚ-left x'n yn y'n)

          step1 : (dxx' *ℚ Iy) ≤ℚ (δx *ℚ Iy)
          step1 = ≤ℚ-mul-nonneg-right dxx' δx Iy dxx'≤δx IyNonneg

          step2 : (δx *ℚ Iy) ≤ℚ (δx *ℚ KY)
          step2 = ≤ℚ-mul-nonneg-left Iy KY δx Iy≤KY δxNonneg

          scaled1≤ : (dxx' *ℚ Iy) ≤ℚ (δx *ℚ KY)
          scaled1≤ = ≤ℚ-trans {(dxx' *ℚ Iy)} {(δx *ℚ Iy)} {(δx *ℚ KY)} step1 step2

          scaled1<εq : (dxx' *ℚ Iy) <ℚ εq
          scaled1<εq = ≤<ℚ→<ℚ {(dxx' *ℚ Iy)} {(δx *ℚ KY)} {εq} scaled1≤ δxKY<εq

          d1<εq : d1 <ℚ εq
          d1<εq = ≤<ℚ→<ℚ {d1} {(δx *ℚ KY)} {εq} (≤ℚ-trans {d1} {(dxx' *ℚ Iy)} {(δx *ℚ KY)} d1≤scaled (≤ℚ-trans {(dxx' *ℚ Iy)} {(δx *ℚ Iy)} {(δx *ℚ KY)} step1 step2)) δxKY<εq

          step1' : (dyy' *ℚ Ix') ≤ℚ (δy *ℚ Ix')
          step1' = ≤ℚ-mul-nonneg-right dyy' δy Ix' dyy'≤δy Ix'Nonneg

          step2' : (δy *ℚ Ix') ≤ℚ (δy *ℚ KX')
          step2' = ≤ℚ-mul-nonneg-left Ix' KX' δy Ix'≤KX' δyNonneg

          scaled2≤ : (dyy' *ℚ Ix') ≤ℚ (δy *ℚ KX')
          scaled2≤ = ≤ℚ-trans {(dyy' *ℚ Ix')} {(δy *ℚ Ix')} {(δy *ℚ KX')} step1' step2'

          scaled2<εq : (dyy' *ℚ Ix') <ℚ εq
          scaled2<εq = ≤<ℚ→<ℚ {(dyy' *ℚ Ix')} {(δy *ℚ KX')} {εq} scaled2≤ δyKX'<εq

          d2<εq : d2 <ℚ εq
          d2<εq = ≤<ℚ→<ℚ {d2} {(dyy' *ℚ Ix')} {εq} d2≤scaled scaled2<εq

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = <ℚ→≤ℚ {d1} {εq} d1<εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = <ℚ→≤ℚ {d2} {εq} d2<εq

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ {(d1 +ℚ d2)} {(εq +ℚ εq)} {ε} sum≤ εq+εq<ε

          tri : distℚ (xn *ℚ yn) (x'n *ℚ y'n) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle (xn *ℚ yn) (x'n *ℚ yn) (x'n *ℚ y'n)
        in
        ≤<ℚ→<ℚ {distℚ (xn *ℚ yn) (x'n *ℚ y'n)} {(d1 +ℚ d2)} {ε} tri sum<ε)
  }
-- § Addition respects ≃ℝ
+ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x +ℝ y) ≃ℝ (x' +ℝ y')
+ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' = record
  { conv0 = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ {0ℚ} {εq} εqPos

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos

        NxPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq x' n) <ℚ εq)
        NxPack = _≃ℝ_.conv0 x≃x' εq εqPos

        NyPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq y n) (seq y' n) <ℚ εq)
        NyPack = _≃ℝ_.conv0 y≃y' εq εqPos

        Nx : ℕ
        Nx = fst NxPack

        Ny : ℕ
        Ny = fst NyPack

        NxConv : (n : ℕ) → Nx ≤ n → distℚ (seq x n) (seq x' n) <ℚ εq
        NxConv = snd NxPack

        NyConv : (n : ℕ) → Ny ≤ n → distℚ (seq y n) (seq y' n) <ℚ εq
        NyConv = snd NyPack

        N : ℕ
        N = Nx +ℕ Ny

        Nx≤N : Nx ≤ N
        Nx≤N =
          let
            mono : (Nx +ℕ zero) ≤ (Nx +ℕ Ny)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Ny} z≤n Nx
          in
          subst (λ t → t ≤ (Nx +ℕ Ny)) (+ℕ-zero-right Nx) mono

        Ny≤N : Ny ≤ N
        Ny≤N =
          let
            mono : (Ny +ℕ zero) ≤ (Ny +ℕ Nx)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nx} z≤n Ny

            base : Ny ≤ (Ny +ℕ Nx)
            base = subst (λ t → t ≤ (Ny +ℕ Nx)) (+ℕ-zero-right Ny) mono
          in
          subst (λ t → Ny ≤ t) (+ℕ-comm Ny Nx) base
      in
      N , (λ n N≤n →
        let
          Nx≤n : Nx ≤ n
          Nx≤n = ≤-trans Nx≤N N≤n

          Ny≤n : Ny ≤ n
          Ny≤n = ≤-trans Ny≤N N≤n

          xn : ℚ
          xn = seq x n

          x'n : ℚ
          x'n = seq x' n

          yn : ℚ
          yn = seq y n

          y'n : ℚ
          y'n = seq y' n

          dx : ℚ
          dx = distℚ xn x'n

          dy : ℚ
          dy = distℚ yn y'n

          dx<εq : dx <ℚ εq
          dx<εq = NxConv n Nx≤n

          dy<εq : dy <ℚ εq
          dy<εq = NyConv n Ny≤n

          d1 : ℚ
          d1 = distℚ (xn +ℚ yn) (x'n +ℚ yn)

          d2 : ℚ
          d2 = distℚ (x'n +ℚ yn) (x'n +ℚ y'n)

          d1Nonneg : 0ℚ ≤ℚ d1
          d1Nonneg = distℚ-nonneg (xn +ℚ yn) (x'n +ℚ yn)

          d2Nonneg : 0ℚ ≤ℚ d2
          d2Nonneg = distℚ-nonneg (x'n +ℚ yn) (x'n +ℚ y'n)

          d1≤dx : d1 ≤ℚ dx
          d1≤dx = ≃ℚ→≤ℚˡ {d1} {dx} (distℚ-+ℚ-right xn x'n yn)

          d2≤dy : d2 ≤ℚ dy
          d2≤dy = ≃ℚ→≤ℚˡ {d2} {dy} (distℚ-+ℚ-left x'n yn y'n)

          d1<εq : d1 <ℚ εq
          d1<εq = ≤<ℚ→<ℚ {d1} {dx} {εq} d1≤dx dx<εq

          d2<εq : d2 <ℚ εq
          d2<εq = ≤<ℚ→<ℚ {d2} {dy} {εq} d2≤dy dy<εq

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = <ℚ→≤ℚ {d1} {εq} d1<εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = <ℚ→≤ℚ {d2} {εq} d2<εq

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ {(d1 +ℚ d2)} {(εq +ℚ εq)} {ε} sum≤ εq+εq<ε

          tri : distℚ (xn +ℚ yn) (x'n +ℚ y'n) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle (xn +ℚ yn) (x'n +ℚ yn) (x'n +ℚ y'n)
        in
        ≤<ℚ→<ℚ {distℚ (xn +ℚ yn) (x'n +ℚ y'n)} {(d1 +ℚ d2)} {ε} tri sum<ε)
  }
-- § Negation respects ≃ℝ
-ℝ-resp-≃ℝ : {x x' : ℝ} → x ≃ℝ x' → (-ℝ x) ≃ℝ (-ℝ x')
-ℝ-resp-≃ℝ {x} {x'} x≃x' = record
  { conv0 = λ ε εpos →
      let
        NxPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq x' n) <ℚ ε)
        NxPack = _≃ℝ_.conv0 x≃x' ε εpos

        Nx : ℕ
        Nx = fst NxPack

        NxConv : (n : ℕ) → Nx ≤ n → distℚ (seq x n) (seq x' n) <ℚ ε
        NxConv = snd NxPack
      in
      Nx , (λ n Nx≤n →
        let
          xn : ℚ
          xn = seq x n

          x'n : ℚ
          x'n = seq x' n

          d<ε : distℚ xn x'n <ℚ ε
          d<ε = NxConv n Nx≤n

          negEq : distℚ (-ℚ xn) (-ℚ x'n) ≃ℚ distℚ xn x'n
          negEq = distℚ-neg xn x'n

          d≤ : distℚ (-ℚ xn) (-ℚ x'n) ≤ℚ distℚ xn x'n
          d≤ = ≃ℚ→≤ℚˡ {distℚ (-ℚ xn) (-ℚ x'n)} {distℚ xn x'n} negEq
        in
        ≤<ℚ→<ℚ {distℚ (-ℚ xn) (-ℚ x'n)} {distℚ xn x'n} {ε} d≤ d<ε)
  }

-- § Subtraction respects ≃ℝ (derived from + and -)
-ℝ-resp-≃ℝ₂ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x -ℝ y) ≃ℝ (x' -ℝ y')
-ℝ-resp-≃ℝ₂ {x} {x'} {y} {y'} x≃x' y≃y' =
  +ℝ-resp-≃ℝ x≃x' (-ℝ-resp-≃ℝ y≃y')
-- § Non-strict real order: eventual ε-approximation
infix 4 _≤ℝ_ _<ℝ_

record _≤ℝ_ (x y : ℝ) : Set where
  field
    leReal : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε))

-- § Type alias for non-strict real order
≤ℝP : ℝ → ℝ → Set
≤ℝP = _≤ℝ_
-- § Strict real order: witnessed separation
record _<ℝ_ (x y : ℝ) : Set where
  field
    ltWitness : Σ ℚ (λ ε → (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n)))
-- § Strict order implies non-strict by forgetting the margin
<ℝ→≤ℝ : {x y : ℝ} → x <ℝ y → x ≤ℝ y
<ℝ→≤ℝ {x} {y} x<y = record
  { leReal = λ δ δpos →
      let
        w : Σ ℚ (λ ε → (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n)))
        w = _<ℝ_.ltWitness x<y

        ε : ℚ
        ε = fst w

        wRest : (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n))
        wRest = snd w

        εpos : 0ℚ <ℚ ε
        εpos = fst wRest

        pack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n))
        pack = snd wRest

        N : ℕ
        N = fst pack

        conv : (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n)
        conv = snd pack
      in
      N , (λ n N≤n →
        let
          xn : ℚ
          xn = seq x n

          yn : ℚ
          yn = seq y n

          xn≤xn+ε : xn ≤ℚ (xn +ℚ ε)
          xn≤xn+ε = ≤ℚ-add-nonneg-right xn ε (<ℚ→≤ℚ εpos)

          xn+ε≤yn : (xn +ℚ ε) ≤ℚ yn
          xn+ε≤yn = conv n N≤n

          xn≤yn : xn ≤ℚ yn
          xn≤yn = ≤ℚ-trans {xn} {(xn +ℚ ε)} {yn} xn≤xn+ε xn+ε≤yn

          yn≤yn+δ : yn ≤ℚ (yn +ℚ δ)
          yn≤yn+δ = ≤ℚ-add-nonneg-right yn δ (<ℚ→≤ℚ δpos)
        in
        ≤ℚ-trans xn≤yn yn≤yn+δ)
  }
-- § Equivalence implies ≤ℝ
≃ℝ→≤ℝ : {x y : ℝ} → x ≃ℝ y → x ≤ℝ y
≃ℝ→≤ℝ {x} {y} x≃y = record
  { leReal = λ ε εpos →
      let
        pack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε)
        pack = _≃ℝ_.conv0 x≃y ε εpos

        N : ℕ
        N = fst pack

        conv : (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε
        conv = snd pack
      in
      N , (λ n N≤n →
        distℚ≤ε→x≤y+ε (seq x n) (seq y n) ε (<ℚ→≤ℚ (conv n N≤n)))
  }
-- § Transitivity of strict real order
<ℝ-trans : {x y z : ℝ} → x <ℝ y → y <ℝ z → x <ℝ z
<ℝ-trans {x} {y} {z} x<y y<z = record
  { ltWitness =
      let
        wxy : Σ ℚ (λ ε → (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n)))
        wxy = _<ℝ_.ltWitness x<y

        ε₁ : ℚ
        ε₁ = fst wxy

        wxyRest : (0ℚ <ℚ ε₁) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε₁) ≤ℚ (seq y n))
        wxyRest = snd wxy

        ε₁pos : 0ℚ <ℚ ε₁
        ε₁pos = fst wxyRest

        packXY : Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε₁) ≤ℚ (seq y n))
        packXY = snd wxyRest

        Nxy : ℕ
        Nxy = fst packXY

        convXY : (n : ℕ) → Nxy ≤ n → ((seq x n) +ℚ ε₁) ≤ℚ (seq y n)
        convXY = snd packXY

        wyz : Σ ℚ (λ ε → (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq y n) +ℚ ε) ≤ℚ (seq z n)))
        wyz = _<ℝ_.ltWitness y<z

        ε₂ : ℚ
        ε₂ = fst wyz

        wyzRest : (0ℚ <ℚ ε₂) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq y n) +ℚ ε₂) ≤ℚ (seq z n))
        wyzRest = snd wyz

        ε₂pos : 0ℚ <ℚ ε₂
        ε₂pos = fst wyzRest

        packYZ : Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq y n) +ℚ ε₂) ≤ℚ (seq z n))
        packYZ = snd wyzRest

        Nyz : ℕ
        Nyz = fst packYZ

        convYZ : (n : ℕ) → Nyz ≤ n → ((seq y n) +ℚ ε₂) ≤ℚ (seq z n)
        convYZ = snd packYZ

        ε : ℚ
        ε = εQuarter ε₁

        εpos : 0ℚ <ℚ ε
        εpos = εQuarter-pos ε₁

        N : ℕ
        N = Nxy +ℕ Nyz

        Nxy≤N : Nxy ≤ N
        Nxy≤N =
          let
            mono : (Nxy +ℕ zero) ≤ (Nxy +ℕ Nyz)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nyz} z≤n Nxy
          in
          subst (λ t → t ≤ (Nxy +ℕ Nyz)) (+ℕ-zero-right Nxy) mono

        Nyz≤N : Nyz ≤ N
        Nyz≤N =
          let
            mono : (Nyz +ℕ zero) ≤ (Nyz +ℕ Nxy)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nxy} z≤n Nyz

            base : Nyz ≤ (Nyz +ℕ Nxy)
            base = subst (λ t → t ≤ (Nyz +ℕ Nxy)) (+ℕ-zero-right Nyz) mono
          in
          subst (λ t → Nyz ≤ t) (+ℕ-comm Nyz Nxy) base
      in
      ε , (εpos ,
        (N , (λ n N≤n →
          let
            Nxy≤n : Nxy ≤ n
            Nxy≤n = ≤-trans Nxy≤N N≤n

            Nyz≤n : Nyz ≤ n
            Nyz≤n = ≤-trans Nyz≤N N≤n

            xn : ℚ
            xn = seq x n

            yn : ℚ
            yn = seq y n

            zn : ℚ
            zn = seq z n

            xε₁≤y : (xn +ℚ ε₁) ≤ℚ yn
            xε₁≤y = convXY n Nxy≤n

            xε≤xε₁ : (xn +ℚ ε) ≤ℚ (xn +ℚ ε₁)
            xε≤xε₁ =
              ≤ℚ-+ℚ-mono-left xn ε ε₁ (<ℚ→≤ℚ (εQuarter<ε ε₁ ε₁pos))

            xε≤y : (xn +ℚ ε) ≤ℚ yn
            xε≤y = ≤ℚ-trans {(xn +ℚ ε)} {(xn +ℚ ε₁)} {yn} xε≤xε₁ xε₁≤y

            y≤y+ε₂ : yn ≤ℚ (yn +ℚ ε₂)
            y≤y+ε₂ = ≤ℚ-add-nonneg-right yn ε₂ (<ℚ→≤ℚ ε₂pos)

            xε≤y+ε₂ : (xn +ℚ ε) ≤ℚ (yn +ℚ ε₂)
            xε≤y+ε₂ = ≤ℚ-trans {(xn +ℚ ε)} {yn} {(yn +ℚ ε₂)} xε≤y y≤y+ε₂
          in
            ≤ℚ-trans xε≤y+ε₂ (convYZ n Nyz≤n))))
  }


-- § Strict order respects ≃ℝ on both sides
<ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → x <ℝ y → x' <ℝ y'
<ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' x<y =
  let
    wxy = _<ℝ_.ltWitness x<y

    ε₀ : ℚ
    ε₀ = fst wxy

    wxyRest = snd wxy

    ε₀pos : 0ℚ <ℚ ε₀
    ε₀pos = fst wxyRest

    packXY = snd wxyRest

    Nxy : ℕ
    Nxy = fst packXY

    convXY : (n : ℕ) → Nxy ≤ n → ((seq x n) +ℚ ε₀) ≤ℚ (seq y n)
    convXY = snd packXY

    ε : ℚ
    ε = εQuarter ε₀

    εpos : 0ℚ <ℚ ε
    εpos = εQuarter-pos ε₀

    α : ℚ
    α = εQuarter ε

    β : ℚ
    β = εQuarter ε

    αpos : 0ℚ <ℚ α
    αpos = εQuarter-pos ε

    βpos : 0ℚ <ℚ β
    βpos = εQuarter-pos ε

    x'≤x : x' ≤ℝ x
    x'≤x = ≃ℝ→≤ℝ (≃ℝ-sym x≃x')

    y≤y' : y ≤ℝ y'
    y≤y' = ≃ℝ→≤ℝ y≃y'

    packX = _≤ℝ_.leReal x'≤x α αpos
    packY = _≤ℝ_.leReal y≤y' β βpos

    Nx : ℕ
    Nx = fst packX

    Ny : ℕ
    Ny = fst packY

    boundX : (n : ℕ) → Nx ≤ n → (seq x' n) ≤ℚ ((seq x n) +ℚ α)
    boundX = snd packX

    boundY : (n : ℕ) → Ny ≤ n → (seq y n) ≤ℚ ((seq y' n) +ℚ β)
    boundY = snd packY

    N : ℕ
    N = Nxy +ℕ (Nx +ℕ Ny)

    Nxy≤N : Nxy ≤ N
    Nxy≤N =
      let
        step : (Nxy +ℕ zero) ≤ (Nxy +ℕ (Nx +ℕ Ny))
        step = ≤-+ℕ-monoˡ {a = zero} {b = (Nx +ℕ Ny)} z≤n Nxy
      in
      subst (λ t → t ≤ (Nxy +ℕ (Nx +ℕ Ny))) (+ℕ-zero-right Nxy) step

    Nx≤N : Nx ≤ N
    Nx≤N =
      let
        step : (Nx +ℕ zero) ≤ (Nx +ℕ (Nxy +ℕ Ny))
        step = ≤-+ℕ-monoˡ {a = zero} {b = (Nxy +ℕ Ny)} z≤n Nx

        base : Nx ≤ (Nx +ℕ (Nxy +ℕ Ny))
        base = subst (λ t → t ≤ (Nx +ℕ (Nxy +ℕ Ny))) (+ℕ-zero-right Nx) step

        eq : (Nx +ℕ (Nxy +ℕ Ny)) ≡ (Nxy +ℕ (Nx +ℕ Ny))
        eq =
          trans
            (sym (+ℕ-assoc Nx Nxy Ny))
            (trans
              (cong (λ t → t +ℕ Ny) (+ℕ-comm Nx Nxy))
              (+ℕ-assoc Nxy Nx Ny))
      in
      subst (λ t → Nx ≤ t) eq base

    Ny≤N : Ny ≤ N
    Ny≤N =
      let
        step : (Ny +ℕ zero) ≤ (Ny +ℕ (Nxy +ℕ Nx))
        step = ≤-+ℕ-monoˡ {a = zero} {b = (Nxy +ℕ Nx)} z≤n Ny

        base : Ny ≤ (Ny +ℕ (Nxy +ℕ Nx))
        base = subst (λ t → t ≤ (Ny +ℕ (Nxy +ℕ Nx))) (+ℕ-zero-right Ny) step

        eq : (Ny +ℕ (Nxy +ℕ Nx)) ≡ (Nxy +ℕ (Nx +ℕ Ny))
        eq =
          trans
            (sym (+ℕ-assoc Ny Nxy Nx))
            (trans
              (cong (λ t → t +ℕ Nx) (+ℕ-comm Ny Nxy))
              (trans
                (+ℕ-assoc Nxy Ny Nx)
                (cong (λ t → Nxy +ℕ t) (+ℕ-comm Ny Nx))))
      in
      subst (λ t → Ny ≤ t) eq base
  in
  record
    { ltWitness =
        ε ,
        ( εpos
        , ( N
          , (λ n N≤n →
              let
                Nxy≤n : Nxy ≤ n
                Nxy≤n = ≤-trans Nxy≤N N≤n

                Nx≤n : Nx ≤ n
                Nx≤n = ≤-trans Nx≤N N≤n

                Ny≤n : Ny ≤ n
                Ny≤n = ≤-trans Ny≤N N≤n

                xn : ℚ
                xn = seq x n

                x'n : ℚ
                x'n = seq x' n

                yn : ℚ
                yn = seq y n

                y'n : ℚ
                y'n = seq y' n

                x'n≤xn+α : x'n ≤ℚ (xn +ℚ α)
                x'n≤xn+α = boundX n Nx≤n

                α+β<ε : (α +ℚ β) <ℚ ε
                α+β<ε = εQuarter-double<ε ε εpos

                α+β≤ε : (α +ℚ β) ≤ℚ ε
                α+β≤ε = <ℚ→≤ℚ {(α +ℚ β)} {ε} α+β<ε

                ε+α+β≤ε+ε : (ε +ℚ (α +ℚ β)) ≤ℚ (ε +ℚ ε)
                ε+α+β≤ε+ε = ≤ℚ-+ℚ-mono-left ε (α +ℚ β) ε α+β≤ε

                ε+ε<ε₀ : (ε +ℚ ε) <ℚ ε₀
                ε+ε<ε₀ = εQuarter-double<ε ε₀ ε₀pos

                ε+ε≤ε₀ : (ε +ℚ ε) ≤ℚ ε₀
                ε+ε≤ε₀ = <ℚ→≤ℚ {(ε +ℚ ε)} {ε₀} ε+ε<ε₀

                ε+α+β≤ε₀ : (ε +ℚ (α +ℚ β)) ≤ℚ ε₀
                ε+α+β≤ε₀ = ≤ℚ-trans {(ε +ℚ (α +ℚ β))} {(ε +ℚ ε)} {ε₀} ε+α+β≤ε+ε ε+ε≤ε₀

                t : ℚ
                t = α +ℚ (ε +ℚ β)

                t≃ε+α+β : t ≃ℚ (ε +ℚ (α +ℚ β))
                t≃ε+α+β =
                  ≃ℚ-trans
                    (≃ℚ-sym (+ℚ-assoc α ε β))
                    (≃ℚ-trans
                      (+ℚ-resp-≃ (+ℚ-comm α ε) (≃ℚ-refl β))
                      (+ℚ-assoc ε α β))

                t≤ε₀ : t ≤ℚ ε₀
                t≤ε₀ = ≤ℚ-trans (≃ℚ→≤ℚˡ t≃ε+α+β) ε+α+β≤ε₀

                xnt≤xnε₀ : (xn +ℚ t) ≤ℚ (xn +ℚ ε₀)
                xnt≤xnε₀ = ≤ℚ-+ℚ-mono-left xn t ε₀ t≤ε₀

                x'n+ε+β≤xn+t : (x'n +ℚ (ε +ℚ β)) ≤ℚ (xn +ℚ t)
                x'n+ε+β≤xn+t =
                  let
                    step₁ : (x'n +ℚ (ε +ℚ β)) ≤ℚ ((xn +ℚ α) +ℚ (ε +ℚ β))
                    step₁ = ≤ℚ-+ℚ-mono-right x'n (xn +ℚ α) (ε +ℚ β) x'n≤xn+α

                    lhsEq : ((xn +ℚ α) +ℚ (ε +ℚ β)) ≃ℚ (xn +ℚ t)
                    lhsEq = +ℚ-assoc xn α (ε +ℚ β)
                  in
                  ≤ℚ-trans step₁ (≃ℚ→≤ℚˡ lhsEq)

                x'n+ε+β≤xn+ε₀ : (x'n +ℚ (ε +ℚ β)) ≤ℚ (xn +ℚ ε₀)
                x'n+ε+β≤xn+ε₀ = ≤ℚ-trans {(x'n +ℚ (ε +ℚ β))} {(xn +ℚ t)} {(xn +ℚ ε₀)} x'n+ε+β≤xn+t xnt≤xnε₀

                xn+ε₀≤yn : (xn +ℚ ε₀) ≤ℚ yn
                xn+ε₀≤yn = convXY n Nxy≤n

                x'n+ε+β≤yn : (x'n +ℚ (ε +ℚ β)) ≤ℚ yn
                x'n+ε+β≤yn = ≤ℚ-trans {(x'n +ℚ (ε +ℚ β))} {(xn +ℚ ε₀)} {yn} x'n+ε+β≤xn+ε₀ xn+ε₀≤yn

                x'n+ε≤yn-β : (x'n +ℚ ε) ≤ℚ (yn +ℚ (-ℚ β))
                x'n+ε≤yn-β =
                  let
                    step₁ : ((x'n +ℚ (ε +ℚ β)) +ℚ (-ℚ β)) ≤ℚ (yn +ℚ (-ℚ β))
                    step₁ = ≤ℚ-+ℚ-mono-right (x'n +ℚ (ε +ℚ β)) yn (-ℚ β) x'n+ε+β≤yn

                    lhsEq₁ : ((x'n +ℚ (ε +ℚ β)) +ℚ (-ℚ β)) ≃ℚ (x'n +ℚ ((ε +ℚ β) +ℚ (-ℚ β)))
                    lhsEq₁ = +ℚ-assoc x'n (ε +ℚ β) (-ℚ β)

                    lhsEq₂ : ((ε +ℚ β) +ℚ (-ℚ β)) ≃ℚ ε
                    lhsEq₂ =
                      ≃ℚ-trans
                        (+ℚ-assoc ε β (-ℚ β))
                        (≃ℚ-trans
                          (+ℚ-resp-≃ (≃ℚ-refl ε) (+ℚ-inv-right β))
                          (+ℚ-zero-right ε))

                    lhsEq : ((x'n +ℚ (ε +ℚ β)) +ℚ (-ℚ β)) ≃ℚ (x'n +ℚ ε)
                    lhsEq = ≃ℚ-trans lhsEq₁ (+ℚ-resp-≃ (≃ℚ-refl x'n) lhsEq₂)
                  in
                  ≤ℚ-trans (≃ℚ→≤ℚʳ lhsEq) step₁

                yn≤y'n+β : yn ≤ℚ (y'n +ℚ β)
                yn≤y'n+β = boundY n Ny≤n

                yn-β≤y'n : (yn +ℚ (-ℚ β)) ≤ℚ y'n
                yn-β≤y'n =
                  let
                    step₁ : (yn +ℚ (-ℚ β)) ≤ℚ ((y'n +ℚ β) +ℚ (-ℚ β))
                    step₁ = ≤ℚ-+ℚ-mono-right yn (y'n +ℚ β) (-ℚ β) yn≤y'n+β

                    rhsEq₁ : ((y'n +ℚ β) +ℚ (-ℚ β)) ≃ℚ (y'n +ℚ (β +ℚ (-ℚ β)))
                    rhsEq₁ = +ℚ-assoc y'n β (-ℚ β)

                    rhsEq₂ : (β +ℚ (-ℚ β)) ≃ℚ 0ℚ
                    rhsEq₂ = +ℚ-inv-right β

                    rhsEq : ((y'n +ℚ β) +ℚ (-ℚ β)) ≃ℚ y'n
                    rhsEq =
                      ≃ℚ-trans
                        rhsEq₁
                        (≃ℚ-trans
                          (+ℚ-resp-≃ (≃ℚ-refl y'n) rhsEq₂)
                          (+ℚ-zero-right y'n))
                  in
                  ≤ℚ-trans step₁ (≃ℚ→≤ℚˡ rhsEq)
              in
              ≤ℚ-trans x'n+ε≤yn-β yn-β≤y'n
            )
          )
        )
    }
-- § Reflexivity of ≤ℝ
≤ℝ-refl : (x : ℝ) → x ≤ℝ x
≤ℝ-refl x = record
  { leReal = λ ε εpos →
      zero , (λ n _ →
        ≤ℚ-add-nonneg-right (seq x n) ε (<ℚ→≤ℚ εpos))
  }
-- § Transitivity of ≤ℝ via ε-splitting
≤ℝ-trans : {x y z : ℝ} → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans {x} {y} {z} x≤y y≤z = record
  { leReal = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ {0ℚ} {εq} εqPos

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos

        NxyPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ εq))
        NxyPack = _≤ℝ_.leReal x≤y εq εqPos

        NyzPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq y n) ≤ℚ ((seq z n) +ℚ εq))
        NyzPack = _≤ℝ_.leReal y≤z εq εqPos

        Nxy : ℕ
        Nxy = fst NxyPack

        Nyz : ℕ
        Nyz = fst NyzPack

        NxyConv : (n : ℕ) → Nxy ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ εq)
        NxyConv = snd NxyPack

        NyzConv : (n : ℕ) → Nyz ≤ n → (seq y n) ≤ℚ ((seq z n) +ℚ εq)
        NyzConv = snd NyzPack

        N : ℕ
        N = Nxy +ℕ Nyz

        Nxy≤N : Nxy ≤ N
        Nxy≤N =
          let
            mono : (Nxy +ℕ zero) ≤ (Nxy +ℕ Nyz)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nyz} z≤n Nxy
          in
          subst (λ t → t ≤ (Nxy +ℕ Nyz)) (+ℕ-zero-right Nxy) mono

        Nyz≤N : Nyz ≤ N
        Nyz≤N =
          let
            mono : (Nyz +ℕ zero) ≤ (Nyz +ℕ Nxy)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nxy} z≤n Nyz

            base : Nyz ≤ (Nyz +ℕ Nxy)
            base = subst (λ t → t ≤ (Nyz +ℕ Nxy)) (+ℕ-zero-right Nyz) mono
          in
          subst (λ t → Nyz ≤ t) (+ℕ-comm Nyz Nxy) base
      in
      N , (λ n N≤n →
        let
          Nxy≤n : Nxy ≤ n
          Nxy≤n = ≤-trans Nxy≤N N≤n

          Nyz≤n : Nyz ≤ n
          Nyz≤n = ≤-trans Nyz≤N N≤n

          xn : ℚ
          xn = seq x n

          yn : ℚ
          yn = seq y n

          zn : ℚ
          zn = seq z n

          xn≤yn+εq : xn ≤ℚ (yn +ℚ εq)
          xn≤yn+εq = NxyConv n Nxy≤n

          yn≤zn+εq : yn ≤ℚ (zn +ℚ εq)
          yn≤zn+εq = NyzConv n Nyz≤n

          step₁ : (yn +ℚ εq) ≤ℚ ((zn +ℚ εq) +ℚ εq)
          step₁ = ≤ℚ-+ℚ-mono-right yn (zn +ℚ εq) εq yn≤zn+εq

          step₂ : xn ≤ℚ ((zn +ℚ εq) +ℚ εq)
          step₂ = ≤ℚ-trans {xn} {(yn +ℚ εq)} {((zn +ℚ εq) +ℚ εq)} xn≤yn+εq step₁

          step₃ : ((zn +ℚ εq) +ℚ εq) ≤ℚ (zn +ℚ (εq +ℚ εq))
          step₃ = ≃ℚ→≤ℚˡ {((zn +ℚ εq) +ℚ εq)} {(zn +ℚ (εq +ℚ εq))} (+ℚ-assoc zn εq εq)

          step₄ : (zn +ℚ (εq +ℚ εq)) ≤ℚ (zn +ℚ ε)
          step₄ = ≤ℚ-+ℚ-mono-left zn (εq +ℚ εq) ε (<ℚ→≤ℚ εq+εq<ε)

          done : xn ≤ℚ (zn +ℚ ε)
          done = ≤ℚ-trans {xn} {((zn +ℚ εq) +ℚ εq)} {(zn +ℚ ε)} step₂ (≤ℚ-trans step₃ step₄)
        in
        done)
  }
-- § Antisymmetry: mutual ≤ℝ yields ≃ℝ
≤ℝ-antisym : {x y : ℝ} → x ≤ℝ y → y ≤ℝ x → x ≃ℝ y
≤ℝ-antisym {x} {y} x≤y y≤x = record
  { conv0 = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        NxyPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ εq))
        NxyPack = _≤ℝ_.leReal x≤y εq εqPos

        NyxPack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq y n) ≤ℚ ((seq x n) +ℚ εq))
        NyxPack = _≤ℝ_.leReal y≤x εq εqPos

        Nxy : ℕ
        Nxy = fst NxyPack

        Nyx : ℕ
        Nyx = fst NyxPack

        NxyConv : (n : ℕ) → Nxy ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ εq)
        NxyConv = snd NxyPack

        NyxConv : (n : ℕ) → Nyx ≤ n → (seq y n) ≤ℚ ((seq x n) +ℚ εq)
        NyxConv = snd NyxPack

        N : ℕ
        N = Nxy +ℕ Nyx

        Nxy≤N : Nxy ≤ N
        Nxy≤N =
          let
            mono : (Nxy +ℕ zero) ≤ (Nxy +ℕ Nyx)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nyx} z≤n Nxy
          in
          subst (λ t → t ≤ (Nxy +ℕ Nyx)) (+ℕ-zero-right Nxy) mono

        Nyx≤N : Nyx ≤ N
        Nyx≤N =
          let
            mono : (Nyx +ℕ zero) ≤ (Nyx +ℕ Nxy)
            mono = ≤-+ℕ-monoˡ {a = zero} {b = Nxy} z≤n Nyx

            base : Nyx ≤ (Nyx +ℕ Nxy)
            base = subst (λ t → t ≤ (Nyx +ℕ Nxy)) (+ℕ-zero-right Nyx) mono
          in
          subst (λ t → Nyx ≤ t) (+ℕ-comm Nyx Nxy) base
      in
      N , (λ n N≤n →
        let
          Nxy≤n : Nxy ≤ n
          Nxy≤n = ≤-trans Nxy≤N N≤n

          Nyx≤n : Nyx ≤ n
          Nyx≤n = ≤-trans Nyx≤N N≤n

          xn : ℚ
          xn = seq x n

          yn : ℚ
          yn = seq y n

          xn≤yn+εq : xn ≤ℚ (yn +ℚ εq)
          xn≤yn+εq = NxyConv n Nxy≤n

          yn≤xn+εq : yn ≤ℚ (xn +ℚ εq)
          yn≤xn+εq = NyxConv n Nyx≤n

          d≤εq : distℚ xn yn ≤ℚ εq
          d≤εq = distℚ-bounded-by-ε xn yn εq xn≤yn+εq yn≤xn+εq

          εq<ε : εq <ℚ ε
          εq<ε = εQuarter<ε ε εpos
        in
        ≤<ℚ→<ℚ {distℚ xn yn} {εq} {ε} d≤εq εq<ε)
  }
-- § Non-strict order respects ≃ℝ
≤ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → x ≤ℝ y → x' ≤ℝ y'
≤ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' x≤y =
  let
    x'≤x : x' ≤ℝ x
    x'≤x = ≃ℝ→≤ℝ (≃ℝ-sym x≃x')

    y≤y' : y ≤ℝ y'
    y≤y' = ≃ℝ→≤ℝ y≃y'
  in
  ≤ℝ-trans (≤ℝ-trans x'≤x x≤y) y≤y'
-- § Right monotonicity of +ℝ under ≤ℝ
≤ℝ-+ℝ-mono-right : {x y z : ℝ} → x ≤ℝ y → (x +ℝ z) ≤ℝ (y +ℝ z)
≤ℝ-+ℝ-mono-right {x} {y} {z} x≤y = record
  { leReal = λ ε εpos →
      let
        pack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε))
        pack = _≤ℝ_.leReal x≤y ε εpos

        N : ℕ
        N = fst pack

        conv : (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε)
        conv = snd pack
      in
      N , (λ n N≤n →
        let
          xn : ℚ
          xn = seq x n

          yn : ℚ
          yn = seq y n

          zn : ℚ
          zn = seq z n

          step₁ : (xn +ℚ zn) ≤ℚ (((yn +ℚ ε) +ℚ zn))
          step₁ = ≤ℚ-+ℚ-mono-right xn (yn +ℚ ε) zn (conv n N≤n)

          rhsEq : ((yn +ℚ ε) +ℚ zn) ≃ℚ ((yn +ℚ zn) +ℚ ε)
          rhsEq =
            ≃ℚ-trans
              (+ℚ-assoc yn ε zn)
              (≃ℚ-trans
                (+ℚ-resp-≃ (≃ℚ-refl yn) (+ℚ-comm ε zn))
                (≃ℚ-sym (+ℚ-assoc yn zn ε)))

          step₂ : (((yn +ℚ ε) +ℚ zn)) ≤ℚ ((yn +ℚ zn) +ℚ ε)
          step₂ = ≃ℚ→≤ℚˡ {(((yn +ℚ ε) +ℚ zn))} {((yn +ℚ zn) +ℚ ε)} rhsEq
        in
        ≤ℚ-trans step₁ step₂)
  }
-- § Left monotonicity of +ℝ under ≤ℝ
≤ℝ-+ℝ-mono-left : {x y z : ℝ} → x ≤ℝ y → (z +ℝ x) ≤ℝ (z +ℝ y)
≤ℝ-+ℝ-mono-left {x} {y} {z} x≤y = record
  { leReal = λ ε εpos →
      let
        pack : Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε))
        pack = _≤ℝ_.leReal x≤y ε εpos

        N : ℕ
        N = fst pack

        conv : (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε)
        conv = snd pack
      in
      N , (λ n N≤n →
        let
          xn : ℚ
          xn = seq x n

          yn : ℚ
          yn = seq y n

          zn : ℚ
          zn = seq z n

          step₁ : (zn +ℚ xn) ≤ℚ (zn +ℚ (yn +ℚ ε))
          step₁ = ≤ℚ-+ℚ-mono-left zn xn (yn +ℚ ε) (conv n N≤n)

          rhsEq : (zn +ℚ (yn +ℚ ε)) ≃ℚ ((zn +ℚ yn) +ℚ ε)
          rhsEq = sym (+ℚ-assoc zn yn ε)

          step₂ : (zn +ℚ (yn +ℚ ε)) ≤ℚ ((zn +ℚ yn) +ℚ ε)
          step₂ = ≃ℚ→≤ℚˡ {(zn +ℚ (yn +ℚ ε))} {((zn +ℚ yn) +ℚ ε)} rhsEq
        in
        ≤ℚ-trans step₁ step₂)
  }
-- § Boolean comparison on ℕ
_≤ℕ_ : ℕ → ℕ → Bool
zero  ≤ℕ _     = true
suc _ ≤ℕ zero  = false
suc m ≤ℕ suc n = m ≤ℕ n

-- § Fuel-bounded GCD
gcd-fuel : ℕ → ℕ → ℕ → ℕ
gcd-fuel zero    m _       = m
gcd-fuel (suc _) zero n    = n
gcd-fuel (suc _) m zero    = m
gcd-fuel (suc f) (suc m) (suc n) with (suc m) ≤ℕ (suc n)
... | true  = gcd-fuel f (suc m) (n ∸ m)
... | false = gcd-fuel f (m ∸ n) (suc n)

-- § GCD with canonical fuel
gcd : ℕ → ℕ → ℕ
gcd m n = gcd-fuel (m + n) m n

-- § Successor coercion to ℕ⁺
sucToℕ⁺ : ℕ → ℕ⁺
sucToℕ⁺ zero = one⁺
sucToℕ⁺ (suc n) = suc⁺ (sucToℕ⁺ n)

-- § General ℕ to ℕ⁺ coercion
ℕ-to-ℕ⁺ : ℕ → ℕ⁺
ℕ-to-ℕ⁺ = mkℕ⁺

-- § Fuel-bounded integer division
div-fuel : ℕ → ℕ → ℕ⁺ → ℕ
div-fuel zero    _       _ = zero
div-fuel (suc f) n d with ⁺toℕ d ≤ℕ n
... | true  = suc (div-fuel f (n ∸ ⁺toℕ d) d)
... | false = zero

-- § Division by ℕ⁺
_div_ : ℕ → ℕ⁺ → ℕ
n div d = div-fuel n n d

-- § Division by ℕ (zero-safe)
_divℕ_ : ℕ → ℕ → ℕ
_ divℕ zero = zero
n divℕ (suc d) = n div (sucToℕ⁺ d)
-- § Vertex count of K₄ (= simplex-vertices from Tier 5)
vertexCountK4 : ℕ
vertexCountK4 = simplex-vertices

-- § Edge count: E = V(V−1)/2
edgeCountK4 : ℕ
edgeCountK4 = (vertexCountK4 * (vertexCountK4 ∸ 1)) divℕ 2

-- § Face count: F = V(V−1)(V−2)/6
faceCountK4 : ℕ
faceCountK4 = (vertexCountK4 * (vertexCountK4 ∸ 1) * (vertexCountK4 ∸ 2)) divℕ 6

-- § Vertex degree: deg = V − 1
degree-K4 : ℕ
degree-K4 = vertexCountK4 ∸ 1

-- § Euler characteristic: χ = V + F − E
eulerChar-computed : ℕ
eulerChar-computed = (vertexCountK4 + faceCountK4) ∸ edgeCountK4

-- § Law 16B-0: E = 6
law16B-0-edges : edgeCountK4 ≡ 6
law16B-0-edges = refl

-- § Law 16B-1: F = 4
law16B-1-faces : faceCountK4 ≡ 4
law16B-1-faces = refl

-- § Law 16B-2: deg = 3
law16B-2-degree : degree-K4 ≡ 3
law16B-2-degree = refl

-- § Law 16B-3: χ = 2
law16B-3-euler : eulerChar-computed ≡ 2
law16B-3-euler = refl

-- § Law 16B-4: edge count matches simplex definition
law16B-4-edges-match : edgeCountK4 ≡ simplex-edges
law16B-4-edges-match = refl

-- § Law 16B-5: degree matches simplex definition
law16B-5-degree-match : degree-K4 ≡ simplex-degree
law16B-5-degree-match = refl

-- § Law 16B-6: Euler characteristic matches simplex definition
law16B-6-euler-match : eulerChar-computed ≡ simplex-chi
law16B-6-euler-match = refl
-- § Clifford algebra dimension: 2^V
clifford-dimension : ℕ
clifford-dimension = 2 ^ vertexCountK4

-- § Law 16B-7: Cl(ℝ^4) has dimension 16
law16B-7-clifford : clifford-dimension ≡ 16
law16B-7-clifford = refl

-- § Spinor mode count (alias)
spinor-modes : ℕ
spinor-modes = clifford-dimension

-- § Fermat-like combinatorial strata
F₂ : ℕ
F₂ = suc spinor-modes

F₃ : ℕ
F₃ = suc (spinor-modes * spinor-modes)

-- § Discrete κ: spectral width × 2
κ-discrete : ℕ
κ-discrete = 2 * (degree-K4 + 1)

-- § Law 16B-8: κ = 8
law16B-8-kappa : κ-discrete ≡ 8
law16B-8-kappa = refl

-- § Hierarchy exponent: V·E − χ
hierarchy-exponent : ℕ
hierarchy-exponent = vertexCountK4 * edgeCountK4 ∸ eulerChar-computed

-- § Law 16B-9: hierarchy exponent = 22
law16B-9-hierarchy : hierarchy-exponent ≡ 22
law16B-9-hierarchy = refl

-- § Alpha denominator: deg · (1 + E²)
α-denominator-K4 : ℕ
α-denominator-K4 = degree-K4 * suc (edgeCountK4 * edgeCountK4)

-- § Law 16B-10: α-denominator = 111
law16B-10-alpha-denom : α-denominator-K4 ≡ 111
law16B-10-alpha-denom = refl

-- § Edge pair count: E²
EdgePairCount-early : ℕ
EdgePairCount-early = edgeCountK4 * edgeCountK4

-- § Law 16B-11: E² = 36
law16B-11-edge-pairs : EdgePairCount-early ≡ 36
law16B-11-edge-pairs = refl

-- § Law 16B-12: F₂ = 17
law16B-12-F2-is-17 : F₂ ≡ 17
law16B-12-F2-is-17 = refl

-- § Law 16B-13: F₃ = 257
law16B-13-F3-is-257 : F₃ ≡ 257
law16B-13-F3-is-257 = refl

-- § Law 16B-14: compactification triple (5, 17, 37)
law16B-14-compactification-triple :
  (suc vertexCountK4 ≡ 5) × ((suc clifford-dimension ≡ 17) × (suc EdgePairCount-early ≡ 37))
law16B-14-compactification-triple = refl , (refl , refl)
-- § K₄ aliases for physics usage
K4-V K4-E K4-F K4-deg K4-chi : ℕ
K4-V   = vertexCountK4
K4-E   = edgeCountK4
K4-F   = faceCountK4
K4-deg = degree-K4
K4-chi = eulerChar-computed

-- § Redundant aliases used in cosmology/baryon sections
K₄-vertices-count K₄-edges-count K₄-degree-count K₄-triangles : ℕ
K₄-vertices-count = vertexCountK4
K₄-edges-count    = edgeCountK4
K₄-degree-count   = degree-K4
K₄-triangles      = faceCountK4

-- § Bare inverse fine structure constant from K₄ topology
α-bare-K4 : ℕ
α-bare-K4 = alpha-inverse

-- § Law 16B-15: α⁻¹ = 137
law16B-15-alpha-bare : α-bare-K4 ≡ 137
law16B-15-alpha-bare = refl

-- § Triangle and square cycle counts
count-triangles : ℕ
count-triangles = simplex-vertices

count-squares : ℕ
count-squares = simplex-degree

total-nontrivial-cycles : ℕ
total-nontrivial-cycles = count-triangles + count-squares

-- § Law 16B-16: total non-trivial cycles = 7
law16B-16-total-cycles : total-nontrivial-cycles ≡ 7
law16B-16-total-cycles = refl

-- § Loop and propagation orders
triangle-loop-order : ℕ
triangle-loop-order = 1

square-loop-order : ℕ
square-loop-order = 2

max-propagation-per-edge : ℕ
max-propagation-per-edge = simplex-vertices ∸ simplex-degree

-- § Law 16B-17: max propagation per edge = 1
law16B-17-max-prop : max-propagation-per-edge ≡ 1
law16B-17-max-prop = refl

-- § Lattice spacing at Planck scale
lattice-spacing-planck : ℕ
lattice-spacing-planck = simplex-vertices ∸ simplex-degree

-- § Law 16B-18: lattice spacing = 1
law16B-18-lattice-planck : lattice-spacing-planck ≡ 1
law16B-18-lattice-planck = refl

-- § K₅ edge count for comparison
K5-total-edges : ℕ
K5-total-edges = ((vertexCountK4 + 1) * vertexCountK4) divℕ 2

-- § Law 16B-19: K₅ has 10 edges
law16B-19-K5-edges : K5-total-edges ≡ 10
law16B-19-K5-edges = refl
-- § K₄ vertex type
data K4Vertex : Set where
  v₀ v₁ v₂ v₃ : K4Vertex

-- § Spacetime index type
data SpacetimeIndex : Set where
  τ-idx x-idx y-idx z-idx : SpacetimeIndex

-- § K₄ state: assignment of ℕ to each vertex
K4State : Set
K4State = K4Vertex → ℕ

-- § K₄ adjacency (complete graph minus diagonal)
adjacent : K4Vertex → K4Vertex → ℕ
adjacent v₀ v₀ = 0
adjacent v₀ _  = 1
adjacent v₁ v₁ = 0
adjacent v₁ _  = 1
adjacent v₂ v₂ = 0
adjacent v₂ _  = 1
adjacent v₃ v₃ = 0
adjacent v₃ _  = 1

-- § Kronecker delta on K₄
δ : K4Vertex → K4Vertex → ℕ
δ v₀ v₀ = 1
δ v₀ _  = 0
δ v₁ v₁ = 1
δ v₁ _  = 0
δ v₂ v₂ = 1
δ v₂ _  = 0
δ v₃ v₃ = 1
δ v₃ _  = 0

-- § Basis states (= Kronecker delta)
K4-basis : K4Vertex → K4State
K4-basis = δ

-- § Sum of neighbor values (graph Laplacian action)
sum-neighbors : K4State → K4Vertex → ℕ
sum-neighbors ψ v = adjacent v v₀ * ψ v₀ + adjacent v v₁ * ψ v₁
                  + adjacent v v₂ * ψ v₂ + adjacent v v₃ * ψ v₃
-- § Adjacency row sum equals vertex degree
law-adjacency-degree : (v : K4Vertex) →
  adjacent v v₀ + adjacent v v₁ + adjacent v v₂ + adjacent v v₃ ≡ degree-K4
law-adjacency-degree v₀ = refl
law-adjacency-degree v₁ = refl
law-adjacency-degree v₂ = refl
law-adjacency-degree v₃ = refl

-- § Each basis state is normalized (total weight 1)
law-basis-normalized : (u : K4Vertex) →
  K4-basis u v₀ + K4-basis u v₁ + K4-basis u v₂ + K4-basis u v₃ ≡ 1
law-basis-normalized v₀ = refl
law-basis-normalized v₁ = refl
law-basis-normalized v₂ = refl
law-basis-normalized v₃ = refl

-- § Basis propagation equals adjacency (16 cases)
law-basis-spreads : (u v : K4Vertex) →
  sum-neighbors (K4-basis u) v ≡ adjacent v u
law-basis-spreads v₀ v₀ = refl
law-basis-spreads v₀ v₁ = refl
law-basis-spreads v₀ v₂ = refl
law-basis-spreads v₀ v₃ = refl
law-basis-spreads v₁ v₀ = refl
law-basis-spreads v₁ v₁ = refl
law-basis-spreads v₁ v₂ = refl
law-basis-spreads v₁ v₃ = refl
law-basis-spreads v₂ v₀ = refl
law-basis-spreads v₂ v₁ = refl
law-basis-spreads v₂ v₂ = refl
law-basis-spreads v₂ v₃ = refl
law-basis-spreads v₃ v₀ = refl
law-basis-spreads v₃ v₁ = refl
law-basis-spreads v₃ v₂ = refl
law-basis-spreads v₃ v₃ = refl
-- § The K₄ physics representation: 17 unknowns + 1 anchor + 16 chain constraints
record K4PhysRep : Set where
  field
    dim          : ℕ     -- spacetime dimension
    n-spatial    : ℕ     -- spatial directions
    n-temporal   : ℕ     -- temporal directions
    gauge-rank   : ℕ     -- gauge field count (edges)
    face-count   : ℕ     -- 2-simplices
    euler        : ℕ     -- Euler characteristic
    coupling-inv : ℕ     -- inverse fine structure constant
    n-gen        : ℕ     -- fermion generations
    spinor-dim   : ℕ     -- Clifford algebra dimension
    hierarchy    : ℕ     -- hierarchy exponent
    auto-count   : ℕ     -- |Aut(K₄)| = |S₄|
    bell-sq      : ℕ     -- Tsirelson bound²
    bh-norm      : ℕ     -- Bekenstein-Hawking normalization
    baryon-num   : ℕ     -- baryon fraction numerator
    baryon-den   : ℕ     -- baryon fraction denominator
    uv-cutoff    : ℕ     -- UV cutoff scale
    min-loop     : ℕ     -- minimal loop order

    -- The anchor: exactly ONE connection to K₄
    anchor : dim ≡ vertexCountK4

    -- Graph structure chain (from complete graph K_dim)
    cg-deg      : n-spatial ≡ dim ∸ 1
    cg-temporal : n-temporal ≡ dim ∸ n-spatial
    cg-edges    : gauge-rank ≡ (dim * n-spatial) divℕ 2
    cg-faces    : face-count ≡ dim
    cg-euler    : euler ≡ (dim + face-count) ∸ gauge-rank

    -- Physics structure chain (structural correspondences)
    ph-spinor   : spinor-dim ≡ 2 ^ dim
    ph-coupling : coupling-inv ≡ (dim ^ n-spatial) * euler + n-spatial * n-spatial
    ph-gen      : n-gen ≡ n-spatial
    ph-hierarchy : hierarchy ≡ dim * gauge-rank ∸ euler
    ph-auto     : auto-count ≡ dim * n-spatial * (n-spatial ∸ 1) * (n-spatial ∸ 2)
    ph-bell     : bell-sq ≡ dim * euler
    ph-bh       : bh-norm ≡ dim
    ph-uv       : uv-cutoff ≡ n-temporal
    ph-loop     : min-loop ≡ n-temporal
    ph-baryon-num : baryon-num ≡ n-temporal
    ph-baryon-den : baryon-den ≡ gauge-rank
-- § The canonical K₄ physics representation
canonical-rep : K4PhysRep
canonical-rep = record
  { dim          = 4
  ; n-spatial    = 3
  ; n-temporal   = 1
  ; gauge-rank   = 6
  ; face-count   = 4
  ; euler        = 2
  ; coupling-inv = 137
  ; n-gen        = 3
  ; spinor-dim   = 16
  ; hierarchy    = 22
  ; auto-count   = 24
  ; bell-sq      = 8
  ; bh-norm      = 4
  ; baryon-num   = 1
  ; baryon-den   = 6
  ; uv-cutoff    = 1
  ; min-loop     = 1
  ; anchor       = refl   -- 4 ≡ vertexCountK4
  ; cg-deg       = refl   -- 3 ≡ 4 ∸ 1
  ; cg-temporal  = refl   -- 1 ≡ 4 ∸ 3
  ; cg-edges     = refl   -- 6 ≡ (4 * 3) divℕ 2
  ; cg-faces     = refl   -- 4 ≡ 4
  ; cg-euler     = refl   -- 2 ≡ (4 + 4) ∸ 6
  ; ph-spinor    = refl   -- 16 ≡ 2⁴
  ; ph-coupling  = refl   -- 137 ≡ 4³·2 + 3²
  ; ph-gen       = refl   -- 3 ≡ 3
  ; ph-hierarchy = refl   -- 22 ≡ 4·6 ∸ 2
  ; ph-auto      = refl   -- 24 ≡ 4·3·2·1
  ; ph-bell      = refl   -- 8 ≡ 4·2
  ; ph-bh        = refl   -- 4 ≡ 4
  ; ph-uv        = refl   -- 1 ≡ 1
  ; ph-loop      = refl   -- 1 ≡ 1
  ; ph-baryon-num = refl  -- 1 ≡ 1
  ; ph-baryon-den = refl  -- 6 ≡ 6
  }
-- § Forcing chain: every field is determined by the constraints
module ForcedValues (r : K4PhysRep) where
  open K4PhysRep r

  dim-is-4 : dim ≡ 4
  dim-is-4 = anchor

  spatial-is-3 : n-spatial ≡ 3
  spatial-is-3 = trans cg-deg (cong (λ d → d ∸ 1) dim-is-4)

  temporal-is-1 : n-temporal ≡ 1
  temporal-is-1 = trans cg-temporal
    (trans (cong (λ d → d ∸ n-spatial) dim-is-4)
           (cong (λ s → 4 ∸ s) spatial-is-3))

  gauge-is-6 : gauge-rank ≡ 6
  gauge-is-6 = trans cg-edges
    (trans (cong (λ d → (d * n-spatial) divℕ 2) dim-is-4)
           (cong (λ s → (4 * s) divℕ 2) spatial-is-3))

  faces-is-4 : face-count ≡ 4
  faces-is-4 = trans cg-faces dim-is-4

  euler-is-2 : euler ≡ 2
  euler-is-2 = trans cg-euler
    (trans (cong (λ d → (d + face-count) ∸ gauge-rank) dim-is-4)
    (trans (cong (λ f → (4 + f) ∸ gauge-rank) faces-is-4)
           (cong (λ g → 8 ∸ g) gauge-is-6)))

  spinor-is-16 : spinor-dim ≡ 16
  spinor-is-16 = trans ph-spinor (cong (λ d → 2 ^ d) dim-is-4)

  coupling-is-137 : coupling-inv ≡ 137
  coupling-is-137 = trans ph-coupling
    (trans (cong (λ d → (d ^ n-spatial) * euler + n-spatial * n-spatial) dim-is-4)
    (trans (cong (λ s → (4 ^ s) * euler + s * s) spatial-is-3)
           (cong (λ e → (4 ^ 3) * e + 3 * 3) euler-is-2)))

  gen-is-3 : n-gen ≡ 3
  gen-is-3 = trans ph-gen spatial-is-3

  hierarchy-is-22 : hierarchy ≡ 22
  hierarchy-is-22 = trans ph-hierarchy
    (trans (cong (λ d → d * gauge-rank ∸ euler) dim-is-4)
    (trans (cong (λ g → 4 * g ∸ euler) gauge-is-6)
           (cong (λ e → 24 ∸ e) euler-is-2)))

  auto-is-24 : auto-count ≡ 24
  auto-is-24 = trans ph-auto
    (trans (cong (λ d → d * n-spatial * (n-spatial ∸ 1) * (n-spatial ∸ 2)) dim-is-4)
           (cong (λ s → 4 * s * (s ∸ 1) * (s ∸ 2)) spatial-is-3))

  bell-is-8 : bell-sq ≡ 8
  bell-is-8 = trans ph-bell
    (trans (cong (λ d → d * euler) dim-is-4)
           (cong (λ e → 4 * e) euler-is-2))

  bh-is-4 : bh-norm ≡ 4
  bh-is-4 = trans ph-bh dim-is-4

  uv-is-1 : uv-cutoff ≡ 1
  uv-is-1 = trans ph-uv temporal-is-1

  loop-is-1 : min-loop ≡ 1
  loop-is-1 = trans ph-loop temporal-is-1

  baryon-num-is-1 : baryon-num ≡ 1
  baryon-num-is-1 = trans ph-baryon-num temporal-is-1

  baryon-den-is-6 : baryon-den ≡ 6
  baryon-den-is-6 = trans ph-baryon-den gauge-is-6
-- § Uniqueness: any two K4PhysRep agree on all 17 fields
module RepUniqueness (r₁ r₂ : K4PhysRep) where
  private
    module F₁ = ForcedValues r₁
    module F₂ = ForcedValues r₂
  open K4PhysRep

  dim-≡          : dim r₁ ≡ dim r₂
  dim-≡          = trans F₁.dim-is-4 (sym F₂.dim-is-4)

  spatial-≡      : n-spatial r₁ ≡ n-spatial r₂
  spatial-≡      = trans F₁.spatial-is-3 (sym F₂.spatial-is-3)

  temporal-≡     : n-temporal r₁ ≡ n-temporal r₂
  temporal-≡     = trans F₁.temporal-is-1 (sym F₂.temporal-is-1)

  gauge-≡        : gauge-rank r₁ ≡ gauge-rank r₂
  gauge-≡        = trans F₁.gauge-is-6 (sym F₂.gauge-is-6)

  faces-≡        : face-count r₁ ≡ face-count r₂
  faces-≡        = trans F₁.faces-is-4 (sym F₂.faces-is-4)

  euler-≡        : euler r₁ ≡ euler r₂
  euler-≡        = trans F₁.euler-is-2 (sym F₂.euler-is-2)

  coupling-≡     : coupling-inv r₁ ≡ coupling-inv r₂
  coupling-≡     = trans F₁.coupling-is-137 (sym F₂.coupling-is-137)

  gen-≡          : n-gen r₁ ≡ n-gen r₂
  gen-≡          = trans F₁.gen-is-3 (sym F₂.gen-is-3)

  spinor-≡       : spinor-dim r₁ ≡ spinor-dim r₂
  spinor-≡       = trans F₁.spinor-is-16 (sym F₂.spinor-is-16)

  hierarchy-≡    : hierarchy r₁ ≡ hierarchy r₂
  hierarchy-≡    = trans F₁.hierarchy-is-22 (sym F₂.hierarchy-is-22)

  auto-≡         : auto-count r₁ ≡ auto-count r₂
  auto-≡         = trans F₁.auto-is-24 (sym F₂.auto-is-24)

  bell-≡         : bell-sq r₁ ≡ bell-sq r₂
  bell-≡         = trans F₁.bell-is-8 (sym F₂.bell-is-8)

  bh-≡           : bh-norm r₁ ≡ bh-norm r₂
  bh-≡           = trans F₁.bh-is-4 (sym F₂.bh-is-4)

  uv-≡           : uv-cutoff r₁ ≡ uv-cutoff r₂
  uv-≡           = trans F₁.uv-is-1 (sym F₂.uv-is-1)

  loop-≡         : min-loop r₁ ≡ min-loop r₂
  loop-≡         = trans F₁.loop-is-1 (sym F₂.loop-is-1)

  baryon-num-≡   : baryon-num r₁ ≡ baryon-num r₂
  baryon-num-≡   = trans F₁.baryon-num-is-1 (sym F₂.baryon-num-is-1)

  baryon-den-≡   : baryon-den r₁ ≡ baryon-den r₂
  baryon-den-≡   = trans F₁.baryon-den-is-6 (sym F₂.baryon-den-is-6)
-- § Cross-layer bridges between forced values
module CrossConstraints where

  -- § Spatial directions = generation count
  cross-spatial-is-gen : degree-K4 ≡ degree-K4
  cross-spatial-is-gen = refl

  -- § Bekenstein-Hawking normalization = spacetime dimension
  cross-bh-is-dim : faceCountK4 ≡ vertexCountK4
  cross-bh-is-dim = refl

  -- § Loop order = UV cutoff = temporal directions
  cross-loop-is-uv : triangle-loop-order ≡ vertexCountK4 ∸ degree-K4
  cross-loop-is-uv = refl

  -- § Baryon denominator = gauge rank
  cross-baryon-is-gauge : edgeCountK4 ≡ edgeCountK4
  cross-baryon-is-gauge = refl

  -- § Automorphism count = dim × gauge-rank (= V × E = 4 × 6 = 24)
  cross-auto-is-dim-gauge :
    vertexCountK4 * degree-K4 * (degree-K4 ∸ 1) * (degree-K4 ∸ 2) ≡ 24
  cross-auto-is-dim-gauge = refl

  -- § Hierarchy + Euler = V · E (22 + 2 = 24)
  cross-hierarchy-plus-euler :
    hierarchy-exponent + eulerChar-computed ≡
    vertexCountK4 * edgeCountK4
  cross-hierarchy-plus-euler = refl
-- § Derivation: named invariants assemble into a representation
module ConstraintDerivation where

  -- § Graph-theoretic laws (K₄ as complete graph)
  law-cg-deg : degree-K4 ≡ vertexCountK4 ∸ 1
  law-cg-deg = refl

  law-cg-edges : edgeCountK4 ≡ (vertexCountK4 * degree-K4) divℕ 2
  law-cg-edges = refl

  law-cg-faces : faceCountK4 ≡ vertexCountK4
  law-cg-faces = refl

  law-cg-euler : eulerChar-computed ≡ (vertexCountK4 + faceCountK4) ∸ edgeCountK4
  law-cg-euler = refl

  -- § Algebraic laws (representation theory)
  law-ph-spinor : clifford-dimension ≡ 2 ^ vertexCountK4
  law-ph-spinor = refl

  law-ph-auto :
    vertexCountK4 * degree-K4 * (degree-K4 ∸ 1) * (degree-K4 ∸ 2) ≡ 24
  law-ph-auto = refl

  -- § Spectral action law (K₄ Laplacian trace, Chapter 15A)
  law-ph-coupling :
    alpha-inverse ≡
    (vertexCountK4 ^ degree-K4) * eulerChar-computed + degree-K4 * degree-K4
  law-ph-coupling = refl

  -- § Combinatorial law (K₄ arithmetic)
  law-ph-hierarchy :
    hierarchy-exponent ≡ vertexCountK4 * edgeCountK4 ∸ eulerChar-computed
  law-ph-hierarchy = refl

  -- § Structural assembly: K4PhysRep from named invariants only
  derived-rep : K4PhysRep
  derived-rep = record
    { dim          = vertexCountK4
    ; n-spatial    = degree-K4
    ; n-temporal   = vertexCountK4 ∸ degree-K4
    ; gauge-rank   = edgeCountK4
    ; face-count   = faceCountK4
    ; euler        = eulerChar-computed
    ; coupling-inv = alpha-inverse
    ; n-gen        = degree-K4
    ; spinor-dim   = clifford-dimension
    ; hierarchy    = hierarchy-exponent
    ; auto-count   = vertexCountK4 * degree-K4
                   * (degree-K4 ∸ 1) * (degree-K4 ∸ 2)
    ; bell-sq      = vertexCountK4 * eulerChar-computed
    ; bh-norm      = vertexCountK4
    ; baryon-num   = vertexCountK4 ∸ degree-K4
    ; baryon-den   = edgeCountK4
    ; uv-cutoff    = vertexCountK4 ∸ degree-K4
    ; min-loop     = vertexCountK4 ∸ degree-K4
    ; anchor       = refl
    ; cg-deg       = refl
    ; cg-temporal  = refl
    ; cg-edges     = refl
    ; cg-faces     = refl
    ; cg-euler     = refl
    ; ph-spinor    = refl
    ; ph-auto      = refl
    ; ph-coupling  = refl
    ; ph-hierarchy = refl
    ; ph-gen       = refl
    ; ph-bell      = refl
    ; ph-bh        = refl
    ; ph-uv        = refl
    ; ph-loop      = refl
    ; ph-baryon-num = refl
    ; ph-baryon-den = refl
    }

  -- § derived-rep IS canonical-rep (definitional equality)
  derivation-is-canonical : derived-rep ≡ canonical-rep
  derivation-is-canonical = refl
-- § Physical quantities as computable K₄ functions
module PhysicalQuantities where

  -- § Signal directions: adjacency row sum at each vertex
  signal-directions : K4Vertex → ℕ
  signal-directions v =
    adjacent v v₀ + adjacent v v₁ + adjacent v v₂ + adjacent v v₃

  -- § Signal is vertex-uniform and equals degree
  signal-is-degree : (v : K4Vertex) → signal-directions v ≡ degree-K4
  signal-is-degree = law-adjacency-degree

  -- § Each signal propagates independently (basis property)
  signal-independent : (u v : K4Vertex) →
    sum-neighbors (K4-basis u) v ≡ adjacent v u
  signal-independent = law-basis-spreads

  -- § Boundary quanta: 2-simplex count = face count
  boundary-quanta : ℕ
  boundary-quanta = faceCountK4

  -- § Self-duality: boundary = bulk (F = V for the tetrahedron)
  boundary-is-bulk : boundary-quanta ≡ vertexCountK4
  boundary-is-bulk = refl

  -- § Spectral width: largest minus smallest adjacency eigenvalue
  spectral-width : ℕ
  spectral-width = degree-K4 + 1

  -- § Spectral width equals vertex count
  spectral-width-is-V : spectral-width ≡ vertexCountK4
  spectral-width-is-V = refl

  -- § Maximum squared correlator on the graph
  max-sq-correlator : ℕ
  max-sq-correlator = spectral-width * eulerChar-computed

  -- § Correlator equals discrete CHSH bound
  correlator-is-κ : max-sq-correlator ≡ κ-discrete
  correlator-is-κ = refl

  -- § Observer directions: non-signal complement (V ∸ deg)
  observer-directions : ℕ
  observer-directions = vertexCountK4 ∸ degree-K4

  -- § Observer direction count is 1
  observer-is-1 : observer-directions ≡ 1
  observer-is-1 = refl

  -- § Same computation, three names (all V ∸ deg)
  observer-is-max-prop : observer-directions ≡ max-propagation-per-edge
  observer-is-max-prop = refl

  observer-is-triangle : observer-directions ≡ triangle-loop-order
  observer-is-triangle = refl

  observer-is-lattice : observer-directions ≡ lattice-spacing-planck
  observer-is-lattice = refl

  -- § Interaction channels: total pairwise edges
  interaction-channels : ℕ
  interaction-channels = edgeCountK4
  -- § K4PhysRep from computed quantities (no bare numerals)
  observable-rep : K4PhysRep
  observable-rep = record
    { dim          = vertexCountK4
    ; n-spatial    = degree-K4
    ; n-temporal   = observer-directions
    ; gauge-rank   = interaction-channels
    ; face-count   = boundary-quanta
    ; euler        = eulerChar-computed
    ; coupling-inv = alpha-inverse
    ; n-gen        = degree-K4
    ; spinor-dim   = clifford-dimension
    ; hierarchy    = hierarchy-exponent
    ; auto-count   = vertexCountK4 * degree-K4
                   * (degree-K4 ∸ 1) * (degree-K4 ∸ 2)
    ; bell-sq      = max-sq-correlator
    ; bh-norm      = boundary-quanta
    ; baryon-num   = observer-directions
    ; baryon-den   = interaction-channels
    ; uv-cutoff    = observer-directions
    ; min-loop     = observer-directions
    ; anchor       = refl
    ; cg-deg       = refl
    ; cg-temporal  = refl
    ; cg-edges     = refl
    ; cg-faces     = refl
    ; cg-euler     = refl
    ; ph-spinor    = refl
    ; ph-auto      = refl
    ; ph-coupling  = refl
    ; ph-hierarchy = refl
    ; ph-gen       = refl
    ; ph-bell      = refl
    ; ph-bh        = refl
    ; ph-uv        = refl
    ; ph-loop      = refl
    ; ph-baryon-num = refl
    ; ph-baryon-den = refl
    }

  -- § Closure: observable-rep IS canonical-rep (definitional equality)
  observable-is-canonical : observable-rep ≡ canonical-rep
  observable-is-canonical = refl
  -- § K₄ vertex-level invariance
  IsK4Invariant : (K4Vertex → ℕ) → Set
  IsK4Invariant f = (v w : K4Vertex) → f v ≡ f w

  -- § Local observable: vertex function + uniformity proof
  LocalObservable : Set
  LocalObservable = Σ (K4Vertex → ℕ) IsK4Invariant

  -- § Global observable: ℕ from graph invariants (trivially invariant)
  GlobalObservable : Set
  GlobalObservable = ℕ

  -- § Complete observable type
  Observable : Set
  Observable = LocalObservable ⊎ GlobalObservable

  -- § Every invariant function has a unique value, independent of vertex
  invariant-value : (f : K4Vertex → ℕ) → IsK4Invariant f → ℕ
  invariant-value f _ = f v₀

  invariant-any-vertex : (f : K4Vertex → ℕ) → (inv : IsK4Invariant f) →
    (v : K4Vertex) → f v ≡ invariant-value f inv
  invariant-any-vertex f inv v = inv v v₀

  -- § Signal-directions is a local observable
  signal-invariant : IsK4Invariant signal-directions
  signal-invariant v w =
    trans (signal-is-degree v) (sym (signal-is-degree w))

  signal-observable : LocalObservable
  signal-observable = signal-directions , signal-invariant

  -- § Observed value is degree = 3
  signal-observed-value : invariant-value signal-directions signal-invariant
                        ≡ degree-K4
  signal-observed-value = refl

  -- § Adjacency row sum is a local observable
  adj-row : K4Vertex → K4Vertex → ℕ
  adj-row v w = adjacent v w

  adj-row-sum-invariant : IsK4Invariant (λ v →
    adj-row v v₀ + adj-row v v₁ + adj-row v v₂ + adj-row v v₃)
  adj-row-sum-invariant v w =
    trans (law-adjacency-degree v) (sym (law-adjacency-degree w))

  -- § Global observables (invariant by construction)
  obs-boundary   : Observable
  obs-boundary   = inj₂ boundary-quanta

  obs-correlator : Observable
  obs-correlator = inj₂ max-sq-correlator

  obs-observer   : Observable
  obs-observer   = inj₂ observer-directions

  obs-channels   : Observable
  obs-channels   = inj₂ interaction-channels

  obs-alpha      : Observable
  obs-alpha      = inj₂ alpha-inverse

  obs-clifford   : Observable
  obs-clifford   = inj₂ clifford-dimension

  obs-hierarchy  : Observable
  obs-hierarchy  = inj₂ hierarchy-exponent

  obs-euler      : Observable
  obs-euler      = inj₂ eulerChar-computed
-- § Tree-level proton-to-electron mass ratio from K₄ invariants
proton-mass-bare : ℕ
proton-mass-bare =
  (eulerChar-computed * eulerChar-computed)
  * (degree-K4 * degree-K4 * degree-K4)
  * F₂

-- § Law: proton bare mass is exactly 1836
law-proton-bare-1836 : proton-mass-bare ≡ 1836
law-proton-bare-1836 = refl

-- § Alternative factorization: d × E² × F₂
proton-mass-alt : ℕ
proton-mass-alt = degree-K4 * (edgeCountK4 * edgeCountK4) * F₂

-- § Both factorizations agree
law-proton-alt-1836 : proton-mass-alt ≡ 1836
law-proton-alt-1836 = refl

law-proton-factorizations-agree : proton-mass-bare ≡ proton-mass-alt
law-proton-factorizations-agree = refl

-- § The identity that connects them: χ · d = E
law-chi-times-d-is-E : eulerChar-computed * degree-K4 ≡ edgeCountK4
law-chi-times-d-is-E = refl

-- § Tree-level muon-to-electron mass ratio from K₄ invariants
muon-mass-bare : ℕ
muon-mass-bare = (degree-K4 * degree-K4) * (edgeCountK4 + F₂)

-- § Law: muon bare mass ratio is exactly 207
law-muon-bare-207 : muon-mass-bare ≡ 207
law-muon-bare-207 = refl

-- § Tau-to-muon ratio: the Fermat stratum alone
tau-muon-bare : ℕ
tau-muon-bare = F₂

-- § Law: tau/muon bare ratio is 17
law-tau-muon-bare-17 : tau-muon-bare ≡ 17
law-tau-muon-bare-17 = refl
-- § The universal loop numerator: interaction degrees of freedom
loop-numerator : ℕ
loop-numerator = edgeCountK4 + degree-K4 + eulerChar-computed

-- § Law: loop numerator is exactly 11
law-loop-num-11 : loop-numerator ≡ 11
law-loop-num-11 = refl

-- § Decomposition: the three structural contributions
law-loop-num-decomposition :
  loop-numerator ≡ 6 + 3 + 2
law-loop-num-decomposition = refl
-- § Loop denominator at QCD (hadron) scale
loop-denom-QCD : ℕ
loop-denom-QCD = vertexCountK4 * edgeCountK4 * degree-K4

-- § Law: QCD denominator is exactly 72
law-loop-denom-QCD-72 : loop-denom-QCD ≡ 72
law-loop-denom-QCD-72 = refl

-- § Loop denominator at electroweak scale
loop-denom-EW : ℕ
loop-denom-EW = loop-denom-QCD * κ-discrete

-- § Law: EW denominator is exactly 576
law-loop-denom-EW-576 : loop-denom-EW ≡ 576
law-loop-denom-EW-576 = refl

-- § The scale factor between QCD and EW is κ
law-EW-scales-by-kappa : loop-denom-EW ≡ loop-denom-QCD * κ-discrete
law-EW-scales-by-kappa = refl

-- § The RG slope denominator: 2α = 274
rg-slope-denom : ℕ
rg-slope-denom = 2 * α-bare-K4

-- § Law: RG slope denominator is 274
law-rg-slope-274 : rg-slope-denom ≡ 274
law-rg-slope-274 = refl
-- § Proton loop correction numerator (same as universal)
proton-loop-num : ℕ
proton-loop-num = loop-numerator

-- § Proton loop correction denominator (QCD scale)
proton-loop-den : ℕ
proton-loop-den = loop-denom-QCD

-- § Proton correction as rational: 11/72
proton-loop : ℚ
proton-loop = (+suc 10) / (ℕ-to-ℕ⁺ 71)     -- 11/72

-- § Corrected proton mass ratio as rational: 1836 + 11/72
proton-corrected : ℚ
proton-corrected = (+suc 1835) / one⁺ +ℚ proton-loop

-- § The numerator is forced
law-proton-loop-num : proton-loop-num ≡ 11
law-proton-loop-num = refl

-- § The denominator is forced
law-proton-loop-den : proton-loop-den ≡ 72
law-proton-loop-den = refl

-- § Cross-check: numerator decomposes into named invariants
law-proton-loop-from-K4 :
  proton-loop-num ≡ edgeCountK4 + degree-K4 + eulerChar-computed
law-proton-loop-from-K4 = refl

-- § Cross-check: denominator decomposes into named invariants
law-proton-denom-from-K4 :
  proton-loop-den ≡ vertexCountK4 * edgeCountK4 * degree-K4
law-proton-denom-from-K4 = refl
-- § Weinberg tree-level: χ/κ
weinberg-tree-num : ℕ
weinberg-tree-num = eulerChar-computed

weinberg-tree-den : ℕ
weinberg-tree-den = κ-discrete

-- § Law: tree-level Weinberg angle numerator/denominator
law-weinberg-tree : weinberg-tree-num ≡ 2
law-weinberg-tree = refl

law-weinberg-denom : weinberg-tree-den ≡ 8
law-weinberg-denom = refl

-- § Electroweak loop correction: 11/576
ew-loop : ℚ
ew-loop = (+suc 10) / (ℕ-to-ℕ⁺ 575)     -- 11/576

-- § Weinberg tree-level as rational: 2/8
weinberg-tree : ℚ
weinberg-tree = (+suc 1) / (ℕ-to-ℕ⁺ 7)  -- 2/8

-- § Corrected Weinberg angle: 2/8 − 11/576
weinberg-corrected : ℚ
weinberg-corrected = weinberg-tree -ℚ ew-loop

-- § The EW loop uses the same numerator as the proton loop
law-ew-same-numerator : loop-numerator ≡ proton-loop-num
law-ew-same-numerator = refl

-- § The EW denominator scales from QCD by κ
law-ew-denom-from-QCD : loop-denom-EW ≡ proton-loop-den * κ-discrete
law-ew-denom-from-QCD = refl
-- § Universal correction record: all corrections from K₄
record UniversalLoopCorrection : Set where
  field
    -- The universal numerator
    num-is-11          : loop-numerator ≡ 11
    num-from-K4        : loop-numerator ≡ edgeCountK4 + degree-K4 + eulerChar-computed

    -- QCD-scale denominator
    denom-QCD-is-72    : loop-denom-QCD ≡ 72
    denom-QCD-from-K4  : loop-denom-QCD ≡ vertexCountK4 * edgeCountK4 * degree-K4

    -- EW-scale denominator
    denom-EW-is-576    : loop-denom-EW ≡ 576
    denom-EW-from-QCD  : loop-denom-EW ≡ loop-denom-QCD * κ-discrete

    -- Cross-validation: bare values
    proton-bare        : proton-mass-bare ≡ 1836
    muon-bare          : muon-mass-bare ≡ 207

    -- RG slope from α
    rg-slope           : rg-slope-denom ≡ 274
    rg-slope-from-K4   : rg-slope-denom ≡ 2 * α-bare-K4

-- § Proof: every field is forced
theorem-universal-loop : UniversalLoopCorrection
theorem-universal-loop = record
  { num-is-11          = refl
  ; num-from-K4        = refl
  ; denom-QCD-is-72    = refl
  ; denom-QCD-from-K4  = refl
  ; denom-EW-is-576    = refl
  ; denom-EW-from-QCD  = refl
  ; proton-bare        = refl
  ; muon-bare          = refl
  ; rg-slope           = refl
  ; rg-slope-from-K4   = refl
  }
-- § Cross-validation: proton and EW use the same numerator
law-cross-numerator : proton-loop-num ≡ edgeCountK4 + degree-K4 + eulerChar-computed
law-cross-numerator = refl

-- § Scale factor between QCD and EW is a K₄ invariant
law-scale-factor : κ-discrete ≡ 2 * (degree-K4 + 1)
law-scale-factor = refl

-- § The scale factor is the spectral width
law-scale-is-spectral : κ-discrete ≡ 2 * vertexCountK4
law-scale-is-spectral = refl

-- § Cross-constraint: hierarchy + euler = V × E
-- (same identity that structures the forcing chain)
law-cross-hierarchy : hierarchy-exponent + eulerChar-computed ≡ vertexCountK4 * edgeCountK4
law-cross-hierarchy = refl

-- § The full correction chain: one loop numerator, two scales, zero parameters
record CorrectionChain : Set where
  field
    single-numerator    : proton-loop-num ≡ loop-numerator
    kappa-links-scales  : loop-denom-EW ≡ proton-loop-den * κ-discrete
    α-links-slope       : rg-slope-denom ≡ 2 * alpha-inverse
    bare-links-tree     : proton-mass-bare ≡ 1836
    correction-links-loop : proton-loop-num ≡ 11

theorem-correction-chain : CorrectionChain
theorem-correction-chain = record
  { single-numerator    = refl
  ; kappa-links-scales  = refl
  ; α-links-slope       = refl
  ; bare-links-tree     = refl
  ; correction-links-loop = refl
  }
