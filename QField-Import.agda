{-# OPTIONS --safe --without-K #-}

-- ═══════════════════════════════════════════════════════════════════════════════
--
--   ℚ FIELD STRUCTURE: Complete Field Laws from K₄ Topology
--
--   This module IMPORTS from FirstDistinction and completes the ℚ field laws.
--   
--   Already available from FirstDistinction:
--     - ℕ, ℤ, ℕ⁺, ℚ types and operations
--     - All ℤ ring laws (+ℤ-comm, +ℤ-assoc, *ℤ-comm, *ℤ-assoc, etc.)
--     - ≃ℤ equivalence with refl, sym, trans
--     - +ℤ-cong, *ℤ-cong (congruence)
--     - ⁺toℕ-+⁺, ⁺toℕ-*⁺, ⁺toℤ-*⁺ (homomorphisms)
--     - ≃ℚ-refl, ≃ℚ-sym
--     - *ℚ-cong
--
-- ═══════════════════════════════════════════════════════════════════════════════

module QField-Import where

open import FirstDistinction public

-- ─────────────────────────────────────────────────────────────────────────────
-- § 1  MISSING ℕ⁺ LAWS
-- ─────────────────────────────────────────────────────────────────────────────

-- We need *⁺-comm for some ℚ proofs
-- First we need +⁺-comm

+⁺-suc⁺ : ∀ a b → (a +⁺ suc⁺ b) ≡ suc⁺ (a +⁺ b)
+⁺-suc⁺ one⁺     b = refl
+⁺-suc⁺ (suc⁺ a) b = cong suc⁺ (+⁺-suc⁺ a b)

+⁺-comm : ∀ a b → (a +⁺ b) ≡ (b +⁺ a)
+⁺-comm one⁺ one⁺         = refl
+⁺-comm one⁺ (suc⁺ b)     = cong suc⁺ (+⁺-comm one⁺ b)
+⁺-comm (suc⁺ a) one⁺     = cong suc⁺ (+⁺-comm a one⁺)
+⁺-comm (suc⁺ a) (suc⁺ b) = cong suc⁺ (trans (+⁺-suc⁺ a b) 
                                       (trans (cong suc⁺ (+⁺-comm a b)) 
                                              (sym (+⁺-suc⁺ b a))))

-- Now *⁺-comm via the homomorphism
-- We show a *⁺ b = b *⁺ a by showing ⁺toℕ (a *⁺ b) = ⁺toℕ (b *⁺ a)
-- and using that ⁺toℕ is injective on equal results

-- ⊥-elim for eliminating absurdity
⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Helper: ⁺toℕ is injective (suc n = suc m implies structural equality)
suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

-- zero≠suc follows from constructors being distinct
zero≢suc : ∀ {n : ℕ} → zero ≡ suc n → ⊥
zero≢suc ()

-- Helper: ⁺toℕ always returns suc something
⁺toℕ-is-suc : ∀ (a : ℕ⁺) → Σ ℕ (λ n → ⁺toℕ a ≡ suc n)
⁺toℕ-is-suc one⁺ = zero , refl
⁺toℕ-is-suc (suc⁺ a) with ⁺toℕ-is-suc a
... | n , pf = suc n , cong suc pf

-- We can use a simpler approach: prove by the structure directly
-- Note: ⁺toℕ one⁺ = suc zero, ⁺toℕ (suc⁺ a) = suc (⁺toℕ a)
⁺toℕ-injective : ∀ (a b : ℕ⁺) → ⁺toℕ a ≡ ⁺toℕ b → a ≡ b
⁺toℕ-injective one⁺ one⁺ eq = refl
⁺toℕ-injective one⁺ (suc⁺ b) eq = 
  -- eq : suc zero ≡ suc (⁺toℕ b), where ⁺toℕ b ≥ suc zero
  -- suc-inj eq : zero ≡ ⁺toℕ b, but ⁺toℕ b is always suc something
  let inner = suc-inj eq  -- zero ≡ ⁺toℕ b
      (n , pf) = ⁺toℕ-is-suc b  -- ⁺toℕ b ≡ suc n  
  in ⊥-elim (zero≢suc (trans inner pf))
⁺toℕ-injective (suc⁺ a) one⁺ eq = 
  let inner = suc-inj eq  -- ⁺toℕ a ≡ zero
      (n , pf) = ⁺toℕ-is-suc a  -- ⁺toℕ a ≡ suc n
  in ⊥-elim (zero≢suc (trans (sym inner) pf))
⁺toℕ-injective (suc⁺ a) (suc⁺ b) eq = cong suc⁺ (⁺toℕ-injective a b (suc-inj eq))

*⁺-comm : ∀ a b → (a *⁺ b) ≡ (b *⁺ a)
*⁺-comm a b = ⁺toℕ-injective (a *⁺ b) (b *⁺ a) 
                             (trans (⁺toℕ-*⁺ a b) 
                              (trans (*-comm (⁺toℕ a) (⁺toℕ b)) 
                                     (sym (⁺toℕ-*⁺ b a))))

-- Also need *⁺-assoc for *ℚ-assoc
*⁺-assoc : ∀ a b c → ((a *⁺ b) *⁺ c) ≡ (a *⁺ (b *⁺ c))
*⁺-assoc a b c = ⁺toℕ-injective ((a *⁺ b) *⁺ c) (a *⁺ (b *⁺ c))
  (trans (⁺toℕ-*⁺ (a *⁺ b) c)
  (trans (cong (λ x → x * ⁺toℕ c) (⁺toℕ-*⁺ a b))
  (trans (sym (*-assoc (⁺toℕ a) (⁺toℕ b) (⁺toℕ c)))
  (trans (cong (λ x → ⁺toℕ a * x) (sym (⁺toℕ-*⁺ b c)))
         (sym (⁺toℕ-*⁺ a (b *⁺ c)))))))

-- ─────────────────────────────────────────────────────────────────────────────
-- § 2  ≃ℚ TRANSITIVITY
-- ─────────────────────────────────────────────────────────────────────────────

-- This is the hardest proof - we need ℤ cancellation with non-zero factor
-- 
-- Given: (a *ℤ ⁺toℤ d) ≃ℤ (c *ℤ ⁺toℤ b)   ... (1)
--        (c *ℤ ⁺toℤ f) ≃ℤ (e *ℤ ⁺toℤ d)   ... (2)
-- Need:  (a *ℤ ⁺toℤ f) ≃ℤ (e *ℤ ⁺toℤ b)
--
-- Strategy: Multiply (1) by ⁺toℤ f and (2) by ⁺toℤ b
--   (1) * f: (a * d) * f ≃ (c * b) * f
--   (2) * b: (c * f) * b ≃ (e * d) * b
-- Rearrange using associativity:
--   a * (d * f) ≃ c * (b * f)   ... (1')
--   c * (f * b) ≃ e * (d * b)   ... (2')
-- By commutativity: b*f = f*b, d*b = b*d
-- So: a * (d * f) ≃ c * (b * f) and c * (b * f) ≃ e * (b * d)
-- Need to cancel (d * f) ≃ (b * d)? No, that's wrong...
--
-- Actually: multiply (1) by f on both sides, (2) by b:
--   a*d*f ≃ c*b*f
--   c*f*b ≃ e*d*b
-- Since c*b*f = c*f*b (by comm), we have a*d*f ≃ e*d*b
-- Cancel d (non-zero!): a*f ≃ e*b? 
-- This requires ℤ cancellation which is tricky...

-- The key insight: we don't need to cancel d explicitly.
-- We use the fact that ≃ℤ is transitive on ℤ (already proven in FirstDistinction).
-- 
-- The proof works by multiplying both equivalences by appropriate factors
-- and then using algebraic manipulation to get the desired form.

≃ℚ-trans : {p q r : ℚ} → p ≃ℚ q → q ≃ℚ r → p ≃ℚ r
≃ℚ-trans {a / b} {c / d} {e / f} pq qr = 
  -- pq : (a *ℤ ⁺toℤ d) ≃ℤ (c *ℤ ⁺toℤ b)
  -- qr : (c *ℤ ⁺toℤ f) ≃ℤ (e *ℤ ⁺toℤ d)
  -- Need: (a *ℤ ⁺toℤ f) ≃ℤ (e *ℤ ⁺toℤ b)
  --
  -- Strategy: Multiply pq by ⁺toℤ f and qr by ⁺toℤ b, then combine.
  --
  -- pq * f: (a*d)*f ≃ (c*b)*f
  -- qr * b: (c*f)*b ≃ (e*d)*b  
  --
  -- Rearranging: a*(d*f) ≃ c*(b*f) and c*(f*b) ≃ e*(d*b)
  -- Since b*f = f*b, we get: a*(d*f) ≃ c*(f*b) ≃ e*(d*b)
  -- By ≃ℤ-trans: a*(d*f) ≃ e*(d*b)
  --
  -- Now: a*(d*f) = (a*f)*d and e*(d*b) = (e*b)*d (by assoc/comm)
  -- So: (a*f)*d ≃ (e*b)*d
  --
  -- Final step: We need (a*f) ≃ (e*b), but we have (a*f)*d ≃ (e*b)*d.
  -- This is where cancellation would be needed. 
  --
  -- Alternative approach: Show directly that the cross-multiplication holds.
  -- (a*f) * ⁺toℤ b ≃ (e*b) * ⁺toℤ f... wait, that's not what we need.
  --
  -- Actually, we need: (a * ⁺toℤ f) ≃ℤ (e * ⁺toℤ b)
  -- i.e., pos(a)*pos(f) + neg(a)*neg(f) + neg(e)*pos(b) + pos(e)*neg(b) = 
  --       pos(a)*neg(f) + neg(a)*pos(f) + pos(e)*pos(b) + neg(e)*neg(b)
  --
  -- This is complex. For now, we use the algebraic approach.
  let
    -- Multiply pq by ⁺toℤ f on the right
    pq-f : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≃ℤ ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    pq-f = *ℤ-cong {a *ℤ ⁺toℤ d} {c *ℤ ⁺toℤ b} {⁺toℤ f} {⁺toℤ f} pq (≃ℤ-refl (⁺toℤ f))
    
    -- Multiply qr by ⁺toℤ b on the right
    qr-b : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≃ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    qr-b = *ℤ-cong {c *ℤ ⁺toℤ f} {e *ℤ ⁺toℤ d} {⁺toℤ b} {⁺toℤ b} qr (≃ℤ-refl (⁺toℤ b))
    
    -- Rearrange (a*d)*f to a*(d*f)
    lhs-assoc : ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≃ℤ (a *ℤ (⁺toℤ d *ℤ ⁺toℤ f))
    lhs-assoc = *ℤ-assoc a (⁺toℤ d) (⁺toℤ f)
    
    -- Rearrange (c*b)*f to c*(b*f)
    mid1-assoc : ((c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≃ℤ (c *ℤ (⁺toℤ b *ℤ ⁺toℤ f))
    mid1-assoc = *ℤ-assoc c (⁺toℤ b) (⁺toℤ f)
    
    -- Rearrange (c*f)*b to c*(f*b)
    mid2-assoc : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≃ℤ (c *ℤ (⁺toℤ f *ℤ ⁺toℤ b))
    mid2-assoc = *ℤ-assoc c (⁺toℤ f) (⁺toℤ b)
    
    -- b*f = f*b
    bf-comm : (⁺toℤ b *ℤ ⁺toℤ f) ≃ℤ (⁺toℤ f *ℤ ⁺toℤ b)
    bf-comm = *ℤ-comm (⁺toℤ b) (⁺toℤ f)
    
    -- c*(b*f) ≃ c*(f*b)
    mid-eq : (c *ℤ (⁺toℤ b *ℤ ⁺toℤ f)) ≃ℤ (c *ℤ (⁺toℤ f *ℤ ⁺toℤ b))
    mid-eq = *ℤ-cong {c} {c} {⁺toℤ b *ℤ ⁺toℤ f} {⁺toℤ f *ℤ ⁺toℤ b} (≃ℤ-refl c) bf-comm
    
    -- Rearrange (e*d)*b to e*(d*b)
    rhs-assoc : ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) ≃ℤ (e *ℤ (⁺toℤ d *ℤ ⁺toℤ b))
    rhs-assoc = *ℤ-assoc e (⁺toℤ d) (⁺toℤ b)
    
    -- Chain: a*(d*f) ≃ c*(b*f) ≃ c*(f*b) ≃ e*(d*b)
    -- step A: a*(d*f) ≃ c*(b*f)
    stepA : (a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)) ≃ℤ (c *ℤ (⁺toℤ b *ℤ ⁺toℤ f))
    stepA = ≃ℤ-trans {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {(a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f} {c *ℤ (⁺toℤ b *ℤ ⁺toℤ f)}
                     (≃ℤ-sym {(a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f} {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} lhs-assoc)
                     (≃ℤ-trans {(a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f} {(c *ℤ ⁺toℤ b) *ℤ ⁺toℤ f} {c *ℤ (⁺toℤ b *ℤ ⁺toℤ f)}
                               pq-f mid1-assoc)
    
    -- step B: c*(f*b) ≃ e*(d*b)
    stepB : (c *ℤ (⁺toℤ f *ℤ ⁺toℤ b)) ≃ℤ (e *ℤ (⁺toℤ d *ℤ ⁺toℤ b))
    stepB = ≃ℤ-trans {c *ℤ (⁺toℤ f *ℤ ⁺toℤ b)} {(c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b} {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)}
                     (≃ℤ-sym {(c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b} {c *ℤ (⁺toℤ f *ℤ ⁺toℤ b)} mid2-assoc)
                     (≃ℤ-trans {(c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b} {(e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b} {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)}
                               qr-b rhs-assoc)
    
    -- Combined: a*(d*f) ≃ e*(d*b)
    combined : (a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)) ≃ℤ (e *ℤ (⁺toℤ d *ℤ ⁺toℤ b))
    combined = ≃ℤ-trans {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {c *ℤ (⁺toℤ b *ℤ ⁺toℤ f)} {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)}
                        stepA 
                        (≃ℤ-trans {c *ℤ (⁺toℤ b *ℤ ⁺toℤ f)} {c *ℤ (⁺toℤ f *ℤ ⁺toℤ b)} {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)}
                                  mid-eq stepB)
    
    -- Now rearrange a*(d*f) = (a*f)*d and e*(d*b) = (e*b)*d
    -- Then factor out d:  (a*f)*d ≃ (e*b)*d
    -- This is where we'd need cancellation to get a*f ≃ e*b
    
    -- Alternative: Use homomorphism ⁺toℤ (d *⁺ f) = ⁺toℤ d * ⁺toℤ f
    -- and show the result directly
    
    -- Rearrange to (a*f)*(⁺toℤ d) ≃ (e*b)*(⁺toℤ d)
    lhs-rearr : (a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)) ≃ℤ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d)
    lhs-rearr = ≃ℤ-trans {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {a *ℤ (⁺toℤ f *ℤ ⁺toℤ d)} {(a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d}
                (*ℤ-cong {a} {a} {⁺toℤ d *ℤ ⁺toℤ f} {⁺toℤ f *ℤ ⁺toℤ d} (≃ℤ-refl a) (*ℤ-comm (⁺toℤ d) (⁺toℤ f)))
                (≃ℤ-sym {(a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d} {a *ℤ (⁺toℤ f *ℤ ⁺toℤ d)} (*ℤ-assoc a (⁺toℤ f) (⁺toℤ d)))
    
    rhs-rearr : (e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)) ≃ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    rhs-rearr = ≃ℤ-trans {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)} {e *ℤ (⁺toℤ b *ℤ ⁺toℤ d)} {(e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d}
                (*ℤ-cong {e} {e} {⁺toℤ d *ℤ ⁺toℤ b} {⁺toℤ b *ℤ ⁺toℤ d} (≃ℤ-refl e) (*ℤ-comm (⁺toℤ d) (⁺toℤ b)))
                (≃ℤ-sym {(e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d} {e *ℤ (⁺toℤ b *ℤ ⁺toℤ d)} (*ℤ-assoc e (⁺toℤ b) (⁺toℤ d)))
    
    -- (a*f)*d ≃ (e*b)*d
    factored : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ≃ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    factored = ≃ℤ-trans {(a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d} {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {(e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d}
               (≃ℤ-sym {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {(a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d} lhs-rearr)
               (≃ℤ-trans {a *ℤ (⁺toℤ d *ℤ ⁺toℤ f)} {e *ℤ (⁺toℤ d *ℤ ⁺toℤ b)} {(e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d}
                         combined rhs-rearr)
    
    -- Now we need to cancel ⁺toℤ d. Since d : ℕ⁺, ⁺toℤ d is always positive (≥ 1).
    -- We need: *ℤ-cancelʳ : x*z ≃ y*z → z ≠ 0 → x ≃ y
    -- This requires additional machinery.
    --
    -- For now, we observe that ≃ℤ on our representation is:
    -- (mkℤ a b) ≃ℤ (mkℤ c d) iff a + d = c + b
    --
    -- So factored says: pos((a*f)*d) + neg((a*f)*d) + neg((e*b)*d) + pos((e*b)*d)
    --                  = pos((a*f)*d) + neg((e*b)*d) + ... 
    -- (this gets complicated)
    --
    -- The clean approach is to prove *ℤ-cancelʳ-⁺toℤ specifically for ⁺toℤ factors.
    
  in *ℤ-cancelʳ-⁺ {a *ℤ ⁺toℤ f} {e *ℤ ⁺toℤ b} d factored
  where
    -- ℕ multiplication cancellation for non-zero factor
    -- Proof: By induction on x and y, using the fact that 
    -- x * suc k = x + x * k, so if x * suc k = y * suc k, then x + x*k = y + y*k
    -- By +-cancelʳ (with x*k as the common term after manipulation)
    *-cancelʳ-ℕ : ∀ (x y k : ℕ) → (x * suc k) ≡ (y * suc k) → x ≡ y
    *-cancelʳ-ℕ zero zero k eq = refl
    *-cancelʳ-ℕ zero (suc y) k eq = 
      -- 0 = suc y * suc k = suc k + y * suc k ≥ suc k ≥ 1, contradiction
      ⊥-elim (zero≢suc (trans eq (sym (+-suc-lemma k (y * suc k)))))
      where
        +-suc-lemma : ∀ a b → suc a + b ≡ suc (a + b)
        +-suc-lemma a b = refl
    *-cancelʳ-ℕ (suc x) zero k eq = 
      -- suc x * suc k = 0, but suc x * suc k ≥ suc k ≥ 1, contradiction
      ⊥-elim (zero≢suc (sym (trans eq refl)))
    *-cancelʳ-ℕ (suc x) (suc y) k eq = 
      -- suc x * suc k = suc k + x * suc k
      -- suc y * suc k = suc k + y * suc k
      -- So: suc k + x * suc k = suc k + y * suc k
      -- By +-cancelʳ: x * suc k = y * suc k
      -- By IH: x = y
      cong suc (*-cancelʳ-ℕ x y k (suc-inj-prod eq))
      where
        -- suc x * suc k = suc k + x * suc k, suc y * suc k = suc k + y * suc k
        -- eq : suc k + x * suc k = suc k + y * suc k
        -- Need: x * suc k = y * suc k (for IH call)
        -- 
        -- Note: suc k + m = suc (k + m), so
        -- suc (k + x * suc k) = suc (k + y * suc k)
        -- By suc-inj: k + x * suc k = k + y * suc k
        -- By +-cancelʳ: x * suc k = y * suc k
        suc-inj-prod : (suc k + x * suc k) ≡ (suc k + y * suc k) → (x * suc k) ≡ (y * suc k)
        suc-inj-prod pf = +-cancelʳ (x * suc k) (y * suc k) k 
                          (trans (+-comm (x * suc k) k) 
                          (trans (suc-inj pf) 
                                 (+-comm k (y * suc k))))
    
    -- Helper: cancellation for multiplication by suc k
    *-cancelʳ-suc : ∀ (x y : ℕ) (n : ℕ) → (Σ ℕ (λ k → n ≡ suc k)) → (x * n) ≡ (y * n) → x ≡ y
    *-cancelʳ-suc x y .(suc k) (k , refl) eq = *-cancelʳ-ℕ x y k eq
    
    -- Lemma: ⁺toℤ n .ℤ.pos ≡ ⁺toℕ n (definitional but let's make it explicit)
    ⁺toℤ-pos : ∀ (n : ℕ⁺) → ℤ.pos (⁺toℤ n) ≡ ⁺toℕ n
    ⁺toℤ-pos n = refl
    
    ⁺toℤ-neg : ∀ (n : ℕ⁺) → ℤ.neg (⁺toℤ n) ≡ zero
    ⁺toℤ-neg n = refl
    
    -- The pos component of (mkℤ a b) *ℤ (mkℤ p 0) = (a*p + b*0) = a*p
    *ℤ-pos-zero-neg : ∀ (a b p : ℕ) → ℤ.pos (mkℤ a b *ℤ mkℤ p zero) ≡ (a * p)
    *ℤ-pos-zero-neg a b p = trans (cong ((a * p) +_) (*-zeroʳ b)) (+-identityʳ (a * p))
    
    *ℤ-neg-zero-neg : ∀ (a b p : ℕ) → ℤ.neg (mkℤ a b *ℤ mkℤ p zero) ≡ (b * p)
    *ℤ-neg-zero-neg a b p = trans (cong (_+ (b * p)) (*-zeroʳ a)) refl
    
    -- Actually: ℤ.neg (mkℤ a b *ℤ mkℤ p 0) = (a * 0) + (b * p), and a*0 = 0
    -- But that's not definitionally 0, we need a proof
    
    -- Multiplicative cancellation for ⁺toℤ factors (always non-zero)
    -- If x * ⁺toℤ n ≃ℤ y * ⁺toℤ n, then x ≃ℤ y
    *ℤ-cancelʳ-⁺ : ∀ {x y : ℤ} (n : ℕ⁺) → (x *ℤ ⁺toℤ n) ≃ℤ (y *ℤ ⁺toℤ n) → x ≃ℤ y
    *ℤ-cancelʳ-⁺ {mkℤ a b} {mkℤ c d} n eq = 
      -- Direct pattern match on the structure
      -- eq : pos(x*⁺toℤ n) + neg(y*⁺toℤ n) ≡ pos(y*⁺toℤ n) + neg(x*⁺toℤ n)
      -- After expanding *ℤ and simplifying:
      -- (a * ⁺toℕ n + b * 0) + (c * 0 + d * ⁺toℕ n) ≡ (c * ⁺toℕ n + d * 0) + (a * 0 + b * ⁺toℕ n)
      let 
        m = ⁺toℕ n  -- abbreviate
        
        -- Simplify all the * 0 terms
        a0 : a * zero ≡ zero
        a0 = *-zeroʳ a
        b0 : b * zero ≡ zero  
        b0 = *-zeroʳ b
        c0 : c * zero ≡ zero
        c0 = *-zeroʳ c
        d0 : d * zero ≡ zero
        d0 = *-zeroʳ d
        
        -- eq has raw type:
        -- (a * m + b * 0) + (c * 0 + d * m) ≡ (c * m + d * 0) + (a * 0 + b * m)
        -- Simplify to: (a * m + 0) + (0 + d * m) ≡ (c * m + 0) + (0 + b * m)
        -- Then to: (a * m) + (d * m) ≡ (c * m) + (b * m)
        
        lhs-pos-simp : (a * m + b * zero) ≡ a * m
        lhs-pos-simp = trans (cong (a * m +_) b0) (+-identityʳ (a * m))
        
        lhs-neg-simp : (c * zero + d * m) ≡ d * m
        lhs-neg-simp = trans (cong (_+ d * m) c0) refl
        
        rhs-pos-simp : (c * m + d * zero) ≡ c * m
        rhs-pos-simp = trans (cong (c * m +_) d0) (+-identityʳ (c * m))
        
        rhs-neg-simp : (a * zero + b * m) ≡ b * m
        rhs-neg-simp = trans (cong (_+ b * m) a0) refl
        
        eq-simplified : (a * m + d * m) ≡ (c * m + b * m)
        eq-simplified = trans (cong₂ _+_ (sym lhs-pos-simp) (sym lhs-neg-simp))
                        (trans eq (cong₂ _+_ rhs-pos-simp rhs-neg-simp))
        
        -- Factor using distribʳ
        eq-factored : ((a + d) * m) ≡ ((c + b) * m)
        eq-factored = trans (*-distribʳ-+ a d m) 
                      (trans eq-simplified (sym (*-distribʳ-+ c b m)))
      in *-cancelʳ-suc (a + d) (c + b) m (⁺toℕ-is-suc n) eq-factored

-- ─────────────────────────────────────────────────────────────────────────────
-- § 3  +ℚ LAWS
-- ─────────────────────────────────────────────────────────────────────────────

-- Commutativity of +ℚ
+ℚ-comm : ∀ p q → (p +ℚ q) ≃ℚ (q +ℚ p)
+ℚ-comm (a / b) (c / d) = 
  -- LHS = ((a * d) + (c * b)) / (b * d)
  -- RHS = ((c * b) + (a * d)) / (d * b)
  -- Need: LHS-num * ⁺toℤ(d*b) ≃ℤ RHS-num * ⁺toℤ(b*d)
  -- 
  -- LHS-num ≃ℤ RHS-num by +ℤ-comm
  -- ⁺toℤ(d*b) ≃ℤ ⁺toℤ(b*d) by *⁺-comm
  let num-eq : ((a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)) ≃ℤ ((c *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ d))
      num-eq = +ℤ-comm (a *ℤ ⁺toℤ d) (c *ℤ ⁺toℤ b)
      den-eq : (d *⁺ b) ≡ (b *⁺ d)
      den-eq = *⁺-comm d b
      -- Now use *ℤ-cong with these equalities
  in *ℤ-cong {(a *ℤ ⁺toℤ d) +ℤ (c *ℤ ⁺toℤ b)} 
             {(c *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ d)}
             {⁺toℤ (d *⁺ b)}
             {⁺toℤ (b *⁺ d)}
             num-eq 
             (≡→≃ℤ (cong ⁺toℤ den-eq))

-- Left identity for +ℚ
+ℚ-identityˡ : ∀ q → (0ℚ +ℚ q) ≃ℚ q
+ℚ-identityˡ (a / b) = 
  -- 0ℚ +ℚ (a/b) = ((0 * b) + (a * 1)) / (1 * b) = (0 + a) / b = a / b
  -- Need: ((0ℤ *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ one⁺)) *ℤ ⁺toℤ b 
  --     ≃ℤ a *ℤ ⁺toℤ (one⁺ *⁺ b)
  -- 
  -- LHS: (0 + a*1) * b = a * b
  -- RHS: a * b
  let lhs-num : (0ℤ *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ one⁺) ≃ℤ a
      lhs-num = ≃ℤ-trans {(0ℤ *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ one⁺)} 
                         {0ℤ +ℤ (a *ℤ 1ℤ)} 
                         {a}
                (+ℤ-cong {0ℤ *ℤ ⁺toℤ b} {0ℤ} {a *ℤ ⁺toℤ one⁺} {a *ℤ 1ℤ} 
                         (*ℤ-zeroˡ (⁺toℤ b)) 
                         (≃ℤ-refl (a *ℤ 1ℤ)))  -- ⁺toℤ one⁺ = 1ℤ definitionally
                (≃ℤ-trans {0ℤ +ℤ (a *ℤ 1ℤ)} {a *ℤ 1ℤ} {a}
                          (+ℤ-identityˡ (a *ℤ 1ℤ))
                          (*ℤ-identityʳ a))
      rhs-den : ⁺toℤ (one⁺ *⁺ b) ≃ℤ ⁺toℤ b
      rhs-den = ≃ℤ-refl (⁺toℤ b)  -- one⁺ *⁺ b = b definitionally
  in *ℤ-cong {(0ℤ *ℤ ⁺toℤ b) +ℤ (a *ℤ ⁺toℤ one⁺)} {a} {⁺toℤ b} {⁺toℤ (one⁺ *⁺ b)}
             lhs-num 
             (≃ℤ-sym {⁺toℤ (one⁺ *⁺ b)} {⁺toℤ b} rhs-den)

-- Right identity follows from commutativity
+ℚ-identityʳ : ∀ q → (q +ℚ 0ℚ) ≃ℚ q
+ℚ-identityʳ q = ≃ℚ-trans {q +ℚ 0ℚ} {0ℚ +ℚ q} {q} (+ℚ-comm q 0ℚ) (+ℚ-identityˡ q)

-- Additive inverse
+ℚ-inverseʳ : ∀ q → (q +ℚ (-ℚ q)) ≃ℚ 0ℚ
+ℚ-inverseʳ (a / b) = 
  -- (a/b) + ((-a)/b) = (a*b + (-a)*b) / (b*b) ≃ 0/1
  -- Need: ((a*⁺toℤ b) + ((negℤ a)*⁺toℤ b)) * ⁺toℤ one⁺ ≃ℤ 0ℤ * ⁺toℤ(b*b)
  -- 
  -- Step 1: (a*⁺toℤ b) + ((negℤ a)*⁺toℤ b) = (a + negℤ a) * ⁺toℤ b  [by distribʳ sym]
  -- Step 2: (a + negℤ a) = 0ℤ  [by +ℤ-inverseʳ]
  -- Step 3: 0ℤ * ⁺toℤ b = 0ℤ  [by *ℤ-zeroˡ]
  -- Step 4: 0ℤ * 1ℤ = 0ℤ
  -- Step 5: 0ℤ * ⁺toℤ(b*b) = 0ℤ  [by *ℤ-zeroˡ]
  let 
      lhs-factored : ((a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)) ≃ℤ ((a +ℤ negℤ a) *ℤ ⁺toℤ b)
      lhs-factored = ≃ℤ-sym {(a +ℤ negℤ a) *ℤ ⁺toℤ b} {(a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)} 
                           (*ℤ-distribʳ-+ℤ a (negℤ a) (⁺toℤ b))
      sum-is-zero : (a +ℤ negℤ a) ≃ℤ 0ℤ
      sum-is-zero = +ℤ-inverseʳ a
      lhs-zero : ((a +ℤ negℤ a) *ℤ ⁺toℤ b) ≃ℤ (0ℤ *ℤ ⁺toℤ b)
      lhs-zero = *ℤ-cong {a +ℤ negℤ a} {0ℤ} {⁺toℤ b} {⁺toℤ b} sum-is-zero (≃ℤ-refl (⁺toℤ b))
      zero-mul : (0ℤ *ℤ ⁺toℤ b) ≃ℤ 0ℤ
      zero-mul = *ℤ-zeroˡ (⁺toℤ b)
      lhs-is-zero : ((a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)) ≃ℤ 0ℤ
      lhs-is-zero = ≃ℤ-trans {(a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)} {(a +ℤ negℤ a) *ℤ ⁺toℤ b} {0ℤ}
                            lhs-factored 
                            (≃ℤ-trans {(a +ℤ negℤ a) *ℤ ⁺toℤ b} {0ℤ *ℤ ⁺toℤ b} {0ℤ} lhs-zero zero-mul)
      lhs-times-one : (((a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)) *ℤ ⁺toℤ one⁺) ≃ℤ (0ℤ *ℤ ⁺toℤ one⁺)
      lhs-times-one = *ℤ-cong {(a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)} {0ℤ} {⁺toℤ one⁺} {⁺toℤ one⁺}
                             lhs-is-zero (≃ℤ-refl (⁺toℤ one⁺))
      zero-times-one : (0ℤ *ℤ ⁺toℤ one⁺) ≃ℤ 0ℤ
      zero-times-one = *ℤ-zeroˡ (⁺toℤ one⁺)
      rhs-zero : (0ℤ *ℤ ⁺toℤ (b *⁺ b)) ≃ℤ 0ℤ
      rhs-zero = *ℤ-zeroˡ (⁺toℤ (b *⁺ b))
  in ≃ℤ-trans {((a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)) *ℤ ⁺toℤ one⁺} {0ℤ} {0ℤ *ℤ ⁺toℤ (b *⁺ b)}
             (≃ℤ-trans {((a *ℤ ⁺toℤ b) +ℤ ((negℤ a) *ℤ ⁺toℤ b)) *ℤ ⁺toℤ one⁺} {0ℤ *ℤ ⁺toℤ one⁺} {0ℤ}
                       lhs-times-one zero-times-one)
             (≃ℤ-sym {0ℤ *ℤ ⁺toℤ (b *⁺ b)} {0ℤ} rhs-zero)

+ℚ-inverseˡ : ∀ q → ((-ℚ q) +ℚ q) ≃ℚ 0ℚ
+ℚ-inverseˡ q = ≃ℚ-trans {(-ℚ q) +ℚ q} {q +ℚ (-ℚ q)} {0ℚ} (+ℚ-comm (-ℚ q) q) (+ℚ-inverseʳ q)

-- Associativity (complex proof)
-- ((a/b) + (c/d)) + (e/f) = (a/b) + ((c/d) + (e/f))
-- 
-- LHS: (((a*d)+(c*b))/(b*d)) + (e/f) = (((a*d)+(c*b))*f + e*(b*d)) / ((b*d)*f)
-- RHS: (a/b) + (((c*f)+(e*d))/(d*f)) = (a*(d*f) + ((c*f)+(e*d))*b) / (b*(d*f))
--
-- Need to show the cross-multiplication equality.
-- Key insight: (b*d)*f = b*(d*f) by *⁺-assoc, so denominators match up to order.
-- For numerators, expand everything and use +ℤ-assoc, *ℤ-assoc, *ℤ-comm, distribˡ/ʳ

+ℚ-assoc : ∀ p q r → ((p +ℚ q) +ℚ r) ≃ℚ (p +ℚ (q +ℚ r))
+ℚ-assoc (a / b) (c / d) (e / f) = 
  -- The numerators after expansion are:
  -- LHS-num = ((a*d + c*b)*f + e*(b*d))
  -- RHS-num = (a*(d*f) + (c*f + e*d)*b)
  -- 
  -- Expanding:
  -- LHS = a*d*f + c*b*f + e*b*d
  -- RHS = a*d*f + c*f*b + e*d*b
  --
  -- These are equal by commutativity: c*b*f = c*f*b and e*b*d = e*d*b
  --
  -- For full formality, we'd need ~30 lines of ≃ℤ-trans chains.
  -- Leaving as hole for now due to complexity.
  {!!}

-- ─────────────────────────────────────────────────────────────────────────────
-- § 4  *ℚ LAWS
-- ─────────────────────────────────────────────────────────────────────────────

-- Commutativity of *ℚ
*ℚ-comm : ∀ p q → (p *ℚ q) ≃ℚ (q *ℚ p)
*ℚ-comm (a / b) (c / d) = 
  -- (a*c)/(b*d) ≃ (c*a)/(d*b)
  -- Need: (a*c) * ⁺toℤ(d*b) ≃ℤ (c*a) * ⁺toℤ(b*d)
  let num-eq : (a *ℤ c) ≃ℤ (c *ℤ a)
      num-eq = *ℤ-comm a c
      den-eq : (d *⁺ b) ≡ (b *⁺ d)
      den-eq = *⁺-comm d b
  in *ℤ-cong {a *ℤ c} {c *ℤ a} {⁺toℤ (d *⁺ b)} {⁺toℤ (b *⁺ d)}
             num-eq
             (≡→≃ℤ (cong ⁺toℤ den-eq))

-- Left identity for *ℚ
*ℚ-identityˡ : ∀ q → (1ℚ *ℚ q) ≃ℚ q
*ℚ-identityˡ (a / b) = 
  -- (1*a)/(1*b) ≃ a/b
  -- Need: (1ℤ *ℤ a) * ⁺toℤ b ≃ℤ a * ⁺toℤ(one⁺ *⁺ b)
  -- LHS: a * ⁺toℤ b (since 1*a = a)
  -- RHS: a * ⁺toℤ b (since one⁺ *⁺ b = b)
  *ℤ-cong {1ℤ *ℤ a} {a} {⁺toℤ b} {⁺toℤ (one⁺ *⁺ b)}
          (*ℤ-identityˡ a)
          (≃ℤ-refl (⁺toℤ b))  -- one⁺ *⁺ b = b definitionally

*ℚ-identityʳ : ∀ q → (q *ℚ 1ℚ) ≃ℚ q
*ℚ-identityʳ q = ≃ℚ-trans {q *ℚ 1ℚ} {1ℚ *ℚ q} {q} (*ℚ-comm q 1ℚ) (*ℚ-identityˡ q)

-- Associativity
*ℚ-assoc : ∀ p q r → ((p *ℚ q) *ℚ r) ≃ℚ (p *ℚ (q *ℚ r))
*ℚ-assoc (a / b) (c / d) (e / f) = 
  -- ((a*c)*e)/((b*d)*f) ≃ (a*(c*e))/(b*(d*f))
  -- Need: ((a*c)*e) * ⁺toℤ(b*(d*f)) ≃ℤ (a*(c*e)) * ⁺toℤ((b*d)*f)
  -- By *ℤ-assoc: (a*c)*e ≃ℤ a*(c*e) 
  -- By *⁺-assoc: (b*d)*f = b*(d*f)
  let num-assoc : ((a *ℤ c) *ℤ e) ≃ℤ (a *ℤ (c *ℤ e))
      num-assoc = *ℤ-assoc a c e
      den-assoc : ((b *⁺ d) *⁺ f) ≡ (b *⁺ (d *⁺ f))
      den-assoc = *⁺-assoc b d f
  in *ℤ-cong {(a *ℤ c) *ℤ e} {a *ℤ (c *ℤ e)} {⁺toℤ (b *⁺ (d *⁺ f))} {⁺toℤ ((b *⁺ d) *⁺ f)}
             num-assoc
             (≡→≃ℤ (cong ⁺toℤ (sym den-assoc)))

-- Distributivity (requires +ℚ-cong which needs ≃ℚ-trans)
*ℚ-distribˡ-+ℚ : ∀ p q r → (p *ℚ (q +ℚ r)) ≃ℚ ((p *ℚ q) +ℚ (p *ℚ r))
*ℚ-distribˡ-+ℚ (a / b) (c / d) (e / f) = 
  -- LHS: (a * ((c*f) + (e*d))) / (b * (d*f))
  -- RHS: ((a*c)*(b*f) + (a*e)*(b*d)) / ((b*d)*(b*f))
  -- This proof requires extensive algebraic manipulation
  {!!}

*ℚ-distribʳ-+ℚ : ∀ p q r → ((p +ℚ q) *ℚ r) ≃ℚ ((p *ℚ r) +ℚ (q *ℚ r))
*ℚ-distribʳ-+ℚ p q r = 
  -- Follows from *ℚ-distribˡ-+ℚ and *ℚ-comm
  -- But needs +ℚ-cong to permute the arguments
  ≃ℚ-trans {(p +ℚ q) *ℚ r} {r *ℚ (p +ℚ q)} {(p *ℚ r) +ℚ (q *ℚ r)}
    (*ℚ-comm (p +ℚ q) r)
    {!!}

-- ─────────────────────────────────────────────────────────────────────────────
-- § 5  SUMMARY
-- ─────────────────────────────────────────────────────────────────────────────
--
-- PROVEN (✓):
--   ⊥-elim, suc-inj, zero≢suc, ⁺toℕ-is-suc, ⁺toℕ-injective
--   +⁺-suc⁺, +⁺-comm
--   *⁺-comm, *⁺-assoc
--   *-cancelʳ-ℕ (ℕ multiplicative cancellation)
--   *ℤ-cancelʳ-⁺ (ℤ multiplicative cancellation by ⁺toℤ)
--   ≃ℚ-trans  ✓ (THE KEY BREAKTHROUGH!)
--   +ℚ-comm
--   +ℚ-identityˡ, +ℚ-identityʳ
--   +ℚ-inverseʳ, +ℚ-inverseˡ
--   *ℚ-comm
--   *ℚ-identityˡ, *ℚ-identityʳ
--   *ℚ-assoc
--
-- REMAINING HOLES (3):
--   +ℚ-assoc          (tedious but straightforward algebraic manipulation)
--   *ℚ-distribˡ-+ℚ    (requires extensive algebraic work)
--   *ℚ-distribʳ-+ℚ    (follows from distribˡ + commutativity manipulation)
--
-- FIELD AXIOM STATUS:
--   Equivalence (≃ℚ): refl ✓, sym ✓, trans ✓  (100% COMPLETE!)
--   0 ≠ 1                              TBD (easy with our definitions)
--   Additive group (ℚ, +, 0, -):
--     - comm ✓, identity ✓, inverse ✓
--     - assoc: HOLE (but straightforward)
--   Multiplicative monoid (ℚ, *, 1):
--     - comm ✓, identity ✓, assoc ✓  (100% COMPLETE!)
--   Distributivity:
--     - distribˡ: HOLE
--     - distribʳ: HOLE
--   Multiplicative inverse (q⁻¹ for q≠0): TBD
--
-- TOTAL: ~70% of field axioms proven


