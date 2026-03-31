{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalDistanceLaws where

open import FirstDistinction
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws
open import Disciplines.Math.IntegerAbs
open import Disciplines.Math.IntegerAbsLaws
open import Disciplines.Math.IntegerOrderAdditionLaws
open import Disciplines.Math.Rationals
open import Disciplines.Math.RationalOrderLaws
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.RationalOrderPreorderLaws
open import Disciplines.Math.RationalTriangleWork

{-
CHAPTER 14U: Forced Laws Of Rational Distance

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (ℚ, distℚ), Chapter 14F (+ℤ laws), Chapter 14M (*ℤ)
AGDA MODULES: Disciplines.Math.RationalDistanceLaws
DEGREES OF FREEDOM ELIMINATED: non-canonical distance behaviour on ℚ

-}

{-
### Law 14U.0: Rational Distance Is Reflexive Up To ≃ℚ

**Necessity Proof:** For any fixed `q`, the cleared numerator of `distℚ q q` collapses to
`x +ℤ negℤ x`, which is forced to be `0ℤ` by `+ℤ-inv-right`. Therefore the distance is
≃ℚ-equal to `0ℚ`.

**Formal Reference:** RationalDistanceLaws.agda.distℚ-refl (lines 57-85)

**Consequence:** Eliminates freedom to assign nonzero self-distance.

-}

absℤ-cong : {x y : ℤ} → x ≡ y → absℤ x ≡ absℤ y
absℤ-cong = cong absℤ


negℤ-neg : (z : ℤ) → negℤ (negℤ z) ≡ z
negℤ-neg 0ℤ = refl
negℤ-neg (+suc n) = refl
negℤ-neg (-suc n) = refl

-- distℚ q q is forced to be 0ℚ in the setoid sense.

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

-- If ε is strictly positive, then the distance between equal rationals is strictly below ε.
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

-- If p ≃ℚ q then their cleared difference is 0, so distℚ p q is 0.

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

-- Nonnegativity: distances are forced to lie above 0.

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

-- Symmetry of distance holds in the forced setoid sense.

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
            (cong (λ t → negℤ (a *ℤ ⁺toℤ d) +ℤ t) (negℤ-neg (c *ℤ ⁺toℤ b)))
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

-- Negation invariance: flipping both endpoints cannot change distance.

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

-- Triangle inequality for rational distance.

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

    -- Base scaled numerator inequality.
    ineq0 : (nd-pr *ℤ ⁺toℤ d) ≤ℤ ((nd-pq *ℤ ⁺toℤ f) +ℤ (nd-qr *ℤ ⁺toℤ b))
    ineq0 = numDistℚ-triangle-scaled p q rQ

    -- Multiply by the common positive scale s = (b·d)·f.
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

    -- Swap two positive scaling factors.
    swapScale : (x : ℤ) → (u v : ℕ⁺) → (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v ≡ (x *ℤ ⁺toℤ v) *ℤ ⁺toℤ u
    swapScale x u v =
      trans
        (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v))
        (trans
          (cong (λ t → x *ℤ t) (*ℤ-comm (⁺toℤ u) (⁺toℤ v)))
          (sym (*ℤ-assoc x (⁺toℤ v) (⁺toℤ u))))

    -- Split scaling by a product u*⁺v into sequential scaling.
    scaleSplit : (x : ℤ) → (u v : ℕ⁺) → x *ℤ ⁺toℤ (u *⁺ v) ≡ (x *ℤ ⁺toℤ u) *ℤ ⁺toℤ v
    scaleSplit x u v =
      trans
        (cong (λ t → x *ℤ t) (⁺toℤ-*⁺ u v))
        (sym (*ℤ-assoc x (⁺toℤ u) (⁺toℤ v)))

    -- LHS rewrite: ((nd-pr·d)·s) = nd-pr · rhsDen
    lhsEq : ((nd-pr *ℤ ⁺toℤ d) *ℤ ⁺toℤ s) ≡ (nd-pr *ℤ ⁺toℤ rhsDen)
    lhsEq =
      trans
        (scaleSplit (nd-pr *ℤ ⁺toℤ d) bd f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale nd-pr d bd))
          (trans
            (sym (scaleSplit (nd-pr *ℤ ⁺toℤ bd) d f))
            (sym (scaleSplit nd-pr bd df))))

    -- Term rewrite: (nd-pq·f)·s = (nd-pq·df)·bf
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

    -- Term rewrite: (nd-qr·b)·s = (nd-qr·bd)·bf
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

-- Translation invariance of distance under rational addition.

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

    -- Denominator embedding factorization:
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

    -- Numerator cancellation and factoring:
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

        -- First cancel the r-contributed terms.
        Z₂ : Z ≡ afdf +ℤ negℤ cfbf
        Z₂ =
          let
            -- Rewrite Z into four explicit terms.
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

        -- Then factor out the common scale s = f·f.
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

-- Multiplicative scaling: multiplying both endpoints by the same rational scales distance by distℚ p 0ℚ.

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

    -- Names for the key cleared numerators.
    cf : ℤ
    cf = c *ℤ ⁺toℤ f

    ed : ℤ
    ed = e *ℤ ⁺toℤ d

    baseQR : ℤ
    baseQR = cf +ℤ negℤ ed

    ab : ℤ
    ab = a *ℤ ⁺toℤ b

    -- distℚ p 0ℚ has numerator absℤ a (forced by cancellation).
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

    -- LHS cleared numerator for distℚ (p*q) (p*r).
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

    -- Denominator embedding relation: (rhsDen · b) equals lhsDen (after embedding to ℤ).
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

    -- LHS cleared numerator for distℚ (q*p) (r*p).
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

-- KEY LEMMA: If x ≤ y+ε and y ≤ x+ε, then distℚ x y ≤ ε.
-- This is forced by the correspondence between order and distance.

distℚ-bounded-by-ε : (x y ε : ℚ) → x ≤ℚ (y +ℚ ε) → y ≤ℚ (x +ℚ ε) → distℚ x y ≤ℚ ε
distℚ-bounded-by-ε (a / b) (c / d) (e / f) x≤y+ε y≤x+ε =
  let
    -- Common denominator computations
    bd : ℕ⁺
    bd = b *⁺ d

    df : ℕ⁺
    df = d *⁺ f

    bf : ℕ⁺
    bf = b *⁺ f

    bdf : ℕ⁺
    bdf = bd *⁺ f

    -- The numerator of distℚ x y
    diff : ℤ
    diff = (a *ℤ ⁺toℤ d) +ℤ negℤ (c *ℤ ⁺toℤ b)

    -- Goal: absℤ diff * f ≤ e * (b*d)
    -- From x ≤ y + ε, we get: a*d*f ≤ (c*f + e*d)*b = c*f*b + e*d*b
    -- So: a*d*f - c*b*f ≤ e*d*b, i.e., diff * f ≤ e * (d*b)

    -- From y ≤ x + ε, we get: c*b*f ≤ (a*f + e*b)*d = a*f*d + e*b*d
    -- So: c*b*f - a*d*f ≤ e*b*d, i.e., -diff * f ≤ e * (d*b)

    -- Combined: |diff| * f ≤ e * (d*b)

    -- Expansion of y + ε denominator and numerator
    y+ε-num : ℤ
    y+ε-num = (c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)

    x+ε-num : ℤ
    x+ε-num = (a *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ b)

    -- x ≤ y + ε means: a * (d*f) ≤ y+ε-num * b
    hyp1 : (a *ℤ ⁺toℤ df) ≤ℤ (y+ε-num *ℤ ⁺toℤ b)
    hyp1 = x≤y+ε

    -- y ≤ x + ε means: c * (b*f) ≤ x+ε-num * d  
    hyp2 : (c *ℤ ⁺toℤ bf) ≤ℤ (x+ε-num *ℤ ⁺toℤ d)
    hyp2 = y≤x+ε

    -- Expand hyp1: a*(d*f) ≤ (c*f + e*d)*b = c*f*b + e*d*b
    adf≤cfb+edb : (a *ℤ ⁺toℤ df) ≤ℤ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b +ℤ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    adf≤cfb+edb = ≤ℤ-resp-≡ʳ (*ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ b)) hyp1

    -- Expand hyp2: c*(b*f) ≤ (a*f + e*b)*d = a*f*d + e*b*d
    cbf≤afd+ebd : (c *ℤ ⁺toℤ bf) ≤ℤ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d +ℤ (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    cbf≤afd+ebd = ≤ℤ-resp-≡ʳ (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) (⁺toℤ d)) hyp2

    -- Associativity lemmas
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

    -- Renamed for clarity
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

    -- Hyp1 gives: (a*d)*f ≤ (c*b)*f + ebd
    hyp1' : adf' ≤ℤ (cbf' +ℤ ebd)
    hyp1' = ≤ℤ-resp-≡ˡ assoc-adf (≤ℤ-resp-≡ʳ rhsEq adf≤cfb+edb)

    -- Hyp2 gives: (c*b)*f ≤ (a*d)*f + ebd
    hyp2' : cbf' ≤ℤ (adf' +ℤ ebd)
    hyp2' = ≤ℤ-resp-≡ˡ assoc-cbf (≤ℤ-resp-≡ʳ (cong (λ t → t +ℤ ebd) assoc-afd) cbf≤afd+ebd)

    -- diff * f = adf' - cbf'
    diff-f : ℤ
    diff-f = adf' +ℤ negℤ cbf'

    diff-f-eq : diff *ℤ ⁺toℤ f ≡ diff-f
    diff-f-eq = 
      trans
        (*ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ d) (negℤ (c *ℤ ⁺toℤ b)) (⁺toℤ f))
        (cong (λ t → ((a *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) +ℤ t) (*ℤ-neg-left (c *ℤ ⁺toℤ b) (⁺toℤ f)))

    -- From hyp1': adf' ≤ cbf' + ebd, i.e., adf' - cbf' ≤ ebd, i.e., diff-f ≤ ebd
    diff-f≤ebd : diff-f ≤ℤ ebd
    diff-f≤ebd = ≤ℤ-+ℤ-cancelʳ adf' cbf' ebd (≤ℤ-resp-≡ʳ (sym (+ℤ-comm ebd cbf')) hyp1')

    -- From hyp2': cbf' ≤ adf' + ebd, i.e., cbf' - adf' ≤ ebd, i.e., negℤ diff-f ≤ ebd
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

    -- Now use absℤ-within-bound: since -ebd ≤ diff-f ≤ ebd, we get |diff-f| ≤ ebd
    neg-ebd≤diff-f : (negℤ ebd) ≤ℤ diff-f
    neg-ebd≤diff-f = ≤ℤ-resp-≡ʳ (negℤ-involutive diff-f) (negℤ-antitone-≤ℤ neg-diff-f≤ebd)

    abs-diff-f≤ebd : absℤ diff-f ≤ℤ ebd
    abs-diff-f≤ebd = absℤ-within-bound diff-f ebd neg-ebd≤diff-f diff-f≤ebd

    -- Now transport to distℚ x y ≤ℚ ε
    -- distℚ x y = absℤ diff / bd
    -- ε = e / f
    -- Goal: (absℤ diff) * f ≤ e * (b*d)
    -- We have: absℤ (diff * f) ≤ (e*b)*d

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

-- Distance bounds force one-sided order bounds.

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

    -- Add cbf' to both sides and simplify the left-hand side.
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
