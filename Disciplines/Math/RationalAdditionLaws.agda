{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalAdditionLaws where

open import FirstDistinction
open import Disciplines.Math.Rationals
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerAbs
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws

cong₂ : {A B C : Set} → (f : A → B → C) → {x x' : A} → {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

-- Commutativity of rational addition holds in the forced setoid sense.

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

-- +ℚ respects the forced setoid equality ≃ℚ.

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

    -- Align the 'a' summands using eqp scaled by d·d'.
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

    -- Align the 'c' summands using eqq scaled by b·b'.
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

-- Associativity of rational addition holds in the forced setoid sense.

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

    -- Expand rhsNum to match lhsNum.
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


-- Zero is a neutral element for +ℚ.

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

-- Additive inverse cancels.

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
