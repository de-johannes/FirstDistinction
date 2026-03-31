{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalMultiplicationLaws where

open import FirstDistinction
open import Disciplines.Math.Rationals
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.RationalAdditionLaws
open import Disciplines.Math.RationalSetoidLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws

{-
CHAPTER 14S′: Forced Laws Of Rational Multiplication

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (*ℚ), Chapter 14M (*ℤ laws), Chapter 14X (⁺toℤ-*⁺)
AGDA MODULES: Disciplines.Math.RationalMultiplicationLaws
DEGREES OF FREEDOM ELIMINATED: missing algebraic coherence of *ℚ
-}

-- Helper: expand ⁺toℤ of a triple ℕ⁺ product into a right-associated ℤ product.

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

-- Commutativity of *ℚ in the forced setoid sense.

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

-- Associativity of *ℚ in the forced setoid sense.

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

-- One is a two-sided identity for *ℚ.

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

    -- (a*1)/ (b*1) ≃ a/b
    cross : ((a *ℤ oneℤ) *ℤ ⁺toℤ b) ≡ (a *ℤ ⁺toℤ (b *⁺ one⁺))
    cross =
      trans
        (cong (λ t → t *ℤ ⁺toℤ b) numEq)
        (cong (λ t → a *ℤ t) denOne)
  in
  cross

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

-- Zero annihilates multiplication.

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
          (*ℤ-zero-left (⁺toℤ (one⁺ *⁺ b)))
          (sym (*ℤ-zero-left (⁺toℤ one⁺))))
  in
  cross

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

-- Distributivity of *ℚ over +ℚ is forced by *ℤ distributivity.

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

    -- Term 1 alignment: (a*(c*F))*denR = ((a*c)*⁺toℤ(b*f))*denL
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

    -- Term 2 alignment: (a*(e*D))*denR = ((a*e)*(B*D))*denL
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
