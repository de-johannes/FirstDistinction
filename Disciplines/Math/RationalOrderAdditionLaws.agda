{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RationalOrderAdditionLaws where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.IntegerAbsLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerOrderPreorderLaws
open import Disciplines.Math.IntegerOrderAdditionLaws
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatPlusLaws
open import Disciplines.Math.Rationals
open import Disciplines.Math.RationalAdditionLaws
open import Disciplines.Math.RationalOrderLaws
open import Disciplines.Math.RationalOrderPreorderLaws

{-
CHAPTER 14V″: Forced Additive Order Laws For ≤ℚ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (ℚ, ≤ℚ), Chapter 14W (≤ℤ transport), Chapter 14Y′ (nonneg + monotonicity)
AGDA MODULES: Disciplines.Math.RationalOrderAdditionLaws
DEGREES OF FREEDOM ELIMINATED: inability to bound sums when combining Cauchy bounds
-}

0≤ℤ-fromℕℤ : (n : ℕ) → 0ℤ ≤ℤ fromℕℤ n
0≤ℤ-fromℕℤ zero = tt
0≤ℤ-fromℕℤ (suc n) = tt

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

-- Nonnegativity is closed under rational addition.

0≤ℚ-+ℚ : (p q : ℚ) → 0ℚ ≤ℚ p → 0ℚ ≤ℚ q → 0ℚ ≤ℚ (p +ℚ q)
0≤ℚ-+ℚ (a / b) (c / d) p≥0 q≥0 =
  let
    a≥0 : 0ℤ ≤ℤ a
    a≥0 = 0≤ℚ→0≤ℤnum (a / b) p≥0

    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) q≥0

    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (sym (*ℤ-zero-left (⁺toℤ s)))
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
  ≤ℤ-resp-≡ˡ lhs0 (≤ℤ-resp-≡ʳ (sym rhs1) sum≥0)

-- If 0≤x,y,z and x≤z and y≤z, then x+y ≤ z+z.

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

    -- m+n ≤ k+n
    step₁ : (m +ℕ n) ≤ (k +ℕ n)
    step₁ =
      subst (λ t → t ≤ (k +ℕ n))
        (sym (+ℕ-comm m n))
        (subst (λ t → (n +ℕ m) ≤ t)
          (+ℕ-comm n k)
          (≤-+ℕ-monoˡ x≤zNat n))

    -- k+n ≤ k+k
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

-- Core bound needed for ε-splitting combination: if p≤r and q≤r (with nonneg), then p+q ≤ r+r.

≤ℚ-sum≤double-nonneg : (p q r : ℚ) → 0ℚ ≤ℚ p → 0ℚ ≤ℚ q → 0ℚ ≤ℚ r → p ≤ℚ r → q ≤ℚ r → (p +ℚ q) ≤ℚ (r +ℚ r)
≤ℚ-sum≤double-nonneg (a / b) (c / d) (e / f) pnonneg qnonneg rnonneg p≤r q≤r =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    ff : ℕ⁺
    ff = f *⁺ f

    bdf : ℕ⁺
    bdf = bd *⁺ f

    -- Extract nonnegativity of the numerators.
    a≥0 : 0ℤ ≤ℤ a
    a≥0 = 0≤ℚ→0≤ℤnum (a / b) pnonneg

    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) qnonneg

    e≥0 : 0ℤ ≤ℤ e
    e≥0 = 0≤ℚ→0≤ℤnum (e / f) rnonneg

    -- Helpful: 0 ≤ z implies 0 ≤ z * den.
    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (sym (*ℤ-zero-left (⁺toℤ s)))
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

    -- Scale p≤r and q≤r so both compare to the same Z.
    pScaled₁ : ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ≤ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d)
    pScaled₁ = ≤ℤ-mul-pos-right (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) d p≤r

    pScaled₂ : (((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f) ≤ℤ (((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) *ℤ ⁺toℤ f)
    pScaled₂ = ≤ℤ-mul-pos-right ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ d) ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ d) f pScaled₁

    qScaled₁ : ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ≤ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b)
    qScaled₁ = ≤ℤ-mul-pos-right (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) b q≤r

    qScaled₂ : (((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f) ≤ℤ (((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) *ℤ ⁺toℤ f)
    qScaled₂ = ≤ℤ-mul-pos-right ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ b) ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ b) f qScaled₁

    -- Rewrite both sides into the X ≤ Z and Y ≤ Z shapes.
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

    -- For q: make the RHS use bd instead of swapping b and d.
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

    -- Re-express goal in terms of X,Y,Z.
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

-- Adding a nonnegative term preserves ≤ on the right.

neg≤normalize : (n m : ℕ) → (-suc m) ≤ℤ normalizeℤ n m
neg≤normalize zero zero = tt
neg≤normalize zero (suc m) = ≤-step (suc m)
neg≤normalize (suc n) zero = tt
neg≤normalize (suc n) (suc m) =
  ≤ℤ-trans negStep (neg≤normalize n m)
  where
    negStep : (-suc (suc m)) ≤ℤ (-suc m)
    negStep = s≤s (≤-step m)

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

≤ℤ-add-nonneg-right : (x y : ℤ) → 0ℤ ≤ℤ y → x ≤ℤ (x +ℤ y)
≤ℤ-add-nonneg-right x y y≥0 with 0≤ℤ→fromℕℤ y y≥0
... | (zero , y≡) =
  ≤ℤ-resp-≡ʳ (sym (cong (λ t → x +ℤ t) y≡)) (≤ℤ-resp-≡ʳ (sym (+ℤ-zero-right x)) (≤ℤ-refl x))
... | (suc n , y≡) =
  ≤ℤ-resp-≡ʳ (sym (cong (λ t → x +ℤ t) y≡)) (≤ℤ-add-pos-right x n)

≤ℚ-add-nonneg-right : (p q : ℚ) → 0ℚ ≤ℚ q → p ≤ℚ (p +ℚ q)
≤ℚ-add-nonneg-right (a / b) (c / d) qnonneg =
  let
    -- Extract nonnegativity of q's numerator.
    c≥0 : 0ℤ ≤ℤ c
    c≥0 = 0≤ℚ→0≤ℤnum (c / d) qnonneg

    nonnegScale : (z : ℤ) → (s : ℕ⁺) → 0ℤ ≤ℤ z → 0ℤ ≤ℤ (z *ℤ ⁺toℤ s)
    nonnegScale z s z≥0 =
      ≤ℤ-resp-≡ˡ (sym (*ℤ-zero-left (⁺toℤ s)))
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

-- Monotonicity: if p ≤ q then (p + r) ≤ (q + r).

≤ℚ-+ℚ-mono-right : (p q r : ℚ) → p ≤ℚ q → (p +ℚ r) ≤ℚ (q +ℚ r)
≤ℚ-+ℚ-mono-right (a / b) (c / d) (e / f) p≤q =
  let
    bd : ℕ⁺
    bd = b *⁺ d

    bf : ℕ⁺
    bf = b *⁺ f

    df : ℕ⁺
    df = d *⁺ f

    -- Scale p ≤ q by f and then by f again.
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

    -- Transform LHS sums.
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

    -- The 'r' term is the same on both sides: (e*b)*df = (e*d)*bf (both = e*b*d*f).
    rTerm : (e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df ≡ (e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf
    rTerm =
      trans
        (scaleSplit (e *ℤ ⁺toℤ b) d f)
        (trans
          (cong (λ t → t *ℤ ⁺toℤ f) (swapScale e b d))
          (sym (scaleSplit (e *ℤ ⁺toℤ d) b f)))

    -- LHS sum = (a*f + e*b) * df, RHS sum = (c*f + e*d) * bf.
    lhsSum : ℤ
    lhsSum = ((a *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ b)) *ℤ ⁺toℤ df

    rhsSum : ℤ
    rhsSum = ((c *ℤ ⁺toℤ f) +ℤ (e *ℤ ⁺toℤ d)) *ℤ ⁺toℤ bf

    lhsExpand : lhsSum ≡ ((a *ℤ ⁺toℤ f) *ℤ ⁺toℤ df) +ℤ ((e *ℤ ⁺toℤ b) *ℤ ⁺toℤ df)
    lhsExpand = *ℤ-distrib-left-+ℤ (a *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ b) (⁺toℤ df)

    rhsExpand : rhsSum ≡ ((c *ℤ ⁺toℤ f) *ℤ ⁺toℤ bf) +ℤ ((e *ℤ ⁺toℤ d) *ℤ ⁺toℤ bf)
    rhsExpand = *ℤ-distrib-left-+ℤ (c *ℤ ⁺toℤ f) (e *ℤ ⁺toℤ d) (⁺toℤ bf)

    -- Use monotonicity of ℤ addition.
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

-- Monotonicity on the left: if q ≤ r then (p + q) ≤ (p + r).

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
