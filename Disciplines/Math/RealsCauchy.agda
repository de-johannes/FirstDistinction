{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.RealsCauchy where

open import FirstDistinction
open import Disciplines.Logic.Truth
open import Disciplines.Math.Rationals
open import Disciplines.Math.Integers
open import Disciplines.Math.IntegersLaws
open import Disciplines.Math.NatPlus
open import Disciplines.Math.NatMultiplicationLaws
open import Disciplines.Math.RationalDistanceLaws
open import Disciplines.Math.RationalOrderLaws
open import Disciplines.Math.RationalOrderPreorderLaws
open import Disciplines.Math.RationalOrderAdditionLaws
open import Disciplines.Math.RationalOrderMultiplicationLaws hiding (≃ℚ→≤ℚˡ ; *ℚ-comm)
open import Disciplines.Math.RationalArchimedeanLaws
open import Disciplines.Math.RationalEpsilonSplitLaws
open import Disciplines.Math.RationalAdditionLaws
open import Disciplines.Math.RationalSetoidLaws
open import Disciplines.Math.RationalMultiplicationLaws
open import Disciplines.Math.IntegerOrder
open import Disciplines.Math.IntegerOrderLaws
open import Disciplines.Math.IntegerMultiplication
open import Disciplines.Math.IntegerMultiplicationLaws
open import Disciplines.Math.IntegerAbsLaws using (fromℕℤ)

{-
CHAPTER 14T: Reals As Forced Cauchy Closure Over ℚ

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14S (ℚ + distℚ), Chapter 8 (≤ on ℕ)
AGDA MODULES: Disciplines.Math.RealsCauchy
DEGREES OF FREEDOM ELIMINATED: completion-as-postulate; real numbers are forced to be Cauchy data
-}

{-
### Law 14T.0: Cauchy Condition Is Forced As “Eventual ε-Clustering”
**Necessity Proof:** Without the ε/∀m,n≥N constraint, the limit notion admits arbitrary nonconvergent sequences.
**Formal Reference:** RealsCauchy.agda.IsCauchyP (lines 48-49)
**Consequence:** Eliminates the freedom to treat arbitrary sequences as reals.
-}

record IsCauchy (seq : ℕ → ℚ) : Set where
  field
    cauchy : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq m) (seq n) <ℚ ε)

IsCauchyP : (ℕ → ℚ) → Set
IsCauchyP = IsCauchy

record ℝ : Set where
  constructor mkℝ
  field
    seq : ℕ → ℚ
    isCauchy : IsCauchy seq

open ℝ public

ℚtoℝ : ℚ → ℝ
ℚtoℝ q = mkℝ (λ _ → q) record
  { cauchy = λ ε εpos →
      zero , (λ m n _ _ → distℚ-const<ε q ε εpos)
  }

-- Real equivalence is forced as “difference converges to 0”.

infix 4 _≃ℝ_

record _≃ℝ_ (x y : ℝ) : Set where
  field
    conv0 : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (n : ℕ) → N ≤ n → distℚ (seq x n) (seq y n) <ℚ ε)

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
          dxy<ε : distℚ (seq x n) (seq y n) <ℚ ε
          dxy<ε = conv n N≤n

          dyx≤dxy : distℚ (seq y n) (seq x n) ≤ℚ distℚ (seq x n) (seq y n)
          dyx≤dxy = ≃ℚ→≤ℚʳ (distℚ-sym (seq x n) (seq y n))
        in
        ≤<ℚ→<ℚ dyx≤dxy dxy<ε)
  }

-- Operations are introduced only after the dist-lemma package forces Cauchy closure.

infixl 6 _+ℝ_

_+ℝ_ : ℝ → ℝ → ℝ
x +ℝ y =
  mkℝ
    (λ n → (seq x n) +ℚ (seq y n))
    record
      { cauchy = λ ε εpos →
          let
            δ : ℚ
            δ = εQuarter ε

            δpos : 0ℚ <ℚ δ
            δpos = εQuarter-pos ε

            NxPack : Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq x m) (seq x n) <ℚ δ)
            NxPack = IsCauchy.cauchy (isCauchy x) δ δpos

            NyPack : Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq y m) (seq y n) <ℚ δ)
            NyPack = IsCauchy.cauchy (isCauchy y) δ δpos

            Nx : ℕ
            Nx = fst NxPack

            Ny : ℕ
            Ny = fst NyPack

            NxC : (m n : ℕ) → Nx ≤ m → Nx ≤ n → distℚ (seq x m) (seq x n) <ℚ δ
            NxC = snd NxPack

            NyC : (m n : ℕ) → Ny ≤ m → Ny ≤ n → distℚ (seq y m) (seq y n) <ℚ δ
            NyC = snd NyPack

            N : ℕ
            N = Nx +ℕ Ny

            Nx≤N : Nx ≤ N
            Nx≤N =
              let
                step : (Nx +ℕ zero) ≤ (Nx +ℕ Ny)
                step = ≤-+ℕ-monoˡ {a = zero} {b = Ny} z≤n Nx
              in
              subst (λ t → t ≤ (Nx +ℕ Ny)) (+ℕ-zero-right Nx) step

            Ny≤N : Ny ≤ N
            Ny≤N =
              let
                step : (Ny +ℕ zero) ≤ (Ny +ℕ Nx)
                step = ≤-+ℕ-monoˡ {a = zero} {b = Nx} z≤n Ny

                base : Ny ≤ (Ny +ℕ Nx)
                base = subst (λ t → t ≤ (Ny +ℕ Nx)) (+ℕ-zero-right Ny) step
              in
              subst (λ t → Ny ≤ t) (+ℕ-comm Ny Nx) base

            δnonneg : 0ℚ ≤ℚ δ
            δnonneg = <ℚ→≤ℚ δpos

            δ+δ<ε : (δ +ℚ δ) <ℚ ε
            δ+δ<ε = εQuarter-double<ε ε εpos
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

              dx<δ : distℚ (seq x m) (seq x n) <ℚ δ
              dx<δ = NxC m n Nx≤m Nx≤n

              dy<δ : distℚ (seq y m) (seq y n) <ℚ δ
              dy<δ = NyC m n Ny≤m Ny≤n

              p : ℚ
              p = seq x m

              q : ℚ
              q = seq y m

              r : ℚ
              r = seq x n

              s : ℚ
              s = seq y n

              d1 : ℚ
              d1 = distℚ (p +ℚ q) (r +ℚ q)

              d2 : ℚ
              d2 = distℚ (r +ℚ q) (r +ℚ s)

              d1≤dx : d1 ≤ℚ distℚ p r
              d1≤dx = ≃ℚ→≤ℚˡ (distℚ-+ℚ-right p r q)

              d2≤dy : d2 ≤ℚ distℚ q s
              d2≤dy = ≃ℚ→≤ℚˡ (distℚ-+ℚ-left r q s)

              d1<δ : d1 <ℚ δ
              d1<δ = ≤<ℚ→<ℚ d1≤dx dx<δ

              d2<δ : d2 <ℚ δ
              d2<δ = ≤<ℚ→<ℚ d2≤dy dy<δ

              d1nonneg : 0ℚ ≤ℚ d1
              d1nonneg = distℚ-nonneg (p +ℚ q) (r +ℚ q)

              d2nonneg : 0ℚ ≤ℚ d2
              d2nonneg = distℚ-nonneg (r +ℚ q) (r +ℚ s)

              d1≤δ : d1 ≤ℚ δ
              d1≤δ = <ℚ→≤ℚ d1<δ

              d2≤δ : d2 ≤ℚ δ
              d2≤δ = <ℚ→≤ℚ d2<δ

              d1+d2≤δ+δ : (d1 +ℚ d2) ≤ℚ (δ +ℚ δ)
              d1+d2≤δ+δ = ≤ℚ-sum≤double-nonneg d1 d2 δ d1nonneg d2nonneg δnonneg d1≤δ d2≤δ

              d1+d2<ε : (d1 +ℚ d2) <ℚ ε
              d1+d2<ε = ≤<ℚ→<ℚ d1+d2≤δ+δ δ+δ<ε

              dsum≤ : distℚ (p +ℚ q) (r +ℚ s) ≤ℚ (d1 +ℚ d2)
              dsum≤ = distℚ-triangle (p +ℚ q) (r +ℚ q) (r +ℚ s)

              dsum<ε : distℚ (p +ℚ q) (r +ℚ s) <ℚ ε
              dsum<ε = ≤<ℚ→<ℚ dsum≤ d1+d2<ε
            in
            dsum<ε)
      }

infixl 7 -ℝ_

-ℝ_ : ℝ → ℝ
-ℝ_ x =
  mkℝ
    (λ n → -ℚ (seq x n))
    record
      { cauchy = λ ε εpos →
          let
            pack : Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq x m) (seq x n) <ℚ ε)
            pack = IsCauchy.cauchy (isCauchy x) ε εpos

            N : ℕ
            N = fst pack

            base : (m n : ℕ) → N ≤ m → N ≤ n → distℚ (seq x m) (seq x n) <ℚ ε
            base = snd pack
          in
          N , (λ m n N≤m N≤n →
            let
              dx<ε : distℚ (seq x m) (seq x n) <ℚ ε
              dx<ε = base m n N≤m N≤n

              dneg≤ : distℚ (-ℚ (seq x m)) (-ℚ (seq x n)) ≤ℚ distℚ (seq x m) (seq x n)
              dneg≤ = ≃ℚ→≤ℚˡ (distℚ-neg (seq x m) (seq x n))
            in
            ≤<ℚ→<ℚ dneg≤ dx<ε)
      }

infixl 6 _-ℝ_

_-ℝ_ : ℝ → ℝ → ℝ
x -ℝ y = x +ℝ (-ℝ y)

0ℝ 1ℝ : ℝ
0ℝ = ℚtoℝ 0ℚ
1ℝ = ℚtoℝ 1ℚ

-- Basic algebra laws for +ℝ are forced pointwise from +ℚ laws.

+ℝ-comm : (x y : ℝ) → (x +ℝ y) ≃ℝ (y +ℝ x)
+ℝ-comm x y = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) +ℚ (seq y n)

          q : ℚ
          q = (seq y n) +ℚ (seq x n)

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-comm (seq x n) (seq y n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

+ℝ-assoc : (x y z : ℝ) → ((x +ℝ y) +ℝ z) ≃ℝ (x +ℝ (y +ℝ z))
+ℝ-assoc x y z = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = ((seq x n) +ℚ (seq y n)) +ℚ (seq z n)

          q : ℚ
          q = (seq x n) +ℚ ((seq y n) +ℚ (seq z n))

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-assoc (seq x n) (seq y n) (seq z n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

+ℝ-zero-right : (x : ℝ) → (x +ℝ 0ℝ) ≃ℝ x
+ℝ-zero-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) +ℚ 0ℚ

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-zero-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

+ℝ-zero-left : (x : ℝ) → (0ℝ +ℝ x) ≃ℝ x
+ℝ-zero-left x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = 0ℚ +ℚ (seq x n)

          q : ℚ
          q = seq x n

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-zero-left (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

+ℝ-inv-right : (x : ℝ) → (x +ℝ (-ℝ x)) ≃ℝ 0ℝ
+ℝ-inv-right x = record
  { conv0 = λ ε εpos →
      zero , (λ n _ →
        let
          p : ℚ
          p = (seq x n) +ℚ (-ℚ (seq x n))

          q : ℚ
          q = 0ℚ

          pq≃ : p ≃ℚ q
          pq≃ = +ℚ-inv-right (seq x n)

          d≃0 : distℚ p q ≃ℚ 0ℚ
          d≃0 = distℚ-≃0 pq≃

          d≤0 : distℚ p q ≤ℚ 0ℚ
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

-- Cauchy sequences are forced to be eventually bounded (in dist from 0).

IsCauchy-eventually-bounded : (s : ℕ → ℚ) → IsCauchy s → Σ ℕ (λ N → Σ ℚ (λ B → (n : ℕ) → N ≤ n → distℚ (s n) 0ℚ ≤ℚ B))
IsCauchy-eventually-bounded s cs =
  let
    onePos : 0ℚ <ℚ 1ℚ
    onePos = 0ℚ<1ℚ

    pack : Σ ℕ (λ N → (m n : ℕ) → N ≤ m → N ≤ n → distℚ (s m) (s n) <ℚ 1ℚ)
    pack = IsCauchy.cauchy cs 1ℚ onePos

    N : ℕ
    N = fst pack

    cN : (m n : ℕ) → N ≤ m → N ≤ n → distℚ (s m) (s n) <ℚ 1ℚ
    cN = snd pack

    B0 : ℚ
    B0 = distℚ (s N) 0ℚ

    r : ℚ
    r = 1ℚ +ℚ B0

    B : ℚ
    B = r +ℚ r

    oneNonneg : 0ℚ ≤ℚ 1ℚ
    oneNonneg = <ℚ→≤ℚ onePos

    B0Nonneg : 0ℚ ≤ℚ B0
    B0Nonneg = distℚ-nonneg (s N) 0ℚ

    rNonneg : 0ℚ ≤ℚ r
    rNonneg = 0≤ℚ-+ℚ 1ℚ B0 oneNonneg B0Nonneg

    one≤r : 1ℚ ≤ℚ r
    one≤r = ≤ℚ-add-nonneg-right 1ℚ B0 B0Nonneg

    B0≤r : B0 ≤ℚ r
    B0≤r =
      let
        B0≤B0+1 : B0 ≤ℚ (B0 +ℚ 1ℚ)
        B0≤B0+1 = ≤ℚ-add-nonneg-right B0 1ℚ oneNonneg

        comm : (B0 +ℚ 1ℚ) ≃ℚ (1ℚ +ℚ B0)
        comm = +ℚ-comm B0 1ℚ

        step : (B0 +ℚ 1ℚ) ≤ℚ r
        step = ≃ℚ→≤ℚˡ comm
      in
      ≤ℚ-trans B0≤B0+1 step
  in
  N , (B , (λ n N≤n →
    let
      d1 : ℚ
      d1 = distℚ (s n) (s N)

      d2 : ℚ
      d2 = distℚ (s N) 0ℚ

      d1<1 : d1 <ℚ 1ℚ
      d1<1 = cN n N N≤n (≤-refl N)

      d1≤1 : d1 ≤ℚ 1ℚ
      d1≤1 = <ℚ→≤ℚ d1<1

      d1Nonneg : 0ℚ ≤ℚ d1
      d1Nonneg = distℚ-nonneg (s n) (s N)

      d2Nonneg : 0ℚ ≤ℚ d2
      d2Nonneg = distℚ-nonneg (s N) 0ℚ

      d1≤r : d1 ≤ℚ r
      d1≤r = ≤ℚ-trans d1≤1 one≤r

      d2≤r : d2 ≤ℚ r
      d2≤r = B0≤r

      sum≤ : (d1 +ℚ d2) ≤ℚ (r +ℚ r)
      sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 r d1Nonneg d2Nonneg rNonneg d1≤r d2≤r

      tri : distℚ (s n) 0ℚ ≤ℚ (d1 +ℚ d2)
      tri = distℚ-triangle (s n) (s N) 0ℚ
    in
    ≤ℚ-trans tri sum≤))

-- Multiplication on ℝ is forced pointwise, but its Cauchy proof requires Archimedean scaling.

infixl 7 _⋅ℝ_

_⋅ℝ_ : ℝ → ℝ → ℝ
x ⋅ℝ y =
  mkℝ
    (λ n → (seq x n) *ℚ (seq y n))
    record
      { cauchy = λ ε εpos →
          let
            εq : ℚ
            εq = εQuarter ε

            εqPos : 0ℚ <ℚ εq
            εqPos = εQuarter-pos ε

            -- Eventual bounds for both factors.
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

            -- Derive nonnegativity for the bounds from dist≥0.
            BxNonneg : 0ℚ ≤ℚ Bx
            BxNonneg =
              let
                d0 : 0ℚ ≤ℚ distℚ (seq x Nx) 0ℚ
                d0 = distℚ-nonneg (seq x Nx) 0ℚ

                d0≤Bx : distℚ (seq x Nx) 0ℚ ≤ℚ Bx
                d0≤Bx = bxBound Nx (≤-refl Nx)
              in
              ≤ℚ-trans d0 d0≤Bx

            ByNonneg : 0ℚ ≤ℚ By
            ByNonneg =
              let
                d0 : 0ℚ ≤ℚ distℚ (seq y Ny) 0ℚ
                d0 = distℚ-nonneg (seq y Ny) 0ℚ

                d0≤By : distℚ (seq y Ny) 0ℚ ≤ℚ By
                d0≤By = byBound Ny (≤-refl Ny)
              in
              ≤ℚ-trans d0 d0≤By

            -- Bound Bx, By by successor-integers.
            bxIntPack = nonneg-bound-sucInt Bx BxNonneg
            byIntPack = nonneg-bound-sucInt By ByNonneg

            mx : ℕ
            mx = fst bxIntPack

            my : ℕ
            my = fst byIntPack

            Ix : ℚ
            Ix = fromℕℤ (suc mx) / one⁺

            Iy : ℚ
            Iy = fromℕℤ (suc my) / one⁺

            Bx≤Ix : Bx ≤ℚ Ix
            Bx≤Ix = snd bxIntPack

            By≤Iy : By ≤ℚ Iy
            By≤Iy = snd byIntPack

            IxNonneg : 0ℚ ≤ℚ Ix
            IxNonneg =
              let
                fromℕ/one-nonneg : (n : ℕ) → 0ℚ ≤ℚ (fromℕℤ n / one⁺)
                fromℕ/one-nonneg n =
                  let
                    a : ℤ
                    a = fromℕℤ n

                    lhs0 : (0ℤ *ℤ ⁺toℤ one⁺) ≡ 0ℤ
                    lhs0 = *ℤ-zero-left (⁺toℤ one⁺)

                    one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
                    one⁺ℤ≡oneℤ = refl

                    rhs1 : (a *ℤ ⁺toℤ one⁺) ≡ a
                    rhs1 = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)
                  in
                  ≤ℤ-resp-≡ʳ (sym rhs1) (≤ℤ-resp-≡ˡ (sym lhs0) (0≤ℤ-fromℕℤ n))
              in
              fromℕ/one-nonneg (suc mx)

            IyNonneg : 0ℚ ≤ℚ Iy
            IyNonneg =
              let
                fromℕ/one-nonneg : (n : ℕ) → 0ℚ ≤ℚ (fromℕℤ n / one⁺)
                fromℕ/one-nonneg n =
                  let
                    a : ℤ
                    a = fromℕℤ n

                    lhs0 : (0ℤ *ℤ ⁺toℤ one⁺) ≡ 0ℤ
                    lhs0 = *ℤ-zero-left (⁺toℤ one⁺)

                    one⁺ℤ≡oneℤ : ⁺toℤ one⁺ ≡ oneℤ
                    one⁺ℤ≡oneℤ = refl

                    rhs1 : (a *ℤ ⁺toℤ one⁺) ≡ a
                    rhs1 = trans (cong (λ t → a *ℤ t) one⁺ℤ≡oneℤ) (*ℤ-one-right a)
                  in
                  ≤ℤ-resp-≡ʳ (sym rhs1) (≤ℤ-resp-≡ˡ (sym lhs0) (0≤ℤ-fromℕℤ n))
              in
              fromℕ/one-nonneg (suc my)

            -- Choose δy so that δy * Ix < εq, and δx so that δx * Iy < εq.
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

            -- Cauchy moduli for x, y at δx, δy.
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

            -- Global N.
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
            εqNonneg = <ℚ→≤ℚ εqPos

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
              dx0≤Ix = ≤ℚ-trans dx0≤Bx Bx≤Ix

              dy0≤Iy : distℚ (seq y n) 0ℚ ≤ℚ Iy
              dy0≤Iy = ≤ℚ-trans dy0≤By By≤Iy

              dy<δy : distℚ (seq y m) (seq y n) <ℚ δy
              dy<δy = cy m n Cy≤m Cy≤n

              dx<δx : distℚ (seq x m) (seq x n) <ℚ δx
              dx<δx = cx m n Cx≤m Cx≤n

              dy≤δy : distℚ (seq y m) (seq y n) ≤ℚ δy
              dy≤δy = <ℚ→≤ℚ dy<δy

              dx≤δx : distℚ (seq x m) (seq x n) ≤ℚ δx
              dx≤δx = <ℚ→≤ℚ dx<δx

              dyNonneg : 0ℚ ≤ℚ distℚ (seq y m) (seq y n)
              dyNonneg = distℚ-nonneg (seq y m) (seq y n)

              dxNonneg : 0ℚ ≤ℚ distℚ (seq x m) (seq x n)
              dxNonneg = distℚ-nonneg (seq x m) (seq x n)

              dx0Nonneg : 0ℚ ≤ℚ distℚ (seq x m) 0ℚ
              dx0Nonneg = distℚ-nonneg (seq x m) 0ℚ

              dy0Nonneg : 0ℚ ≤ℚ distℚ (seq y n) 0ℚ
              dy0Nonneg = distℚ-nonneg (seq y n) 0ℚ

              -- Split the product distance via triangle and multiplicative scaling.
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
              d1≤ = ≃ℚ→≤ℚˡ (distℚ-*ℚ-left p q s)

              d2≤ : d2 ≤ℚ (distℚ p r *ℚ distℚ s 0ℚ)
              d2≤ = ≃ℚ→≤ℚˡ (distℚ-*ℚ-right s p r)

              -- Bound distℚ p 0ℚ by Ix and distℚ s 0ℚ by Iy.
              d1Bound : (distℚ q s *ℚ distℚ p 0ℚ) ≤ℚ (distℚ q s *ℚ Ix)
              d1Bound = ≤ℚ-mul-nonneg-left (distℚ p 0ℚ) Ix (distℚ q s) dx0≤Ix dyNonneg

              d2Bound : (distℚ p r *ℚ distℚ s 0ℚ) ≤ℚ (distℚ p r *ℚ Iy)
              d2Bound = ≤ℚ-mul-nonneg-left (distℚ s 0ℚ) Iy (distℚ p r) dy0≤Iy dxNonneg

              -- Use the chosen δx, δy to make these products < εq.
              dqsIx≤ : (distℚ q s *ℚ Ix) ≤ℚ (δy *ℚ Ix)
              dqsIx≤ = ≤ℚ-mul-nonneg-right (distℚ q s) δy Ix dy≤δy IxNonneg

              dprIy≤ : (distℚ p r *ℚ Iy) ≤ℚ (δx *ℚ Iy)
              dprIy≤ = ≤ℚ-mul-nonneg-right (distℚ p r) δx Iy dx≤δx IyNonneg

              d1'<εq : (distℚ q s *ℚ Ix) <ℚ εq
              d1'<εq = ≤<ℚ→<ℚ dqsIx≤ δyIx<εq

              d2'<εq : (distℚ p r *ℚ Iy) <ℚ εq
              d2'<εq = ≤<ℚ→<ℚ dprIy≤ δxIy<εq

              d1<εq : d1 <ℚ εq
              d1<εq = ≤<ℚ→<ℚ (≤ℚ-trans d1≤ d1Bound) d1'<εq

              d2<εq : d2 <ℚ εq
              d2<εq = ≤<ℚ→<ℚ (≤ℚ-trans d2≤ d2Bound) d2'<εq

              d1Nonneg : 0ℚ ≤ℚ d1
              d1Nonneg = distℚ-nonneg (p *ℚ q) (p *ℚ s)

              d2Nonneg : 0ℚ ≤ℚ d2
              d2Nonneg = distℚ-nonneg (p *ℚ s) (r *ℚ s)

              d1≤εq : d1 ≤ℚ εq
              d1≤εq = <ℚ→≤ℚ d1<εq

              d2≤εq : d2 ≤ℚ εq
              d2≤εq = <ℚ→≤ℚ d2<εq

              sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
              sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

              sum<ε : (d1 +ℚ d2) <ℚ ε
              sum<ε = ≤<ℚ→<ℚ sum≤ εq+εq<ε

              tri : distℚ (p *ℚ q) (r *ℚ s) ≤ℚ (d1 +ℚ d2)
              tri = distℚ-triangle (p *ℚ q) (p *ℚ s) (r *ℚ s)
            in
            ≤<ℚ→<ℚ tri sum<ε)
      }

-- Basic algebra laws for ⋅ℝ are forced pointwise from ⋅ℚ laws.

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

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
          d≤0 = ≃ℚ→≤ℚˡ d≃0
        in
        ≤<ℚ→<ℚ d≤0 εpos)
  }

-- Multiplication is forced to respect ≃ℝ (well-defined on equivalence classes).

⋅ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x ⋅ℝ y) ≃ℝ (x' ⋅ℝ y')
⋅ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' = record
  { conv0 = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ εqPos

        εq+εq<ε : (εq +ℚ εq) <ℚ ε
        εq+εq<ε = εQuarter-double<ε ε εpos

        -- Eventual bounds on dist from 0.
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
          ≤ℚ-trans
            (distℚ-nonneg (seq y Ny0) 0ℚ)
            (ByBound Ny0 (≤-refl Ny0))

        Bx'Nonneg : 0ℚ ≤ℚ Bx'
        Bx'Nonneg =
          ≤ℚ-trans
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
        δxNonneg = <ℚ→≤ℚ δxPos

        δxKY<εq : (δx *ℚ KY) <ℚ εq
        δxKY<εq = snd (snd δxPack)

        δy : ℚ
        δy = fst δyPack

        δyPos : 0ℚ <ℚ δy
        δyPos = fst (snd δyPack)

        δyNonneg : 0ℚ ≤ℚ δy
        δyNonneg = <ℚ→≤ℚ δyPos

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

          -- shorthands
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
          dxx'≤δx = <ℚ→≤ℚ dxx'<δx

          dyy'≤δy : dyy' ≤ℚ δy
          dyy'≤δy = <ℚ→≤ℚ dyy'<δy

          Iy≤KY : Iy ≤ℚ KY
          Iy≤KY = ≤ℚ-trans Iy≤By By≤KY

          Ix'≤KX' : Ix' ≤ℚ KX'
          Ix'≤KX' = ≤ℚ-trans Ix'≤Bx' Bx'≤KX'

          d1 : ℚ
          d1 = distℚ (xn *ℚ yn) (x'n *ℚ yn)

          d2 : ℚ
          d2 = distℚ (x'n *ℚ yn) (x'n *ℚ y'n)

          d1Nonneg : 0ℚ ≤ℚ d1
          d1Nonneg = distℚ-nonneg (xn *ℚ yn) (x'n *ℚ yn)

          d2Nonneg : 0ℚ ≤ℚ d2
          d2Nonneg = distℚ-nonneg (x'n *ℚ yn) (x'n *ℚ y'n)

          d1≤scaled : d1 ≤ℚ (dxx' *ℚ Iy)
          d1≤scaled = ≃ℚ→≤ℚˡ (distℚ-*ℚ-right yn xn x'n)

          d2≤scaled : d2 ≤ℚ (dyy' *ℚ Ix')
          d2≤scaled = ≃ℚ→≤ℚˡ (distℚ-*ℚ-left x'n yn y'n)

          -- bound dxx'*Iy by δx*KY
          step1 : (dxx' *ℚ Iy) ≤ℚ (δx *ℚ Iy)
          step1 = ≤ℚ-mul-nonneg-right dxx' δx Iy dxx'≤δx IyNonneg

          step2 : (δx *ℚ Iy) ≤ℚ (δx *ℚ KY)
          step2 = ≤ℚ-mul-nonneg-left Iy KY δx Iy≤KY δxNonneg

          scaled1≤ : (dxx' *ℚ Iy) ≤ℚ (δx *ℚ KY)
          scaled1≤ = ≤ℚ-trans step1 step2

          scaled1<εq : (dxx' *ℚ Iy) <ℚ εq
          scaled1<εq = ≤<ℚ→<ℚ scaled1≤ δxKY<εq

          d1<εq : d1 <ℚ εq
          d1<εq = ≤<ℚ→<ℚ (≤ℚ-trans d1≤scaled (≤ℚ-trans step1 step2)) δxKY<εq

          -- bound dyy'*Ix' by δy*KX'
          step1' : (dyy' *ℚ Ix') ≤ℚ (δy *ℚ Ix')
          step1' = ≤ℚ-mul-nonneg-right dyy' δy Ix' dyy'≤δy Ix'Nonneg

          step2' : (δy *ℚ Ix') ≤ℚ (δy *ℚ KX')
          step2' = ≤ℚ-mul-nonneg-left Ix' KX' δy Ix'≤KX' δyNonneg

          scaled2≤ : (dyy' *ℚ Ix') ≤ℚ (δy *ℚ KX')
          scaled2≤ = ≤ℚ-trans step1' step2'

          scaled2<εq : (dyy' *ℚ Ix') <ℚ εq
          scaled2<εq = ≤<ℚ→<ℚ scaled2≤ δyKX'<εq

          d2<εq : d2 <ℚ εq
          d2<εq = ≤<ℚ→<ℚ d2≤scaled scaled2<εq

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = <ℚ→≤ℚ d1<εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = <ℚ→≤ℚ d2<εq

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ sum≤ εq+εq<ε

          tri : distℚ (xn *ℚ yn) (x'n *ℚ y'n) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle (xn *ℚ yn) (x'n *ℚ yn) (x'n *ℚ y'n)
        in
        ≤<ℚ→<ℚ tri sum<ε)
  }

-- Addition is forced to respect ≃ℝ (well-defined on equivalence classes).

+ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x +ℝ y) ≃ℝ (x' +ℝ y')
+ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' = record
  { conv0 = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ εqPos

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
          d1≤dx = ≃ℚ→≤ℚˡ (distℚ-+ℚ-right xn x'n yn)

          d2≤dy : d2 ≤ℚ dy
          d2≤dy = ≃ℚ→≤ℚˡ (distℚ-+ℚ-left x'n yn y'n)

          d1<εq : d1 <ℚ εq
          d1<εq = ≤<ℚ→<ℚ d1≤dx dx<εq

          d2<εq : d2 <ℚ εq
          d2<εq = ≤<ℚ→<ℚ d2≤dy dy<εq

          d1≤εq : d1 ≤ℚ εq
          d1≤εq = <ℚ→≤ℚ d1<εq

          d2≤εq : d2 ≤ℚ εq
          d2≤εq = <ℚ→≤ℚ d2<εq

          sum≤ : (d1 +ℚ d2) ≤ℚ (εq +ℚ εq)
          sum≤ = ≤ℚ-sum≤double-nonneg d1 d2 εq d1Nonneg d2Nonneg εqNonneg d1≤εq d2≤εq

          sum<ε : (d1 +ℚ d2) <ℚ ε
          sum<ε = ≤<ℚ→<ℚ sum≤ εq+εq<ε

          tri : distℚ (xn +ℚ yn) (x'n +ℚ y'n) ≤ℚ (d1 +ℚ d2)
          tri = distℚ-triangle (xn +ℚ yn) (x'n +ℚ yn) (x'n +ℚ y'n)
        in
        ≤<ℚ→<ℚ tri sum<ε)
  }

-- Negation is forced to respect ≃ℝ.

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
          d≤ = ≃ℚ→≤ℚˡ negEq
        in
        ≤<ℚ→<ℚ d≤ d<ε)
  }

-- Subtraction is forced to respect ≃ℝ (derived from + and -).

-ℝ-resp-≃ℝ₂ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → (x -ℝ y) ≃ℝ (x' -ℝ y')
-ℝ-resp-≃ℝ₂ {x} {x'} {y} {y'} x≃x' y≃y' =
  +ℝ-resp-≃ℝ x≃x' (-ℝ-resp-≃ℝ y≃y')

{-
### Law 14T.10: Order On ℝ Is Forced By Eventual Comparison
**Necessity Proof:** Without eventual ε-approximation, the ordering would depend on finite prefixes rather than limit behavior.
**Formal Reference:** RealsCauchy.agda.≤ℝP (lines 1582-1583)
**Consequence:** Eliminates the freedom to compare reals by non-limit criteria.
-}

-- x ≤ℝ y iff for all ε>0, eventually seq x n ≤ seq y n + ε

infix 4 _≤ℝ_ _<ℝ_

record _≤ℝ_ (x y : ℝ) : Set where
  field
    leReal : (ε : ℚ) → (0ℚ <ℚ ε) → Σ ℕ (λ N → (n : ℕ) → N ≤ n → (seq x n) ≤ℚ ((seq y n) +ℚ ε))

≤ℝP : ℝ → ℝ → Set
≤ℝP = _≤ℝ_

-- x <ℝ y iff there exists ε>0 such that eventually seq x n + ε ≤ seq y n

record _<ℝ_ (x y : ℝ) : Set where
  field
    ltWitness : Σ ℚ (λ ε → (0ℚ <ℚ ε) × Σ ℕ (λ N → (n : ℕ) → N ≤ n → ((seq x n) +ℚ ε) ≤ℚ (seq y n)))

-- Strict order forces non-strict order by forgetting the witness margin.

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
          xn≤yn = ≤ℚ-trans xn≤xn+ε xn+ε≤yn

          yn≤yn+δ : yn ≤ℚ (yn +ℚ δ)
          yn≤yn+δ = ≤ℚ-add-nonneg-right yn δ (<ℚ→≤ℚ δpos)
        in
        ≤ℚ-trans xn≤yn yn≤yn+δ)
  }

-- Equivalence forces mutual ≤ℝ bounds (distance→order transport).

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

-- Transitivity of <ℝ is forced by composing witness margins.

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
            xε≤y = ≤ℚ-trans xε≤xε₁ xε₁≤y

            y≤y+ε₂ : yn ≤ℚ (yn +ℚ ε₂)
            y≤y+ε₂ = ≤ℚ-add-nonneg-right yn ε₂ (<ℚ→≤ℚ ε₂pos)

            xε≤y+ε₂ : (xn +ℚ ε) ≤ℚ (yn +ℚ ε₂)
            xε≤y+ε₂ = ≤ℚ-trans xε≤y y≤y+ε₂
          in
            ≤ℚ-trans xε≤y+ε₂ (convYZ n Nyz≤n))))
  }

-- Strict order respects ≃ℝ on both sides by shrinking the witness margin.

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
                α+β≤ε = <ℚ→≤ℚ α+β<ε

                ε+α+β≤ε+ε : (ε +ℚ (α +ℚ β)) ≤ℚ (ε +ℚ ε)
                ε+α+β≤ε+ε = ≤ℚ-+ℚ-mono-left ε (α +ℚ β) ε α+β≤ε

                ε+ε<ε₀ : (ε +ℚ ε) <ℚ ε₀
                ε+ε<ε₀ = εQuarter-double<ε ε₀ ε₀pos

                ε+ε≤ε₀ : (ε +ℚ ε) ≤ℚ ε₀
                ε+ε≤ε₀ = <ℚ→≤ℚ ε+ε<ε₀

                ε+α+β≤ε₀ : (ε +ℚ (α +ℚ β)) ≤ℚ ε₀
                ε+α+β≤ε₀ = ≤ℚ-trans ε+α+β≤ε+ε ε+ε≤ε₀

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
                x'n+ε+β≤xn+ε₀ = ≤ℚ-trans x'n+ε+β≤xn+t xnt≤xnε₀

                xn+ε₀≤yn : (xn +ℚ ε₀) ≤ℚ yn
                xn+ε₀≤yn = convXY n Nxy≤n

                x'n+ε+β≤yn : (x'n +ℚ (ε +ℚ β)) ≤ℚ yn
                x'n+ε+β≤yn = ≤ℚ-trans x'n+ε+β≤xn+ε₀ xn+ε₀≤yn

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

-- Reflexivity of ≤ℝ is forced by ≤ℚ-add-nonneg-right.

≤ℝ-refl : (x : ℝ) → x ≤ℝ x
≤ℝ-refl x = record
  { leReal = λ ε εpos →
      zero , (λ n _ →
        ≤ℚ-add-nonneg-right (seq x n) ε (<ℚ→≤ℚ εpos))
  }

-- Transitivity of ≤ℝ is forced by ε-splitting and ≤ℚ transitivity.

≤ℝ-trans : {x y z : ℝ} → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans {x} {y} {z} x≤y y≤z = record
  { leReal = λ ε εpos →
      let
        εq : ℚ
        εq = εQuarter ε

        εqPos : 0ℚ <ℚ εq
        εqPos = εQuarter-pos ε

        εqNonneg : 0ℚ ≤ℚ εq
        εqNonneg = <ℚ→≤ℚ εqPos

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

          -- (yn + εq) ≤ (zn + εq + εq) by monotonicity.
          step₁ : (yn +ℚ εq) ≤ℚ ((zn +ℚ εq) +ℚ εq)
          step₁ = ≤ℚ-+ℚ-mono-right yn (zn +ℚ εq) εq yn≤zn+εq

          -- xn ≤ (zn + εq + εq).
          step₂ : xn ≤ℚ ((zn +ℚ εq) +ℚ εq)
          step₂ = ≤ℚ-trans xn≤yn+εq step₁

          -- (zn + εq + εq) ≤ (zn + ε) because εq + εq < ε.
          step₃ : ((zn +ℚ εq) +ℚ εq) ≤ℚ (zn +ℚ (εq +ℚ εq))
          step₃ = ≃ℚ→≤ℚˡ (+ℚ-assoc zn εq εq)

          step₄ : (zn +ℚ (εq +ℚ εq)) ≤ℚ (zn +ℚ ε)
          step₄ = ≤ℚ-+ℚ-mono-left zn (εq +ℚ εq) ε (<ℚ→≤ℚ εq+εq<ε)

          done : xn ≤ℚ (zn +ℚ ε)
          done = ≤ℚ-trans step₂ (≤ℚ-trans step₃ step₄)
        in
        done)
  }

-- Antisymmetry: x ≤ y ∧ y ≤ x forces x ≃ y.

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

          -- distℚ xn yn ≤ εq follows from the two bounds.
          d≤εq : distℚ xn yn ≤ℚ εq
          d≤εq = distℚ-bounded-by-ε xn yn εq xn≤yn+εq yn≤xn+εq

          εq<ε : εq <ℚ ε
          εq<ε = εQuarter<ε ε εpos
        in
        ≤<ℚ→<ℚ d≤εq εq<ε)
  }

≤ℝ-resp-≃ℝ : {x x' y y' : ℝ} → x ≃ℝ x' → y ≃ℝ y' → x ≤ℝ y → x' ≤ℝ y'
≤ℝ-resp-≃ℝ {x} {x'} {y} {y'} x≃x' y≃y' x≤y =
  let
    x'≤x : x' ≤ℝ x
    x'≤x = ≃ℝ→≤ℝ (≃ℝ-sym x≃x')

    y≤y' : y ≤ℝ y'
    y≤y' = ≃ℝ→≤ℝ y≃y'
  in
  ≤ℝ-trans (≤ℝ-trans x'≤x x≤y) y≤y'

-- Monotonicity of +ℝ under ≤ℝ is forced pointwise from ≤ℚ monotonicity.

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
            trans
              (+ℚ-assoc yn ε zn)
              (trans
                (cong (λ t → yn +ℚ t) (+ℚ-comm ε zn))
                (sym (+ℚ-assoc yn zn ε)))

          step₂ : (((yn +ℚ ε) +ℚ zn)) ≤ℚ ((yn +ℚ zn) +ℚ ε)
          step₂ = ≃ℚ→≤ℚˡ rhsEq
        in
        ≤ℚ-trans step₁ step₂)
  }

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
          step₂ = ≃ℚ→≤ℚˡ rhsEq
        in
        ≤ℚ-trans step₁ step₂)
  }
