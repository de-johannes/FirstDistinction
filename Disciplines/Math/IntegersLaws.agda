{-# OPTIONS --safe --without-K #-}

module Disciplines.Math.IntegersLaws where

open import FirstDistinction
open import Disciplines.Math.Counting
open import Disciplines.Math.Integers
open import Disciplines.Math.FiniteSumsZ

{-
CHAPTER 14F: Forced Additive Laws (ℕ and ℤ)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14C (ℤ normal forms)
AGDA MODULES: Disciplines.Math.IntegersLaws
DEGREES OF FREEDOM ELIMINATED: re-ordering / re-parenthesization freedom in finite sums
-}

normalizeDiag0ℤ : (n : ℕ) → normalizeℤ n n ≡ 0ℤ
normalizeDiag0ℤ zero = refl
normalizeDiag0ℤ (suc n) = normalizeDiag0ℤ n

+ℕ-zero-right : (n : ℕ) → n +ℕ zero ≡ n
+ℕ-zero-right zero = refl
+ℕ-zero-right (suc n) = cong suc (+ℕ-zero-right n)

+ℕ-suc-right : (n m : ℕ) → n +ℕ suc m ≡ suc (n +ℕ m)
+ℕ-suc-right zero m = refl
+ℕ-suc-right (suc n) m = cong suc (+ℕ-suc-right n m)

+ℕ-assoc : (a b c : ℕ) → (a +ℕ b) +ℕ c ≡ a +ℕ (b +ℕ c)
+ℕ-assoc zero b c = refl
+ℕ-assoc (suc a) b c = cong suc (+ℕ-assoc a b c)

+ℕ-comm : (a b : ℕ) → a +ℕ b ≡ b +ℕ a
+ℕ-comm zero b = sym (+ℕ-zero-right b)
+ℕ-comm (suc a) b =
  trans
    refl
    (trans
      (cong suc (+ℕ-comm a b))
      (sym (+ℕ-suc-right b a)))

normalizeℤ-cong : {a a' b b' : ℕ} → a ≡ a' → b ≡ b' → normalizeℤ a b ≡ normalizeℤ a' b'
normalizeℤ-cong {a} {a'} {b} {b'} pa pb = trans (cong (λ t → normalizeℤ t b) pa) (cong (normalizeℤ a') pb)

normalize-plusRight : (a b c d : ℕ) →
  normalizeℤ (pos (toPairℤ (normalizeℤ a b)) +ℕ c) (neg (toPairℤ (normalizeℤ a b)) +ℕ d)
    ≡
  normalizeℤ (a +ℕ c) (b +ℕ d)
normalize-plusRight zero zero c d = refl
normalize-plusRight (suc a) zero c d = refl
normalize-plusRight zero (suc b) c d = refl
normalize-plusRight (suc a) (suc b) c d = normalize-plusRight a b c d

+ℤ-comm : (x y : ℤ) → x +ℤ y ≡ y +ℤ x
+ℤ-comm x y with toPairℤ x | toPairℤ y
... | px | py =
  normalizeℤ-cong (+ℕ-comm (pos px) (pos py)) (+ℕ-comm (neg px) (neg py))

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

+ℤ-zero-left : (x : ℤ) → 0ℤ +ℤ x ≡ x
+ℤ-zero-left 0ℤ = refl
+ℤ-zero-left (+suc n) = refl
+ℤ-zero-left (-suc n) = refl

+ℤ-zero-right : (x : ℤ) → x +ℤ 0ℤ ≡ x
+ℤ-zero-right x = trans (+ℤ-comm x 0ℤ) (+ℤ-zero-left x)

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

+ℤ-inv-left : (x : ℤ) → negℤ x +ℤ x ≡ 0ℤ
+ℤ-inv-left x = trans (+ℤ-comm (negℤ x) x) (+ℤ-inv-right x)

negℤ-zero : negℤ 0ℤ ≡ 0ℤ
negℤ-zero = refl

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

negℤ-zero→zero : (z : ℤ) → negℤ z ≡ 0ℤ → z ≡ 0ℤ
negℤ-zero→zero 0ℤ _ = refl
negℤ-zero→zero (+suc n) ()
negℤ-zero→zero (-suc n) ()

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

swapPairℕ : Pairℕ → Pairℕ
swapPairℕ p = ⟪ neg p , pos p ⟫

toPair-negℤ : (z : ℤ) → toPairℤ (negℤ z) ≡ swapPairℕ (toPairℤ z)
toPair-negℤ 0ℤ = refl
toPair-negℤ (+suc n) = refl
toPair-negℤ (-suc n) = refl

negℤ-involutive : (z : ℤ) → negℤ (negℤ z) ≡ z
negℤ-involutive 0ℤ = refl
negℤ-involutive (+suc n) = refl
negℤ-involutive (-suc n) = refl

pos-toPair-negℤ : (z : ℤ) → pos (toPairℤ (negℤ z)) ≡ neg (toPairℤ z)
pos-toPair-negℤ z = cong pos (toPair-negℤ z)

neg-toPair-negℤ : (z : ℤ) → neg (toPairℤ (negℤ z)) ≡ pos (toPairℤ z)
neg-toPair-negℤ z = cong neg (toPair-negℤ z)

neg-normalizeℤ : (a b : ℕ) → negℤ (normalizeℤ a b) ≡ normalizeℤ b a
neg-normalizeℤ zero zero = refl
neg-normalizeℤ (suc a) zero = refl
neg-normalizeℤ zero (suc b) = refl
neg-normalizeℤ (suc a) (suc b) = neg-normalizeℤ a b

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

neg-+ℤ : (x y : ℤ) → negℤ (x +ℤ y) ≡ negℤ x +ℤ negℤ y
neg-+ℤ x y =
  let A = pos (toPairℤ x) +ℕ pos (toPairℤ y) in
  let B = neg (toPairℤ x) +ℕ neg (toPairℤ y) in
  trans (neg-normalizeℤ A B) (sym (negAdd-normalizeSwap x y))

neg-sum3ℤ : (a b c : ℤ) → negℤ (sum3ℤ a b c) ≡ sum3ℤ (negℤ a) (negℤ b) (negℤ c)
neg-sum3ℤ a b c =
  trans (neg-+ℤ a (b +ℤ c))
        (cong (λ t → negℤ a +ℤ t) (neg-+ℤ b c))

neg-sum4ℤ : (a b c d : ℤ) → negℤ (sum4ℤ a b c d) ≡ sum4ℤ (negℤ a) (negℤ b) (negℤ c) (negℤ d)
neg-sum4ℤ a b c d =
  trans
    (neg-+ℤ a (b +ℤ (c +ℤ d)))
    (cong (λ t → negℤ a +ℤ t)
          (trans
            (neg-+ℤ b (c +ℤ d))
            (cong (λ t → negℤ b +ℤ t) (neg-+ℤ c d))))

neg-fourTimesℤ : (x : ℤ) → negℤ (fourTimesℤ x) ≡ fourTimesℤ (negℤ x)
neg-fourTimesℤ x = neg-sum4ℤ x x x x

neg-sumFin3ℤ : (f : Fin3 → ℤ) → negℤ (sumFin3ℤ f) ≡ sumFin3ℤ (λ k → negℤ (f k))
neg-sumFin3ℤ f = neg-sum3ℤ (f f0) (f f1) (f f2)
