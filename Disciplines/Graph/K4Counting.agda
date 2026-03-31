{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4Counting where

open import FirstDistinction
open import Disciplines.Math.Counting

{-
CHAPTER 14B: Counting On The Canonical K₄ Carrier

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: FirstDistinction (EndoCase classification)
AGDA MODULES: Disciplines.Graph.K4Counting
DEGREES OF FREEDOM ELIMINATED: non-canonical enumeration of the four K₄ vertices
-}

vertexAt : Fin4 → EndoCase
vertexAt g0 = case-constL
vertexAt g1 = case-constR
vertexAt g2 = case-id
vertexAt g3 = case-dual

vertexIndex : EndoCase → Fin4
vertexIndex case-constL = g0
vertexIndex case-constR = g1
vertexIndex case-id     = g2
vertexIndex case-dual   = g3

vertexAt-index : (v : EndoCase) → vertexAt (vertexIndex v) ≡ v
vertexAt-index case-constL = refl
vertexAt-index case-constR = refl
vertexAt-index case-id     = refl
vertexAt-index case-dual   = refl

index-vertexAt : (i : Fin4) → vertexIndex (vertexAt i) ≡ i
index-vertexAt g0 = refl
index-vertexAt g1 = refl
index-vertexAt g2 = refl
index-vertexAt g3 = refl
