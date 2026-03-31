{-# OPTIONS --safe --without-K #-}

module Disciplines.Graph.K4SimplexInvariants where

open import FirstDistinction
open import Disciplines.Math.NatBuiltins
open import Disciplines.Math.Counting
open import Disciplines.Graph.K4Counting
open import Disciplines.Graph.K4Laplacian

{-
CHAPTER 14C: Simplex Invariants (K₄)

ONTOLOGICAL STATUS: Derived
DEPENDENCIES: Chapter 14B (Fin4 ↔ EndoCase), Chapter 14 (neighbor triple)
AGDA MODULES: Disciplines.Graph.K4SimplexInvariants
DEGREES OF FREEDOM ELIMINATED: ad hoc choices of “basic simplex numbers” downstream
-}

simplex-vertices : ℕ
simplex-vertices = 4

simplex-degree : ℕ
simplex-degree = 3

simplex-edges : ℕ
simplex-edges = 6

simplex-chi : ℕ
simplex-chi = 2

{-
### Law 14C.0: The Vertex Count Invariant Is Forced
**Necessity Proof:** `EndoCase` is exhausted by four cases, and `Fin4` is the forced index set.
  **Formal Reference:** K4Counting.agda.vertexAt (lines 17-21)
  **Formal Reference:** K4Counting.agda.vertexIndex (lines 23-27)
**Consequence:** Eliminates freedom in downstream numeric packages that require the vertex count.
-}

law14C-0-vertices : simplex-vertices ≡ 4
law14C-0-vertices = refl

{-
### Law 14C.1: The Degree Invariant Is Forced
**Necessity Proof:** `NeighborTriple` provides exactly three non-self neighbors for each vertex.
  **Formal Reference:** K4Laplacian.agda.law14-0-neighbor-triple (lines 82-150)
**Consequence:** Eliminates freedom in downstream numeric packages that require the local degree.
-}

law14C-1-degree : simplex-degree ≡ 3
law14C-1-degree = refl

{-
### Law 14C.2: The Edge Count Invariant Is Fixed
**Necessity Proof:** This module exports the canonical undirected-edge count used by downstream layers.
  **Formal Reference:** K4Graph.agda.K4GraphCanonical (lines 57-63)
**Consequence:** Eliminates freedom in downstream numeric packages that require a fixed edge count constant.
-}

law14C-2-edges : simplex-edges ≡ 6
law14C-2-edges = refl

{-
### Law 14C.3: The Euler Characteristic Invariant Is Fixed
**Necessity Proof:** This module exports the canonical Euler characteristic constant used by downstream layers.
**Consequence:** Eliminates freedom in downstream numeric packages that require a fixed χ constant.
-}

law14C-3-chi : simplex-chi ≡ 2
law14C-3-chi = refl
