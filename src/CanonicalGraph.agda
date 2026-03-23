{-# OPTIONS --safe --without-K #-}

module CanonicalGraph where

open import OntologyClassification

-- A simple undirected, loopless graph structure.
record Graph : Set₁ where
  field
    Vertex  : Set
    _~_     : Vertex → Vertex → Set
    sym~    : ∀ {a b} → a ~ b → b ~ a
    irrefl~ : ∀ a → ¬ (a ~ a)

open Graph public

-- Graph isomorphism (bijection preserving adjacency in both directions).
record GraphIso (G H : Graph) : Set where
  open Graph G renaming (Vertex to V₁; _~_ to _~G_)
  open Graph H renaming (Vertex to V₂; _~_ to _~H_)
  field
    to   : V₁ → V₂
    from : V₂ → V₁

    to-from : ∀ v → to (from v) ≡ v
    from-to : ∀ v → from (to v) ≡ v

    to-pres~   : ∀ {a b} → _~G_ a b → _~H_ (to a) (to b)
    from-pres~ : ∀ {a b} → _~H_ a b → _~G_ (from a) (from b)

open GraphIso public

-- Canonical graph of an ontology: vertices are states, and an edge is just inequality.
GraphOfOntology : Ontology → Graph
GraphOfOntology O = record
  { Vertex = State O
  ; _~_ = λ s t → ¬ (s ≡ t)
  ; sym~ = λ {a} {b} a≢b → λ b≡a → a≢b (sym b≡a)
  ; irrefl~ = λ a a≢a → a≢a refl
  }

K₄-Graph : Graph
K₄-Graph = GraphOfOntology K₄

-- Helpers: an ontology isomorphism gives injectivity of the underlying maps.
iso-to-injective : ∀ {O₁ O₂ : Ontology} → (iso : O₁ ≅ O₂) →
  ∀ {x y : State O₁} → map (_≅_.to iso) x ≡ map (_≅_.to iso) y → x ≡ y
iso-to-injective {O₁} {O₂} iso {x} {y} eq =
  trans (sym (_≅_.from-to iso x))
    (trans (cong (map (_≅_.from iso)) eq)
      (_≅_.from-to iso y))

iso-from-injective : ∀ {O₁ O₂ : Ontology} → (iso : O₁ ≅ O₂) →
  ∀ {x y : State O₂} → map (_≅_.from iso) x ≡ map (_≅_.from iso) y → x ≡ y
iso-from-injective {O₁} {O₂} iso {x} {y} eq =
  trans (sym (_≅_.to-from iso x))
    (trans (cong (map (_≅_.to iso)) eq)
      (_≅_.to-from iso y))

-- Turn an ontology isomorphism into a graph isomorphism between the canonical graphs.
GraphIso-from-OntologyIso : ∀ {O₁ O₂ : Ontology} → O₁ ≅ O₂ →
  GraphIso (GraphOfOntology O₁) (GraphOfOntology O₂)
GraphIso-from-OntologyIso {O₁} {O₂} iso = record
  { to = map (_≅_.to iso)
  ; from = map (_≅_.from iso)
  ; to-from = _≅_.to-from iso
  ; from-to = _≅_.from-to iso
  ; to-pres~ = λ {a} {b} a≢b → λ eq → a≢b (iso-to-injective iso eq)
  ; from-pres~ = λ {a} {b} a≢b → λ eq → a≢b (iso-from-injective iso eq)
  }

-- The K₄ graph is the canonical information field for any complete ontology.
InfoField : CompleteOntology → Graph
InfoField _ = K₄-Graph

-- Canonical identification: every complete ontology's canonical graph is isomorphic to K₄.
InfoField-iso : (C : CompleteOntology) →
  GraphIso (GraphOfOntology (base C)) (InfoField C)
InfoField-iso C =
  GraphIso-from-OntologyIso (theorem-K₄-classification-complete C)


-- ═══════════════════════════════════════════════════════════════════════════
-- FIELDS ON THE INFORMATION GRAPH (ADJACENCY-FIRST)
-- ═══════════════════════════════════════════════════════════════════════════

-- Oriented edges: a concrete pair together with an adjacency proof.
OrientedEdge : Graph → Set
OrientedEdge G = Σ (Vertex G) (λ a → Σ (Vertex G) (λ b → _~_ G a b))

-- Vertex fields and (oriented) edge fields.
VertexField : Graph → Set → Set
VertexField G A = Vertex G → A

EdgeField : Graph → Set → Set
EdgeField G A = (a b : Vertex G) → _~_ G a b → A

-- Evaluate an edge field on an oriented edge package.
evalEdgeField : ∀ {G : Graph} {A : Set} → EdgeField G A → OrientedEdge G → A
evalEdgeField {G} Φ e = Φ a b a~b
  where
    a : Vertex G
    a = fst e

    b : Vertex G
    b = fst (snd e)

    a~b : _~_ G a b
    a~b = snd (snd e)

-- Flip an oriented edge (a,b, a~b) ↦ (b,a, b~a).
flipEdge : ∀ {G : Graph} → OrientedEdge G → OrientedEdge G
flipEdge {G} e = b , (a , sym~ G a~b)
  where
    a : Vertex G
    a = fst e

    b : Vertex G
    b = fst (snd e)

    a~b : _~_ G a b
    a~b = snd (snd e)

-- Undirected edge fields: invariant under swapping endpoints.
--
-- Key subtlety: adjacency proofs live in `Set`, so they are generally NOT
-- proof-irrelevant. For transport to be well-behaved without FunExt/K,
-- we package a minimal proof-irrelevance requirement: the observable depends
-- only on the endpoints (not on the particular adjacency proof term).
record UndirectedEdgeField (G : Graph) (A : Set) : Set where
  field
    val : EdgeField G A

    proof-irrelevant : ∀ a b (p q : _~_ G a b) → val a b p ≡ val a b q

    symmetric : ∀ a b (p : _~_ G a b) → val a b p ≡ val b a (sym~ G p)

open UndirectedEdgeField public

-- Transport of fields along a graph isomorphism.
transportVertexField : ∀ {G H : Graph} {A : Set} → GraphIso G H → VertexField H A → VertexField G A
transportVertexField iso φ v = φ (to iso v)

transportEdgeField : ∀ {G H : Graph} {A : Set} → GraphIso G H → EdgeField H A → EdgeField G A
transportEdgeField {G} {H} {A} iso Φ a b a~b =
  Φ (to iso a) (to iso b) (to-pres~ iso a~b)

transportUndirectedEdgeField : ∀ {G H : Graph} {A : Set} → GraphIso G H → UndirectedEdgeField H A → UndirectedEdgeField G A
transportUndirectedEdgeField {G} {H} {A} iso U = record
  { val = transportEdgeField iso (val U)
  ; proof-irrelevant = pir
  ; symmetric = symm
  }
  where
    pir : ∀ a b (p q : _~_ G a b) → transportEdgeField iso (val U) a b p ≡ transportEdgeField iso (val U) a b q
    pir a b p q = proof-irrelevant U (to iso a) (to iso b) (to-pres~ iso p) (to-pres~ iso q)

    symm : ∀ a b (p : _~_ G a b) → transportEdgeField iso (val U) a b p ≡ transportEdgeField iso (val U) b a (sym~ G p)
    symm a b p =
      trans
        (symmetric U (to iso a) (to iso b) (to-pres~ iso p))
        (sym (proof-irrelevant U (to iso b) (to iso a)
          (to-pres~ iso (sym~ G p))
          (sym~ H (to-pres~ iso p))))

-- Inverse of a graph isomorphism (useful for pushforwards).
inverseGraphIso : ∀ {G H : Graph} → GraphIso G H → GraphIso H G
inverseGraphIso iso = record
  { to = from iso
  ; from = to iso
  ; to-from = from-to iso
  ; from-to = to-from iso
  ; to-pres~ = from-pres~ iso
  ; from-pres~ = to-pres~ iso
  }

-- Pushforward = transport along the forward direction (implemented via inverse).
pushVertexField : ∀ {G H : Graph} {A : Set} → GraphIso G H → VertexField G A → VertexField H A
pushVertexField iso φ = transportVertexField (inverseGraphIso iso) φ

pushEdgeField : ∀ {G H : Graph} {A : Set} → GraphIso G H → EdgeField G A → EdgeField H A
pushEdgeField iso Φ = transportEdgeField (inverseGraphIso iso) Φ

pushUndirectedEdgeField : ∀ {G H : Graph} {A : Set} → GraphIso G H → UndirectedEdgeField G A → UndirectedEdgeField H A
pushUndirectedEdgeField iso U = transportUndirectedEdgeField (inverseGraphIso iso) U


-- ═══════════════════════════════════════════════════════════════════════════
-- K₄ AS THE CANONICAL INFORMATION FIELD (NEIGHBORS)
-- ═══════════════════════════════════════════════════════════════════════════
--
-- This is the minimal combinatorial interface needed for later operators
-- (degree, Laplacian, spectra): each vertex has exactly three neighbors.

pattern g0 = zero
pattern g1 = suc zero
pattern g2 = suc (suc zero)

neighbors : K₄-State → Fin 3 → K₄-State
neighbors v₀ g0 = v₁
neighbors v₀ g1 = v₂
neighbors v₀ g2 = v₃
neighbors v₁ g0 = v₀
neighbors v₁ g1 = v₂
neighbors v₁ g2 = v₃
neighbors v₂ g0 = v₀
neighbors v₂ g1 = v₁
neighbors v₂ g2 = v₃
neighbors v₃ g0 = v₀
neighbors v₃ g1 = v₁
neighbors v₃ g2 = v₂

neighbor≢self : (v : K₄-State) → (i : Fin 3) → ¬ (neighbors v i ≡ v)
neighbor≢self v₀ g0 = λ eq → v₀≢v₁ (sym eq)
neighbor≢self v₀ g1 = v₂≢v₀
neighbor≢self v₀ g2 = v₃≢v₀
neighbor≢self v₁ g0 = v₀≢v₁
neighbor≢self v₁ g1 = v₂≢v₁
neighbor≢self v₁ g2 = v₃≢v₁
neighbor≢self v₂ g0 = λ eq → v₂≢v₀ (sym eq)
neighbor≢self v₂ g1 = λ eq → v₂≢v₁ (sym eq)
neighbor≢self v₂ g2 = λ eq → v₂≢v₃ (sym eq)
neighbor≢self v₃ g0 = λ eq → v₃≢v₀ (sym eq)
neighbor≢self v₃ g1 = λ eq → v₃≢v₁ (sym eq)
neighbor≢self v₃ g2 = v₂≢v₃

-- Every distinct vertex is one of the 3 neighbors.
neighbor-index : (v u : K₄-State) → ¬ (u ≡ v) → Σ (Fin 3) (λ i → neighbors v i ≡ u)
neighbor-index v₀ v₀ p = ⊥-elim (p refl)
neighbor-index v₀ v₁ p = g0 , refl
neighbor-index v₀ v₂ p = g1 , refl
neighbor-index v₀ v₃ p = g2 , refl
neighbor-index v₁ v₀ p = g0 , refl
neighbor-index v₁ v₁ p = ⊥-elim (p refl)
neighbor-index v₁ v₂ p = g1 , refl
neighbor-index v₁ v₃ p = g2 , refl
neighbor-index v₂ v₀ p = g0 , refl
neighbor-index v₂ v₁ p = g1 , refl
neighbor-index v₂ v₂ p = ⊥-elim (p refl)
neighbor-index v₂ v₃ p = g2 , refl
neighbor-index v₃ v₀ p = g0 , refl
neighbor-index v₃ v₁ p = g1 , refl
neighbor-index v₃ v₂ p = g2 , refl
neighbor-index v₃ v₃ p = ⊥-elim (p refl)

degreeK₄ : ℕ
degreeK₄ = 3
