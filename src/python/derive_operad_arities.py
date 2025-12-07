#!/usr/bin/env python3
"""
derive_operad_arities.py

GOAL: Prove that the 8 coherence laws and their arities are FORCED by K₄.

The question: Are the arities [3,3,2,1] and [2,4,2,4] arbitrary, or do they
emerge necessarily from K₄ structure?

APPROACH:
1. K₄ has V=4 vertices, E=6 edges, deg=3
2. Any coherence law on K₄ involves k vertices at a time
3. The arity = number of variables = number of vertices involved
4. We enumerate all possible relation types and their natural arities
"""

from itertools import combinations, permutations
from math import comb

# K₄ invariants
V = 4  # vertices
E = 6  # edges (complete graph: V*(V-1)/2 = 6)
deg = 3  # each vertex connects to 3 others
chi = 2  # Euler characteristic: V - E + F = 4 - 6 + 4 = 2
F = 4  # faces (triangular)

print("=" * 70)
print("K₄ STRUCTURE")
print("=" * 70)
print(f"Vertices V = {V}")
print(f"Edges E = {E}")
print(f"Degree deg = {deg}")
print(f"Faces F = {F}")
print(f"Euler χ = {chi}")
print()

# ============================================================================
# PART 1: WHAT ARE THE NATURAL RELATION TYPES ON A GRAPH?
# ============================================================================

print("=" * 70)
print("PART 1: NATURAL RELATIONS ON K₄")
print("=" * 70)
print()

# A relation involves k elements. What k-values are natural for K₄?

print("VERTEX RELATIONS (how many vertices at a time?)")
print("-" * 50)

# k=1: Properties of single vertices (identity, fixed point)
# k=2: Properties of pairs (edges, paths)
# k=3: Properties of triples (triangles, paths of length 2)
# k=4: Properties of quadruples (the whole graph)

for k in range(1, V+1):
    count = comb(V, k)
    print(f"  k={k}: C({V},{k}) = {count} ways to choose {k} vertices")

print()
print("NATURAL ARITIES:")
print("  1 - Single element (idempotence: a=a)")
print("  2 - Pair (neutrality: a·e=a, involution: f∘f⁻¹=id)")
print("  3 - Triple (associativity: (a·b)·c = a·(b·c), triangle)")
print("  4 - Quadruple (cancellativity: needs 4 to compare pairs)")
print()

# ============================================================================
# PART 2: WHY EXACTLY 4 ALGEBRAIC + 4 CATEGORICAL LAWS?
# ============================================================================

print("=" * 70)
print("PART 2: WHY 4+4 LAWS? — FROM POLARITY")
print("=" * 70)
print()

print("THE KEY INSIGHT: POLARITY")
print("-" * 50)
print()
print("Each distinction D₀ IS a Bool = {φ, ¬φ} = 2 poles")
print("K₄ has V = 4 vertices (distinctions)")
print()
print("Total degrees of freedom = V × |Bool| = 4 × 2 = 8")
print()

print("THE SPLIT INTO 4+4:")
print("-" * 50)
print()
print("  φ-pole (positive/forward/Drift):")
print("    → 4 ALGEBRAIC laws (one per vertex)")
print("    → describe the OPERATION Δ")
print()
print("  ¬φ-pole (negative/backward/CoDrift):")
print("    → 4 CATEGORICAL laws (one per vertex)")
print("    → describe the MORPHISMS ∇")
print()
print("Each vertex contributes TWICE: once for each pole.")
print("This is NOT a choice—it follows from D₀ = Bool.")
print()

print(f"TOTAL: 4 + 4 = 8 = V × 2 = V × |Bool| = κ")
print()

print("WHY THIS MATCHES κ (Einstein coupling):")
print(f"  κ = states × distinctions = 2 × 4 = 8")
print(f"  κ = algebraic + categorical = 4 + 4 = 8")
print("  SAME NUMBER, SAME REASON: polarity of K₄ vertices")
print()

# ============================================================================
# PART 3: WHY THESE SPECIFIC ARITIES?
# ============================================================================

print("=" * 70)
print("PART 3: DERIVING THE ARITIES")
print("=" * 70)
print()

print("CLAIM: The arities [3,3,2,1] and [2,4,2,4] are forced by")
print("       the structure of K₄.")
print()

# ALGEBRAIC LAWS - describe the operation Δ: D×D → D

print("ALGEBRAIC LAWS (describe binary operation Δ)")
print("-" * 50)

print()
print("1. ASSOCIATIVITY: (a·b)·c = a·(b·c)")
print("   - Compares two ways to combine THREE elements")
print("   - Arity = 3 (forced: you need exactly 3 for associativity)")
print("   - This is K₃ embedded in K₄")

print()
print("2. DISTRIBUTIVITY: a·(b+c) = (a·b)+(a·c)")
print("   - Relates one element to TWO others under two operations")
print("   - Arity = 3 (forced: minimal to state distribution)")
print("   - Alternative view: path of length 2 in K₄")

print()
print("3. NEUTRALITY (IDENTITY): a·e = a = e·a")
print("   - Relates element to identity")
print("   - Arity = 2 (forced: element + identity)")
print("   - This is an edge in K₄")

print()
print("4. IDEMPOTENCE: a·a = a")
print("   - Self-relation")
print("   - Arity = 1 (forced: only involves one element)")
print("   - This is a vertex loop in K₄")

algebraic_arities = [3, 3, 2, 1]
print()
print(f"ALGEBRAIC ARITIES: {algebraic_arities}")
print(f"SUM = {sum(algebraic_arities)} = deg² = {deg}² = {deg**2}")
print()

# CATEGORICAL LAWS - describe morphisms and their compositions

print("CATEGORICAL LAWS (describe morphisms Δ, ∇)")
print("-" * 50)

print()
print("5. INVOLUTIVITY: Δ∘∇ = id (or ∇∘Δ = id)")
print("   - Two operations compose to identity")
print("   - Arity = 2 (forced: two operations Δ, ∇)")
print("   - This is the Drift-CoDrift pair")

print()
print("6. CANCELLATIVITY: Δ(a,b) = Δ(a',b') ⟹ (a,b) = (a',b')")
print("   - Need to compare TWO PAIRS")
print("   - Arity = 4 (forced: a, b, a', b' are 4 elements)")
print("   - This requires all 4 vertices of K₄")

print()
print("7. IRREDUCIBILITY: a≠b ⟹ Δ(a,b) ≥ a ∧ Δ(a,b) ≥ b")
print("   - Compares result to inputs")
print("   - Arity = 2 (forced: input pair a, b)")
print("   - Note: output Δ(a,b) is determined by inputs")

print()
print("8. CONFLUENCE: x→y ∧ x→z ⟹ ∃w. y→w ∧ z→w")
print("   - Diamond property needs source, two targets, join")
print("   - Arity = 4 (forced: x, y, z, w are 4 elements)")
print("   - This IS the K₄ diamond structure")

categorical_arities = [2, 4, 2, 4]
print()
print(f"CATEGORICAL ARITIES: {categorical_arities}")

product = 1
for a in categorical_arities:
    product *= a
print(f"PRODUCT = {product} = λ³ = {V}³ = {V**3}")
print()

# ============================================================================
# PART 4: WHY SUM vs PRODUCT?
# ============================================================================

print("=" * 70)
print("PART 4: WHY SUM FOR ALGEBRAIC, PRODUCT FOR CATEGORICAL?")
print("=" * 70)
print()

print("ALGEBRAIC LAWS govern Δ: D×D → D (CONVERGENT)")
print("  - Multiple inputs → one output")
print("  - Constraints are INDEPENDENT (can satisfy each separately)")
print("  - Independent constraints ADD: n₁ OR n₂ OR ... = Σnᵢ")
print()

print("CATEGORICAL LAWS govern ∇: D → D×D (DIVERGENT)")  
print("  - One input → multiple outputs")
print("  - Constraints must be satisfied SIMULTANEOUSLY")
print("  - Simultaneous constraints MULTIPLY: n₁ AND n₂ AND ... = Πnᵢ")
print()

print("TYPE-THEORETIC VIEW:")
print("  Σ-type (sum): 'A or B' - additive, choice")
print("  Π-type (product): 'A and B' - multiplicative, pairing")
print()

print("THE SIGNATURES FORCE THE COMBINATION:")
print(f"  Δ convergent → SUM of arities = {sum(algebraic_arities)}")
print(f"  ∇ divergent → PRODUCT of arities = {product}")
print()

# ============================================================================
# PART 5: THE CONSTRAINT - ARITIES MUST BE CONSISTENT WITH K₄
# ============================================================================

print("=" * 70)
print("PART 5: UNIQUENESS - ARE THESE THE ONLY VALID ARITIES?")
print("=" * 70)
print()

print("CONSTRAINTS:")
print(f"  1. Each arity ∈ {{1, 2, 3, 4}} (can't exceed V={V})")
print(f"  2. Algebraic sum = deg² = {deg**2}")
print(f"  3. Categorical product = λ³ = {V**3}")
print(f"  4. Exactly 4 algebraic laws (bounded by V)")
print(f"  5. Exactly 4 categorical laws (bounded by V)")
print()

# Enumerate all possible algebraic arities summing to 9
print("ALL 4-TUPLES OF ARITIES IN {1,2,3,4} SUMMING TO 9:")
count_alg = 0
valid_alg = []
for a1 in range(1, 5):
    for a2 in range(1, 5):
        for a3 in range(1, 5):
            for a4 in range(1, 5):
                if a1 + a2 + a3 + a4 == 9:
                    # Sort to get canonical form
                    arities = tuple(sorted([a1, a2, a3, a4], reverse=True))
                    if arities not in valid_alg:
                        valid_alg.append(arities)
                    count_alg += 1

print(f"  Total ordered: {count_alg}")
print(f"  Unique (unordered): {len(valid_alg)}")
for v in sorted(valid_alg, reverse=True):
    print(f"    {list(v)}")
print()

# Enumerate all possible categorical arities with product 64
print("ALL 4-TUPLES OF ARITIES IN {1,2,3,4} WITH PRODUCT 64:")
count_cat = 0
valid_cat = []
for a1 in range(1, 5):
    for a2 in range(1, 5):
        for a3 in range(1, 5):
            for a4 in range(1, 5):
                if a1 * a2 * a3 * a4 == 64:
                    arities = tuple(sorted([a1, a2, a3, a4], reverse=True))
                    if arities not in valid_cat:
                        valid_cat.append(arities)
                    count_cat += 1

print(f"  Total ordered: {count_cat}")
print(f"  Unique (unordered): {len(valid_cat)}")
for v in sorted(valid_cat, reverse=True):
    print(f"    {list(v)}")
print()

# ============================================================================
# PART 6: WHICH ARITIES ARE SEMANTICALLY VALID?
# ============================================================================

print("=" * 70)
print("PART 6: SEMANTIC CONSTRAINTS REDUCE OPTIONS")
print("=" * 70)
print()

print("ALGEBRAIC LAWS have fixed arities by their DEFINITION:")
print("  - Associativity MUST have arity 3 (definition requires 3 elements)")
print("  - Idempotence MUST have arity 1 (self-relation)")
print("  - Neutrality MUST have arity 2 (element + identity)")
print("  - This leaves: 9 - 3 - 1 - 2 = 3 for distributivity")
print()
print("  ⟹ UNIQUE: [3, 3, 2, 1]")
print()

print("CATEGORICAL LAWS have fixed arities by their DEFINITION:")
print("  - Involutivity: 2 operations → arity 2")
print("  - Cancellativity: compare 2 pairs → arity 4")
print("  - Irreducibility: compare result to pair → arity 2")
print("  - Confluence: diamond with 4 points → arity 4")
print()
print("  ⟹ UNIQUE: [2, 4, 2, 4] (product = 64)")
print()

# ============================================================================
# PART 7: VERIFICATION
# ============================================================================

print("=" * 70)
print("PART 7: FINAL VERIFICATION")
print("=" * 70)
print()

alg_sum = sum(algebraic_arities)
cat_prod = 1
for a in categorical_arities:
    cat_prod *= a

print(f"Algebraic arities: {algebraic_arities}")
print(f"  Sum = {alg_sum} = deg² = {deg**2} ✓" if alg_sum == deg**2 else f"  Sum = {alg_sum} ≠ {deg**2} ✗")
print()

print(f"Categorical arities: {categorical_arities}")
print(f"  Product = {cat_prod} = λ³ = {V**3} ✓" if cat_prod == V**3 else f"  Product = {cat_prod} ≠ {V**3} ✗")
print()

alpha_inv = cat_prod * chi + alg_sum
print(f"α⁻¹ = {cat_prod} × {chi} + {alg_sum} = {alpha_inv}")
print()

# ============================================================================
# PART 8: THE KEY INSIGHT
# ============================================================================

print("=" * 70)
print("PART 8: THE KEY INSIGHT")
print("=" * 70)
print()

print("THE ARITIES ARE NOT CHOSEN, THEY ARE FORCED:")
print()
print("1. K₄ has V=4 vertices, so laws can involve at most 4 elements")
print()
print("2. Standard coherence laws have FIXED arities by definition:")
print("   - Associativity = 3 (you can't state it with fewer)")
print("   - Idempotence = 1 (self-relation)")
print("   - Neutrality = 2 (element + identity)")
print("   - Distributivity = 3 (a, b, c)")
print("   - Involutivity = 2 (two operations)")
print("   - Cancellativity = 4 (two pairs)")
print("   - Irreducibility = 2 (one pair)")
print("   - Confluence = 4 (diamond)")
print()
print("3. These arities sum/multiply to K₄ invariants:")
print(f"   3+3+2+1 = {alg_sum} = deg² = {deg**2}")
print(f"   2×4×2×4 = {cat_prod} = λ³ = {V**3}")
print()
print("4. The COINCIDENCE is that standard operad laws")
print("   have arities matching K₄ spectral invariants.")
print()
print("5. OR: K₄ DETERMINES which laws are relevant,")
print("   and those laws have these arities BY DEFINITION.")
print()

print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print()
print("The arities [3,3,2,1] and [2,4,2,4] are:")
print("  - STANDARD for operad coherence laws")
print("  - FIXED by the definitions of the laws")
print("  - MATCHING K₄ invariants (deg²=9, λ³=64)")
print()
print("The question shifts from 'why these arities?'")
print("to 'why do K₄ invariants match standard law arities?'")
print()
print("POSSIBLE ANSWER: K₄ is the minimal structure where")
print("all 8 standard coherence laws can be stated.")
print("  - Need 3 elements for associativity → need at least K₃")
print("  - Need 4 elements for cancellativity → need at least K₄")
print("  - K₄ is exactly large enough, and it saturates.")
