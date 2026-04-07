# Separation Plan: Void ↔ Physics.agda

## The Epistemological Cut

The boundary is **not** thematic ("physics chapters go there"). It is logical:

| **Void** | **Physics.agda** |
|---|---|
| What the compiler can verify | What a physicist must interpret |
| `refl` closes it | A human names it |
| "137 is forced" | "137 is α⁻¹" |
| Elimination, construction, uniqueness | Correspondence, comparison, prediction |

**Void proves that certain numbers survive.**  
**Physics.agda claims those survivors are physical observables.**

That claim — the *identification* — is the first sentence that cannot be typechecked. It is the cut.

---

## Current State

### Void.lagda.tex (~27500 lines)

55 chapters. The chain runs:

```
D₀ → Two → Drift → Classification → K₄ (unique fixpoint)
   → Arithmetic → ℚ → ℝ → Spectral Action → K4PhysRep (singleton)
   → Discrete-Continuum Bridge → Physics ⇔ Distinction
```

**Problem zones** — chapters where Void *names physics*:

| Ch. | Line | Title | Issue |
|---|---|---|---|
| 1 | 376 | Introduction | Frames the physics question — OK as motivation |
| 14 | 4239 | An Unexpected Correspondence | Calls `coupling-inv` a "coupling constant" — **interpretation** |
| 22332 | — | K₄ Physics Constants Layer | Name says "physics" but content is formal. Already has the theorem/interpretation disclaimer. **Rename?** |
| 22564 | — | K₄ Representation Theory | `K4PhysRep` fields carry physical names (dim → "spacetime dimension", coupling-inv → "fine structure constant"). **Core tension.** |
| 25045 | — | Discrete-Continuum Bridge | Corrections target experimental values (α⁻¹ = 137.036…). **Deepest tension.** |

### Physics.agda (1880 lines)

Currently a "rapid-development scratch pad" that:
- Re-exports all Void results
- Defines convenience aliases
- Adds PDG 2024 comparison values
- Develops exploratory directions (Λ, Ω, η, n_s)
- Cross-validates with `refl`

**Problem:** The real physics interpretation is scattered across *both* files.

---

## The Principle

> **Void contains everything the compiler forces.**
> **Physics.agda contains everything a physicist identifies.**

Concretely:

- **Void** may say: "the unique survivor of the coupling chain evaluates to 137"
- **Void** may NOT say: "this is the fine-structure constant"
- **Physics.agda** says: "Void's coupling-inv = 137 corresponds to α⁻¹ ≈ 137.036"

---

## The Plan

### Phase 0: Rename in Void (prose only, no code changes)

The K4PhysRep *field names* (`coupling-inv`, `n-gen`, `gauge-rank`, …) are the stickiest problem. Renaming them would break 500+ references. But they don't need renaming — they are *structurally* named:

- `coupling-inv` = "the inverse coupling constant of this graph" (formal)
- `n-gen` = "the generation count of this graph's vertex structure" (formal)

What needs rewriting is the **prose** that presents them. Anywhere Void says "this is the fine-structure constant" must become "this invariant evaluates to 137".

**Affected sections (prose-only edits):**

1. **Ch. 14 "An Unexpected Correspondence"** — rewrite to present the spectral coincidence *without claiming it IS physics*. Frame: "the graph forces 137; the question of whether this matches α⁻¹ belongs to the interpretation layer."

2. **Ch. "K₄ Physics Constants Layer"** — already has the theorem/interpretation disclaimer (lines 22340-22365). May need a stronger title: → **"K₄ Forced Constants Layer"** or **"K₄ Invariant Ledger"**?

3. **Ch. "K₄ Representation Theory"** — the `K4PhysRep` prologue already has the skeleton disclaimer we added today. Sufficient.

4. **Ch. "Discrete-Continuum Bridge"** — this is the hardest case. The corrections (11/72, 16/69, …) are formally forced, but the *target* (137.036 vs. 137) is physical. Possible solution: Void proves the correction is forced as a rational number. Physics.agda identifies the target.

5. **"Physics Presupposes Distinction"** — use term "admissible record" instead of "physics". Already mostly clean after today's edit.

### Phase 1: Move interpretation to Physics.agda

Everything in Physics.agda that currently re-exports Void with physical names — that is *correct placement*. What's missing:

**Must move FROM Void TO Physics.agda (interpretation prose only):**

- Any sentence in Void that says "this matches the observed X" → move to Physics.agda as a comment or documentation section
- PDG comparison values → already in Physics.agda ✓
- Cosmological speculation → already in Physics.agda ✓

**Must ADD to Physics.agda:**

A new top-level documentation block that explicitly states the identification:

```agda
-- §══════════════════════════════════════════════════════════════════════════
-- § THE IDENTIFICATION LAYER
-- §
-- § Void proves that certain numbers are the unique survivors of the
-- § elimination chain from D₀. This module identifies those survivors
-- § with measured physical quantities.
-- §
-- § Every identification below is a CLAIM, not a theorem.
-- § The claim is: "Void's forced invariant X corresponds to measured Y."
-- § Agda checks the algebra. A physicist checks the correspondence.
-- §══════════════════════════════════════════════════════════════════════════
```

### Phase 2: Sharpen the Discrete-Continuum Bridge

This is the deepest problem. The bridge computes:
- Proton correction: 11/72 → yields 1836.15... 
- Muon correction: 16/69 → yields 206.768...
- These corrections are *forced* (Void proves the numerator/denominator uniqueness)
- But the *comparison to PDG values* is interpretation

**Solution:** The bridge stays in Void as a formal result. The code proves: "the unique correction quotient is 11/72". Physics.agda then says: "11/72 applied to the bare value 1836 yields 1836.15…, compared to PDG 2024: 1836.15267…".

**Check:** Does Void's bridge prose currently say "matches PDG"? If yes → rewrite to "evaluates to" and move the comparison to Physics.agda.

### Phase 3: 5-Pillar records for Physics.agda

Six sections in Physics.agda lack proper justification records:

1. Lepton Mass Hierarchies
2. Wilson/Gauge Theory connections  
3. Regge trajectory
4. Geodesic structure
5. Confinement scale
6. Loop correction details

Each needs a `5-Pillar` record showing: irreducibility, coprimality, K₄ invariance, unique factorization, and comparison with PDG.

(Deferred — separate task, not part of the separation.)

---

## Work Order

| Step | What | Where | Risk |
|---|---|---|---|
| 1 | Audit every Void sentence that names a physical observable | Void prose | Low (find & replace) |
| 2 | Rewrite those sentences to state the formal result only | Void prose | Medium (must preserve clarity) |
| 3 | Add identification-layer header to Physics.agda | Physics.agda | Low |
| 4 | Move observable identifications to Physics.agda | Physics.agda | Low |
| 5 | Verify Void contains zero sentences of the form "this is the X" | Void prose | Low (grep check) |
| 6 | Typecheck both files | Both | None (prose changes don't break types) |
| 7 | Deferred: 5-Pillar records in Physics.agda | Physics.agda | Separate task |

---

## What Does NOT Move

- **K4PhysRep** stays in Void. It is formal: a record with 17 ℕ fields and 16 chain equalities. The field *names* are suggestive, but the *proofs* are structural.
- **ForcedValues** stays in Void. Every line closes by `refl`.
- **Discrete-Continuum Bridge code** stays in Void. The elimination of numerator candidates is formal.
- **`physics-presupposes-distinction`** stays in Void. It is a type-level theorem about the record, not an empirical claim.
- **All 27,000+ lines of elimination chain** stay in Void. Untouched.

## What DOES Change

- **~20 sentences of prose** in Void that currently cross the interpretation line
- **~1 new documentation block** in Physics.agda declaring the identification protocol
- **Chapter title "K₄ Physics Constants Layer"** → consider **"K₄ Forced Constants Layer"**
- **Zero lines of Agda code move.** The code is correctly placed. Only the prose needs sharpening.
