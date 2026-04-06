# Copilot Agent Protocol: The Dual-Layer Manifest

## 1. MISSION
Transform `Void.lagda.tex` into a mathematical manifest. Every section must pull the reader in like a high-level philosophical book, but lock them into absolute logical necessity like a rigorous paper. **Nothing is chosen. Everything is forced.** We do not design a system; we execute the annihilation of logically unstable alternatives until only $K_4$ remains.

## 2. THE DUAL-LAYER STYLE (CORE DIRECTIVE)
Every section introducing a new concept MUST be split into two distinct, consecutive layers.

### Layer 1: Narrative (Motivation & Intuition)
- **Purpose:** Draw the reader in. Explain the "Why" before the "How". Formulate the exact problem or paradox that needs solving. Use strong, conceptual metaphors (e.g., "uncorrupted elevator", "collapses into noise").
- **Rule:** Never imply human choice or arbitrary design. 
- **Forbidden:** "We need...", "We formalize this by...", "We introduce...", "We define..."
- **Required:** "Nature forces...", "If we do not establish X, the system collapses...", "This constraint leaves us with only one path..."

### Layer 2: Formal (The Iron Logic)
Immediately following the narrative, harden the logic right before the Agda code block. Use exactly this bolded structure to make the reasoning logically unassailable (Reviewer-Safe). The middle term depends on what the code does:

**When the code eliminates** (enumerates candidates, filters by absurd patterns, uses sandwich arguments, proves by negation):
- **\textbf{Constraint:}** What structural force or paradox makes this code physically/logically unavoidable?
- **\textbf{Elimination:}** What alternatives are annihilated? What is the unique structure that survives?
- **\textbf{Consequence:}** What weaker alternatives are eliminated? What invariant survives?

**When the code constructs** (defines types/records, builds witnesses, proves by computation/refl, equational chaining):
- **\textbf{Constraint:}** What structural force or paradox makes this code physically/logically unavoidable?
- **\textbf{Construction:}** What is the unique structure forced by this constraint? Why does no alternative type/witness/proof exist?
- **\textbf{Consequence:}** What weaker alternatives are eliminated? What invariant survives?

In constructive type theory, some steps are irreduzibel constructive: type definitions, existence witnesses ($\Sigma$-inhabitants), and computational verification by \texttt{refl} must build terms. Use **Construction:** for these honestly. Use **Elimination:** only where the code genuinely kills candidates (absurd patterns, sandwich arguments, $\neg$-proofs).

## 3. PROSE TONE: "SURVIVAL OF THE FITTEST"
- **Narrative:** Logic is the judge, the Agda compiler is the executioner. Every chapter is a verdict.
- **Actionable verbs:** Use words like *forge*, *shatter*, *eliminate*, *force*, *collapse*, *survive*. 
- **Mindset:** We are not building a theory; we are discovering the only theory that survives self-consistency.

## 4. STRICT COMPLIANCE & FORMALISM
- **No LaTeX-Voodoo:** Use strict, clean LaTeX. No unnecessary packages.
- **Set-Omega:** Always use `$\mathit{Set}_\omega$` for the top universe.
- **Observable Rule:** When a fundamental constant ($\alpha$, $\kappa$, $d$) appears, state:
  > "This quantity is an invariant under $Aut(K_4)$. Any deviation would break the symmetry chain. It is therefore a necessary observable."

## 5. DIAGRAMS AS MILESTONES
Use TikZ diagrams strategically where logic becomes "visible":
- The primordial cut ($D_0$)
- The instability and failure of $K_3$
- The final victory of $K_4$ (The Tetrahedron)

## 6. PROSE AS FINAL TEXT — NOT AS PATCH
This is a book, not a pull request. Never write prose that refers to a previous version of itself:
- **Forbidden:** "We have updated...", "This replaces the earlier...", "Previously we said...", "The following sharpens..."
- **Required:** Write the final intended text directly. Every sentence stands on its own as if it has always been there.
- **Reason:** A reader encounters the text once, linearly. They have no access to revision history. Any meta-commentary about changes breaks the prose and signals that the author was uncertain. Write as if the words were forced by necessity—because they were.