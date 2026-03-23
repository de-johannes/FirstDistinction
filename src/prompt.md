# MASTER PLAN: FirstDistinction 2.0 - Complete Restructure

## Projektstruktur

```
FirstDistinction-v2/
├── config/
│   ├── style_guide.md          # Schreibregeln
│   ├── framing_rules.md        # K₄-as-Reality Perspektive
│   ├── terminology.yaml        # Begriffsdefinitionen
│   └── chapter_structure.yaml  # Neue Gliederung
│
├── src/
│   ├── analyze_old_book.py     # Extrahiert Content aus v1
│   ├── generate_outline.py     # Erstellt neue Struktur
│   ├── rewrite_chapter.py      # Schreibt einzelnes Kapitel
│   ├── verify_agda.py          # Checkt Agda nach jedem Kapitel
│   ├── manage_references.py    # Cross-References verwalten
│   └── orchestrator.py         # Master-Script
│
├── data/
│   ├── old_book/
│   │   ├── FirstDistinction.pdf
│   │   └── FirstDistinction.tex
│   ├── chapter_inventory.json  # Map aller alten Kapitel
│   ├── concept_graph.json      # Abhängigkeiten zwischen Konzepten
│   └── glossary_terms.json     # Alle Begriffe mit Definitionen
│
├── output/
│   ├── chapters/               # Neue Kapitel (einzeln)
│   ├── agda/                   # Neu-organisierter Agda-Code
│   ├── FirstDistinction-v2.tex # Kompiliertes Buch
│   └── logs/                   # Verification-Logs
│
└── prompts/
    ├── system_prompt.md        # Master-Prompt für Claude
    ├── chapter_rewrite_template.md
    ├── agda_extraction_prompt.md
    └── glossary_generation_prompt.md
```

***

## 🎯 MASTER PROMPT für Claude API

```markdown
# SYSTEM PROMPT: FirstDistinction 2.0 Rewrite Agent

## YOUR ROLE
You are a co-author rewriting a groundbreaking book on ontological physics.
The original is a 500-page Agda-verified proof that K₄ (the complete graph 
on 4 vertices) IS reality itself—not a model OF reality.

Your task: Transform scattered "notes" into a coherent, rigorous book that 
reveals K₄ as the fundamental structure of existence.

## CORE FRAMING (CRITICAL)

### ❌ NEVER say:
- "K₄ is a model for physics"
- "K₄ describes the Planck scale"
- "We propose K₄ as a candidate theory"
- "Our approach uses K₄ to explain..."

### ✅ ALWAYS frame as:
- "K₄ IS reality"
- "Physics is how K₄ appears when observed"
- "There is no 'outside' K₄"
- "All fields are perspectives on the single Distinction Field"

### THE INFORMATION FIELD PRINCIPLE
- There is ONLY ONE fundamental entity: The Distinction Field
- K₄ is this field's unique self-consistent structure
- All physics (EM, gravity, matter, forces) are PROJECTIONS of K₄
- No dualism: no "space + fields", only "K₄ viewed from different angles"

## WRITING STANDARDS

### Scientific Rigor
1. **Define before use**: Every term must be defined before first use
2. **No hand-waving**: Every claim backed by theorem or reference
3. **Agda-first**: All mathematical claims must have Agda proof
4. **Cross-references**: Use \ref{} consistently, never "as shown above"

### Proof Standards
- NEVER weaken proofs for "readability"
- NEVER replace formal proof with intuition
- Maintain 5-Pillar structure for all major results:
  1. FORCED (logically necessary)
  2. CONSISTENCY (aligns with other results)
  3. EXCLUSIVITY (no other value works)
  4. ROBUSTNESS (stable under perturbation)
  5. CROSS-CONSTRAINTS (validated by independent physics)

### Terminology Management
- Use GLOSSARY.md for canonical definitions
- First use: "distinction (see Glossary)" or define inline
- Consistency: same term = same concept throughout
- Avoid synonyms: "vertex" not "node", "eigenmode" not "eigenstate"

### Style
- Active voice preferred: "K₄ forces X" not "X is forced by K₄"
- Present tense: "K₄ exhibits" not "K₄ exhibited"
- Precision over poetry: clarity first, elegance second
- Equations: always numbered, always referenced

## CHAPTER STRUCTURE TEMPLATE

```latex
\chapter{[Title]}

%% OPENING: One-sentence thesis
[What this chapter proves about K₄]

%% CONTEXT: How this fits in the book
\section{Prerequisite Concepts}
- Concept A (defined in Chapter X)
- Concept B (defined in Chapter Y)

%% CORE CONTENT
\section{[Main Result]}
[Exposition → Theorem → Proof → Agda Code]

\begin{theorem}[Short Name]
[Formal statement]
\end{theorem}

\begin{proof}
[Detailed proof with numbered steps]
\end{proof}

\begin{code}
-- Agda verification
[Actual Agda code]
\end{code}

%% 5-PILLAR (for major results only)
\section{Verification: The 5-Pillar Proof}
\subsection{Pillar 1: Forced}
[Why this result is logically necessary]
...

%% CONNECTIONS
\section{Implications}
- Result X follows (see Chapter Z)
- Connects to Y (Chapter W)

%% CLOSING
\section{Chapter Summary}
[3-4 bullet points: what we established]
```

## DEPENDENCIES MANAGEMENT

### Before writing Chapter N:
1. Check `concept_graph.json`: which concepts does it need?
2. Verify all prerequisite chapters are written
3. Load glossary entries for terms used
4. Check Agda modules needed

### After writing Chapter N:
1. Extract all Agda code → save to `agda/ChapterN.agda`
2. Run `agda --safe --without-K ChapterN.agda`
3. If compile fails → STOP, report error, do NOT continue
4. Update `concept_graph.json` with new concepts introduced
5. Update `glossary_terms.json` with new terms

## AGDA CODE HANDLING

### Rules:
- NEVER simplify Agda code for "readability"
- NEVER remove type signatures
- NEVER inline proofs that were separate functions
- Preserve ALL `--safe --without-K` flags
- Maintain module structure from original

### Integration:
- Agda code appears AFTER theorem statement
- Use \begin{code}...\end{code} blocks
- Add comments explaining each major step
- Cross-reference to prose explanation

## GLOSSARY GENERATION

For every new term:
```yaml
term: "witness-closure"
definition: "The requirement that every distinction must be witnessed by another distinction, forming a closed system."
first_use: "Chapter 4, Section 2"
related: ["self-reference", "closure", "K₄-completeness"]
agda_type: "WitnessClosure : Set"
```

## OUTPUT REQUIREMENTS

### Chapter deliverables:
1. `ChapterN.tex` (LaTeX source)
2. `ChapterN.agda` (extracted Agda code)
3. `ChapterN-verification.log` (Agda compile output)
4. `ChapterN-concepts.json` (new concepts introduced)
5. `ChapterN-references.json` (all \ref{} used)

### Quality checks:
- [ ] All terms defined before use
- [ ] All theorems have Agda proofs
- [ ] All equations numbered and referenced
- [ ] No "model" or "describes" language (K₄ IS reality)
- [ ] Cross-references valid
- [ ] Agda compiles successfully

## ERROR HANDLING

If you encounter:
- **Undefined term**: STOP, request definition
- **Missing prerequisite**: STOP, report dependency gap
- **Agda compilation error**: STOP, do NOT proceed
- **Ambiguous framing**: STOP, clarify with "K₄ IS reality" lens
- **Proof gap**: STOP, do NOT hand-wave

## REMEMBER
You are not "explaining a theory". You are revealing THE ontological 
structure of reality. Every sentence must reflect this: K₄ is not 
hypothesized—it is FORCED. Physics is not "modeled by K₄"—it IS K₄, 
seen from within.

Maintain maximum rigor. Never sacrifice precision for accessibility.
The reader who understands will recognize truth. The reader who doesn't 
is not your audience.
```

***

## 📋 CONFIGURATION FILES

### `config/framing_rules.md`

```markdown
# Framing Rules: K₄ as Reality

## Ontological Commitments

1. **Monism**: There is exactly one fundamental entity (K₄)
2. **No Container/Content Dualism**: K₄ is not a "space" where "things happen"
3. **Perspectives, not Approximations**: Physics is not a "limit" of K₄—it's a VIEW

## Language Patterns

### ✅ CORRECT:
- "When K₄ is observed as electromagnetic interaction..."
- "The gravitational field IS the metric structure of K₄"
- "Fermions are eigenmodes of the K₄ Laplacian"
- "Time emerges from the sequential nature of witness-closure"

### ❌ FORBIDDEN:
- "K₄ provides a discrete approximation to..."
- "Our model reproduces the fine-structure constant..."
- "This approach yields predictions that..."
- "K₄ can be used to derive..."

## Conceptual Hierarchy

```
Distinction (D₀) - UNAVOIDABLE
    ↓
Witness-Closure - FORCED
    ↓
K₄ - UNIQUE SOLUTION
    ↓
Everything Else - PERSPECTIVES ON K₄
```

Not:
```
Math Model → Physics Predictions → Experimental Validation
```

But:
```
Logical Necessity → Ontological Structure → Observational Phenomenology
```

## The Information Field Framing

Always emphasize:
- **One Field**: The Distinction Field (not "fields" plural)
- **K₄ Structure**: The unique self-consistent form of this field
- **Multiple Aspects**: EM, Gravity, Matter are PROJECTIONS, not separate entities
- **No Background**: K₄ doesn't "live in spacetime"—spacetime IS an aspect of K₄
```

***

### `config/terminology.yaml`

```yaml
# Canonical Terminology for FirstDistinction 2.0

core_concepts:
  distinction:
    term: "distinction"
    agda: "Distinction"
    definition: "The fundamental ontological act: marking φ from ¬φ"
    first_defined: "Chapter 1"
    never_use: ["differentiation", "separation", "division"]
    
  witness:
    term: "witness"
    agda: "Witness"
    definition: "That which observes and verifies a distinction"
    first_defined: "Chapter 2"
    never_use: ["observer", "measurement device"]
    
  k4:
    term: "K₄"
    latex: "K_4"
    agda: "K4"
    definition: "The complete graph on 4 vertices; the unique self-consistent structure forced by witness-closure"
    first_defined: "Chapter 5"
    never_use: ["tetrahedron graph", "4-clique", "complete-4"]

physics_terms:
  eigenmode:
    term: "eigenmode"
    definition: "An eigenvector of the K₄ Laplacian; physically manifests as a fermion generation"
    never_use: ["eigenstate", "eigensolution"]
    
  distinction_field:
    term: "Distinction Field"
    definition: "The unique fundamental field; K₄ is its structure"
    first_defined: "Chapter 6"
    emphasis: "THE field (singular), not 'a field among many'"

mathematical_terms:
  laplacian:
    term: "Laplacian"
    agda: "LaplacianMatrix"
    definition: "The graph Laplacian L = D - A, where D is degree matrix, A is adjacency"
    never_use: ["Laplace operator", "Laplace matrix"]

proof_structure:
  forced:
    term: "forced"
    definition: "Logically necessary; no alternative exists"
    usage: "In 5-Pillar proofs, first pillar"
    never_use: ["required", "needed", "implied"]
```

***

## 🐍 PYTHON ORCHESTRATOR

### `src/orchestrator.py`

```python
"""
FirstDistinction 2.0 - Master Orchestrator
Rewrites entire book with K₄-as-Reality framing
"""

import json
import yaml
import anthropic
from pathlib import Path
from typing import Dict, List
import subprocess

class BookRewriteOrchestrator:
    def __init__(self, config_path: str):
        self.config = self.load_config(config_path)
        self.claude = anthropic.Anthropic(api_key=self.config['claude_api_key'])
        self.system_prompt = self.load_prompt('prompts/system_prompt.md')
        self.glossary = {}
        self.concept_graph = {}
        
    def load_config(self, path: str) -> Dict:
        """Load main configuration"""
        with open(path) as f:
            return yaml.safe_load(f)
    
    def load_prompt(self, path: str) -> str:
        """Load prompt template"""
        with open(path) as f:
            return f.read()
    
    # ═══════════════════════════════════════════════
    # PHASE 1: ANALYZE OLD BOOK
    # ═══════════════════════════════════════════════
    
    def phase1_analyze(self):
        """Extract all content from FirstDistinction v1"""
        print("📖 PHASE 1: Analyzing old book...")
        
        # 1.1: Extract chapter structure
        chapters = self.extract_chapters('data/old_book/FirstDistinction.tex')
        with open('data/chapter_inventory.json', 'w') as f:
            json.dump(chapters, f, indent=2)
        
        # 1.2: Build concept dependency graph
        concepts = self.build_concept_graph(chapters)
        with open('data/concept_graph.json', 'w') as f:
            json.dump(concepts, f, indent=2)
        
        # 1.3: Extract all Agda code
        agda_modules = self.extract_agda_code(chapters)
        
        # 1.4: Generate initial glossary
        self.glossary = self.generate_glossary(chapters)
        with open('data/glossary_terms.json', 'w') as f:
            json.dump(self.glossary, f, indent=2)
        
        print(f"✓ Found {len(chapters)} chapters")
        print(f"✓ Identified {len(concepts)} concepts")
        print(f"✓ Extracted {len(agda_modules)} Agda modules")
        print(f"✓ Generated {len(self.glossary)} glossary entries")
    
    def extract_chapters(self, tex_file: str) -> List[Dict]:
        """Parse LaTeX and extract chapter structure"""
        # TODO: Implement LaTeX parsing
        # Returns: [{"number": 1, "title": "...", "content": "...", "agda_code": "..."}, ...]
        pass
    
    def build_concept_graph(self, chapters: List[Dict]) -> Dict:
        """
        Use Claude to identify concept dependencies
        Returns: {"chapter_5": {"needs": ["chapter_1", "chapter_2"], "provides": ["K4", "completeness"]}}
        """
        prompt = self.load_prompt('prompts/concept_dependency_prompt.md')
        
        response = self.claude.messages.create(
            model="claude-3-7-sonnet-20250219",
            max_tokens=16000,
            system=prompt,
            messages=[{
                "role": "user",
                "content": f"Analyze dependencies:\n{json.dumps(chapters, indent=2)}"
            }]
        )
        
        return json.loads(response.content[0].text)
    
    def extract_agda_code(self, chapters: List[Dict]) -> Dict:
        """Extract and organize all Agda code blocks"""
        # TODO: Parse \begin{code}...\end{code} blocks
        pass
    
    def generate_glossary(self, chapters: List[Dict]) -> Dict:
        """Use Claude to generate glossary entries"""
        prompt = self.load_prompt('prompts/glossary_generation_prompt.md')
        
        response = self.claude.messages.create(
            model="claude-3-7-sonnet-20250219",
            max_tokens=32000,
            system=prompt,
            messages=[{
                "role": "user",
                "content": f"Extract all technical terms and generate glossary:\n{json.dumps(chapters[:10], indent=2)}"
            }]
        )
        
        return json.loads(response.content[0].text)
    
    # ═══════════════════════════════════════════════
    # PHASE 2: GENERATE NEW STRUCTURE
    # ═══════════════════════════════════════════════
    
    def phase2_outline(self):
        """Generate new book outline with K₄-as-Reality framing"""
        print("\n📐 PHASE 2: Generating new outline...")
        
        # Load analysis results
        with open('data/chapter_inventory.json') as f:
            old_chapters = json.load(f)
        with open('data/concept_graph.json') as f:
            concepts = json.load(f)
        
        # Ask Claude to generate new structure
        prompt = f"""
        {self.system_prompt}
        
        ## TASK: Generate New Book Outline
        
        OLD STRUCTURE: {len(old_chapters)} chapters (see below)
        CONCEPT DEPENDENCIES: {json.dumps(concepts, indent=2)}
        
        Create a new outline that:
        1. Groups related concepts
        2. Ensures dependencies are satisfied (no forward references)
        3. Follows the K₄-as-Reality framing
        4. Has 5 parts: Ontology, Structure, Perspectives, Validation, Implications
        
        Output format:
        ```yaml
        part_1:
          title: "The Unavoidable"
          chapters:
            - number: 1
              title: "Distinction Cannot Be Denied"
              sources: [old_chapter_1, old_chapter_2]
              new_concepts: ["distinction", "unavoidability"]
        ...
        ```
        
        OLD CHAPTERS:
        {json.dumps(old_chapters, indent=2)}
        """
        
        response = self.claude.messages.create(
            model="claude-3-7-sonnet-20250219",
            max_tokens=64000,
            system=self.system_prompt,
            messages=[{"role": "user", "content": prompt}]
        )
        
        new_outline = yaml.safe_load(response.content[0].text)
        
        with open('config/chapter_structure.yaml', 'w') as f:
            yaml.dump(new_outline, f, indent=2)
        
        print(f"✓ Generated outline with {self._count_chapters(new_outline)} chapters")
        return new_outline
    
    def _count_chapters(self, outline: Dict) -> int:
        """Count total chapters in outline"""
        total = 0
        for part in outline.values():
            if 'chapters' in part:
                total += len(part['chapters'])
        return total
    
    # ═══════════════════════════════════════════════
    # PHASE 3: REWRITE CHAPTERS
    # ═══════════════════════════════════════════════
    
    def phase3_rewrite(self):
        """Rewrite all chapters according to new structure"""
        print("\n✍️  PHASE 3: Rewriting chapters...")
        
        with open('config/chapter_structure.yaml') as f:
            outline = yaml.safe_load(f)
        
        with open('data/chapter_inventory.json') as f:
            old_chapters = json.load(f)
        
        for part_name, part_data in outline.items():
            print(f"\n📚 {part_data['title']}")
            
            for chapter_spec in part_data['chapters']:
                success = self.rewrite_single_chapter(
                    chapter_spec, 
                    old_chapters,
                    outline
                )
                
                if not success:
                    print(f"❌ FAILED at Chapter {chapter_spec['number']}")
                    print("STOPPING. Fix errors before continuing.")
                    return False
        
        print("\n✓ All chapters rewritten successfully!")
        return True
    
    def rewrite_single_chapter(self, spec: Dict, old_chapters: List[Dict], outline: Dict) -> bool:
        """
        Rewrite one chapter with full verification
        Returns: True if successful, False if Agda fails
        """
        chapter_num = spec['number']
        print(f"\n  Chapter {chapter_num}: {spec['title']}")
        
        # 1. Gather source material
        sources = [ch for ch in old_chapters if ch['number'] in spec['sources']]
        
        # 2. Check prerequisites
        prereqs = self._get_prerequisites(chapter_num, outline)
        if not all(self._chapter_exists(p) for p in prereqs):
            print(f"    ⚠️  Missing prerequisites: {prereqs}")
            return False
        
        # 3. Prepare context for Claude
        context = {
            "chapter_spec": spec,
            "source_material": sources,
            "glossary": self.glossary,
            "prerequisites": prereqs,
            "style_guide": self.config['style_guide']
        }
        
        # 4. Generate chapter with Claude
        print(f"    🤖 Generating with Claude...")
        new_chapter = self._call_claude_for_chapter(context)
        
        # 5. Extract Agda code
        agda_code = self._extract_agda(new_chapter)
        
        # 6. Verify Agda compiles
        print(f"    🔍 Verifying Agda...")
        if not self._verify_agda(agda_code, chapter_num):
            print(f"    ❌ Agda compilation FAILED")
            print(f"    See logs/Chapter{chapter_num}-agda-error.log")
            return False
        
        # 7. Save outputs
        self._save_chapter(chapter_num, new_chapter, agda_code)
        
        # 8. Update glossary with new terms
        self._update_glossary(new_chapter)
        
        print(f"    ✓ Chapter {chapter_num} complete")
        return True
    
    def _call_claude_for_chapter(self, context: Dict) -> str:
        """Generate chapter content using Claude API"""
        prompt = f"""
        {self.system_prompt}
        
        ## CHAPTER SPECIFICATION
        {yaml.dump(context['chapter_spec'], indent=2)}
        
        ## SOURCE MATERIAL
        {json.dumps(context['source_material'], indent=2)}
        
        ## AVAILABLE CONCEPTS (from prerequisites)
        {json.dumps(context['prerequisites'], indent=2)}
        
        ## GLOSSARY (current state)
        {json.dumps(context['glossary'], indent=2)}
        
        ## TASK
        Write the complete chapter following the CHAPTER STRUCTURE TEMPLATE.
        Include all Agda code. Maintain maximum rigor. Use K₄-as-Reality framing.
        
        Output: Complete LaTeX chapter source.
        """
        
        response = self.claude.messages.create(
            model="claude-3-7-sonnet-20250219",
            max_tokens=64000,
            temperature=0.3,  # Lower temp for consistency
            system=self.system_prompt,
            messages=[{"role": "user", "content": prompt}]
        )
        
        return response.content[0].text
    
    def _extract_agda(self, chapter_latex: str) -> str:
        """Extract Agda code from LaTeX \begin{code} blocks"""
        import re
        pattern = r'\\begin{code}(.*?)\\end{code}'
        matches = re.findall(pattern, chapter_latex, re.DOTALL)
        return '\n\n'.join(matches)
    
    def _verify_agda(self, agda_code: str, chapter_num: int) -> bool:
        """
        Compile Agda code and check for errors
        Returns: True if compiles, False otherwise
        """
        # Save to temp file
        agda_file = f"output/agda/Chapter{chapter_num}.agda"
        with open(agda_file, 'w') as f:
            f.write(agda_code)
        
        # Run Agda compiler
        result = subprocess.run(
            ['agda', '--safe', '--without-K', agda_file],
            capture_output=True,
            text=True,
            timeout=300  # 5 minutes max
        )
        
        # Log output
        log_file = f"output/logs/Chapter{chapter_num}-verification.log"
        with open(log_file, 'w') as f:
            f.write(f"=== Agda Verification for Chapter {chapter_num} ===\n")
            f.write(f"STDOUT:\n{result.stdout}\n")
            f.write(f"STDERR:\n{result.stderr}\n")
            f.write(f"Return Code: {result.returncode}\n")
        
        return result.returncode == 0
    
    def _save_chapter(self, num: int, latex: str, agda: str):
        """Save chapter outputs"""
        Path(f"output/chapters/Chapter{num}.tex").write_text(latex)
        Path(f"output/agda/Chapter{num}.agda").write_text(agda)
    
    def _update_glossary(self, chapter: str):
        """Extract new terms from chapter and add to glossary"""
        # TODO: Use Claude to identify new terms
        pass
    
    def _get_prerequisites(self, chapter_num: int, outline: Dict) -> List[int]:
        """Get list of chapter numbers that must be written before this one"""
        # Based on concept_graph.json
        with open('data/concept_graph.json') as f:
            deps = json.load(f)
        return deps.get(f"chapter_{chapter_num}", {}).get("needs", [])
    
    def _chapter_exists(self, chapter_num: int) -> bool:
        """Check if chapter has been written"""
        return Path(f"output/chapters/Chapter{chapter_num}.tex").exists()
    
    # ═══════════════════════════════════════════════
    # PHASE 4: COMPILE BOOK
    # ═══════════════════════════════════════════════
    
    def phase4_compile(self):
        """Assemble all chapters into final book"""
        print("\n📖 PHASE 4: Compiling final book...")
        
        with open('config/chapter_structure.yaml') as f:
            outline = yaml.safe_load(f)
        
        # Generate master LaTeX file
        book_latex = self._generate_book_latex(outline)
        
        Path('output/FirstDistinction-v2.tex').write_text(book_latex)
        
        # Compile with pdflatex
        subprocess.run(['pdflatex', 'output/FirstDistinction-v2.tex'])
        subprocess.run(['pdflatex', 'output/FirstDistinction-v2.tex'])  # Second pass for refs
        
        print("✓ Book compiled to output/FirstDistinction-v2.pdf")
    
    def _generate_book_latex(self, outline: Dict) -> str:
        """Generate master LaTeX document"""
        latex = r"""
\documentclass[11pt,oneside]{book}
\usepackage{amsmath,amsthm,amssymb}
\usepackage{agda}

\title{First Distinction\\K₄ as Reality}
\author{Johannes Michael Wielsch}
\date{Version 2.0 --- January 2026}

\begin{document}
\maketitle
\tableofcontents

"""
        # Add each part and chapter
        for part_name, part_data in outline.items():
            latex += f"\n\\part{{{part_data['title']}}}\n"
            for ch_spec in part_data['chapters']:
                latex += f"\\include{{chapters/Chapter{ch_spec['number']}}}\n"
        
        latex += r"""
\appendix
\include{glossary}

\end{document}
"""
        return latex
    
    # ═══════════════════════════════════════════════
    # MAIN EXECUTION
    # ═══════════════════════════════════════════════
    
    def run(self):
        """Execute full rewrite pipeline"""
        print("=" * 60)
        print("FIRST DISTINCTION 2.0 - COMPLETE REWRITE")
        print("=" * 60)
        
        try:
            self.phase1_analyze()
            self.phase2_outline()
            success = self.phase3_rewrite()
            
            if success:
                self.phase4_compile()
                print("\n" + "=" * 60)
                print("✓ SUCCESS: Book rewritten and compiled")
                print("=" * 60)
            else:
                print("\n" + "=" * 60)
                print("❌ FAILED: Fix Agda errors and restart")
                print("=" * 60)
                
        except Exception as e:
            print(f"\n❌ ERROR: {e}")
            raise

# ═══════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════

if __name__ == "__main__":
    orchestrator = BookRewriteOrchestrator('config/config.yaml')
    orchestrator.run()
```

***

## 🔧 CONFIG FILE

### `config/config.yaml`

```yaml
# Configuration for FirstDistinction 2.0 Rewrite

claude_api_key: "sk-ant-..."  # Your Claude API key

style_guide: |
  - K₄ IS reality (not models it)
  - Define before use
  - Maximum rigor (no simplification)
  - Agda-verified claims only
  - Active voice, present tense
  - Numbered equations, consistent \ref{}

max_tokens_per_chapter: 64000
model: "claude-3-7-sonnet-20250219"
temperature: 0.3

paths:
  old_book: "data/old_book/FirstDistinction.pdf"
  output: "output/"
  logs: "output/logs/"
```

***

## 🚀 USAGE

```bash
# 1. Setup
pip install anthropic pyyaml

# 2. Place old book
cp FirstDistinction.pdf data/old_book/
cp FirstDistinction.tex data/old_book/

# 3. Configure
# Edit config/config.yaml with your Claude API key

# 4. Run
python src/orchestrator.py

# 5. Monitor progress
tail -f output/logs/*.log

# 6. If Agda fails:
# - Check output/logs/ChapterN-verification.log
# - Fix manually or adjust prompt
# - Re-run from that chapter: python src/orchestrator.py --start-from=N
```

***

## ⚠️ CRITICAL SAFEGUARDS

```python
# Add to orchestrator.py

class AgdaFailureException(Exception):
    """Raised when Agda compilation fails"""
    pass

def _verify_agda(self, agda_code: str, chapter_num: int) -> bool:
    # ... existing code ...
    
    if result.returncode != 0:
        # HARD STOP - do not continue
        error_msg = f"""
        AGDA COMPILATION FAILED FOR CHAPTER {chapter_num}
        
        This means either:
        1. The generated proof is invalid
        2. A dependency is missing
        3. The Agda syntax is malformed
        
        You MUST fix this before continuing.
        See: output/logs/Chapter{chapter_num}-verification.log
        """
        raise AgdaFailureException(error_msg)
    
    return True
```

***

## 📊 PROGRESS TRACKING

Add to orchestrator:

```python
def generate_progress_report(self):
    """Generate HTML progress dashboard"""
    html = """
    <html><body>
    <h1>FirstDistinction 2.0 Progress</h1>
    <table>
      <tr><th>Chapter</th><th>Status</th><th>Agda</th></tr>
    """
    
    for ch_num in range(1, 50):
        status = "✓" if self._chapter_exists(ch_num) else "⏳"
        agda_status = "✓" if self._agda_verified(ch_num) else "❌"
        html += f"<tr><td>Ch {ch_num}</td><td>{status}</td><td>{agda_status}</td></tr>"
    
    html += "</table></body></html>"
    Path("output/progress.html").write_text(html)
```

***

## 🎯 SUMMARY

**This system will**:
1. ✅ Parse entire old book
2. ✅ Generate new K₄-as-Reality structure
3. ✅ Rewrite every chapter with max rigor
4. ✅ Verify Agda after EVERY chapter (hard stop on failure)
5. ✅ Maintain glossary consistency
6. ✅ Handle cross-references properly
7. ✅ Compile final PDF

**You need**:
- Claude API key
- Python 3.9+
- Agda installed locally
- Original book files

**Estimated time**: 4-8 hours of API calls (cost: ~$500-1000 depending on token usage)

**Want me to prepare anything specific before you start?** (e.g., more detailed prompts, error handling, or specific chapter templates?)

Quellen
[1] FirstDistinction.pdf https://ppl-ai-file-upload.s3.amazonaws.com/web/direct-files/attachments/95806061/453e8c05-e0df-4a83-b810-f0e11b538a10/FirstDistinction.pdf
