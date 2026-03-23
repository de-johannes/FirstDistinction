"""
FirstDistinction 2.0 - Master Orchestrator
Rewrites entire book with K₄-as-Reality framing
"""

import json
import os
import yaml
import re
import subprocess
import time
from pathlib import Path
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
import anthropic

# ═══════════════════════════════════════════════════════════════════
# DATA STRUCTURES
# ═══════════════════════════════════════════════════════════════════

@dataclass
class Chapter:
    number: int
    title: str
    content: str
    agda_code: str
    line_start: int
    line_end: int

@dataclass
class NewChapterSpec:
    number: int
    title: str
    part: str
    agda_modules: List[str]
    five_pillar: bool = False
    prerequisites: List[int] = field(default_factory=list)

# ═══════════════════════════════════════════════════════════════════
# MAIN ORCHESTRATOR
# ═══════════════════════════════════════════════════════════════════

class BookRewriteOrchestrator:
    def __init__(self, config_path: str = "config/config.yaml"):
        self.base_path = Path(__file__).parent
        self.config = self.load_config(config_path)
        self.client = anthropic.Anthropic(api_key=self.config['claude_api_key'])
        
        # Load prompts and rules
        self.system_prompt = self.load_file('prompts/system_prompt.md')
        self.chapter_template = self.load_file('prompts/chapter_rewrite_template.md')
        self.framing_rules = self.load_file('config/framing_rules.md')
        self.terminology = self.load_yaml('config/terminology.yaml')
        self.new_structure = self.load_yaml('config/chapter_structure.yaml')
        
        # State
        self.old_chapters: List[Chapter] = []
        self.glossary: Dict = {}
        self.concept_graph: Dict = {}
        self.progress: Dict = {}
        
        # Output paths
        self.output_path = self.base_path / "output"
        self.chapters_path = self.output_path / "chapters"
        self.agda_path = self.output_path / "agda"
        self.logs_path = self.output_path / "logs"
        
        # Create output directories
        for p in [self.output_path, self.chapters_path, self.agda_path, self.logs_path]:
            p.mkdir(parents=True, exist_ok=True)
    
    def load_config(self, path: str) -> Dict:
        with open(self.base_path / path) as f:
            config = yaml.safe_load(f)

        api_key = config.get('claude_api_key')
        if api_key == "${ANTHROPIC_API_KEY}":
            config['claude_api_key'] = os.environ.get('ANTHROPIC_API_KEY', '')

        return config
    
    def load_file(self, path: str) -> str:
        with open(self.base_path / path) as f:
            return f.read()
    
    def load_yaml(self, path: str) -> Dict:
        with open(self.base_path / path) as f:
            return yaml.safe_load(f)
    
    def load_progress(self):
        progress_file = self.output_path / "progress.json"
        if progress_file.exists():
            with open(progress_file) as f:
                self.progress = json.load(f)
        else:
            self.progress = {"completed_chapters": [], "current_phase": "init"}
    
    def save_progress(self):
        with open(self.output_path / "progress.json", 'w') as f:
            json.dump(self.progress, f, indent=2)
    
    # ═══════════════════════════════════════════════════════════════
    # PHASE 1: ANALYZE OLD BOOK
    # ═══════════════════════════════════════════════════════════════
    
    def phase1_analyze(self):
        """Extract all content from FirstDistinction v1"""
        print("=" * 70)
        print("PHASE 1: Analyzing old book...")
        print("=" * 70)
        
        old_book_path = self.base_path / self.config['paths']['old_book']
        print(f"Reading {old_book_path}...")
        
        with open(old_book_path, encoding='utf-8') as f:
            content = f.read()
        
        # 1.1: Extract chapters
        self.old_chapters = self.extract_chapters(content)
        print(f"  ✓ Found {len(self.old_chapters)} chapters")
        
        # Save chapter inventory
        inventory = [
            {
                "number": ch.number,
                "title": ch.title,
                "lines": f"{ch.line_start}-{ch.line_end}",
                "content_length": len(ch.content),
                "agda_length": len(ch.agda_code)
            }
            for ch in self.old_chapters
        ]
        with open(self.output_path / "chapter_inventory.json", 'w') as f:
            json.dump(inventory, f, indent=2)
        
        # 1.2: Build concept graph
        self.concept_graph = self.build_concept_graph()
        with open(self.output_path / "concept_graph.json", 'w') as f:
            json.dump(self.concept_graph, f, indent=2)
        print(f"  ✓ Built concept graph")
        
        # 1.3: Generate glossary from terminology
        self.glossary = self.generate_glossary()
        with open(self.output_path / "glossary.json", 'w') as f:
            json.dump(self.glossary, f, indent=2)
        print(f"  ✓ Generated glossary with {len(self.glossary)} entries")
        
        self.progress["current_phase"] = "analyzed"
        self.save_progress()
        print("\nPhase 1 complete!\n")
    
    def extract_chapters(self, content: str) -> List[Chapter]:
        """Parse LaTeX and extract chapter structure"""
        lines = content.split('\n')
        chapters = []
        
        # Find all chapter positions
        chapter_pattern = re.compile(r'^\\chapter\{(.+?)\}')
        chapter_positions = []
        
        for i, line in enumerate(lines):
            match = chapter_pattern.match(line)
            if match:
                chapter_positions.append((i, match.group(1)))
        
        # Extract each chapter
        for idx, (line_num, title) in enumerate(chapter_positions):
            # Determine end line
            if idx + 1 < len(chapter_positions):
                end_line = chapter_positions[idx + 1][0] - 1
            else:
                end_line = len(lines) - 1
            
            # Extract content
            chapter_content = '\n'.join(lines[line_num:end_line + 1])
            
            # Extract Agda code
            agda_blocks = re.findall(
                r'\\begin\{code\}(.*?)\\end\{code\}',
                chapter_content,
                re.DOTALL
            )
            agda_code = '\n\n'.join(agda_blocks)
            
            chapters.append(Chapter(
                number=idx + 1,
                title=title,
                content=chapter_content,
                agda_code=agda_code,
                line_start=line_num + 1,
                line_end=end_line + 1
            ))
        
        return chapters
    
    def build_concept_graph(self) -> Dict:
        """Build dependency graph between chapters based on new structure"""
        graph = {}
        
        # From new structure, build dependencies
        chapter_num = 0
        for part_key, part_data in self.new_structure.get('parts', {}).items():
            # Skip non-dict entries (like appendices list)
            if not isinstance(part_data, dict):
                continue
            for ch in part_data.get('chapters', []):
                chapter_num += 1
                graph[f"chapter_{chapter_num}"] = {
                    "title": ch['title'],
                    "part": part_data['title'],
                    "agda_modules": ch.get('agda_modules', []),
                    "five_pillar": ch.get('five_pillar', False),
                    "needs": list(range(1, chapter_num))  # Simplified: needs all previous
                }
        
        return graph
    
    def generate_glossary(self) -> Dict:
        """Generate glossary from terminology.yaml"""
        glossary = {}
        
        for category, terms in self.terminology.items():
            if isinstance(terms, dict):
                for term_key, term_data in terms.items():
                    if isinstance(term_data, dict) and 'definition' in term_data:
                        glossary[term_data.get('term', term_key)] = {
                            "definition": term_data['definition'],
                            "agda": term_data.get('agda', ''),
                            "latex": term_data.get('latex', ''),
                            "never_use": term_data.get('never_use', [])
                        }
        
        return glossary
    
    # ═══════════════════════════════════════════════════════════════
    # PHASE 2: MAPPING OLD TO NEW
    # ═══════════════════════════════════════════════════════════════
    
    def phase2_mapping(self):
        """Create mapping from old chapters to new structure"""
        print("=" * 70)
        print("PHASE 2: Creating chapter mapping...")
        print("=" * 70)
        
        # Build mapping using Claude
        mapping = self.create_chapter_mapping()
        
        with open(self.output_path / "chapter_mapping.json", 'w') as f:
            json.dump(mapping, f, indent=2)
        
        print(f"  ✓ Created mapping for {len(mapping)} new chapters")
        
        self.progress["current_phase"] = "mapped"
        self.save_progress()
        print("\nPhase 2 complete!\n")
    
    def create_chapter_mapping(self) -> Dict:
        """Map old chapters to new structure"""
        # Load chapter inventory
        with open(self.output_path / "chapter_inventory.json") as f:
            old_inventory = json.load(f)
        
        old_titles = [ch['title'] for ch in old_inventory]
        
        # Create mapping based on new structure
        mapping = {}
        new_chapter_num = 0
        
        for part_key, part_data in self.new_structure.get('parts', {}).items():
            # Skip non-dict entries (like appendices list)
            if not isinstance(part_data, dict):
                continue
            for new_ch in part_data.get('chapters', []):
                new_chapter_num += 1
                
                # Find matching old chapters by title similarity
                matching_old = []
                for i, old_title in enumerate(old_titles):
                    # Simple matching - could use Claude for better matching
                    if any(word.lower() in old_title.lower() 
                           for word in new_ch['title'].split()):
                        matching_old.append(i + 1)
                
                mapping[f"new_chapter_{new_chapter_num}"] = {
                    "title": new_ch['title'],
                    "part": part_data['title'],
                    "source_chapters": matching_old,
                    "agda_modules": new_ch.get('agda_modules', []),
                    "five_pillar": new_ch.get('five_pillar', False)
                }
        
        return mapping
    
    # ═══════════════════════════════════════════════════════════════
    # PHASE 3: REWRITE CHAPTERS
    # ═══════════════════════════════════════════════════════════════
    
    def phase3_rewrite(self):
        """Rewrite all chapters according to new structure"""
        print("=" * 70)
        print("PHASE 3: Rewriting chapters...")
        print("=" * 70)
        
        # Load mapping
        with open(self.output_path / "chapter_mapping.json") as f:
            mapping = json.load(f)
        
        completed = self.progress.get("completed_chapters", [])
        
        for ch_key, ch_spec in mapping.items():
            ch_num = int(ch_key.split('_')[-1])
            
            if ch_num in completed:
                print(f"[{ch_num}] {ch_spec['title']} - already done, skipping")
                continue
            
            print(f"\n[{ch_num}/{len(mapping)}] Rewriting: {ch_spec['title']}")
            
            success = self.rewrite_single_chapter(ch_num, ch_spec)
            
            if success:
                completed.append(ch_num)
                self.progress["completed_chapters"] = completed
                self.save_progress()
                print(f"  ✓ Chapter {ch_num} complete")
            else:
                print(f"  ✗ Chapter {ch_num} FAILED - stopping")
                break
        
        self.progress["current_phase"] = "rewritten"
        self.save_progress()
        print("\nPhase 3 complete!\n")
    
    def rewrite_single_chapter(self, ch_num: int, spec: Dict) -> bool:
        """Rewrite a single chapter"""
        
        # Gather source content from old chapters
        source_content = ""
        source_agda = ""
        
        for old_num in spec.get('source_chapters', []):
            if old_num <= len(self.old_chapters):
                old_ch = self.old_chapters[old_num - 1]
                source_content += f"\n\n% === From old Chapter {old_num}: {old_ch.title} ===\n"
                source_content += old_ch.content
                source_agda += old_ch.agda_code + "\n"
        
        # If no source, use placeholder
        if not source_content:
            source_content = f"% New chapter: {spec['title']}\n% Content to be developed"
            source_agda = "-- No source Agda code"
        
        # Prepare prompt
        five_pillar_instructions = ""
        if spec.get('five_pillar', False):
            five_pillar_instructions = """
This is a MAJOR RESULT requiring full 5-Pillar proof:

1. FORCED: Prove this result is logically necessary
2. CONSISTENCY: Show alignment with other K₄ results  
3. EXCLUSIVITY: Prove no other value works
4. ROBUSTNESS: Demonstrate stability
5. CROSS-CONSTRAINTS: Cite independent physics validation
"""
        
        prompt = self.chapter_template.format(
            chapter_number=ch_num,
            chapter_title=spec['title'],
            part_name=spec['part'],
            prev_chapter=f"Chapter {ch_num - 1}" if ch_num > 1 else "None",
            next_chapter=f"Chapter {ch_num + 1}",
            prerequisites=f"Chapters 1-{ch_num - 1}" if ch_num > 1 else "None",
            new_concepts=", ".join(spec.get('agda_modules', [])),
            agda_modules=", ".join(spec.get('agda_modules', [])),
            original_content=source_content[:20000],  # Truncate if too long
            original_agda=source_agda[:10000],
            five_pillar=spec.get('five_pillar', False),
            five_pillar_instructions=five_pillar_instructions
        )
        
        # Call Claude
        try:
            rewritten = self.call_claude(prompt)
        except Exception as e:
            print(f"  Error calling Claude: {e}")
            return False
        
        # Extract Agda code
        agda_code = self.extract_agda(rewritten)
        
        # Verify Agda compiles
        # Skip per-chapter Agda verification - individual chapters can't compile
        # without the full module context. Verification happens in Phase 4.
        # if agda_code.strip():
        #     if not self.verify_agda(agda_code, ch_num):
        #         print(f"  ✗ Agda verification FAILED")
        #         (self.logs_path / f"chapter_{ch_num}_failed.tex").write_text(rewritten)
        #         (self.logs_path / f"chapter_{ch_num}_failed.agda").write_text(agda_code)
        #         return False
        
        # Save outputs
        (self.chapters_path / f"chapter_{ch_num:02d}.tex").write_text(rewritten)
        if agda_code.strip():
            (self.agda_path / f"Chapter{ch_num:02d}.agda").write_text(agda_code)
        
        return True
    
    def call_claude(self, user_prompt: str) -> str:
        """Call Claude API with streaming"""
        full_system = f"{self.system_prompt}\n\n## FRAMING RULES\n\n{self.framing_rules}"
        
        result = ""
        with self.client.messages.stream(
            model=self.config['model'],
            max_tokens=self.config['max_tokens_per_chapter'],
            system=full_system,
            messages=[{"role": "user", "content": user_prompt}]
        ) as stream:
            for text in stream.text_stream:
                result += text
        
        return result
    
    def extract_agda(self, latex: str) -> str:
        """Extract Agda code from LaTeX"""
        blocks = re.findall(
            r'\\begin\{code\}(.*?)\\end\{code\}',
            latex,
            re.DOTALL
        )
        return '\n\n'.join(blocks)
    
    def verify_agda(self, agda_code: str, ch_num: int) -> bool:
        """Verify Agda code compiles"""
        # Create temp file - use TempChapterN format (no leading numbers)
        temp_file = self.agda_path / f"TempChapter{ch_num}.agda"
        
        # Add module header
        full_code = f"""{{-# OPTIONS --safe --without-K #-}}

module TempChapter{ch_num} where

-- Imports from main module would go here
open import Agda.Primitive

{agda_code}
"""
        temp_file.write_text(full_code)
        
        # Run Agda
        result = subprocess.run(
            ['agda', '--safe', '--without-K', str(temp_file)],
            capture_output=True,
            text=True,
            timeout=120
        )
        
        # Save log
        log_file = self.logs_path / f"chapter_{ch_num}_agda.log"
        log_file.write_text(f"STDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}")
        
        # Cleanup
        temp_file.unlink(missing_ok=True)
        
        return result.returncode == 0
    
    # ═══════════════════════════════════════════════════════════════
    # PHASE 4: COMPILE BOOK
    # ═══════════════════════════════════════════════════════════════
    
    def phase4_compile(self):
        """Assemble all chapters into final book"""
        print("=" * 70)
        print("PHASE 4: Compiling book...")
        print("=" * 70)
        
        # Generate master document
        master_latex = self.generate_master_latex()
        
        master_file = self.output_path / "FirstDistinction-v2.lagda.tex"
        master_file.write_text(master_latex)
        
        print(f"  ✓ Generated {master_file}")
        
        # Run Agda
        print("  Running Agda...")
        result = subprocess.run(
            ['agda', '--latex', str(master_file)],
            capture_output=True,
            text=True,
            cwd=self.output_path
        )
        
        if result.returncode != 0:
            print(f"  ✗ Agda failed: {result.stderr[:500]}")
            return False
        
        print("  ✓ Agda compilation successful")
        
        # Run XeLaTeX
        print("  Running XeLaTeX...")
        latex_dir = self.output_path / "latex"
        latex_dir.mkdir(exist_ok=True)
        
        # Would run xelatex here...
        
        self.progress["current_phase"] = "compiled"
        self.save_progress()
        print("\nPhase 4 complete!\n")
        return True
    
    def generate_master_latex(self) -> str:
        """Generate master LaTeX document"""
        # Read preamble from original
        with open(self.base_path / self.config['paths']['old_book']) as f:
            original = f.read()
        
        # Extract preamble (before first \chapter)
        preamble_match = re.search(r'^(.*?)\\chapter\{', original, re.DOTALL)
        preamble = preamble_match.group(1) if preamble_match else ""
        
        # Update module name
        preamble = re.sub(
            r'module FirstDistinction where',
            'module FirstDistinction-v2 where',
            preamble
        )
        
        # Build document
        latex = preamble
        
        # Add chapters by part
        for part_key, part_data in self.new_structure.get('parts', {}).items():
            # Skip non-dict entries (like appendices list)
            if not isinstance(part_data, dict):
                continue
            latex += f"\n\\part{{{part_data['title']}}}\n\n"
            
            for ch in part_data.get('chapters', []):
                ch_num = ch['number']
                ch_file = self.chapters_path / f"chapter_{ch_num:02d}.tex"
                
                if ch_file.exists():
                    latex += ch_file.read_text()
                else:
                    latex += f"\\chapter{{{ch['title']}}}\n\n[Content pending]\n\n"
        
        latex += "\n\\end{document}\n"
        
        return latex
    
    # ═══════════════════════════════════════════════════════════════
    # MAIN EXECUTION
    # ═══════════════════════════════════════════════════════════════
    
    def run(self, start_phase: int = 1):
        """Execute full rewrite pipeline"""
        print("\n" + "=" * 70)
        print("FIRSTDISTINCTION 2.0 - MASTER ORCHESTRATOR")
        print("=" * 70 + "\n")
        
        self.load_progress()
        
        if start_phase <= 1:
            self.phase1_analyze()
        
        if start_phase <= 2:
            self.phase2_mapping()
        
        if start_phase <= 3:
            self.phase3_rewrite()
        
        if start_phase <= 4:
            self.phase4_compile()
        
        print("\n" + "=" * 70)
        print("PIPELINE COMPLETE")
        print("=" * 70)


# ═══════════════════════════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description='FirstDistinction 2.0 Rewrite')
    parser.add_argument('--start-phase', type=int, default=1,
                       help='Start from phase (1=analyze, 2=map, 3=rewrite, 4=compile)')
    parser.add_argument('--config', default='config/config.yaml',
                       help='Path to config file')
    
    args = parser.parse_args()
    
    orchestrator = BookRewriteOrchestrator(args.config)
    orchestrator.run(start_phase=args.start_phase)
