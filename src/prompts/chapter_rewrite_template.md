# Chapter Rewrite Prompt Template

You are rewriting Chapter {chapter_number}: "{chapter_title}"

## CONTEXT

### Position in Book
- Part: {part_name}
- Previous Chapter: {prev_chapter}
- Next Chapter: {next_chapter}

### Prerequisites (must be understood)
{prerequisites}

### Concepts This Chapter Introduces
{new_concepts}

### Agda Modules Required
{agda_modules}

## ORIGINAL CONTENT

The original chapter content is:

```latex
{original_content}
```

## ORIGINAL AGDA CODE

```agda
{original_agda}
```

## TASK

Rewrite this chapter according to the system prompt guidelines:

1. **Reframe** all language to "K₄ IS reality" perspective
2. **Structure** according to chapter template
3. **Preserve** ALL Agda code exactly
4. **Add** 5-Pillar proof if this is a major result (marked in structure)
5. **Cross-reference** using \ref{{}} to other chapters
6. **Define** all terms before use

## CONSTRAINTS

- The Agda code MUST compile with `--safe --without-K`
- Do NOT simplify or omit any proofs
- Use terminology from the glossary
- Every claim must have formal backing

## OUTPUT FORMAT

Return the complete chapter as a LaTeX document with:
- \chapter{{...}}
- \section{{...}} structure
- \begin{{code}}...\end{{code}} blocks
- All cross-references

## 5-PILLAR REQUIRED: {five_pillar}

{five_pillar_instructions}
