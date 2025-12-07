---
layout: default
title: Verification
---

# Verification

How to check this yourself.

---

## Requirements

- Agda 2.7.0.1 or later
- Git

No external libraries needed. The proof is self-contained.

---

## Installation

### macOS

```bash
brew install agda
```

### Linux (Ubuntu/Debian)

```bash
apt-get install agda
```

### From Source

```bash
cabal update
cabal install Agda
```

---

## Clone and Compile---

## What the Flags Mean

| Flag | Purpose |
|------|---------|
| --safe | Disables postulate, trustMe, unsafe pragmas |
| --without-K | No uniqueness of identity proofs |

These flags enforce constructive mathematics. Nothing is assumed, everything is constructed.

---

## Interpreting the Output

### Success

No output means success.

```bash
agda --safe --without-K FirstDistinction.agda
# (no output)
```

The file compiles. All proofs are valid.

### Failure

Any error means something is wrong:

```
Error in ... at line N
```

If you see this, either:
1. Your Agda version is incompatible
2. The file was modified incorrectly
3. There is a genuine bug (report it)

---

## What Compilation Proves

Agda is a dependently-typed proof assistant. When a file compiles under --safe --without-K:

1. Every type is inhabited only by valid proofs
2. Every function terminates
3. No axioms were assumed (--safe)
4. No K-axiom was used (--without-K)

A compiling Agda file IS a proof certificate.

---

## File Statistics

| Metric | Value |
|--------|-------|
| Total lines | 14,923 |
| Code lines | 8,559 |
| Comment lines | 6,364 |
| Named theorems | 911 |
| Refl proofs | 626 |
| Postulates | 0 |
| Holes | 0 |
| External imports | 0 |

---

## Code Structure

The file is self-contained and derives everything inline:

1. Natural numbers and their arithmetic
2. Integers as signed pairs
3. Positive naturals
4. Rationals as quotients
5. Field axioms for Q
6. Genesis process (D0 through D3)
7. K4 graph structure
8. Eigenvalue calculations
9. Physical predictions

All 17 field axioms for rationals are proven:

| Operation | Axioms |
|-----------|--------|
| Equality | refl, sym, trans |
| Addition | comm, assoc, id-left, id-right, inv-left, inv-right, cong |
| Multiplication | comm, assoc, id-left, id-right, distrib-left, distrib-right, cong |

---

## Quick Checks

Verify Agda version:

```bash
agda --version
```

Expected: Agda version 2.7.0.1 or higher

Check file exists:

```bash
ls -la FirstDistinction.agda
```

Expected: File with approximately 15000 lines

Count theorems:

```bash
grep -c "theorem-\|lemma-" FirstDistinction.agda
```

Expected: Approximately 911

---

## Common Issues

### Wrong Agda Version

```
Unsupported Agda version
```

Solution: Upgrade to 2.7.0.1 or later.

### Missing Standard Library

This proof uses NO standard library. If you see import errors, you have a modified file.

### Timeout

Large proofs may take time. Wait for completion.

---

## For CI/CD

```yaml
# .github/workflows/verify.yml
name: Verify
on: [push]
jobs:
  agda:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: wenkokke/setup-agda@v2
      - run: agda --safe --without-K FirstDistinction.agda
```

---

## Source

Repository: [github.com/de-johannes/FirstDistinction](https://github.com/de-johannes/FirstDistinction)

Main file: [FirstDistinction.agda](https://github.com/de-johannes/FirstDistinction/blob/main/FirstDistinction.agda)

---

[Back](./) | [For Mathematicians](for-mathematicians)
