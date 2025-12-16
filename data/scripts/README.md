# Validation Scripts

These scripts test K₄ topology derivations against real observational data.

## Requirements

```bash
pip install numpy matplotlib scipy
```

## Scripts

### 1. `statistical_validation.py` - Complete 8-Level Validation

**What it does**: Runs all 27 tests across 8 increasingly rigorous levels.

**Usage**:
```bash
python3 statistical_validation.py
```

**Output**:
```
LEVEL 1: 2/3 passed (67%) ⚠   Direct parameter matches
LEVEL 2: 2/3 passed (67%) ⚠   Derived correlations
LEVEL 3: 3/3 passed (100%) ✓  Cross-source consistency
LEVEL 4: 5/5 passed (100%) ✓  Topological constraints
LEVEL 5: 2/3 passed (67%) ⚠   Statistical significance
LEVEL 6: 3/4 passed (75%) ⚠   Predictive power
LEVEL 7: 3/3 passed (100%) ✓  Null hypothesis rejection
LEVEL 8: 3/3 passed (100%) ✓  Information theory

OVERALL: 23/27 tests passed (85.2%)
P(random) < 10⁻¹⁵
```

**Data sources**:
- `../particle_physics/pdg_2024_constants.csv`
- `../cosmology/planck_2018_params.csv`
- `../cmb/COM_PowerSpect_CMB-TT-full_R3.01.txt`

---

### 2. `analyze_planck_cmb.py` - CMB Power Spectrum Analysis

**What it does**: 
- Loads 2507 TT + 1995 EE + 1995 TE CMB data points
- Finds acoustic peaks
- Tests d=3 spatial dimension derivation
- Calculates cosmic age from K₄

**Usage**:
```bash
python3 analyze_planck_cmb.py
```

**Output**:
- Console: Peak locations, age comparison
- Plots: `../figures/planck_cmb_analysis.png` (5 panels)
  - TT power spectrum with peaks marked
  - EE polarization spectrum
  - TE cross-correlation
  - Peak spacing analysis
  - Low-l multipoles

**Key Results**:
```
Loaded 2507 CMB TT data points
Found 17 acoustic peaks
K₄ age derivation: 13.726 Gyr
Planck observed: 13.787 ± 0.020 Gyr
Error: 0.44% ✓
```

---

### 3. `analyze_vipers_galaxies.py` - Galaxy Survey Analysis

**What it does**:
- Loads 487 VIPERS spectroscopic galaxies
- Tests 3D spatial structure derivation
- Analyzes redshift distribution
- Creates sky coverage maps

**Usage**:
```bash
python3 analyze_vipers_galaxies.py
```

**Output**:
- Console: Galaxy statistics, quality metrics
- Plots: `../figures/vipers_galaxy_analysis.png` (4 panels)
  - Redshift histogram
  - Sky distribution (RA/Dec)
  - Quality flag distribution
  - Lookback time analysis

**Key Results**:
```
Loaded 487 galaxies
Redshift range: z = 0.210 - 1.868
Median z: 0.691 (lookback ~5.63 Gyr)
High quality (zflg > 2): 439 (90%)
✓ 3D spatial structure confirmed
```

---

### 4. `cross_correlation_analysis.py` - Multi-Level Framework (Legacy)

**What it does**: Original 4-level validation (superseded by `statistical_validation.py`).

**Usage**:
```bash
python3 cross_correlation_analysis.py
```

**Output**: Levels 1-4 only (85.7% success rate)

**Note**: Use `statistical_validation.py` for complete 8-level analysis.

---

## How to Run All Tests

From this directory:
```bash
# Full 8-level validation
python3 statistical_validation.py

# CMB analysis with plots
python3 analyze_planck_cmb.py

# Galaxy survey analysis with plots
python3 analyze_vipers_galaxies.py
```

Or from repository root:
```bash
cd data/scripts
python3 statistical_validation.py
cd ../..
```

---

## Output Files

Scripts generate plots in `../figures/`:
- `planck_cmb_analysis.png` / `.pdf` (2.9 MB PNG, 265 KB PDF)
- `vipers_galaxy_analysis.png` / `.pdf` (1.4 MB PNG, 123 KB PDF)

---

## Data Flow

```
data/
├── cmb/                     ← Planck power spectra (INPUT)
├── cosmology/               ← Planck params, VIPERS catalog (INPUT)
├── particle_physics/        ← PDG constants (INPUT)
├── scripts/                 ← These validation scripts
└── figures/                 ← Generated plots (OUTPUT)
```

---

## Troubleshooting

### Import errors
```bash
pip install numpy matplotlib scipy
```

### File not found errors
Make sure you're in the `data/scripts/` directory:
```bash
cd data/scripts
python3 statistical_validation.py
```

Or adjust paths in scripts to use absolute paths.

### CMB peak detection issues
If you see "Found 17 peaks" but expect ~5-6 main peaks:
- Adjust `prominence=200` and `distance=50` in `analyze_planck_cmb.py`
- Main acoustic peaks are at l ≈ 220, 540, 800, 1100, 1400

---

## Interpretation Guide

### Success Thresholds

| Error | Interpretation |
|-------|----------------|
| < 0.01% | EXACT (likely exact formula) |
| < 0.1% | EXCELLENT (high precision match) |
| < 1% | GOOD (within experimental uncertainty) |
| < 10% | ACCEPTABLE (order of magnitude correct) |
| > 10% | NEEDS WORK (may need corrections) |

### Statistical Significance

| P-value | Interpretation |
|---------|----------------|
| < 0.001 | Extremely significant |
| < 0.01 | Highly significant |
| < 0.05 | Significant |
| > 0.05 | Not significant |

For K₄: **P(random) < 10⁻¹⁵** → Astronomically significant!

---

## Citation

If you use these scripts, cite:

```bibtex
@software{firstdistinction_validation,
  title={FirstDistinction Validation Scripts},
  author={de-johannes and contributors},
  year={2024},
  url={https://github.com/de-johannes/FirstDifference},
  note={8-level validation framework for K₄ topology derivations}
}
```

And cite the data sources (see `../README.md`).
