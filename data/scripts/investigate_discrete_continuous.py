#!/usr/bin/env python3
"""
SYSTEMATIC INVESTIGATION: Discrete → Continuous Transition

K₄ gives discrete integers. Observers measure smooth values.
What is the universal mechanism?

Hypotheses to test:
1. CENTROID: Observer at tetrahedron center sees averaged vertices
2. LATTICE: Discretization error from finite lattice spacing
3. RENORMALIZATION: Running couplings from UV to IR scale
4. GEOMETRIC AVERAGING: Solid angle weighted mean
5. EIGENVALUE SPACING: Gap between λ=0 and λ=4 modes

We fit each hypothesis to data and compare R² values.
"""

import numpy as np
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt
from pathlib import Path

# ============================================================================
# DATA: K₄ predictions vs observations
# ============================================================================

# All masses relative to electron mass
# (K4_bare, observed_dressed, name)
DATA = [
    (207, 206.768, "μ/e"),           # Muon/electron
    (3519, 3477.2, "τ/e"),           # Tau/electron = 207 × 17
    (1836, 1836.15, "p/e"),          # Proton/electron
    (251468, 244814, "H/e"),         # Higgs/electron (128.5 GeV / 0.511 MeV)
]

# Compute corrections in permille
def get_corrections():
    result = []
    for m_bare, m_dressed, name in DATA:
        eps = 1000 * (m_bare - m_dressed) / m_dressed
        log_m = np.log10(m_dressed)
        result.append({
            'name': name,
            'm_bare': m_bare,
            'm_dressed': m_dressed,
            'eps': eps,
            'log_m': log_m,
        })
    return result

# ============================================================================
# K₄ STRUCTURE
# ============================================================================

V = 4  # Vertices
E = 6  # Edges
chi = 2  # Euler characteristic
deg = 3  # Vertex degree
kappa = 8  # κ = V + E - χ
C3 = 4  # Triangles
C4 = 3  # Squares

# Laplacian eigenvalues
lambda_0 = 0
lambda_4 = 4  # 3-fold degenerate

# Geometric properties
Omega = np.arccos(-1/3)  # Solid angle per vertex ≈ 1.911 rad
r_centroid = np.sqrt(3/8)  # Centroid to vertex distance (edge=1)

print("=" * 80)
print("K₄ STRUCTURE:")
print("=" * 80)
print(f"  V = {V}, E = {E}, χ = {chi}, deg = {deg}, κ = {kappa}")
print(f"  Triangles C₃ = {C3}, Squares C₄ = {C4}")
print(f"  Eigenvalues: {{{lambda_0}, {lambda_4}, {lambda_4}, {lambda_4}}}")
print(f"  Solid angle Ω = {Omega:.4f} rad = {np.degrees(Omega):.2f}°")
print(f"  Centroid distance r/a = {r_centroid:.4f}")
print()

# ============================================================================
# HYPOTHESIS 1: CENTROID AVERAGING
# ============================================================================

def hypothesis_centroid(log_m, A, B):
    """
    Observer at centroid sees averaged field values.
    
    ε = A + B × log(m)
    
    From geometry:
    A = -(E×χ + V) = -16 (topological)
    B = E + (χ/π)×Ω ≈ 7.22 (geometric)
    """
    return A + B * log_m

def centroid_geometric_params():
    A = -(E * chi + V)
    B = E + (chi / np.pi) * Omega
    return A, B

# ============================================================================
# HYPOTHESIS 2: LATTICE DISCRETIZATION
# ============================================================================

def hypothesis_lattice(log_m, A, B):
    """
    Lattice discretization error.
    
    In lattice QFT, errors scale as:
    ε ∼ (a/λ)² × log(Λ/m)
    
    For K₄: a ~ Planck length, Λ ~ Planck mass
    → ε = A + B × log(m)
    
    From structure:
    A = -V × E / χ = -12
    B = deg × χ = 6
    """
    return A + B * log_m

def lattice_geometric_params():
    A = -V * E / chi
    B = deg * chi
    return A, B

# ============================================================================
# HYPOTHESIS 3: RENORMALIZATION GROUP
# ============================================================================

def hypothesis_rg(log_m, A, B):
    """
    Running couplings from RG equations.
    
    β(g) = -b₀ g³ + ...
    → g(μ) ~ 1/log(μ/Λ)
    → ε = A + B × log(m)
    
    From K₄:
    A = -κ × χ = -16
    B = E + deg = 9
    """
    return A + B * log_m

def rg_geometric_params():
    A = -kappa * chi
    B = E + deg
    return A, B

# ============================================================================
# HYPOTHESIS 4: SOLID ANGLE AVERAGE
# ============================================================================

def hypothesis_solid_angle(log_m, A, B):
    """
    Averaging over solid angles from centroid.
    
    Each vertex subtends Ω = arccos(-1/3).
    Total coverage = 4Ω ≈ 7.64 rad.
    Normalized: 4Ω / 4π ≈ 0.61.
    
    From K₄:
    A = -V × Ω = -7.64
    B = 4Ω / π = 2.43
    """
    return A + B * log_m

def solid_angle_geometric_params():
    A = -V * Omega
    B = 4 * Omega / np.pi
    return A, B

# ============================================================================
# HYPOTHESIS 5: EIGENVALUE GAP
# ============================================================================

def hypothesis_eigenvalue(log_m, A, B):
    """
    Correction from spectral gap Δλ = 4 - 0 = 4.
    
    Heavy modes (λ=4) decouple logarithmically.
    
    From K₄:
    A = -λ₄ × V = -16
    B = λ₄ + χ = 6
    """
    return A + B * log_m

def eigenvalue_geometric_params():
    A = -lambda_4 * V
    B = lambda_4 + chi
    return A, B

# ============================================================================
# HYPOTHESIS 6: LOOP CORRECTIONS
# ============================================================================

def hypothesis_loops(log_m, A, B):
    """
    Quantum loop corrections from K₄ subgraphs.
    
    1-loop: C₃ triangles = 4
    2-loop: C₄ squares = 3
    
    From K₄:
    A = -(C₃ × C₄ + V) = -16
    B = C₃ + C₄ = 7
    """
    return A + B * log_m

def loops_geometric_params():
    A = -(C3 * C4 + V)
    B = C3 + C4
    return A, B

# ============================================================================
# TESTING
# ============================================================================

def test_hypothesis(name, param_func, corrections):
    """Test a hypothesis against data."""
    A_theory, B_theory = param_func()
    
    log_m = np.array([c['log_m'] for c in corrections])
    eps_obs = np.array([c['eps'] for c in corrections])
    
    # Theoretical predictions
    eps_theory = A_theory + B_theory * log_m
    
    # Error
    residuals = eps_obs - eps_theory
    ss_res = np.sum(residuals**2)
    ss_tot = np.sum((eps_obs - np.mean(eps_obs))**2)
    R2_theory = 1 - ss_res / ss_tot
    
    # Best fit
    try:
        popt, _ = curve_fit(hypothesis_centroid, log_m, eps_obs)
        A_fit, B_fit = popt
        eps_fit = A_fit + B_fit * log_m
        residuals_fit = eps_obs - eps_fit
        ss_res_fit = np.sum(residuals_fit**2)
        R2_fit = 1 - ss_res_fit / ss_tot
    except:
        A_fit, B_fit = np.nan, np.nan
        R2_fit = np.nan
    
    return {
        'name': name,
        'A_theory': A_theory,
        'B_theory': B_theory,
        'A_fit': A_fit,
        'B_fit': B_fit,
        'R2_theory': R2_theory,
        'R2_fit': R2_fit,
        'eps_theory': eps_theory,
        'residuals': residuals,
    }

def main():
    corrections = get_corrections()
    
    print("=" * 80)
    print("OBSERVED DATA:")
    print("=" * 80)
    print(f"{'Name':8} {'m_bare':>10} {'m_dressed':>12} {'ε (‰)':>10} {'log₁₀(m)':>10}")
    print("-" * 80)
    for c in corrections:
        print(f"{c['name']:8} {c['m_bare']:>10.0f} {c['m_dressed']:>12.1f} {c['eps']:>10.2f} {c['log_m']:>10.3f}")
    print()
    
    # Define hypotheses
    hypotheses = [
        ("Centroid", centroid_geometric_params),
        ("Lattice", lattice_geometric_params),
        ("RG", rg_geometric_params),
        ("Solid Angle", solid_angle_geometric_params),
        ("Eigenvalue", eigenvalue_geometric_params),
        ("Loops", loops_geometric_params),
    ]
    
    # Test all
    results = []
    for name, param_func in hypotheses:
        result = test_hypothesis(name, param_func, corrections)
        results.append(result)
    
    # Print results
    print("=" * 80)
    print("HYPOTHESIS COMPARISON:")
    print("=" * 80)
    print(f"{'Hypothesis':15} {'A_theory':>10} {'B_theory':>10} {'R²_theory':>12} {'A_fit':>10} {'B_fit':>10} {'R²_fit':>10}")
    print("-" * 80)
    
    for r in results:
        print(f"{r['name']:15} {r['A_theory']:>10.2f} {r['B_theory']:>10.2f} {r['R2_theory']:>12.4f} {r['A_fit']:>10.2f} {r['B_fit']:>10.2f} {r['R2_fit']:>10.4f}")
    
    # Best hypothesis
    best_theory = max(results, key=lambda x: x['R2_theory'])
    
    print()
    print("=" * 80)
    print(f"BEST HYPOTHESIS: {best_theory['name']}")
    print("=" * 80)
    print(f"  A = {best_theory['A_theory']:.2f}")
    print(f"  B = {best_theory['B_theory']:.2f}")
    print(f"  R² = {best_theory['R2_theory']:.4f}")
    print()
    
    # Best fit comparison
    print(f"BEST FIT (to data):")
    print(f"  A_fit = {results[0]['A_fit']:.2f}")
    print(f"  B_fit = {results[0]['B_fit']:.2f}")
    print(f"  R²_fit = {results[0]['R2_fit']:.4f}")
    print()
    
    # Prediction test
    print("=" * 80)
    print("PREDICTIONS WITH BEST HYPOTHESIS:")
    print("=" * 80)
    A, B = best_theory['A_theory'], best_theory['B_theory']
    print(f"Using: ε = {A:.2f} + {B:.2f} × log₁₀(m)")
    print()
    print(f"{'Name':8} {'ε_obs':>10} {'ε_pred':>10} {'Δε':>10} {'Status':>10}")
    print("-" * 80)
    
    for c in corrections:
        eps_pred = A + B * c['log_m']
        delta = abs(eps_pred - c['eps'])
        status = "✓" if delta < 5 else "~" if delta < 10 else "✗"
        print(f"{c['name']:8} {c['eps']:>10.2f} {eps_pred:>10.2f} {delta:>10.2f} {status:>10}")
    
    # Create visualization
    create_figure(corrections, results)
    
    return results

def create_figure(corrections, results):
    """Create comparison figure."""
    fig, axes = plt.subplots(2, 2, figsize=(14, 10))
    
    log_m = np.array([c['log_m'] for c in corrections])
    eps_obs = np.array([c['eps'] for c in corrections])
    names = [c['name'] for c in corrections]
    
    # Panel 1: Data and fits
    ax1 = axes[0, 0]
    ax1.scatter(log_m, eps_obs, s=150, c='red', marker='o', 
                edgecolors='black', linewidth=2, zorder=5, label='Observed')
    
    # Plot each hypothesis
    x_plot = np.linspace(1.5, 6, 100)
    colors = ['blue', 'green', 'orange', 'purple', 'cyan', 'brown']
    
    for r, color in zip(results[:4], colors):  # Top 4
        y_plot = r['A_theory'] + r['B_theory'] * x_plot
        ax1.plot(x_plot, y_plot, '-', color=color, lw=2, alpha=0.7,
                label=f"{r['name']}: A={r['A_theory']:.1f}, B={r['B_theory']:.1f}")
    
    ax1.set_xlabel('log₁₀(m/mₑ)', fontsize=12)
    ax1.set_ylabel('Correction ε [‰]', fontsize=12)
    ax1.set_title('Hypothesis Comparison', fontsize=13, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=9)
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: R² comparison
    ax2 = axes[0, 1]
    names_h = [r['name'] for r in results]
    r2_values = [r['R2_theory'] for r in results]
    colors = ['green' if r > 0 else 'red' for r in r2_values]
    
    bars = ax2.barh(names_h, r2_values, color=colors, alpha=0.7, 
                     edgecolor='black', linewidth=1.5)
    ax2.axvline(0, color='black', lw=1)
    ax2.set_xlabel('R² (theory vs observed)', fontsize=12)
    ax2.set_title('Hypothesis Quality', fontsize=13, fontweight='bold')
    ax2.grid(True, alpha=0.3, axis='x')
    
    # Panel 3: Residuals for best
    ax3 = axes[1, 0]
    best = max(results, key=lambda x: x['R2_theory'])
    
    ax3.bar(names, best['residuals'], color='steelblue', alpha=0.7,
            edgecolor='black', linewidth=1.5)
    ax3.axhline(0, color='black', lw=1)
    ax3.set_xlabel('Particle', fontsize=12)
    ax3.set_ylabel('Residual ε_obs - ε_pred [‰]', fontsize=12)
    ax3.set_title(f'Residuals: {best["name"]} Hypothesis', fontsize=13, fontweight='bold')
    ax3.grid(True, alpha=0.3, axis='y')
    
    # Panel 4: Summary
    ax4 = axes[1, 1]
    ax4.axis('off')
    
    summary_text = f"""
SYSTEMATIC INVESTIGATION: Discrete → Continuous

K₄ gives: 207, 3519, 1836, 251468 (integers)
Observed: 206.8, 3477, 1836, 244814 (smooth)

Universal formula: ε = A + B × log₁₀(m/mₑ)

BEST HYPOTHESIS: {best['name']}
  A = {best['A_theory']:.2f} (from K₄ structure)
  B = {best['B_theory']:.2f} (from K₄ structure)
  R² = {best['R2_theory']:.4f}

BEST FIT (empirical):
  A = {results[0]['A_fit']:.2f}
  B = {results[0]['B_fit']:.2f}
  R² = {results[0]['R2_fit']:.4f}

Difference:
  ΔA = {abs(best['A_theory'] - results[0]['A_fit']):.2f}
  ΔB = {abs(best['B_theory'] - results[0]['B_fit']):.2f}
"""
    
    ax4.text(0.05, 0.95, summary_text, transform=ax4.transAxes,
             fontsize=10, verticalalignment='top', fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))
    
    plt.tight_layout()
    
    # Save
    output_dir = Path(__file__).parent.parent / "figures"
    output_dir.mkdir(exist_ok=True)
    
    for ext in ['png', 'pdf']:
        output_file = output_dir / f"discrete_continuous_investigation.{ext}"
        plt.savefig(output_file, dpi=300 if ext == 'png' else None, bbox_inches='tight')
        print(f"Saved: {output_file}")

if __name__ == "__main__":
    main()
