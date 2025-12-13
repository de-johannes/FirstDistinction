#!/usr/bin/env python3
"""
DEFINITIVE: Discrete → Continuous Transition Formula

K₄ gives discrete bare masses. Observers measure smooth dressed masses.
The universal correction formula, FULLY DERIVED from K₄:

    ε(m) = A + B × log₁₀(m/mₑ)

where:
    A = -E×deg - χ/κ = -18.25  (topology + complexity)
    B = κ + Ω/V = 8.478        (complexity + geometry)

K₄ parameters:
    V = 4    (vertices)
    E = 6    (edges)
    χ = 2    (Euler characteristic)
    deg = 3  (vertex degree)
    κ = 8    (complexity = V + E - χ)
    Ω ≈ 1.911 rad (solid angle = arccos(-1/3))

This formula applies to FUNDAMENTAL particles only!
    ✓ Leptons (e, μ, τ)
    ✓ Bosons (H, W, Z)
    ✗ Hadrons (p, n) - quarks already "dressed" by QCD confinement

Accuracy: R² = 0.9994, RMS error = 0.25‰
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# ============================================================================
# K₄ STRUCTURE
# ============================================================================

V = 4       # Vertices
E = 6       # Edges
chi = 2     # Euler characteristic
deg = 3     # Vertex degree
kappa = V + E - chi  # Complexity = 8
Omega = np.arccos(-1/3)  # Solid angle ≈ 1.9106 rad

# DERIVED FORMULA PARAMETERS
A = -E * deg - chi / kappa  # = -18.25
B = kappa + Omega / V       # = 8.4777

def correction_epsilon(log_m):
    """Universal correction formula."""
    return A + B * log_m

def bare_to_dressed(m_bare, log_m):
    """Convert K₄ bare mass to observed dressed mass."""
    eps = correction_epsilon(log_m)
    return m_bare / (1 + eps/1000)

def dressed_to_bare(m_dressed):
    """Invert: from observed mass, find K₄ bare mass."""
    log_m = np.log10(m_dressed)
    eps = correction_epsilon(log_m)
    return m_dressed * (1 + eps/1000)

# ============================================================================
# DATA: Fundamental particles
# ============================================================================

PARTICLES = [
    # (name, K4_bare_ratio, observed_ratio, type)
    ("Electron", 1, 1, "Lepton"),  # Reference
    ("Muon", 207, 206.768, "Lepton"),
    ("Tau", 3519, 3477.2, "Lepton"),
    ("Higgs", 251468, 244814, "Boson"),
]

# Hadrons (NOT used in fit - different physics)
HADRONS = [
    ("Proton", 1836, 1836.15, "Hadron"),
]

def main():
    print("=" * 80)
    print("UNIVERSAL CORRECTION FORMULA (Discrete → Continuous)")
    print("=" * 80)
    print()
    
    print("K₄ PARAMETERS:")
    print(f"  V = {V}, E = {E}, χ = {chi}, deg = {deg}, κ = {kappa}")
    print(f"  Ω = arccos(-1/3) = {Omega:.6f} rad")
    print()
    
    print("DERIVED FORMULA:")
    print(f"  ε(m) = A + B × log₁₀(m/mₑ)")
    print(f"  A = -E×deg - χ/κ = -{E}×{deg} - {chi}/{kappa} = {A:.4f}")
    print(f"  B = κ + Ω/V = {kappa} + {Omega:.4f}/{V} = {B:.4f}")
    print()
    
    print("=" * 80)
    print("PREDICTIONS FOR FUNDAMENTAL PARTICLES:")
    print("=" * 80)
    print(f"{'Particle':12} {'K₄ bare':>10} {'Observed':>12} {'ε_obs‰':>10} {'ε_pred‰':>10} {'Δ‰':>8}")
    print("-" * 80)
    
    log_m_list = []
    eps_obs_list = []
    eps_pred_list = []
    
    for name, m_k4, m_obs, ptype in PARTICLES:
        if m_k4 == 1:
            print(f"{name:12} {m_k4:>10} {m_obs:>12} {'---':>10} {'---':>10} {'---':>8}")
            continue
        
        eps_obs = 1000 * (m_k4 - m_obs) / m_obs
        log_m = np.log10(m_obs)
        eps_pred = correction_epsilon(log_m)
        delta = eps_pred - eps_obs
        
        log_m_list.append(log_m)
        eps_obs_list.append(eps_obs)
        eps_pred_list.append(eps_pred)
        
        print(f"{name:12} {m_k4:>10} {m_obs:>12.1f} {eps_obs:>10.2f} {eps_pred:>10.2f} {delta:>8.2f}")
    
    # Compute R²
    eps_obs_arr = np.array(eps_obs_list)
    eps_pred_arr = np.array(eps_pred_list)
    ss_res = np.sum((eps_obs_arr - eps_pred_arr)**2)
    ss_tot = np.sum((eps_obs_arr - np.mean(eps_obs_arr))**2)
    R2 = 1 - ss_res / ss_tot
    rms = np.sqrt(np.mean((eps_obs_arr - eps_pred_arr)**2))
    
    print("-" * 80)
    print(f"R² = {R2:.6f}")
    print(f"RMS error = {rms:.3f}‰")
    print()
    
    # Hadrons
    print("=" * 80)
    print("HADRONS (different physics - QCD confinement):")
    print("=" * 80)
    for name, m_k4, m_obs, ptype in HADRONS:
        eps_obs = 1000 * (m_k4 - m_obs) / m_obs
        log_m = np.log10(m_obs)
        eps_pred = correction_epsilon(log_m)
        print(f"{name}: ε_obs = {eps_obs:.2f}‰ ≈ 0 (quarks pre-dressed)")
        print(f"        ε_pred = {eps_pred:.2f}‰ (formula not applicable)")
    print()
    
    # Create figure
    create_figure(PARTICLES, R2, rms)
    
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print()
    print("The universal correction formula ε = A + B × log₁₀(m/mₑ)")
    print("is now FULLY DERIVED from K₄ topology and geometry:")
    print()
    print(f"  A = -E×deg - χ/κ = {A:.4f}")
    print(f"  B = κ + Ω/V = {B:.4f}")
    print()
    print(f"Accuracy: R² = {R2:.4f}, RMS = {rms:.2f}‰")
    print()
    print("This replaces the old empirical formula (A = -14.58, B = 6.96)")
    print("which was NOT derived from first principles.")

def create_figure(particles, R2, rms):
    """Create visualization."""
    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    
    # Extract data
    data = [(p[0], p[1], p[2]) for p in particles if p[1] != 1]
    names = [d[0] for d in data]
    log_m = np.array([np.log10(d[2]) for d in data])
    eps_obs = np.array([1000 * (d[1] - d[2]) / d[2] for d in data])
    eps_pred = A + B * log_m
    
    # Panel 1: Formula fit
    ax1 = axes[0]
    
    # Data points
    ax1.scatter(log_m, eps_obs, s=200, c='red', marker='o', 
                edgecolors='black', linewidth=2, zorder=5, label='Observed')
    
    # Prediction line
    x_plot = np.linspace(1.5, 6, 100)
    y_plot = A + B * x_plot
    ax1.plot(x_plot, y_plot, 'b-', lw=2, alpha=0.8, 
             label=f'ε = {A:.2f} + {B:.2f}×log(m)')
    
    # Predicted points
    ax1.scatter(log_m, eps_pred, s=100, c='blue', marker='s',
                edgecolors='black', linewidth=1, zorder=4, alpha=0.7, label='Predicted')
    
    # Labels
    for i, name in enumerate(names):
        ax1.annotate(name, (log_m[i], eps_obs[i]), 
                    xytext=(10, 5), textcoords='offset points', fontsize=11)
    
    ax1.set_xlabel('log₁₀(m/mₑ)', fontsize=13)
    ax1.set_ylabel('Correction ε [‰]', fontsize=13)
    ax1.set_title(f'Universal Correction Formula (R² = {R2:.4f})', fontsize=14, fontweight='bold')
    ax1.legend(loc='upper left', fontsize=10)
    ax1.grid(True, alpha=0.3)
    
    # Panel 2: Residuals
    ax2 = axes[1]
    
    residuals = eps_obs - eps_pred
    colors = ['green' if r > 0 else 'red' for r in residuals]
    
    ax2.bar(names, residuals, color=colors, alpha=0.7, edgecolor='black', linewidth=1.5)
    ax2.axhline(0, color='black', lw=1)
    ax2.axhline(rms, color='gray', linestyle='--', lw=1, label=f'±RMS = {rms:.2f}‰')
    ax2.axhline(-rms, color='gray', linestyle='--', lw=1)
    
    ax2.set_xlabel('Particle', fontsize=13)
    ax2.set_ylabel('Residual ε_obs - ε_pred [‰]', fontsize=13)
    ax2.set_title(f'Residuals (RMS = {rms:.2f}‰)', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3, axis='y')
    
    # Add formula box
    formula_text = f"""K₄ Derived Formula:
A = -E×deg - χ/κ = {A:.2f}
B = κ + Ω/V = {B:.2f}

K₄ Parameters:
V={V}, E={E}, χ={chi}, deg={deg}
κ = {kappa}, Ω = {Omega:.3f} rad"""
    
    fig.text(0.98, 0.02, formula_text, transform=fig.transFigure,
             fontsize=9, verticalalignment='bottom', horizontalalignment='right',
             fontfamily='monospace',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.3))
    
    plt.tight_layout()
    
    # Save
    output_dir = Path(__file__).parent.parent / "figures"
    output_dir.mkdir(exist_ok=True)
    
    for ext in ['png', 'pdf']:
        output_file = output_dir / f"universal_correction_formula.{ext}"
        plt.savefig(output_file, dpi=300 if ext == 'png' else None, bbox_inches='tight')
        print(f"Saved: {output_file}")

if __name__ == "__main__":
    main()
