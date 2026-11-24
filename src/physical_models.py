"""
Authentic Physical Quantum Continuum-Edge Models (Exact Analytic + Finite-Lattice ED Cross-Checks):
  1. 1D One-Center Point Interaction (Karapetyan et al. arXiv:2611.06454 benchmark):
       H = -d^2/dx^2 - 2*kappa*delta(x)
     Exact ground state E_0 = -kappa^2, continuum [0, inf), Delta = kappa^2.
     - Even-parity local overlap -> w_even(x) = sqrt(x) / (x + kappa^2), alpha = 3/2, c2 = +1/kappa^4.
     - Odd-parity / p-wave-free / resonant overlap -> w_odd(x) = 1 / (sqrt(x) * (x + kappa^2)), alpha = 1/2, c2 = +1/kappa^4.
  2. 3D One-Center Point Interaction (zero-range bound state, Delta = kappa^2):
       w_3D(x) = sqrt(x) / (x + kappa^2)^2, alpha = 3/2, c2 = +2/kappa^4.
  3. 1D Lattice Tight-Binding Impurity Model (exact L=400 tridiagonal ED + thermodynamic van Hove band):
       H = -t * sum (|j><j+1| + h.c.) - V_0 |0><0|
     Exact bound state E_0 = -sqrt(V_0^2 + 4 t^2), continuum [-2t, 2t], Delta = sqrt(V_0^2 + 4 t^2) - 2t.
     Plus pure 1D van Hove band density w(x) = 1 / sqrt(x * (4 - x)) on [0, 4] (alpha = 1/2, x V'(x) decreasing!).
  4. 2D Step Continuum on [0, 4]: w(x) = 1 - x/4 (alpha = 1, log-concave, c2 = -1/16 < 0).
  5. Discrete Isolated Excited State & Stretched-Exponential Pseudogap (Theorem 3.1 Trichotomy).
"""
import math
import numpy as np
from scipy.linalg import eigh_tridiagonal


def point_1d_even_density(kappa: float = 1.0):
    """Exact 1D delta-potential even-parity scattering density w(x) = sqrt(x)/(x + kappa^2), alpha=3/2."""
    k2 = kappa * kappa
    return (lambda x: math.sqrt(x) / (x + k2)), k2, 1.5, 1.0 / (k2 * k2)


def point_1d_odd_density(kappa: float = 1.0):
    """1D delta-potential threshold density w(x) = 1/(sqrt(x)*(x + kappa^2)), alpha=1/2."""
    k2 = kappa * kappa
    return (lambda x: 1.0 / (math.sqrt(x) * (x + k2))), k2, 0.5, 1.0 / (k2 * k2)


def point_3d_density(kappa: float = 1.0):
    """3D short-range/point-interaction threshold density w(x) = sqrt(x)/(x + kappa^2)^2, alpha=3/2."""
    k2 = kappa * kappa
    return (lambda x: math.sqrt(x) / ((x + k2) ** 2)), k2, 1.5, 2.0 / (k2 * k2)


def tb_1d_vanhove_density(Delta: float = 0.5, bandwidth: float = 4.0):
    """1D tight-binding van Hove band edge w(x) = 1/sqrt(x*(B - x)) on (0, B), alpha=1/2, c2=+1/(2 B^2)."""
    B = bandwidth
    return (lambda x: 1.0 / math.sqrt(x * (B - x)) if 0.0 < x < B else 0.0), Delta, 0.5, 1.0 / (2.0 * B * B)


def step_2d_density(Delta: float = 0.5, bandwidth: float = 4.0):
    """2D compact linear-step band edge w(x) = 1 - x/B on [0, B], alpha=1.0, c2=-1/B^2 < 0 (log-concave)."""
    B = bandwidth
    return (lambda x: max(0.0, 1.0 - x / B)), Delta, 1.0, -1.0 / (B * B)


def pseudogap_density(Delta: float = 0.5, c_pg: float = 2.0, gamma: float = 0.5):
    """Stretched-exponential pseudogap w(x) = exp(-c * x^{-gamma}) * exp(-0.2*x), alpha_VF ~ tau^{gamma/(gamma+1)}."""
    return (lambda x: math.exp(-c_pg * (x ** (-gamma)) - 0.2 * x) if x > 1e-12 else 0.0), Delta


def lattice_1d_impurity_ed(L: int = 401, t_hop: float = 1.0, V0: float = 1.5):
    """
    Exact diagonalization of 1D tight-binding chain with a single attractive impurity at center site c = L//2:
      H = -t * sum_{j=0}^{L-2} (|j><j+1| + h.c.) - V0 |c><c|.
    Returns exact bound-state energy E0, exact continuum edge E_th = -2t, exact gap Delta_exact,
    and excited-state spectral weights |(psi_init, phi_n)|^2 for an initial state localized at site c+1
    (giving exact alpha = 3/2 threshold density at the band edge!).
    """
    diag = np.zeros(L, dtype=np.float64)
    center = L // 2
    diag[center] = -V0
    off = np.full(L - 1, -t_hop, dtype=np.float64)
    evals, evecs = eigh_tridiagonal(diag, off)
    E0 = float(evals[0])
    # Exact thermodynamic bound state energy: -sqrt(V0^2 + 4 t^2), continuum edge: -2t
    E0_thermo = -math.sqrt(V0 * V0 + 4.0 * t_hop * t_hop)
    Delta_thermo = (-2.0 * t_hop) - E0_thermo
    # Initial state localized at site center + 1 -> weights |evecs[center + 1, n]|^2
    w_all = evecs[center + 1, :] ** 2
    # Excited spectrum: n >= 1 (subtracting ground state E0)
    exc_energies = evals[1:] - E0
    exc_weights = w_all[1:]
    exc_weights = exc_weights / np.sum(exc_weights)
    return {
        "L": L,
        "E0_ed": E0,
        "E0_thermo": E0_thermo,
        "Delta_thermo": Delta_thermo,
        "exc_energies": exc_energies,
        "exc_weights": exc_weights,
    }
