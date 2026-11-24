"""
Shift-Invariant Cumulant Estimators for Continuum Spectral Edges and Threshold Exponents
from Imaginary-Time Evolution.

Implements:
  - Exact continuous-time cumulants g(tau) = -(log F)', kappa_2(tau) = (log F)'', kappa_3(tau) = -(log F)'''
    computed directly from exact moment integrals m_r(tau) = int x^r e^{-tau x} w(x) dx.
  - Raw Karapetyan et al. (arXiv:2611.06454) estimator g(tau).
  - Variance-Free (VF) estimator: Delta_VF = g(tau) - tau * kappa_2(tau), alpha_VF = tau^2 * kappa_2(tau).
  - Shift-Invariant (SI) estimators:
      Delta_SI = g(tau) - 2 * kappa_2(tau)^2 / kappa_3(tau)   [O(tau^-3) bias, exact on Gamma-Exp!]
      alpha_SI = 4 * kappa_2(tau)^3 / kappa_3(tau)^2          [O(tau^-2) bias, exact on Gamma-Exp!]
  - Discrete grid central finite-difference estimators on uniform imaginary-time grids tau_j = tau_0 + j*h
    for noisy finite-sample quantum imaginary-time measurements.
"""
import math
import numpy as np
from scipy.integrate import quad


def cumulants_from_density(w_fn, Delta: float, tau: float, xmax: float = np.inf) -> dict:
    """
    Compute exact excited-measure cumulants at imaginary time tau for spectral density
    w(x) supported on [0, xmax] (so total energy is E - E_0 = Delta + x).
    """
    ms = []
    umax = np.inf if math.isinf(xmax) else tau * xmax
    for r in range(4):
        val, _ = quad(
            lambda u, r=r: ((u / tau) ** r) * math.exp(-u) * w_fn(u / tau) / tau,
            0.0, umax, limit=250, epsabs=0.0, epsrel=1e-13
        )
        ms.append(val)
    m0, m1, m2, m3 = ms
    mu1 = m1 / m0
    mu2 = m2 / m0
    mu3 = m3 / m0
    k2 = mu2 - mu1 * mu1
    k3 = mu3 - 3.0 * mu1 * mu2 + 2.0 * (mu1 ** 3)
    g = Delta + mu1
    delta_vf = g - tau * k2
    alpha_vf = (tau * tau) * k2
    if k3 > 1e-30:
        delta_si = g - 2.0 * (k2 * k2) / k3
        alpha_si = 4.0 * (k2 ** 3) / (k3 * k3)
    else:
        delta_si = delta_vf
        alpha_si = 0.0
    return {
        "tau": tau,
        "F_shifted": m0,
        "g_raw": g,
        "k2": k2,
        "k3": k3,
        "Delta_VF": delta_vf,
        "Delta_SI": delta_si,
        "alpha_VF": alpha_vf,
        "alpha_SI": alpha_si,
    }


def cumulants_from_discrete_spectrum(energies: np.ndarray, weights: np.ndarray, tau: float) -> dict:
    """
    Exact cumulants for a discrete (e.g., finite-lattice ED) excited spectral measure
    sum_r weights[r] * delta(energies[r]) with energies >= Delta.
    Uses log-sum-exp stabilization for zero overflow/underflow.
    """
    e = np.asarray(energies, dtype=np.float64)
    w = np.asarray(weights, dtype=np.float64)
    e_min = float(np.min(e))
    dx = e - e_min
    lw = np.log(np.maximum(w, 1e-300)) - tau * dx
    m = float(np.max(lw))
    p = np.exp(lw - m)
    p /= np.sum(p)
    mu1 = float(np.sum(p * dx))
    c = dx - mu1
    k2 = float(np.sum(p * (c ** 2)))
    k3 = float(np.sum(p * (c ** 3)))
    g = e_min + mu1
    delta_vf = g - tau * k2
    alpha_vf = (tau * tau) * k2
    delta_si = (g - 2.0 * (k2 * k2) / k3) if k3 > 1e-24 else delta_vf
    alpha_si = (4.0 * (k2 ** 3) / (k3 * k3)) if k3 > 1e-24 else 0.0
    return {
        "tau": tau,
        "g_raw": g,
        "k2": k2,
        "k3": k3,
        "Delta_VF": delta_vf,
        "Delta_SI": delta_si,
        "alpha_VF": alpha_vf,
        "alpha_SI": alpha_si,
    }


def discrete_fd_cumulants_from_logF(L_vals: np.ndarray, h: float, tau_center: float) -> dict:
    """
    Estimate g = L', k2 = -L'', k3 = L''' at the center point of a 5-point uniform stencil
    L_vals = [L(t-2h), L(t-h), L(t), L(t+h), L(t+2h)] where L(t) = -log F(t),
    using exact 4th-order central differences for g, k2 and 2nd-order central difference for k3.
    """
    Lm2, Lm1, L0, Lp1, Lp2 = [float(x) for x in L_vals]
    # 4th-order central first derivative: (Lm2 - 8*Lm1 + 8*Lp1 - Lp2) / (12*h)
    g = (Lm2 - 8.0 * Lm1 + 8.0 * Lp1 - Lp2) / (12.0 * h)
    # 4th-order central second derivative of (-L): -(-Lm2 + 16*Lm1 - 30*L0 + 16*Lp1 - Lp2) / (12*h^2)
    k2 = (Lm2 - 16.0 * Lm1 + 30.0 * L0 - 16.0 * Lp1 + Lp2) / (12.0 * h * h)
    # 2nd-order central third derivative of L: (-Lm2 + 2*Lm1 - 2*Lp1 + Lp2) / (2*h^3)
    k3 = (-Lm2 + 2.0 * Lm1 - 2.0 * Lp1 + Lp2) / (2.0 * (h ** 3))
    delta_vf = g - tau_center * k2
    alpha_vf = (tau_center ** 2) * k2
    if k2 > 0.0 and k3 > 1e-18:
        delta_si = g - 2.0 * (k2 * k2) / k3
        alpha_si = 4.0 * (k2 ** 3) / (k3 * k3)
    else:
        delta_si = delta_vf
        alpha_si = max(0.0, alpha_vf)
    return {
        "tau": tau_center,
        "g_raw": g,
        "k2": k2,
        "k3": k3,
        "Delta_VF": delta_vf,
        "Delta_SI": delta_si,
        "alpha_VF": alpha_vf,
        "alpha_SI": alpha_si,
    }
