# Shift-Invariant Cumulant Laws, Exact Stieltjes–Hankel Upper Certificates, and Minimax Resolution Limits for Continuum Spectral Edges from Imaginary-Time Evolution

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.35.0%20(0%20deps%2C%200%20sorry)-brightgreen)](lean/ContinuumEdge.lean)
[![Verifier](https://img.shields.io/badge/Certificate%20Verifier-Exact%20%E2%84%9A%20(zero%20float%20trust)-blue)](src/hankel_certifier.py)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Companion code, zero-dependency Lean 4 formalization, exact rational ($\mathbb{Q}$) Stieltjes–Hankel certificates, reproducible experiments, and LaTeX manuscript for:

> **Shift-Invariant Cumulant Laws, Exact Stieltjes–Hankel Upper Certificates, and Minimax Resolution Limits for Continuum Spectral Edges from Imaginary-Time Evolution**
> *Antigravity Frontier Research Agent* (autonomous scientific research conducted in the workspace of Lluis Eriksson)

## Core Contributions

1. **Exact Cumulant–Covariance Identity & Chebyshev Monotonicity Law (`Theorem 2.1`, `Remark 2.2`):** Proves $\widehat{\Delta}_{\mathrm{VF}}(\tau) - \Delta = \frac{d}{d\tau}(\tau\,\mathbb{E}[X_\tau]) = \frac{1}{\tau^2}\operatorname{Cov}_{U_\tau}(U_\tau, U_\tau V'(U_\tau/\tau)) + \mathcal{B}_B(\tau)$ (with nonnegative upper-edge boundary term $\mathcal{B}_B(\tau)$ for finite $B$), yielding exact non-asymptotic one-sided bounds ($\widehat{\Delta}_{\mathrm{VF}}(\tau) \ge \Delta$ whenever $x V'(x)$ is nondecreasing, e.g. 1D/3D point interactions and 2D steps; $\le \Delta$ on $(0,\infty)$ whenever $x V'(x)$ is nonincreasing) plus the exact modified-Bessel crossover $\tau > 2z_*/B \approx 0.8512$ for the 1D tight-binding van Hove band ($B=4$).
2. **Shift-Invariant Cumulant Estimators & Exact Cancellation Miracle (`Theorem 2.2`):** Introduces $\widehat{\Delta}_{\mathrm{SI}}(\tau) = g(\tau) - \frac{2\kappa_2(\tau)^2}{\kappa_3(\tau)}$ and $\widehat{\alpha}_{\mathrm{SI}}(\tau) = \frac{4\kappa_2(\tau)^3}{\kappa_3(\tau)^2}$, which are identically exact on the entire 3-parameter Gamma–Exponential family and achieve $O(\tau^{-3})$ gap error ($\frac{c_2 \alpha(\alpha+1)}{(\tau+\lambda)^3}$) and $O(\tau^{-2})$ exponent error ($-\frac{3c_2 \alpha(\alpha+1)}{(\tau+\lambda)^2}$) on general smooth continuum edges — delivering **$267\times$** gain on the 1D point interaction ($\alpha=3/2$), **$397\times$** on $\alpha=1/2$, **$169\times$** on $L=401$ lattice impurity ED, and **$7{,}630\times$** on 1D tight-binding van Hove bands at $\tau = 20$.
3. **Spectral-Edge Trichotomy (`Theorem 3.1`):** Proves that $\tau^2 \kappa_2(\tau)$ uniquely separates isolated discrete excited states ($\to 0$ exponentially), power-law continuum edges ($\to \alpha > 0$), and stretched-exponential pseudogaps ($\sim \tau^{\gamma/(\gamma+1)} \to +\infty$).
4. **Assumption-Free Exact-$\mathbb{Q}$ Stieltjes–Hankel Upper Certificates (`Theorem 4.1`):** Certifies $\Delta < \Delta_{\mathrm{ub}}^{\mathbb{Q}}$ for *arbitrary* positive spectral measures (discrete, continuous, or mixed) from finite-$\tau$ moment intervals via rational witness vectors $v \in \mathbb{Q}^{n+1}$ and exact rational logarithm upper bounds $\log_{\mathbb{Q}}^{\mathrm{ub}}(1/u_0)$ with zero floating-point trust.
5. **Finite-Sample Additive Shot-Noise Minimax Resolution Limits (`Theorem 5.1`):** Establishes asymptotic-window poly-logarithmic Le Cam lower bounds $\Omega((\log(\sqrt{K}/\sigma))^{-3})$ for $\Delta$ and $\Omega((\log(\sqrt{K}/\sigma))^{-2})$ for $\alpha$ over smooth $C^2$ edges, matching our optimal-horizon upper bounds ($6.74\times$ lower RMSE at $\sigma=10^{-7}$) and documenting the honest finite-noise bias–variance crossover between $\widehat{\Delta}_{\mathrm{VF}}$ and $\widehat{\Delta}_{\mathrm{SI}}$.
6. **Zero-Dependency Lean 4 Kernel:** 16 audited theorems (`leanprover/lean4:v4.35.0`, 0 external deps, 0 `sorry`, 0 `Classical.choice`) + 6 independently replayable exact-$\mathbb{Q}$ `.cert.json` files.

## Single-Command Gate-2 Verification

```bash
python scripts/verify_all.py
```
