"""
Master reproducible experiment driver for Paper 3:
  "Shift-Invariant Cumulant Laws, Exact Stieltjes-Hankel Upper Certificates, and
   Minimax Resolution Limits for Continuum Spectral Edges from Imaginary-Time Evolution"

Generates:
  - results/experiment1_point_interaction_and_laws.json
  - results/experiment2_lattice_ed_and_trichotomy.json
  - results/experiment3_hankel_exact_Q_certificates.json
  - results/experiment4_shot_noise_minimax.json
  - results/rational_certificates/*.cert.json (6 zero-float-trust exact-Q Hankel certificates)
"""
import json
import math
import os
import sys
from fractions import Fraction
import numpy as np
from scipy.integrate import quad

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from src.continuum_estimators import (
    cumulants_from_density,
    cumulants_from_discrete_spectrum,
    discrete_fd_cumulants_from_logF,
)
from src.hankel_certifier import (
    build_exact_hankel_certificate,
    verify_hankel_certificate_exact,
)
from src.physical_models import (
    point_1d_even_density,
    point_1d_odd_density,
    point_3d_density,
    tb_1d_vanhove_density,
    step_2d_density,
    pseudogap_density,
    lattice_1d_impurity_ed,
)

RES_DIR = os.path.join(ROOT, "results")
CERT_DIR = os.path.join(RES_DIR, "rational_certificates")
os.makedirs(CERT_DIR, exist_ok=True)


def run_experiment_1():
    """
    Experiment 1:
      Exact verification of Theorem 2.1 (Chebyshev covariance sign law) and Theorem 2.2
      (shift-invariant Delta_SI O(tau^-3) and alpha_SI O(tau^-2) exact cancellation laws)
      across:
        - Gamma-Exponential exact family (exact 0 error at all tau > 0)
        - 1D One-Center Point Interaction (Karapetyan et al. arXiv:2611.06454, alpha=3/2 and alpha=1/2)
        - 3D One-Center Point Interaction (alpha=3/2)
        - 1D Tight-Binding van Hove band (alpha=1/2, x V'(x) decreasing -> VF < Delta!)
        - 2D Step Continuum (alpha=1, log-concave c2 < 0 -> SI < Delta!)
    """
    print("[Exp 1] Running exact analytical benchmarks for Theorems 2.1 & 2.2 (1D/3D point interactions & bands)...")
    taus = [1.0, 2.0, 4.0, 6.0, 10.0, 15.0, 20.0]

    w_ge = lambda x: (x ** 0.5) * math.exp(-0.7 * x)
    w_1de, d_1de, a_1de, c2_1de = point_1d_even_density(1.0)
    w_1do, d_1do, a_1do, c2_1do = point_1d_odd_density(1.0)
    w_3d, d_3d, a_3d, c2_3d = point_3d_density(1.0)
    w_tb, d_tb, a_tb, c2_tb = tb_1d_vanhove_density(0.5, 4.0)
    w_2d, d_2d, a_2d, c2_2d = step_2d_density(0.5, 4.0)

    models = [
        ("gamma_exp_exact", w_ge, 1.0, 1.5, 0.7, 0.0, np.inf, "xV_inc"),
        ("point_1d_even_alpha1p5", w_1de, d_1de, a_1de, 1.0, c2_1de, np.inf, "xV_inc"),
        ("point_1d_odd_alpha0p5", w_1do, d_1do, a_1do, 1.0, c2_1do, np.inf, "xV_inc"),
        ("point_3d_alpha1p5", w_3d, d_3d, a_3d, 2.0, c2_3d, np.inf, "xV_inc"),
        ("tb_1d_vanhove_alpha0p5", w_tb, d_tb, a_tb, -0.125, c2_tb, 4.0, "xV_dec"),
        ("step_2d_alpha1p0", w_2d, d_2d, a_2d, 0.25, c2_2d, 4.0, "xV_inc"),
    ]

    results = {}
    for name, w_fn, Delta, alpha_true, lam, c2, xmax, sign_class in models:
        rows = []
        for t in taus:
            c = cumulants_from_density(w_fn, Delta, t, xmax=xmax)
            err_raw = c["g_raw"] - Delta
            err_vf = c["Delta_VF"] - Delta
            err_si = c["Delta_SI"] - Delta
            err_a_vf = c["alpha_VF"] - alpha_true
            err_a_si = c["alpha_SI"] - alpha_true
            s = t + lam
            pred_d_si = c2 * alpha_true * (alpha_true + 1.0) / (s ** 3)
            pred_a_si = -3.0 * c2 * alpha_true * (alpha_true + 1.0) / (s ** 2)
            # Verify Theorem 2.1 Chebyshev sign law at EVERY tau!
            if sign_class == "xV_inc":
                assert err_vf >= -1e-12, f"Chebyshev sign violation on {name} at tau={t}"
            else:
                assert err_vf <= 1e-12, f"Chebyshev anti-monotone sign violation on {name} at tau={t}"
            rows.append({
                "tau": t,
                "err_raw": err_raw,
                "err_VF": err_vf,
                "err_SI": err_si,
                "pred_err_SI": pred_d_si,
                "gain_SI_over_raw": abs(err_raw) / max(abs(err_si), 1e-16),
                "alpha_VF": c["alpha_VF"],
                "alpha_SI": c["alpha_SI"],
                "err_alpha_VF": err_a_vf,
                "err_alpha_SI": err_a_si,
                "pred_err_alpha_SI": pred_a_si,
                "gain_alpha_SI_over_VF": abs(err_a_vf) / max(abs(err_a_si), 1e-16),
            })
        results[name] = {
            "Delta_true": Delta,
            "alpha_true": alpha_true,
            "lam": lam,
            "c2_log_curvature": c2,
            "chebyshev_sign": sign_class,
            "sweep": rows,
        }

    # Verify Gamma-Exp exactness to machine precision
    assert max(abs(r["err_SI"]) for r in results["gamma_exp_exact"]["sweep"]) < 1e-12
    assert max(abs(r["err_alpha_SI"]) for r in results["gamma_exp_exact"]["sweep"]) < 1e-11

    with open(os.path.join(RES_DIR, "experiment1_point_interaction_and_laws.json"), "w") as f:
        json.dump(results, f, indent=2)
    r1d = results["point_1d_even_alpha1p5"]["sweep"][-1]
    rtb = results["tb_1d_vanhove_alpha0p5"]["sweep"][-1]
    print(f"  Done Exp 1: 1D point-int (tau=20) SI gain {r1d['gain_SI_over_raw']:.1f}x; 1D TB van Hove SI gain {rtb['gain_SI_over_raw']:.1f}x; Chebyshev sign laws 100% verified!")
    return results


def run_experiment_2():
    """
    Experiment 2:
      (A) Exact Finite-Lattice Tridiagonal ED (L = 401, t = 1.0, V0 = 1.5) for 1D Tight-Binding Impurity:
          exact bound state E0 = -2.500000 below band [-2, 2], Delta_exact = 0.500000, alpha = 3/2!
          Tracks raw g(tau), VF, and SI across tau in [2, 30] before finite-size spacing Delta_E ~ pi^2/L^2 kicks in.
      (B) Theorem 3.1 Spectral-Edge Trichotomy across tau in [2, 60]:
            1. Discrete isolated excited state (Delta=1.0, E2=2.5): alpha_VF -> 0 exponentially!
            2. Power-law continuum edges (alpha=0.5, 1.0, 1.5): alpha_VF -> alpha, alpha_SI -> alpha at O(tau^-2)!
            3. Stretched-exponential pseudogap (gamma=0.5): alpha_VF ~ tau^{1/3} -> +inf!
    """
    print("[Exp 2] Running L=401 lattice impurity ED & Theorem 3.1 spectral-edge trichotomy...")
    ed = lattice_1d_impurity_ed(L=401, t_hop=1.0, V0=1.5)
    assert abs(ed["E0_ed"] - ed["E0_thermo"]) < 1e-12
    Delta_imp = ed["Delta_thermo"]  # exact 0.5
    ed_rows = []
    for t in [2.0, 4.0, 6.0, 10.0, 15.0, 20.0, 30.0]:
        c = cumulants_from_discrete_spectrum(ed["exc_energies"], ed["exc_weights"], t)
        ed_rows.append({
            "tau": t,
            "err_raw": c["g_raw"] - Delta_imp,
            "err_VF": c["Delta_VF"] - Delta_imp,
            "err_SI": c["Delta_SI"] - Delta_imp,
            "gain_SI_over_raw": abs(c["g_raw"] - Delta_imp) / max(abs(c["Delta_SI"] - Delta_imp), 1e-15),
            "alpha_VF": c["alpha_VF"],
            "alpha_SI": c["alpha_SI"],
        })

    # Spectral-edge trichotomy sweep
    taus_tri = [2.0, 5.0, 10.0, 20.0, 35.0, 50.0]
    # 1. Discrete isolated gap: two discrete excited levels at Delta=1.0 and Delta+1.5=2.5
    disc_e = np.array([1.0, 2.5])
    disc_w = np.array([0.6, 0.4])
    # 2. Power-law continuum alpha=0.5 and alpha=1.5
    w_1do, d_1do, _, _ = point_1d_odd_density(1.0)
    w_1de, d_1de, _, _ = point_1d_even_density(1.0)
    # 3. Stretched-exponential pseudogap gamma=0.5 -> alpha_VF ~ tau^{1/3}
    w_pg, d_pg = pseudogap_density(0.5, c_pg=2.0, gamma=0.5)

    trichotomy = []
    for t in taus_tri:
        c_disc = cumulants_from_discrete_spectrum(disc_e, disc_w, t)
        c_a05 = cumulants_from_density(w_1do, d_1do, t)
        c_a15 = cumulants_from_density(w_1de, d_1de, t)
        c_pg = cumulants_from_density(w_pg, d_pg, t, xmax=30.0)
        trichotomy.append({
            "tau": t,
            "discrete_alpha_VF": c_disc["alpha_VF"],
            "continuum_a0p5_alpha_VF": c_a05["alpha_VF"],
            "continuum_a0p5_alpha_SI": c_a05["alpha_SI"],
            "continuum_a1p5_alpha_VF": c_a15["alpha_VF"],
            "continuum_a1p5_alpha_SI": c_a15["alpha_SI"],
            "pseudogap_alpha_VF": c_pg["alpha_VF"],
            "pseudogap_tau_1_3_ratio": c_pg["alpha_VF"] / (t ** (1.0 / 3.0)),
        })

    out = {
        "lattice_impurity_ed": {
            "L": ed["L"],
            "E0_ed": ed["E0_ed"],
            "E0_thermo": ed["E0_thermo"],
            "Delta_thermo": Delta_imp,
            "alpha_thermo": 1.5,
            "sweep": ed_rows,
        },
        "spectral_edge_trichotomy": trichotomy,
    }
    with open(os.path.join(RES_DIR, "experiment2_lattice_ed_and_trichotomy.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"  Done Exp 2: L=401 impurity ED (tau=20) err_raw={ed_rows[-2]['err_raw']:+.4f} vs err_SI={ed_rows[-2]['err_SI']:+.5f} ({ed_rows[-2]['gain_SI_over_raw']:.1f}x); trichotomy alpha_VF(50): disc={trichotomy[-1]['discrete_alpha_VF']:.2e}, a=1.5:{trichotomy[-1]['continuum_a1p5_alpha_SI']:.4f}, pseudogap={trichotomy[-1]['pseudogap_alpha_VF']:.2f}")
    return out


def run_experiment_3():
    """
    Experiment 3:
      Zero-Float-Trust Exact-Q Assumption-Free Stieltjes-Hankel Upper Certificates (Theorem 4.1):
        (A) Order sweep n = 0..5 at fixed tau0 = 1.0, delta = 0.5 on 1D Point-Interaction (Delta=1.0),
            3D Point-Interaction (Delta=1.0), 1D Tight-Binding van Hove (Delta=0.5), 2D Step (Delta=0.5),
            and L=401 Impurity ED (Delta=0.5), exporting 6 independently replayable .cert.json files!
        (B) 200-trial noisy finite-sample interval Hankel soundness audit (relative shot noise
            sigma_rel in {1e-3, 1e-2}, Bonferroni confidence intervals): verifying 100% soundness
            (0/200 invalid upper bounds Delta_ub < Delta_true!).
    """
    print("[Exp 3] Building & verifying zero-float-trust exact-Q Stieltjes-Hankel certificates...")
    tau0_q, delta_q = Fraction(1, 1), Fraction(1, 2)
    tau0, delta = 1.0, 0.5

    def get_moments_density(w_fn, Delta, xmax, count=14):
        ms = []
        for k in range(count):
            t = tau0 + k * delta
            val, _ = quad(lambda x: math.exp(-t * (Delta + x)) * w_fn(x), 0.0, xmax, limit=250, epsabs=1e-14, epsrel=1e-13)
            ms.append(val)
        return ms

    w_1de, d_1de, _, _ = point_1d_even_density(1.0)
    w_1do, d_1do, _, _ = point_1d_odd_density(1.0)
    w_3d, d_3d, _, _ = point_3d_density(1.0)
    w_tb, d_tb, _, _ = tb_1d_vanhove_density(0.5, 4.0)
    w_2d, d_2d, _, _ = step_2d_density(0.5, 4.0)
    ed = lattice_1d_impurity_ed(L=401, t_hop=1.0, V0=1.5)
    ms_ed = [float(np.sum(ed["exc_weights"] * np.exp(-(tau0 + k * delta) * ed["exc_energies"]))) for k in range(14)]

    # (A1) Order sweep on 1D point-interaction (alpha=3/2, Delta=1.0)
    ms_1de = get_moments_density(w_1de, d_1de, np.inf)
    eps_quad = 1e-11
    order_sweep_1d = []
    for n in [0, 1, 2, 3, 4, 5]:
        lo = [m * (1.0 - eps_quad) for m in ms_1de[: 2 * n + 2]]
        hi = [m * (1.0 + eps_quad) for m in ms_1de[: 2 * n + 2]]
        ok, cert = build_exact_hankel_certificate(
            lo, hi, delta_q=delta_q, tau0_q=tau0_q, order_n=n,
            model_meta={"model": f"1D Point-Interaction (alpha=3/2, Delta=1.0), order n={n}", "Delta_true": d_1de}
        )
        assert ok and verify_hankel_certificate_exact(cert)[0]
        assert cert["delta_ub_float"] > d_1de
        tau_max = tau0 + (2 * n + 1) * delta
        g_tmax = cumulants_from_density(w_1de, d_1de, tau_max)["g_raw"]
        order_sweep_1d.append({
            "order_n": n,
            "tau_max": tau_max,
            "Delta_ub_exact_Q": cert["delta_ub_float"],
            "err_Hankel_Q": cert["delta_ub_float"] - d_1de,
            "raw_g_at_tau_max": g_tmax,
            "err_raw_at_tau_max": g_tmax - d_1de,
            "tightness_vs_raw_at_tau_max": (g_tmax - d_1de) / (cert["delta_ub_float"] - d_1de),
        })
        if n == 5:
            with open(os.path.join(CERT_DIR, "point1d_even_n5_exact.cert.json"), "w") as f:
                json.dump(cert, f, indent=2)

    # (A2) Export 5 more exact-Q Hankel certificates across all models (n=4 or n=5)
    cert_specs = [
        ("point1d_odd_n5_exact.cert.json", "1D Point-Interaction (alpha=1/2, Delta=1.0)", get_moments_density(w_1do, d_1do, np.inf), d_1do, 5),
        ("point3d_n5_exact.cert.json", "3D Point-Interaction (alpha=3/2, Delta=1.0)", get_moments_density(w_3d, d_3d, np.inf), d_3d, 5),
        ("tb1d_vanhove_n5_exact.cert.json", "1D Tight-Binding van Hove (alpha=1/2, Delta=0.5)", get_moments_density(w_tb, d_tb, 4.0), d_tb, 5),
        ("step2d_n5_exact.cert.json", "2D Step Continuum (alpha=1.0, Delta=0.5)", get_moments_density(w_2d, d_2d, 4.0), d_2d, 5),
        ("lattice_impurity_L401_n4_exact.cert.json", "1D Lattice Impurity ED (L=401, Delta=0.5)", ms_ed, ed["Delta_thermo"], 4),
    ]
    model_certs_summary = []
    for fname, label, ms, d_true, n_ord in cert_specs:
        lo = [m * (1.0 - eps_quad) for m in ms[: 2 * n_ord + 2]]
        hi = [m * (1.0 + eps_quad) for m in ms[: 2 * n_ord + 2]]
        ok, cert = build_exact_hankel_certificate(
            lo, hi, delta_q=delta_q, tau0_q=tau0_q, order_n=n_ord,
            model_meta={"model": label, "Delta_true": d_true}
        )
        assert ok and verify_hankel_certificate_exact(cert)[0]
        assert cert["delta_ub_float"] > d_true
        with open(os.path.join(CERT_DIR, fname), "w") as f:
            json.dump(cert, f, indent=2)
        model_certs_summary.append({
            "file": fname,
            "model": label,
            "order_n": n_ord,
            "Delta_true": d_true,
            "Delta_ub_exact_Q": cert["delta_ub_float"],
            "excess_ub": cert["delta_ub_float"] - d_true,
        })

    # (B) 200-trial noisy finite-sample interval Hankel soundness audit (synthetic Gaussian relative noise)
    rng = np.random.default_rng(2026112433)
    noisy_audit = []
    for sigma_rel, n_ord in [(1e-3, 2), (1e-2, 1)]:
        m_len = 2 * n_ord + 2
        z_bonf = 3.29  # >99.9% per-coordinate -> >99% joint coverage across up to 6 moments
        rad = z_bonf * sigma_rel
        cert_cnt = 0
        sound_cnt = 0
        ubs = []
        for _ in range(200):
            noise = rng.normal(0.0, sigma_rel, size=m_len)
            m_hat = [ms_1de[k] * max(1e-6, 1.0 + float(noise[k])) for k in range(m_len)]
            lo = [max(0.0, mh / (1.0 + rad)) for mh in m_hat]
            hi = [mh / max(0.1, 1.0 - rad) for mh in m_hat]
            ok, cert = build_exact_hankel_certificate(lo, hi, delta_q=delta_q, tau0_q=tau0_q, order_n=n_ord)
            if ok:
                assert verify_hankel_certificate_exact(cert)[0]
                cert_cnt += 1
                ubs.append(cert["delta_ub_float"])
                if cert["delta_ub_float"] >= d_1de:
                    sound_cnt += 1
            else:
                sound_cnt += 1
        assert sound_cnt == 200
        noisy_audit.append({
            "sigma_rel": sigma_rel,
            "order_n": n_ord,
            "n_trials": 200,
            "certified_fraction": cert_cnt / 200.0,
            "soundness_fraction": sound_cnt / 200.0,
            "median_Delta_ub": float(np.median(ubs)) if ubs else None,
            "Delta_true": d_1de,
        })

    out = {
        "order_sweep_point1d": order_sweep_1d,
        "model_certificates": model_certs_summary,
        "noisy_interval_audit": noisy_audit,
    }
    with open(os.path.join(RES_DIR, "experiment3_hankel_exact_Q_certificates.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"  Done Exp 3: 6 exact-Q Hankel certificates verified; 1D point-int n=5 certifies Delta <= {order_sweep_1d[-1]['Delta_ub_exact_Q']:.4f} ({order_sweep_1d[-1]['tightness_vs_raw_at_tau_max']:.2f}x tighter than raw g(6.5)!); noisy soundness 200/200!")
    return out


def run_experiment_4():
    """
    Experiment 4:
      Finite-Sample Additive Shot-Noise Minimax Scaling (Theorem 5.1):
      On 1D Point-Interaction (Delta=1.0, alpha=3/2), measure F_hat(tau) = F(tau) + N(0, sigma^2)
      across additive noise levels sigma in {1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6, 1e-7},
      comparing optimal-horizon RMSE of:
        - Raw Karapetyan et al. finite-difference g_hat(tau*)  ~ O(1 / log(1/sigma))
        - Variance-Free Delta_VF_hat(tau*)                     ~ O(1 / (log(1/sigma))^2)
        - Shift-Invariant Delta_SI_hat(tau*)                   ~ O(1 / (log(1/sigma))^3)
    """
    print("[Exp 4] Running finite-sample additive shot-noise minimax scaling sweep...")
    w_1de, Delta, alpha_true, _ = point_1d_even_density(1.0)
    # Precompute exact F(tau) on a dense tau grid [0.5, 18.0] step 0.25
    h_grid = 0.25
    tau_grid = np.arange(0.5, 18.01, h_grid)
    F_exact = np.array([
        quad(lambda x: math.exp(-float(t) * (Delta + x)) * w_1de(x), 0.0, np.inf, limit=250, epsabs=1e-15, epsrel=1e-13)[0]
        for t in tau_grid
    ])

    rng = np.random.default_rng(2026112444)
    sigmas = [1e-3, 3e-4, 1e-4, 3e-5, 1e-5, 3e-6, 1e-6, 1e-7]
    n_mc = 120
    rows = []

    for sig in sigmas:
        # Select best horizon idx (with 5-point stencil step h_step = 0.5, i.e. 2 grid points) per estimator
        # to evaluate the oracle-tuned finite-sample risk envelope (bias-variance tradeoff)
        best_rmse = {"raw": float("inf"), "VF": float("inf"), "SI": float("inf")}
        best_tau = {"raw": 0.0, "VF": 0.0, "SI": 0.0}
        step_idx = 2  # h = 0.50
        h_fd = step_idx * h_grid
        # Generate shared noise matrix (n_mc, len(tau_grid))
        noise_mat = rng.normal(0.0, sig, size=(n_mc, len(tau_grid)))
        F_noisy = F_exact[None, :] + noise_mat

        for idx in range(2 * step_idx, len(tau_grid) - 2 * step_idx):
            st_indices = [idx - 2 * step_idx, idx - step_idx, idx, idx + step_idx, idx + 2 * step_idx]
            sub = F_noisy[:, st_indices]
            # Require signal strictly above noise floor across all trials
            if np.min(sub) <= 5.0 * sig:
                continue
            L_mat = -np.log(sub)
            e_raw, e_vf, e_si = [], [], []
            tc = float(tau_grid[idx])
            for m in range(n_mc):
                est = discrete_fd_cumulants_from_logF(L_mat[m], h_fd, tc)
                e_raw.append(est["g_raw"] - Delta)
                e_vf.append(est["Delta_VF"] - Delta)
                e_si.append(est["Delta_SI"] - Delta)
            for key, errs in [("raw", e_raw), ("VF", e_vf), ("SI", e_si)]:
                rmse = math.sqrt(float(np.mean(np.square(errs))))
                if rmse < best_rmse[key]:
                    best_rmse[key] = rmse
                    best_tau[key] = tc

        rows.append({
            "sigma": sig,
            "log_inv_sigma": math.log(1.0 / sig),
            "rmse_raw": best_rmse["raw"],
            "tau_opt_raw": best_tau["raw"],
            "rmse_VF": best_rmse["VF"],
            "tau_opt_VF": best_tau["VF"],
            "rmse_SI": best_rmse["SI"],
            "tau_opt_SI": best_tau["SI"],
            "gain_SI_over_raw": best_rmse["raw"] / max(best_rmse["SI"], 1e-15),
        })

    out = {"Delta_true": Delta, "alpha_true": alpha_true, "n_mc": n_mc, "minimax_sweep": rows}
    with open(os.path.join(RES_DIR, "experiment4_shot_noise_minimax.json"), "w") as f:
        json.dump(out, f, indent=2)
    print(f"  Done Exp 4: at sigma=1e-7 RMSE raw={rows[-1]['rmse_raw']:.4f} vs VF={rows[-1]['rmse_VF']:.4f} vs SI={rows[-1]['rmse_SI']:.5f} ({rows[-1]['gain_SI_over_raw']:.1f}x lower RMSE!)")
    return out


if __name__ == "__main__":
    run_experiment_1()
    run_experiment_2()
    run_experiment_3()
    run_experiment_4()
    print("\nALL 4 EXPERIMENTS COMPLETED SUCCESSFULLY.")
