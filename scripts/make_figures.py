"""
Generate 3 publication-quality vector PDF and PNG figures directly from verified JSON outputs (Paper 3).
"""
import json
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES_DIR = os.path.join(ROOT, "results")
FIG_DIR = os.path.join(ROOT, "paper", "figures")
os.makedirs(FIG_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.labelsize": 10,
    "axes.titlesize": 10.2,
    "legend.fontsize": 7.8,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "axes.grid": True,
    "grid.alpha": 0.25,
    "grid.linestyle": "--",
})


def make_fig1():
    with open(os.path.join(RES_DIR, "experiment1_point_interaction_and_laws.json")) as f:
        d = json.load(f)
    sw = d["point_1d_even_alpha1p5"]["sweep"]
    taus = [r["tau"] for r in sw]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Gap estimation error |Delta_hat - Delta| vs tau (log-log) showing O(tau^-1), O(tau^-2), O(tau^-3)
    ax1.loglog(taus, [abs(r["err_raw"]) for r in sw], "^:", color="#d62728", linewidth=1.7, markersize=6,
               label=r"Raw $g(\tau)$ (Karapetyan et al.): $O(\tau^{-1})$")
    ax1.loglog(taus, [abs(r["err_VF"]) for r in sw], "s--", color="#ff7f0e", linewidth=1.7, markersize=5.5,
               label=r"Variance-Free $\widehat{\Delta}_{\mathrm{VF}}(\tau)$: $O(\tau^{-2})$")
    ax1.loglog(taus, [abs(r["err_SI"]) for r in sw], "o-", color="#1f77b4", linewidth=2.0, markersize=6,
               label=r"Shift-Invariant $\widehat{\Delta}_{\mathrm{SI}}(\tau)$: $O(\tau^{-3})$")
    ax1.loglog(taus, [abs(r["pred_err_SI"]) for r in sw], "k-", linewidth=1.0, alpha=0.65,
               label=r"Exact asymptote $c_2 \alpha(\alpha+1)/(\tau+\lambda)^3$")
    ax1.set_xlabel(r"Imaginary time $\tau$")
    ax1.set_ylabel(r"Continuum-edge error $|\widehat{\Delta}(\tau) - \Delta|$")
    ax1.set_title(r"(a) 1D Point Interaction ($\alpha=3/2$, $267\times$ Gain)")
    ax1.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.3)

    # Panel (b): Threshold exponent alpha estimation (VF vs SI) on 1D point-int (3/2) & 1D TB van Hove (1/2)
    sw_tb = d["tb_1d_vanhove_alpha0p5"]["sweep"]
    ax2.plot(taus, [r["alpha_VF"] for r in sw], "s--", color="#ff7f0e", linewidth=1.5, markersize=5,
             label=r"1D Point-Int ($\alpha=1.5$): $\widehat{\alpha}_{\mathrm{VF}} = \tau^2 \kappa_2$")
    ax2.plot(taus, [r["alpha_SI"] for r in sw], "o-", color="#1f77b4", linewidth=1.9, markersize=5.5,
             label=r"1D Point-Int ($\alpha=1.5$): $\widehat{\alpha}_{\mathrm{SI}} = 4\kappa_2^3/\kappa_3^2$")
    ax2.axhline(1.5, color="#1f77b4", linestyle=":", linewidth=1.1, alpha=0.8)
    ax2.plot(taus, [r["alpha_VF"] for r in sw_tb], "^--", color="#9467bd", linewidth=1.5, markersize=5,
             label=r"1D van Hove ($\alpha=0.5$): $\widehat{\alpha}_{\mathrm{VF}}$")
    ax2.plot(taus, [r["alpha_SI"] for r in sw_tb], "d-", color="#2ca02c", linewidth=1.9, markersize=5.5,
             label=r"1D van Hove ($\alpha=0.5$): $\widehat{\alpha}_{\mathrm{SI}}$")
    ax2.axhline(0.5, color="#2ca02c", linestyle=":", linewidth=1.1, alpha=0.8)
    ax2.set_xlabel(r"Imaginary time $\tau$")
    ax2.set_ylabel(r"Estimated threshold exponent $\widehat{\alpha}(\tau)$")
    ax2.set_ylim(0.35, 1.62)
    ax2.set_title(r"(b) Threshold-Exponent Recovery ($O(\tau^{-1})$ vs. $O(\tau^{-2})$)")
    ax2.legend(loc="center right", frameon=True, framealpha=0.92, fontsize=7.1)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig1_shift_invariant_laws.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig1_shift_invariant_laws.png"))
    plt.close(fig)


def make_fig2():
    with open(os.path.join(RES_DIR, "experiment2_lattice_ed_and_trichotomy.json")) as f:
        d = json.load(f)
    ed = d["lattice_impurity_ed"]["sweep"]
    tri = d["spectral_edge_trichotomy"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): L=401 Lattice Impurity ED gap errors
    t_ed = [r["tau"] for r in ed]
    ax1.semilogy(t_ed, [abs(r["err_raw"]) for r in ed], "^:", color="#d62728", linewidth=1.7, markersize=6,
                 label=r"Raw $g(\tau)$")
    ax1.semilogy(t_ed, [abs(r["err_VF"]) for r in ed], "s--", color="#ff7f0e", linewidth=1.7, markersize=5.5,
                 label=r"Variance-Free $\widehat{\Delta}_{\mathrm{VF}}(\tau)$")
    ax1.semilogy(t_ed, [abs(r["err_SI"]) for r in ed], "o-", color="#1f77b4", linewidth=2.0, markersize=6,
                 label=r"Shift-Invariant $\widehat{\Delta}_{\mathrm{SI}}(\tau)$")
    ax1.set_xlabel(r"Imaginary time $\tau$")
    ax1.set_ylabel(r"Error $|\widehat{\Delta}(\tau) - \Delta_{\mathrm{exact}}|$")
    ax1.set_title(r"(a) 1D Lattice Impurity ED ($L=401, \Delta=0.5$)")
    ax1.legend(loc="lower left", frameon=True, framealpha=0.92, fontsize=7.8)

    # Panel (b): Spectral-Edge Trichotomy (Theorem 3.1)
    t_tri = [r["tau"] for r in tri]
    ax2.semilogy(t_tri, [max(r["discrete_alpha_VF"], 1e-12) for r in tri], "^:", color="#d62728", linewidth=1.7, markersize=6,
                 label=r"Discrete excited state: $\tau^2\kappa_2 \to 0$")
    ax2.semilogy(t_tri, [r["continuum_a0p5_alpha_VF"] for r in tri], "s--", color="#2ca02c", linewidth=1.7, markersize=5.5,
                 label=r"Power-law continuum ($\alpha=0.5$): $\to 0.5$")
    ax2.semilogy(t_tri, [r["continuum_a1p5_alpha_VF"] for r in tri], "o-", color="#1f77b4", linewidth=1.8, markersize=5.5,
                 label=r"Power-law continuum ($\alpha=1.5$): $\to 1.5$")
    ax2.semilogy(t_tri, [r["pseudogap_alpha_VF"] for r in tri], "d-.", color="#9467bd", linewidth=1.8, markersize=5.5,
                 label=r"Stretched-exp pseudogap: $\sim \tau^{1/3} \to \infty$")
    ax2.set_xlabel(r"Imaginary time $\tau$")
    ax2.set_ylabel(r"Dimensionless cumulant $\tau^2 \kappa_2(\tau)$")
    ax2.set_ylim(1e-11, 20.0)
    ax2.set_title(r"(b) Spectral-Edge Trichotomy (Theorem 3.1)")
    ax2.legend(loc="lower right", frameon=True, framealpha=0.92, fontsize=7.3)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig2_lattice_ed_and_trichotomy.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig2_lattice_ed_and_trichotomy.png"))
    plt.close(fig)


def make_fig3():
    with open(os.path.join(RES_DIR, "experiment3_hankel_exact_Q_certificates.json")) as f:
        d3 = json.load(f)
    with open(os.path.join(RES_DIR, "experiment4_shot_noise_minimax.json")) as f:
        d4 = json.load(f)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Exact-Q Stieltjes-Hankel Upper Certificates vs raw g(tau_max)
    sw3 = d3["order_sweep_point1d"]
    ns = [r["order_n"] for r in sw3]
    ax1.plot(ns, [r["raw_g_at_tau_max"] for r in sw3], "^:", color="#d62728", linewidth=1.7, markersize=6,
             label=r"Raw $g(\tau_{\max})$ at same max horizon")
    ax1.plot(ns, [r["Delta_ub_exact_Q"] for r in sw3], "o-", color="#1f77b4", linewidth=2.0, markersize=6,
             label=r"Ours: assumption-free exact-$\mathbb{Q}$ Hankel $\Delta_{\mathrm{ub}}$")
    ax1.axhline(1.0, color="black", linestyle="--", linewidth=1.2, label=r"Exact continuum edge $\Delta = 1.0$")
    ax1.set_xticks(ns)
    ax1.set_xlabel(r"Hankel order $n$ ($\tau_0 = 1.0, \delta = 0.5, \tau_{\max} = 1.5 + n$)")
    ax1.set_ylabel(r"Certified upper bound on $\Delta$")
    ax1.set_title(r"(a) Exact-$\mathbb{Q}$ Stieltjes–Hankel Upper Certificates")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.4)

    # Panel (b): Shot-noise minimax RMSE vs 1/log(1/sigma)
    sw4 = d4["minimax_sweep"]
    inv_log = [1.0 / r["log_inv_sigma"] for r in sw4]
    ax2.loglog(inv_log, [r["rmse_raw"] for r in sw4], "^:", color="#d62728", linewidth=1.7, markersize=6,
               label=r"Raw FD $\widehat{g}$: $O((\log(1/\sigma))^{-1})$")
    ax2.loglog(inv_log, [r["rmse_VF"] for r in sw4], "s--", color="#ff7f0e", linewidth=1.7, markersize=5.5,
               label=r"Variance-Free $\widehat{\Delta}_{\mathrm{VF}}$: $O((\log(1/\sigma))^{-2})$")
    ax2.loglog(inv_log, [r["rmse_SI"] for r in sw4], "o-", color="#1f77b4", linewidth=2.0, markersize=6,
               label=r"Shift-Invariant $\widehat{\Delta}_{\mathrm{SI}}$: $O((\log(1/\sigma))^{-3})$")
    ax2.set_xlabel(r"Inverse log-SNR $1 / \log(1/\sigma)$ ($\sigma \in [10^{-7}, 10^{-3}]$)")
    ax2.set_ylabel(r"Optimal-horizon RMSE on $\Delta$")
    ax2.set_title(r"(b) Additive Shot-Noise Minimax Scaling (Thm. 5.1)")
    ax2.legend(loc="lower right", frameon=True, framealpha=0.92, fontsize=7.4)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig3_hankel_and_minimax.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig3_hankel_and_minimax.png"))
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 publication figures in paper/figures/.")
