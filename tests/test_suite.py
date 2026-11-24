"""
Comprehensive Gate-2 verification & adversarial falsification test suite (pytest) for Paper 3.
"""
import glob
import json
import math
import os
import sys
from fractions import Fraction
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from src.continuum_estimators import cumulants_from_density, discrete_fd_cumulants_from_logF
from src.hankel_certifier import (
    log_rational_upper_bound,
    verify_hankel_certificate_exact,
)
from src.physical_models import (
    point_1d_even_density,
    tb_1d_vanhove_density,
    step_2d_density,
    lattice_1d_impurity_ed,
)


def test_gamma_exponential_exact_invariance():
    """Verify Delta_SI == Delta and alpha_SI == alpha identically on Gamma-Exponential family."""
    for alpha, lam, Delta in [(0.5, 0.4, 1.2), (1.5, 0.7, 0.8), (2.5, 1.1, 0.3)]:
        w = lambda x, a=alpha, l=lam: (x ** (a - 1.0)) * math.exp(-l * x)
        for tau in [1.0, 3.0, 10.0]:
            c = cumulants_from_density(w, Delta, tau)
            assert abs(c["Delta_SI"] - Delta) < 1e-11
            assert abs(c["alpha_SI"] - alpha) < 1e-10
            # Verify Theorem 2.1 exact VF excess alpha*lam / (tau + lam)^2
            pred_vf = alpha * lam / ((tau + lam) ** 2)
            assert abs((c["Delta_VF"] - Delta) - pred_vf) < 1e-11


def test_chebyshev_sign_law_monotone_and_antimonotone():
    """Verify Theorem 2.1: VF > Delta for xV' increasing (1D point int), VF < Delta for xV' decreasing on (0,inf),
    and the exact Remark 2.2 Bessel crossover on 1D van Hove (VF > Delta at tau=0.2, VF < Delta at tau>=1)."""
    w_1d, d_1d, _, _ = point_1d_even_density(1.0)
    w_grow = lambda x: (x ** 0.5) * math.sqrt(1.0 + x)  # B=inf, xV'(x) = -x/(2(1+x)) strictly decreasing
    w_tb, d_tb, _, _ = tb_1d_vanhove_density(0.5, 4.0)
    for tau in [0.2, 1.0, 3.0, 10.0]:
        assert cumulants_from_density(w_1d, d_1d, tau)["Delta_VF"] > d_1d
        assert cumulants_from_density(w_grow, 1.0, tau)["Delta_VF"] < 1.0
    # 1D van Hove Bessel crossover at z_* ~ 1.7024 => tau_* = 2*z_*/4 ~ 0.8512
    # Plus direct quantitative verification of Remark 2.2: Delta_VF - Delta = (B/2) * [1 - z + z*(I1(z)/I0(z))^2]
    from scipy.special import i0, i1
    B = 4.0
    assert cumulants_from_density(w_tb, d_tb, 0.2, xmax=B)["Delta_VF"] > d_tb
    assert cumulants_from_density(w_tb, d_tb, 0.80, xmax=B)["Delta_VF"] > d_tb
    for tau in [0.2, 0.80, 0.90, 1.0, 3.0, 10.0, 20.0]:
        c_tb = cumulants_from_density(w_tb, d_tb, tau, xmax=B)
        z = 0.5 * tau * B
        bessel_pred = 0.5 * B * (1.0 - z + z * ((i1(z) / i0(z)) ** 2))
        assert abs((c_tb["Delta_VF"] - d_tb) - bessel_pred) < 1e-9
    for tau in [0.90, 1.0, 3.0, 10.0]:
        assert cumulants_from_density(w_tb, d_tb, tau, xmax=B)["Delta_VF"] < d_tb


def test_exact_si_asymptotic_c2_law():
    """Verify exact c2*alpha*(alpha+1)/s^3 and -3*c2*alpha*(alpha+1)/s^2 laws on log-concave 2D step."""
    w_2d, d_2d, a_2d, c2_2d = step_2d_density(0.5, 4.0)
    tau = 100.0
    s = tau + 0.25
    c = cumulants_from_density(w_2d, d_2d, tau, xmax=4.0)
    pred_d = c2_2d * a_2d * (a_2d + 1.0) / (s ** 3)
    pred_a = -3.0 * c2_2d * a_2d * (a_2d + 1.0) / (s ** 2)
    assert abs((c["Delta_SI"] - d_2d) / pred_d - 1.0) < 0.03
    assert abs((c["alpha_SI"] - a_2d) / pred_a - 1.0) < 0.03


def test_lattice_impurity_ed_exact_ground_state():
    ed = lattice_1d_impurity_ed(L=401, t_hop=1.0, V0=1.5)
    assert abs(ed["E0_ed"] - (-2.5)) < 1e-12
    assert abs(ed["Delta_thermo"] - 0.5) < 1e-12


def test_discrete_fd_stencil_accuracy():
    """Verify 5-point stencil recovers Delta and alpha on exact Gamma-Exponential F(tau)."""
    Delta, alpha, lam = 1.0, 1.5, 0.5
    tc, h = 6.0, 0.01
    ts = [tc + k * h for k in [-2, -1, 0, 1, 2]]
    L_vals = np.array([t * Delta + alpha * math.log(t + lam) for t in ts])
    est = discrete_fd_cumulants_from_logF(L_vals, h, tc)
    assert abs(est["Delta_SI"] - Delta) < 5e-6
    assert abs(est["alpha_SI"] - alpha) < 1e-4


def test_exact_rational_log_upper_bound():
    for num, den in [(3, 2), (5, 2), (10, 1), (1000, 3)]:
        x = Fraction(num, den)
        ub = log_rational_upper_bound(x)
        exact = math.log(num / den)
        assert float(ub) >= exact - 1e-15
        assert float(ub) - exact < 1e-10


def test_hankel_verifier_adversarial_falsifiers():
    """Adversarial falsification: verifier MUST reject forged witnesses, invalid intervals, and tampered delta_ub."""
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    with open(os.path.join(cert_dir, "point1d_even_n5_exact.cert.json")) as f:
        good = json.load(f)
    assert verify_hankel_certificate_exact(good)[0]

    # 1. Tamper delta_ub_q below exact rational log upper bound (fake tight gap!)
    bad_q = dict(good, delta_ub_q="1/10", delta_ub_float=0.1)
    assert not verify_hankel_certificate_exact(bad_q)[0]

    # 2. Tamper display float delta_ub_float alone
    bad_fl = dict(good, delta_ub_float=0.1)
    assert not verify_hankel_certificate_exact(bad_fl)[0]

    # 3. Tamper u0 upward so margin becomes >= 0 (fails refutation!)
    bad_u0 = dict(good, u0="999/1000")
    assert not verify_hankel_certificate_exact(bad_u0)[0]

    # 4. Negative order_n
    bad_n = dict(good, order_n=-1)
    assert not verify_hankel_certificate_exact(bad_n)[0]

    # 5. Inverted interval m_lo > m_hi
    bad_inv = dict(good, m_lo=list(good["m_hi"]), m_hi=list(good["m_lo"]))
    assert not verify_hankel_certificate_exact(bad_inv)[0]

    # 6. Negative quant_denom=-1 exploit attempting to forge delta_ub = 0
    bad_qd_neg = dict(good, quant_denom=-1, delta_ub_q="0/1", delta_ub_float=0.0)
    assert not verify_hankel_certificate_exact(bad_qd_neg)[0]

    # 7. Zero quant_denom
    bad_qd_zero = dict(good, quant_denom=0)
    assert not verify_hankel_certificate_exact(bad_qd_zero)[0]

    # 8. NaN / Inf display float bypass
    bad_nan = dict(good, delta_ub_float=float("nan"))
    assert not verify_hankel_certificate_exact(bad_nan)[0]
    bad_inf = dict(good, delta_ub_float=float("inf"))
    assert not verify_hankel_certificate_exact(bad_inf)[0]

    # 9. Tampered witness_margin
    bad_margin = dict(good, witness_margin="-1/1")
    assert not verify_hankel_certificate_exact(bad_margin)[0]

    # 10. Boolean order_n type confusion
    bad_bool = dict(good, order_n=True)
    assert not verify_hankel_certificate_exact(bad_bool)[0]


def test_exported_hankel_certificates_exact_replay():
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    files = sorted(glob.glob(os.path.join(cert_dir, "*.cert.json")))
    assert len(files) >= 6, f"Expected >= 6 exact-Q Hankel certificates, found {len(files)}"
    for fp in files:
        with open(fp) as f:
            cert = json.load(f)
        ok, info = verify_hankel_certificate_exact(cert)
        assert ok, f"Exact-Q Hankel replay failed for {fp}: {info}"
        assert info["margin"] < Fraction(0)
        assert info["delta_ub_q"] > Fraction(0)
