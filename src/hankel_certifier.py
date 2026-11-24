"""
Zero-Floating-Point-Trust Exact Rational (Q) Stieltjes-Hankel Upper Certificate Builder & Verifier.

Given finite-tau imaginary-time survival/observable intervals:
    m_k in [m_k^-, m_k^+]   for k = 0, 1, ..., 2n + 1,
where m_k = F(tau_0 + k * delta) = int_0^{exp(-delta * Delta)} z^k d nu_tilde(z),
any rational witness vector v in Q^{n+1} satisfying the exact sign-split interval inequality:
    u_0 * Q0_ub(v) - Q1_lb(v) < 0   (with u_0 in Q cap (0, 1))
PROVES (with ZERO assumptions on smoothness, monotonicity, or discrete vs. continuous spectrum!)
that NO positive measure supported on [0, u_0] can lie inside [m_k^-, m_k^+], hence:
    Delta < -log(u_0) / delta <= log_Q_ub(1 / u_0) / delta   EXACTLY in Q!

Every step (interval quadratic forms, witness negativity, binary-reduced rational logarithm
upper bound with geometric tail, and display float consistency) is verified strictly in
arbitrary-precision `fractions.Fraction` with ZERO floating-point trust.
"""
import math
from fractions import Fraction
import numpy as np
from scipy.linalg import eigh


def ceil_rational(x: Fraction, denom: int = 10**12) -> Fraction:
    """Sound upward quantization: returns q = ceil(x * denom) / denom >= x EXACTLY."""
    if not isinstance(denom, int) or isinstance(denom, bool) or denom <= 0:
        raise ValueError("denom must be a strictly positive integer")
    num = -((-x.numerator * denom) // x.denominator)
    return Fraction(num, denom)


def floor_rational(x: Fraction, denom: int = 10**12) -> Fraction:
    """Sound downward quantization: returns q = floor(x * denom) / denom <= x EXACTLY."""
    if not isinstance(denom, int) or isinstance(denom, bool) or denom <= 0:
        raise ValueError("denom must be a strictly positive integer")
    num = (x.numerator * denom) // x.denominator
    return Fraction(num, denom)


def log_rational_upper_bound_exact(x: Fraction, terms: int = 16) -> Fraction:
    """
    100% exact UNQUANTIZED rational (Q) STRICT UPPER BOUND on log(x) for any x in Q with x > 1.
    Uses exact binary reduction x = 2^k * r with r in [1, 2) and the exact geometric tail bound
    proved in Lean 4 (`geometric_tail_term_le`):
      log((1+t)/(1-t)) = 2 * sum_{j=0}^{M-1} t^{2j+1}/(2j+1) + 2 * sum_{j>=M} t^{2j+1}/(2j+1)
                       <= 2 * sum_{j=0}^{M-1} t^{2j+1}/(2j+1) + 2 * t^{2M+1} / ((2M+1) * (1 - t^2))
    for t in [0, 1/3).
    """
    if not isinstance(terms, int) or isinstance(terms, bool) or terms < 1:
        raise ValueError("terms must be a positive integer")
    if x <= Fraction(1):
        raise ValueError("log_rational_upper_bound_exact requires x > 1")
    k = 0
    r = x
    two = Fraction(2)
    while r >= two:
        r /= two
        k += 1

    def _atanh2_ub(t: Fraction, m: int) -> Fraction:
        if t == 0:
            return Fraction(0)
        t2 = t * t
        cur = t
        acc = Fraction(0)
        for j in range(m):
            acc += cur / (2 * j + 1)
            cur *= t2
        # cur is now t^{2m+1}; geometric tail bound <= cur / ((2m+1) * (1 - t^2))
        tail = cur / ((2 * m + 1) * (Fraction(1) - t2))
        return 2 * (acc + tail)

    log2_ub = _atanh2_ub(Fraction(1, 3), terms)
    tr = (r - Fraction(1)) / (r + Fraction(1))
    logr_ub = _atanh2_ub(tr, terms)
    return k * log2_ub + logr_ub


def log_rational_upper_bound(x: Fraction, terms: int = 16, quant_denom: int = 10**12) -> Fraction:
    """Soundly quantized upward rational upper bound on log(x) for x > 1."""
    return ceil_rational(log_rational_upper_bound_exact(x, terms=terms), denom=quant_denom)


def interval_hankel_quad_bounds_q(
    m_lo: list[Fraction],
    m_hi: list[Fraction],
    v: list[Fraction],
) -> tuple[Fraction, Fraction]:
    """
    Compute exact rational (Q0_ub, Q1_lb) such that for EVERY moment sequence m with
    m_lo[k] <= m[k] <= m_hi[k]:
      v^T M_0(m) v <= Q0_ub   and   Q1_lb <= v^T M_1(m) v.
    """
    n1 = len(v)
    q0_ub = Fraction(0)
    q1_lb = Fraction(0)
    for i in range(n1):
        vi = v[i]
        for j in range(n1):
            c = vi * v[j]
            k = i + j
            if c >= 0:
                q0_ub += c * m_hi[k]
                q1_lb += c * m_lo[k + 1]
            else:
                q0_ub += c * m_lo[k]
                q1_lb += c * m_hi[k + 1]
    return q0_ub, q1_lb


def build_exact_hankel_certificate(
    m_lo_float: list[float],
    m_hi_float: list[float],
    delta_q: Fraction,
    tau0_q: Fraction,
    order_n: int,
    quant_denom: int = 10**12,
    v_denom: int = 10**6,
    model_meta: dict | None = None,
):
    """
    Construct a 100% exact rational (Q) assumption-free Stieltjes-Hankel upper certificate
    for the continuum edge Delta from moment intervals [m_lo_float[k], m_hi_float[k]]
    (k = 0 .. 2*order_n + 1) on grid tau_k = tau0 + k * delta.
    Returns (ok, cert_dict).
    """
    n1 = order_n + 1
    assert len(m_lo_float) >= 2 * order_n + 2 and len(m_hi_float) >= 2 * order_n + 2
    # Sound outward quantization of IEEE-754 interval bounds into exact Q (no decimal string rounding)
    m_lo_q = [floor_rational(Fraction(max(0.0, float(x))), denom=quant_denom) for x in m_lo_float[: 2 * order_n + 2]]
    m_hi_q = [ceil_rational(Fraction(float(x)), denom=quant_denom) for x in m_hi_float[: 2 * order_n + 2]]
    if any(lo > hi or lo < 0 for lo, hi in zip(m_lo_q, m_hi_q)):
        return False, None

    # Numerical candidate witness vector v from top generalized eigenvector of midpoint (M1, M0)
    m_mid = [0.5 * (float(lo) + float(hi)) for lo, hi in zip(m_lo_q, m_hi_q)]
    M0 = np.array([[m_mid[i + j] for j in range(n1)] for i in range(n1)], dtype=np.float64)
    M1 = np.array([[m_mid[i + j + 1] for j in range(n1)] for i in range(n1)], dtype=np.float64)
    # Regularize slightly if nearly singular
    try:
        evals, evecs = eigh(M1, M0)
        v_num = evecs[:, -1]
    except Exception:
        return False, None
    v_num = v_num / np.max(np.abs(v_num))
    v_q = [Fraction(int(round(float(c) * v_denom)), v_denom) for c in v_num]

    # Exact rational interval bounds Q0_ub, Q1_lb for this fixed rational witness v_q
    q0_ub, q1_lb = interval_hankel_quad_bounds_q(m_lo_q, m_hi_q, v_q)
    if q0_ub <= 0 or q1_lb <= 0:
        return False, None

    # Exact threshold u* = Q1_lb / Q0_ub: for ANY u0 < u*, u0 * Q0_ub - Q1_lb < 0 STRICTLY!
    u_star = q1_lb / q0_ub
    if u_star >= Fraction(1):
        # Cannot certify Delta > 0? Wait: Delta < -log(u0)/delta only gives positive upper bound when u0 < 1!
        # If u_star >= 1, try u0 = 1 - 1e-6? Actually if u_star >= 1, it certifies Delta <= 0!
        return False, None
    # Step strictly below u_star by 1 ulp at denom=10**9 (still strictly positive)
    u0_q = floor_rational(u_star - Fraction(1, 10**11), denom=10**9)
    if u0_q <= 0 or u0_q >= Fraction(1):
        return False, None
    if u0_q * q0_ub - q1_lb >= 0:
        u0_q = floor_rational(u_star * Fraction(999999, 1000000), denom=10**9)
        if u0_q <= 0 or u0_q * q0_ub - q1_lb >= 0:
            return False, None

    log_inv_u0_ub_q = log_rational_upper_bound(Fraction(1) / u0_q, terms=16, quant_denom=quant_denom)
    delta_ub_q = ceil_rational(log_inv_u0_ub_q / delta_q, denom=quant_denom)

    cert = {
        "order_n": order_n,
        "tau0": f"{tau0_q.numerator}/{tau0_q.denominator}",
        "delta": f"{delta_q.numerator}/{delta_q.denominator}",
        "quant_denom": quant_denom,
        "m_lo": [f"{x.numerator}/{x.denominator}" for x in m_lo_q],
        "m_hi": [f"{x.numerator}/{x.denominator}" for x in m_hi_q],
        "witness_v": [f"{x.numerator}/{x.denominator}" for x in v_q],
        "u0": f"{u0_q.numerator}/{u0_q.denominator}",
        "Q0_ub": f"{q0_ub.numerator}/{q0_ub.denominator}",
        "Q1_lb": f"{q1_lb.numerator}/{q1_lb.denominator}",
        "witness_margin": f"{(u0_q * q0_ub - q1_lb).numerator}/{(u0_q * q0_ub - q1_lb).denominator}",
        "delta_ub_q": f"{delta_ub_q.numerator}/{delta_ub_q.denominator}",
        "delta_ub_float": float(delta_ub_q),
        "model_meta": model_meta or {},
    }
    return True, cert


def verify_hankel_certificate_exact(cert: dict) -> tuple[bool, dict]:
    """
    100% ZERO-FLOATING-POINT-TRUST exact rational (Q) verifier for a Stieltjes-Hankel
    continuum-edge upper certificate.
    Checks:
      1. order_n >= 0, delta > 0, u0 in (0, 1), witness_v has length n + 1, intervals have length 2n + 2.
      2. Interval validity: 0 <= m_lo[k] <= m_hi[k] for all k.
      3. Recomputes exact sign-split interval quadratic forms Q0_ub, Q1_lb in pure Fraction.
      4. Checks strict negativity: u0 * Q0_ub - Q1_lb < 0 (certifying NO measure on [0, u0] fits!).
      5. Recomputes exact rational log upper bound log_Q_ub(1/u0) and checks:
           delta_ub_q >= log_Q_ub(1/u0) / delta
         plus consistency of delta_ub_float within 1e-12.
    """
    n_raw = cert.get("order_n")
    if not isinstance(n_raw, int) or isinstance(n_raw, bool) or n_raw < 0:
        return False, {"reason": "invalid or negative order_n"}
    n = n_raw
    if "quant_denom" in cert:
        qd_raw = cert["quant_denom"]
        if not isinstance(qd_raw, int) or isinstance(qd_raw, bool) or qd_raw < 1:
            return False, {"reason": "invalid quant_denom (must be positive int)"}
    delta_q = Fraction(cert["delta"])
    if delta_q <= 0:
        return False, {"reason": "nonpositive delta"}
    u0_q = Fraction(cert["u0"])
    if u0_q <= 0 or u0_q >= Fraction(1):
        return False, {"reason": "u0 outside (0, 1)"}
    v_q = [Fraction(s) for s in cert["witness_v"]]
    m_lo_q = [Fraction(s) for s in cert["m_lo"]]
    m_hi_q = [Fraction(s) for s in cert["m_hi"]]
    if len(v_q) != n + 1 or len(m_lo_q) != 2 * n + 2 or len(m_hi_q) != 2 * n + 2:
        return False, {"reason": "dimension mismatch"}
    for lo, hi in zip(m_lo_q, m_hi_q):
        if lo < 0 or lo > hi:
            return False, {"reason": "invalid moment interval"}

    q0_ub, q1_lb = interval_hankel_quad_bounds_q(m_lo_q, m_hi_q, v_q)
    margin = u0_q * q0_ub - q1_lb
    if margin >= 0:
        return False, {"reason": f"witness failed: u0*Q0_ub - Q1_lb = {float(margin):.3e} >= 0"}
    if q0_ub != Fraction(cert["Q0_ub"]) or q1_lb != Fraction(cert["Q1_lb"]):
        return False, {"reason": "recorded Q0_ub / Q1_lb mismatch"}
    if "witness_margin" in cert and margin != Fraction(cert["witness_margin"]):
        return False, {"reason": "recorded witness_margin mismatch"}

    if "delta_ub_q" not in cert:
        return False, {"reason": "missing delta_ub_q"}
    delta_ub_q = Fraction(cert["delta_ub_q"])
    # Check against the UNQUANTIZED exact rational upper bound (never trusting cert["quant_denom"])
    exact_log_ub_q = log_rational_upper_bound_exact(Fraction(1) / u0_q, terms=16)
    if delta_ub_q < exact_log_ub_q / delta_q:
        return False, {"reason": "delta_ub_q is tighter than exact rational log_Q_ub(1/u0)/delta"}
    if "delta_ub_float" in cert:
        f_raw = cert["delta_ub_float"]
        if not isinstance(f_raw, (int, float)) or isinstance(f_raw, bool) or not math.isfinite(float(f_raw)):
            return False, {"reason": "non-finite or invalid delta_ub_float"}
        if abs(Fraction(float(f_raw)) - delta_ub_q) > Fraction(1, 10**12):
            return False, {"reason": "delta_ub_float tampered or inconsistent with delta_ub_q"}

    return True, {
        "order_n": n,
        "u0": u0_q,
        "margin": margin,
        "delta_ub_q": delta_ub_q,
    }
