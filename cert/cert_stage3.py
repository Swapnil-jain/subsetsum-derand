"""Exact-rational certificate for Stage 3 (PROOF.md). Pure standard library, one core, < 20 MB, < 1 min.

Stage 3 = Stage 2 (derand/stage2, refereed) with two independently refereed changes:
  * the outside-sum dedupe (PROOF.md Sec. 3): no few-sums branch, no gamma; Step 6 costs 2^{n/2 - xi' m + 2 eps m};
  * the re-tuned Ye-Li Sec. 3.5 circuit (PROOF.md Sec. 2): lookup sets of size q = ceil(r u), a0 zeros and a1 ones
    outside D, at (a0, a1, 1-b, r) = (1/1842, 1/1474, 1/83, 29/17). This gives a pair (dL, dR) with
    dL + dR = 1/2 - 2 xi, xi >= 3.63145e-5, from a MODIFIED proof of Ye-Li Prop. 4.2 (not Prop. 4.2 as stated).

No floating point enters any asserted inequality. Irrational quantities are enclosed outward:
  * natural logs of positive rationals by the atanh series with an explicit tail, rounded outward at 2^-220;
  * log2(3) < 317/200 by the integer comparison 3^200 < 2^317.
The tangent points of the Gibbs majorants and the crossing points t1, t2 are fixed rational DATA below. Their
choice is heuristic (a float search found them, `--search` re-runs that search); every choice gives a valid bound.

What is certified (labels as in PROOF.md):
  [P]  the parameter conditions of the generalised Sec. 3.5: 0 < a0, a1 <= 1/4; 0 <= 1-b-a0-a1 <= 1/2; r >= 1;
       r (a0+a1) <= 1-b; and (a0+a1)/(1-b) <= 1/2 (used by [Apos]).
  [U]  for i = 1, 2, 3 and tau in {t1, t2}: g_i(tau; mu, theta) <= c(tau) on the whole colour polygon
       Poly = {a1 <= mu <= a1+a0, mu <= theta <= r mu}, with c(t1) = t1 and c(t2) = (1-t2)/2. Method: Gibbs'
       inequality h(n,k) <= k (-log2 p) + (n-k)(-log2(1-p)) for any p in (0,1), applied with a rational p at a
       tangent point, makes g_i an affine function of (mu, theta) (k, n-k >= 0 on Poly), whose max is at a vertex.
  [Apos] A(mu) = h(1-b, mu) - r mu H(1/r) > 0 on [a1, a1+a0]. The second left term's true exponent is max(A, 0)
       (its count |Q| is >= 1), so [U] for g_2 bounds it only because A > 0.
  [L]  the line through (t1, t1) and (t2, (1-t2)/2) has slope in (-1/2, 1), dL = line(1) >= 0, dR = line(0) >= 0;
       hence min{V, tau, (1-tau)/2} <= line on [0, 1] (V is a max of functions affine in tau), and
       xi_cert = 1/4 - line(1/2).
  [F1] must-fail for xi: rigorous LOWER bounds give V(s1) > s1 and V(s2) > (1-s2)/2 just outside the crossings, so
       no line valid for this V has xi > xi_max, and xi_max < xi_cert (1 + 1e-4).
  [S3] Stage 3 at the re-tuned pair: the rational pair (dL', dR') is the 12-place round-up of (dL, dR);
       xi' = (1/2 - dL' - dR')/2 <= xi_cert; Lemma 3.5's conditions; the fit (Lemma 3.3 of PROOF.md) with its n0;
       every cost term of Theorem 3 is <= E3. Cor. 3.2's block length kappa from both of its conditions, and N'.
  [FA] fallback without the re-tune (Ye-Li Prop. 4.2 as in Stage 2; table pair as upper bounds):
       xi' = 2.0035e-5, E <= 0.499994991801.   [FB] statement only, xi' = 2e-5: E <= 0.4999950006.
Must-fail controls (each must be REJECTED by the same checker):
  [K1] E3 claim 1e-12 below the certified bound;   [K2] pi = 0.2501 (blocks do not fit);   [K3] pi = 1/3;
  [K4] xi' = 0;   [K5] eps = 1e-6;   [K6] one-sided dedupe (left only) at N = 1;   [K7] pi one grid step above;
  [K8] the pair rounded below (dL, dR);   [K9] xi' = xi_cert + 1e-12 with the rounded pair;
  [K10] the re-tuned xi' with Ye-Li's table pair;   [K11] the fallback claim 1e-12 lower;
  [C1] [U] for g_3 at t1 - 1e-8;   [C2] [U] for g_3 at t2 + 1e-6;   [C3] r(a0+a1) > 1-b;   [C4] r < 1;
  [C5] kappa_0 - 2 fails Cor. 3.2's second condition.
Run: nice -n 15 python3 -I cert_stage3.py          Exit 0 iff every claim holds and every control is rejected.
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
import sys

# ---------------------------------------------------------------- rigorous logs of positive rationals
PREC = 2 ** 220


def rdn(x):
    return F((x.numerator * PREC) // x.denominator, PREC)


def rup(x):
    return -rdn(-x)


def atanh_enc(z, terms=60):
    """Enclosure of atanh(z) = sum z^{2j+1}/(2j+1), |z| <= 1/5; tail <= |z|^{2N+1} / ((2N+1)(1-z^2))."""
    assert abs(z) <= F(1, 5)
    p, z2 = z, z * z
    lo = hi = F(0)
    for j in range(terms):
        t = p / (2 * j + 1)
        lo += rdn(t)
        hi += rup(t)
        p *= z2
        p = rdn(p) if p >= 0 else rup(p)
    tail = F(abs(z.numerator) ** (2 * terms + 1), z.denominator ** (2 * terms + 1)) / ((2 * terms + 1) * (1 - z2))
    slack = F(terms * terms, PREC)          # rounding p at each step moves term j by at most j / PREC
    return lo - tail - slack, hi + tail + slack


def ln_small(y):
    """ln y for y in [2/3, 3/2], as 2 atanh((y-1)/(y+1)), |(y-1)/(y+1)| <= 1/5."""
    lo, hi = atanh_enc((y - 1) / (y + 1))
    return 2 * lo, 2 * hi


_a, _b = ln_small(F(4, 3)), ln_small(F(3, 2))
LN2 = (_a[0] + _b[0], _a[1] + _b[1])          # ln 2 = ln(4/3) + ln(3/2)
assert F(6931, 10000) < LN2[0] < LN2[1] < F(6932, 10000)


def ln_enc(x):
    x = F(x)
    assert x > 0
    k = 0
    while x > F(3, 2):
        x /= 2
        k += 1
    while x < F(2, 3):
        x *= 2
        k -= 1
    lo, hi = ln_small(x)
    return (lo + k * LN2[0], hi + k * LN2[1]) if k >= 0 else (lo + k * LN2[1], hi + k * LN2[0])


def lg_enc(x):
    lo, hi = ln_enc(x)
    c = [lo / LN2[0], lo / LN2[1], hi / LN2[0], hi / LN2[1]]
    return min(c), max(c)


def xlg(x):
    """Enclosure of x log2 x for rational x >= 0 (0 at 0)."""
    x = F(x)
    if x == 0:
        return F(0), F(0)
    lo, hi = lg_enc(x)
    return (x * lo, x * hi) if x > 0 else (x * hi, x * lo)


def hh_enc(n, k):
    """Enclosure of h(n, k) = n lg n - k lg k - (n-k) lg(n-k) = n H(k/n), for rationals 0 <= k <= n."""
    A, B, C = xlg(F(n)), xlg(F(k)), xlg(F(n) - F(k))
    return A[0] - B[1] - C[1], A[1] - B[0] - C[0]


def up(x, k):
    """Round x up to k decimal places."""
    s = 10 ** k
    return F(-((-x.numerator * s) // x.denominator), s)


def dn(x, k):
    s = 10 ** k
    return F((x.numerator * s) // x.denominator, s)


def dec(x, places=12, upward=True):
    q = up(x, places) if upward else dn(x, places)
    s = 10 ** places
    v = q.numerator * (s // q.denominator)
    sg = "-" if v < 0 else ""
    v = abs(v)
    return f"{sg}{v // s}.{v % s:0{places}d}"


# ---------------------------------------------------------------- the generalised Sec. 3.5 circuit
A0, A1, OMB, R = F(1, 1842), F(1, 1474), F(1, 83), F(29, 17)     # (a0, a1, 1 - b, r)
SLACK = F(1, 10 ** 22)                                           # added to every log-derived rational below
DIG = 24                                                         # decimal places of those rationals


def params_ok(a0, a1, omb, r):
    return (0 < a0 <= F(1, 4) and 0 < a1 <= F(1, 4) and 0 <= omb - a0 - a1 <= F(1, 2) and r >= 1
            and r * (a0 + a1) <= omb and 0 < omb < 1 and (a0 + a1) / omb <= F(1, 2))


def E1_enc():
    """E1 = H(b) - h(1/4, a0) - h(1/4, a1) - h(1/2, 1-b-a0-a1)."""
    hb = hh_enc(1, 1 - OMB)
    t = [hh_enc(F(1, 4), A0), hh_enc(F(1, 4), A1), hh_enc(F(1, 2), OMB - A0 - A1)]
    return hb[0] - sum(x[1] for x in t), hb[1] - sum(x[0] for x in t)


E0 = F(1, 2) - OMB + A0 + A1                     # b - 1/2 + a0 + a1: the stars of D, per n
_e1, _hr = E1_enc(), hh_enc(1, 1 / R)
E1U, E1L = up(_e1[1], DIG) + SLACK, dn(_e1[0], DIG) - SLACK     # E1L <= E1 <= E1U
HRL, HRU = dn(_hr[0], DIG) - SLACK, up(_hr[1], DIG) + SLACK     # HRL <= H(1/r) <= HRU

# Crossing points: t1 >= the float crossing of V with tau, t2 <= that of V with (1 - tau)/2.
T1 = F(33113713552533, 10 ** 14)
T2 = F(5018822029108, 10 ** 13)
# Tangent points (mu, theta) per (i, tau). The g_1 and g_2 bounds have margins near 1e-3 and need no care.
PTS = {
    (1, "t1"): (F("0.00101498245"), F("0.00101498245")),
    (2, "t1"): (F("0.00108194823"), F("0.00108194823")),
    (3, "t1"): (F("0.0010693185104"), F("0.0013508800076")),
    (1, "t2"): (F("0.00101498245"), F("0.00101498245")),
    (2, "t2"): (F("0.00113074077"), F("0.00113074077")),
    (3, "t2"): (F("0.0011147150341"), F("0.0013442486464")),
}
# [F1] points just outside the crossings, and the colour (mu, theta) that witnesses V there.
S1 = F(33113713442532, 10 ** 14)                 # about t1* - 1e-9
S2 = F(5018822729109, 10 ** 13)                  # about t2* + 2e-8
F1PTS = {"s1": (F("0.0010693185101"), F("0.0013508800076")), "s2": (F("0.0011147150559"), F("0.0013442486441"))}


def ent_terms(i):
    """Entropy terms of g_i as (side, n_aff, k_aff), affine maps (c_mu, c_theta, c_1); side 'L' has weight tau,
    side 'R' weight 1 - tau. And the exact affine part of each side, with E1 <= E1U and -H(1/r) <= -HRL."""
    ent = [("R", (F(0), F(0), A0), (F(1), F(0), -A1))]                    # h(a0, mu - a1)
    lin = {"L": [F(0), F(0), F(0)], "R": [F(0), F(0), E0]}
    if i == 3:
        ent.append(("R", (R - 1, F(0), F(0)), (F(-1), F(1), F(0))))       # h((r-1) mu, theta - mu)
        ent.append(("L", (R, F(0), F(0)), (F(0), F(1), F(0))))            # h(r mu, theta)
        lin["L"][0] -= R                                                   # - r mu
    else:
        lin["R"][0] += R - 1                                               # h((r-1)mu, .) <= (r-1) mu
    if i in (2, 3):
        ent.append(("L", (F(0), F(0), OMB), (F(1), F(0), F(0))))          # h(1-b, mu)
        lin["L"][0] -= R * HRL                                             # - r mu H(1/r) <= - r mu HRL
    if i in (1, 3):
        lin["L"][2] += E1U
    return ent, lin


def aff(c, m, t):
    return c[0] * m + c[1] * t + c[2]


def vertices(a0=A0, a1=A1, r=R):
    return [(a1, a1), (a1, r * a1), (a1 + a0, a1 + a0), (a1 + a0, r * (a1 + a0))]


def ent_coeffs(p):
    """cp >= -log2 p and cq >= -log2(1-p), rationals with DIG places (+ SLACK)."""
    return up(-lg_enc(p)[0], DIG) + SLACK, up(-lg_enc(1 - p)[0], DIG) + SLACK


def majorant(i, tau, pt):
    """The affine majorant M(mu, theta) = A mu + B theta + C of g_i(tau; .) on Poly, and its entropy data
    [(side, n_aff, k_aff, p, cp, cq)]. p = k/n at the tangent point, rounded to 12 places."""
    tau = F(tau)
    ent, lin = ent_terms(i)
    w = {"L": tau, "R": 1 - tau}
    M = [F(0), F(0), F(0)]
    for s, c in lin.items():
        for j in range(3):
            M[j] += w[s] * c[j]
    data = []
    for s, n, k in ent:
        nv, kv = aff(n, *pt), aff(k, *pt)
        p = min(max(dn(kv / nv, 12), F(1, 10 ** 12)), 1 - F(1, 10 ** 12))
        cp, cq = ent_coeffs(p)
        for j in range(3):
            M[j] += w[s] * (k[j] * cp + (n[j] - k[j]) * cq)
        data.append((s, n, k, p, cp, cq))
    for (vm, vt) in vertices():                  # k >= 0 and n - k >= 0 at every vertex, hence on Poly
        for s, n, k in ent:
            assert aff(k, vm, vt) >= 0 and aff(n, vm, vt) - aff(k, vm, vt) >= 0
    return M, data


def vmax(M):
    return max(aff(M, vm, vt) for vm, vt in vertices())


def U_bound(i, tau, key):
    M, _ = majorant(i, tau, PTS[(i, key)])
    return vmax(M)


def g3_lower(tau, pt):
    """Rigorous LOWER bound on g_3(tau; m, t) with the true right term h((r-1)m, t-m), at a rational point."""
    tau = F(tau)
    m, t = pt
    assert A1 <= m <= A1 + A0 and m <= t <= R * m
    L = E1L + hh_enc(OMB, m)[0] - R * m * HRU + hh_enc(R * m, t)[0] - R * m
    Rt = E0 + hh_enc(A0, m - A1)[0] + hh_enc((R - 1) * m, t - m)[0]
    return tau * L + (1 - tau) * Rt


# ---------------------------------------------------------------- Stage 3 exponent (PROOF.md Theorem 3)
assert 3 ** 200 < 2 ** 317
LOG2_3_UP = F(317, 200)
E20 = F(1, 10 ** 20)
DL_T = F("0.00727587055962990941")   # Ye-Li v1 Sec. 4 table, 20-place truncations (fallback only)
DR_T = F("0.49268405898808998771")
XI_T = F("0.00002003522614005143")
DL_YL = F("0.007275870560")          # Stage 2's rational pair, just above the table (fallback only)
DR_YL = F("0.492684058989")


def terms(pi, xi, eps, one_sided=False):
    t = {
        "T_blocks": pi,                                   # 4 * 2^m block sums, sorted and deduped
        "T_cover": 2 * pi,                                # prime scan, layer sets, greedy coverings
        "T_hist": LOG2_3_UP * pi,                         # right prefix histogram over 3^m vectors
        "T_outside": 1 - 3 * pi,                          # Sigma(B1 \\ Qa), Sigma(B2 \\ Qc): <= n - 3m coordinates
        "T_left1": F(3, 2) * pi,                          # half of P x Sigma(Qa)
        "T_left2": pi / 2 + 1 - 3 * pi,                   # half of P x Sigma(B1 \\ Qa)
        "T_right1": LOG2_3_UP * pi / 2 + 1 - 3 * pi,      # ternary half of P x Sigma(B2 \\ Qc)
        "T_right2": LOG2_3_UP * pi / 2 + pi,              # ternary half of P x Sigma(Qc)
        "T_many": F(1, 2) - xi * pi + 2 * eps * pi,       # Step 6: poly 2^{X_j - m}
    }
    if one_sided:                                         # right list raw: weight 2^{X_j}, filter 1/N with N = 1
        t["T_many_right_raw"] = F(1, 2) + (1 - xi) * pi + 2 * eps * pi
    return t


def side_ok(pi, xi, dl, dr, dl_lo, dr_lo, xi_cap):
    """PROOF.md Lemma 3.5's hypotheses for the rational pair, and the fit of Lemma 3.3."""
    if not (0 <= xi <= xi_cap):
        return False
    if not (dl >= dl_lo and dr >= dr_lo and dl >= 0 and dr >= 0 and dl + dr <= F(1, 2) - 2 * xi):
        return False
    if not (0 < pi <= F(1, 3) and 4 * pi < 1):
        return False
    g = dr - dl
    if not (g < F(1, 2)):
        return False
    f0, fh = 2 * g, F(3, 2) + g                          # f(0) and f(1/2) of Lemma 3.3
    return (4 - f0) * pi < 1 and (2 + fh) * pi < 1


def check(pi, xi, eps, claim, dl, dr, dl_lo, dr_lo, xi_cap, one_sided=False, verbose=False):
    if not side_ok(pi, xi, dl, dr, dl_lo, dr_lo, xi_cap):
        return False, None
    t = terms(pi, xi, eps, one_sided)
    E = max(t.values())
    if verbose:
        for k, v in t.items():
            print(f"      {k:16s} <= {dec(v)}")
        print(f"      max E <= {dec(E)} ({max(t, key=t.get)}); gain 1/2 - E >= {dec(F(1, 2) - E, upward=False)}")
    return E <= claim, E


def best_pi(xi, eps, grid=10 ** 8):
    """Largest grid pi with 2 pi <= T_many, i.e. pi <= (1/2)/(2 + xi - 2 eps)."""
    star = F(1, 2) / (2 + xi - 2 * eps)
    return dn(star, 8) if grid == 10 ** 8 else F((star.numerator * grid) // star.denominator, grid), star


def fit_n0(pi, dl, dr):
    """Least n0 with (4 - f(0)) pi n <= n - 2 and (2 + f(1/2)) pi n <= n - 2 for every n >= n0 (then
    m <= l_j <= n - 2m in every layer, for every rounding |l_j - l*_j| <= 1); and the last n that fails these
    sufficient conditions at the algorithm's m = 2 floor(pi n / 2)."""
    g = dr - dl
    cs = [4 - 2 * g, F(7, 2) + g]
    n0 = 0
    for c in cs:
        q = F(2) / (1 - c * pi)
        n0 = max(n0, -((-q.numerator) // q.denominator))
    for c in cs:                                          # n >= n0 really suffices
        assert c * pi * n0 <= n0 - 2
    last = 0
    for n in range(1, n0 + 1):
        m = 2 * ((pi * n).numerator // (2 * (pi * n).denominator))
        if any(c * m > n - 2 for c in cs):
            last = n
    return n0, last


def kappa(dl, dr, eps):
    """Cor. 3.2's least even block length for the pair, from both conditions (the second by bisection)."""
    getcontext().prec = 60
    k1 = 8 * (max(dl, dr) + eps / 4) / eps
    ln2 = Decimal(2).ln()
    e4 = Decimal(eps.numerator) / Decimal(eps.denominator) / 4

    def cond2(k):
        return (Decimal(k + 1).ln() / ln2) / Decimal(k) <= e4
    lo, hi = 10 ** 6, 10 ** 15
    assert cond2(hi) and not cond2(lo)
    while lo < hi:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if cond2(mid) else (mid + 1, hi)
    k2 = lo + (lo % 2)
    kmin = max(-((-k1.numerator) // k1.denominator), k2)
    kmin += kmin % 2
    return k1, k2, kmin, cond2


# ---------------------------------------------------------------- main
def retune():
    """[P], [U], [Apos], [L], [F1]. Returns (ok, dL, dR, xi_cert, xi_max)."""
    ok = True
    pc = params_ok(A0, A1, OMB, R)
    print(f"[P] (a0, a1, 1-b, r) = ({A0}, {A1}, {OMB}, {R}): {'PASS' if pc else 'FAIL'}")
    ok &= pc
    print(f"    E1 in [{dec(E1L, 15, False)}, {dec(E1U, 15)}], H(1/r) in [{dec(HRL, 15, False)}, {dec(HRU, 15)}]")
    for key, tau, c in (("t1", T1, T1), ("t2", T2, (1 - T2) / 2)):
        for i in (1, 2, 3):
            u = U_bound(i, tau, key)
            r = u <= c
            print(f"[U] g_{i}({key}) <= {dec(u, 14)} <= c = {dec(c, 14, False)}: {'PASS' if r else 'FAIL'}"
                  f" (margin {float(c - u):.2e})")
            ok &= r
    lo_h = hh_enc(1, A1 / OMB)[0]
    apos = OMB * lo_h - R * (A0 + A1) * HRU
    print(f"[Apos] A(mu) >= (1-b) H(a1/(1-b)) - r (a0+a1) H(1/r) >= {dec(apos, 12, False)} > 0 on [a1, a1+a0]:"
          f" {'PASS' if apos > 0 else 'FAIL'}")
    ok &= apos > 0
    slope = ((1 - T2) / 2 - T1) / (T2 - T1)
    line = lambda tau: T1 + (tau - T1) * slope
    dL, dR = line(1), line(0)
    c3 = 0 < T1 < F(1, 3) < F(1, 2) < T2 < 1 and F(-1, 2) < slope < 1 and dL >= 0 and dR >= 0
    xi = F(1, 4) - line(F(1, 2))
    assert xi == F(1, 4) - (dL + dR) / 2
    print(f"[L] slope {dec(slope, 9, False)} in (-1/2, 1); dL = line(1) = {dec(dL, 15)}, dR = line(0) = {dec(dR, 15)}:"
          f" {'PASS' if c3 else 'FAIL'}")
    print(f"    xi_cert = 1/4 - line(1/2) = {dec(xi, 15, False)}")
    ok &= c3
    l1, l2 = g3_lower(S1, F1PTS["s1"]), g3_lower(S2, F1PTS["s2"])
    f1 = l1 > S1 and l2 > (1 - S2) / 2 and S1 < F(1, 3) < F(1, 2) < S2
    z1, z2 = S1, (1 - S2) / 2
    xi_max = F(1, 4) - (z1 + (F(1, 2) - S1) * (z2 - z1) / (S2 - S1))
    print(f"[F1] V(s1) >= {dec(l1, 14, False)} > s1 = {dec(S1, 14)}; V(s2) >= {dec(l2, 14, False)} > (1-s2)/2 ="
          f" {dec(z2, 14)}: {'PASS' if f1 else 'FAIL'}")
    tight = xi <= xi_max < xi * (1 + F(1, 10 ** 4))
    print(f"[F1] no valid line has xi > xi_max = {dec(xi_max, 15)}; xi_cert <= xi_max < xi_cert (1 + 1e-4):"
          f" {'PASS' if tight else 'FAIL'}")
    ok &= f1 and tight
    return ok, dL, dR, xi, xi_max


def main():
    if "--search" in sys.argv:
        return search()
    ok = True
    eps = F(1, 10 ** 9)
    print("== The re-tuned Sec. 3.5 circuit")
    r, dL, dR, xi_cert, xi_max = retune()
    ok &= r

    print("== [S3] Stage 3 at the re-tuned pair")
    dLp, dRp = up(dL, 12), up(dR, 12)
    xi3 = (F(1, 2) - dLp - dRp) / 2
    pi3, star3 = best_pi(xi3, eps)
    print(f"    pair (dL', dR') = ({dec(dLp)}, {dec(dRp)}); xi' = (1/2 - dL' - dR')/2 = {dec(xi3, 13, False)}"
          f" <= xi_cert: {xi3 <= xi_cert}")
    print(f"    pi* = (1/2)/(2 + xi' - 2 eps) = {dec(star3, 13)}; grid pi = {dec(pi3, 8)}")
    r, E3 = check(pi3, xi3, eps, F(1, 2), dLp, dRp, dL, dR, xi_cert, verbose=True)
    E3c = up(E3, 12)
    r = r and E3 <= E3c and xi3 <= xi_cert
    print(f"    THEOREM 3: E3 <= {dec(E3c)}  (exact max {E3}); 2 pi* = {dec(2 * star3, 13, False)}"
          f": {'PASS' if r else 'FAIL'}")
    print(f"    closed form xi'/(4 + 2 xi') = {dec(xi3 / (4 + 2 * xi3), 13, False)}; gain 1/2 - E3 >="
          f" {dec(F(1, 2) - E3c, 12, False)}")
    ok &= r
    n0, last = fit_n0(pi3, dLp, dRp)
    print(f"    fit (Lemma 3.3): the sufficient condition holds for every n >= {last + 1} (exhaustively below"
          f" {n0}, by the closed form from {n0} on); it fails at n = {last}")
    lem35 = dLp >= dL and dRp >= dR and 0 <= dRp <= dLp + dRp <= F(1, 2) and dLp >= 0 and pi3 <= F(1, 3)
    print(f"    Lemma 3.5 hypotheses (dL' >= dL, dR' >= dR, 0 <= dL', dR', dL'+dR' <= 1/2 - 2xi', pi <= 1/3):"
          f" {'PASS' if lem35 else 'FAIL'}")
    ok &= lem35
    k1, k2, kmin, cond2 = kappa(dLp, dRp, eps)
    Np = kmin * kmin + 2 * kmin
    kk = cond2(kmin) and not cond2(kmin - 2) and kmin >= k1 and k2 > k1 and kmin % 2 == 0
    print(f"    Cor. 3.2 at (dL', dR'): condition (1) kappa >= {float(k1):.5e}; condition (2) kappa >= {k2:.5e}"
          f" (binds); kappa_0 = {kmin}; N' = {Np}: {'PASS' if kk else 'FAIL'}")
    ok &= kk and kmin == 148444531984

    print("== [FA] fallback: Ye-Li Prop. 4.2 as in Stage 2 (table pair as upper bounds), xi' = 2.0035e-5")
    xiA = F(20035, 10 ** 9)
    piA, starA = best_pi(xiA, eps)
    claimA = F("0.499994991801")
    rA, EA = check(piA, xiA, eps, claimA, DL_YL, DR_YL, DL_T + E20, DR_T + E20, XI_T, verbose=True)
    nA, lastA = fit_n0(piA, DL_YL, DR_YL)
    print(f"    grid pi = {dec(piA, 8)}; E <= {dec(claimA)}: {'PASS' if rA else 'FAIL'}; the fit holds for every"
          f" n >= {lastA + 1} (closed form from {nA} on)")
    ok &= rA
    print("== [FB] fallback, statement only (xi > 2e-5), xi' = 2e-5")
    xiB = F(2, 10 ** 5)
    piB, _ = best_pi(xiB, eps)
    rB, EB = check(piB, xiB, eps, F("0.4999950006"), DL_YL, DR_YL, DL_T + E20, DR_T + E20, xiB)
    print(f"    grid pi = {dec(piB, 8)}; E <= {dec(EB)} <= 0.4999950006: {'PASS' if rB else 'FAIL'}")
    ok &= rB

    print("== must-fail controls")
    S3 = dict(dl=dLp, dr=dRp, dl_lo=dL, dr_lo=dR, xi_cap=xi_cert)
    FAk = dict(dl=DL_YL, dr=DR_YL, dl_lo=DL_T + E20, dr_lo=DR_T + E20, xi_cap=XI_T)
    controls = [
        ("K1 E3 claim 1e-12 lower", lambda: check(pi3, xi3, eps, E3c - F(1, 10 ** 12), **S3)[0]),
        ("K2 pi = 0.2501", lambda: check(F(2501, 10 ** 4), xi3, eps, F(1, 2), **S3)[0]),
        ("K3 pi = 1/3", lambda: check(F(1, 3), xi3, eps, F(1, 2), **S3)[0]),
        ("K4 xi' = 0", lambda: check(pi3, F(0), eps, E3c, **S3)[0]),
        ("K5 eps = 1e-6", lambda: check(pi3, xi3, F(1, 10 ** 6), E3c, **S3)[0]),
        ("K6 one-sided dedupe at N = 1", lambda: check(pi3, xi3, eps, F(1, 2), one_sided=True, **S3)[0]),
        ("K7 pi one grid step above", lambda: check(pi3 + F(1, 10 ** 8), xi3, eps, E3c, **S3)[0]),
        ("K8 pair rounded below (dL, dR)", lambda: check(pi3, xi3, eps, E3c, dLp - F(2, 10 ** 12), dRp, dL, dR,
                                                         xi_cert)[0]),
        ("K9 xi' = xi_cert + 1e-12", lambda: check(pi3, xi_cert + F(1, 10 ** 12), eps, E3c, dLp, dRp, dL, dR,
                                                   F(1))[0]),
        ("K10 re-tuned xi' with Ye-Li's pair", lambda: check(pi3, xi3, eps, E3c, DL_YL, DR_YL, DL_T + E20,
                                                             DR_T + E20, F(1))[0]),
        ("K11 fallback claim 1e-12 lower", lambda: check(piA, xiA, eps, claimA - F(1, 10 ** 12), **FAk)[0]),
        ("C1 [U] g_3 at t1 - 1e-8", lambda: majorant_ok(3, T1 - F(1, 10 ** 8), "t1", lambda t: t)),
        ("C2 [U] g_3 at t2 + 1e-6", lambda: majorant_ok(3, T2 + F(1, 10 ** 6), "t2", lambda t: (1 - t) / 2)),
        ("C3 r(a0+a1) > 1-b", lambda: params_ok(A0, A1, F(1, 600), R)),
        ("C4 r < 1", lambda: params_ok(A0, A1, OMB, F(99, 100))),
        ("C5 kappa_0 - 2 meets condition (2)", lambda: cond2(kmin - 2)),
    ]
    for name, fn in controls:
        res = fn()
        print(f"    [{name}]: {'accepted (CONTROL FAILED)' if res else 'rejected (ok)'}")
        ok &= not res
    print("CERTIFICATE PASS" if ok else "CERTIFICATE FAIL")
    return 0 if ok else 1


def majorant_ok(i, tau, key, c):
    M, _ = majorant(i, tau, PTS[(i, key)])
    return vmax(M) <= c(tau)


# ---------------------------------------------------------------- optional: the float search behind the DATA
def search():
    """Heuristic only. Float model of g_i; tangent points by bisection on derivative signs (g_i is concave in
    (mu, theta)); crossings t1, t2 by bisection. Prints values to compare with T1, T2, PTS."""
    import math
    lg = lambda x: math.log2(x) if x > 0 else 0.0
    hf = lambda n, k: (n * lg(n) if n > 0 else 0) - (k * lg(k) if k > 0 else 0) - ((n - k) * lg(n - k) if n > k else 0)
    a0, a1, omb, r = (float(x) for x in (A0, A1, OMB, R))
    b = 1 - omb
    E1 = hf(1, b) - hf(.25, a0) - hf(.25, a1) - hf(.5, omb - a0 - a1)
    e0, Hr = float(E0), hf(1, 1 / r)

    def g3(tau, m, t):
        return (tau * (E1 + hf(omb, m) - r * m * Hr + hf(r * m, t) - r * m)
                + (1 - tau) * (e0 + hf(a0, m - a1) + hf((r - 1) * m, t - m)))

    def argmax(f, lo, hi, it=100):
        for _ in range(it):
            c, d = lo + (hi - lo) / 3, hi - (hi - lo) / 3
            lo, hi = (lo, d) if f(c) > f(d) else (c, hi)
        return (lo + hi) / 2

    def V3(tau):
        best = lambda m: g3(tau, m, argmax(lambda t: g3(tau, m, t), m, r * m))
        m = argmax(best, a1, a1 + a0)
        return best(m), m, argmax(lambda t: g3(tau, m, t), m, r * m)

    def root(f, lo, hi):
        for _ in range(60):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if (f(mid) > 0) == (f(lo) > 0) else (lo, mid)
        return (lo + hi) / 2
    t1 = root(lambda t: V3(t)[0] - t, .3, 1 / 3)
    t2 = root(lambda t: V3(t)[0] - (1 - t) / 2, .5, .6)
    print("float crossings", t1, t2, "data", float(T1), float(T2))
    for tau in (float(T1), float(T2), float(S1), float(S2)):
        print("g_3 tangent at", tau, V3(tau)[1:])
    return 0


if __name__ == "__main__":
    sys.exit(main())
