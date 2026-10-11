"""Certificate for proofs/stage2b-explicit.md Sec. 13 ("Smaller n0"): leads B17 (Lemma 3.1') and A19 (ladder), and the small-q + POS
variant. Exact rationals only (fractions.Fraction). Its inequalities are kernel-checked in Lean
(lean/SubsetsumLean/ExplicitAnchors.lean and ExplicitN0.lean; [G]'s enumeration and K3 stay here). Reuses cert_explicit.py (must exit 0) for
the enclosures of ln 2, ln x and H, the window loss eps_win, the flip count J and Ye-Li's anchors at their own
(a, b); reuses cert_eps.py, Stage 2's certificate (must import), for S2's cost terms at design [A']. Both are
loaded from this script's own directory, so the script runs where it sits.

Parts.
[G]  Lemma 3.1' (halving splitter with the canonical-member rule):
     - exhaustive: every half-set S of [n] gets, from the canonical member, exactly half of every leaf specified,
       for leaf sizes (4,4,4), (4,4,4,4), (6,4,2,2), (8,4,2) (and n = 16 means all 12870 half-sets);
     - the family-size bound: prod over internal nodes of u <= 2^{(9/4)(D-1)} G^{D-1} / D, checked as the integer
       inequality (D * prod m_v)^4 <= 2^{9(D-1)} for D <= 400 (the induction in Sec. 13 proves it for all D).
[V]  Certified anchors V(0), V(1/2), V(1) at any rational (a, b) by concavity (Sec. 13.4): V(tau) maximises a
     jointly concave f over the polygon K = {a <= mu <= 2a, mu <= theta <= 2mu}, so
     max_K f <= f(x0) + max over the 4 vertices v of grad f(x0) . (v - x0), with every log enclosed. Each anchor is
     rounded up to the grid 10^-18, and x0 at tau = 1/2 is a float Newton point rounded to the grid a * 10^-15, so
     every number downstream is a short rational (the Lean check reads the same numbers). Validated at Ye-Li's
     (a, b): each bound is >= the table value (which is <= the true value) and within 2e-17 of it.
     Then at D4 (a = 1/2635, 1-b = 1/110, q = 115940) and at q = 2664 (a = 1/2664, 1-b = 1/111): Ye-Li's parameter
     conditions, both Sec. 3.5 dominance inequalities, Lemma E6's H(b) <= 1/10 and 1-b <= 1/100, the hull pair
     (dL'', dR'') rounded up to 12 places, and xi'' := (1/2 - dL'' - dR'')/2.
[A'] B17 at Ye-Li's (a, b), N0 = q = 10^26, E3 hole fixing: every Stage 2 and explicit condition of Certificate
     [A] re-checked at N0 = q, with eps_L = eps_V + (log2 N0 + 9/4)/N0 and eps_R = eps_V, both <= 1e-9, so S2
     Certificate 7.2 applies verbatim. n0 with E4's constant (Lean-checked lemma) and with B16's (Sec. 12).
[Q]  Small q (D4 and q = 2664), each with: E3 hole fixing; POS union (Sec. 13.5); POS + ladder (A19, Sec. 13.6).
     The exponent uses S2 Lemma 6.1 with general (pi, gamma, xi', eps): E = max of its terms, with
     gamma = 2(xi' - 2 eps)/3 and pi just below 3/(12 + 2(xi' - 2 eps)). N0 is searched over q * 2^j.
     n0 := max(2 (B + 1)/(1 - g), 2 (log2 C + 1)/g), where 2^B bounds the build (B = c_b N0 with c_b = 4; the
     ladder adds 1, for the circuits of the Delta and tail levels, all built once, up front) and C is the
     multiplicative run-time constant. For n >= n0 each of the two terms of the run time is at most
     2^{(1/2 - g/2) n - 1} poly(n, L), so the run time is below 2^{(1/2 - g/2) n} poly(n, L): n0 is where the
     constant has eaten at most half of the gain g = 1/2 - E, not where the run time reaches 2^{E n}.
     The ladder also needs every PM length n' to satisfy n' + 2 >= T0 + q. S2 calls PM with n' = 2m - 2j >= m
     > pi n - 2, so n >= (T0 + q)/pi suffices; this is a third term of n0 for the ladder rows.
Must-fail controls: [K1] Lemma 3.1 at N0 = q: no even k has k(k+2) = 10^26; [K2] q does not divide N0 = q/2;
[K3] the splitter with offset 0 only (no search) misses some half-set; [K4] the family bound with 2 in place of
9/4 fails at D = 3; [K5] S2's pair (dL', dR') with the D4 anchors fails the secant check (so certifying the
anchors at D4 is required); [K6] the claim xi'' >= 2.004e-5 at D4; [K7] E3 hole fixing at the POS design's N0
(no gain); [K8] the ladder with no tail (single scale) claiming log2 C <= 0.1 N0; [K9] the concave bound at
tau = 1/2 claimed below f at a feasible point.
Exit 0 iff every check holds and every control is rejected. Pure standard library. Run with nice -n 15.
"""
from fractions import Fraction as F
import contextlib
import io
import itertools
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ns = {"__name__": "cert"}
with contextlib.redirect_stdout(io.StringIO()):
    try:
        exec(compile(open(os.path.join(HERE, "cert_explicit.py")).read(), "cert_explicit.py", "exec"), ns)
    except SystemExit as e:
        assert e.code == 0, "cert_explicit.py must pass"
s2 = {"__name__": "cert_eps"}
exec(compile(open(os.path.join(HERE, "cert_eps.py")).read(), "cert_eps.py", "exec"), s2)

ln_encl, H_encl, eps_win, J_of, lg_up = ns["ln_encl"], ns["H_encl"], ns["eps_win"], ns["J_of"], ns["lg_up"]
L2_LO, L2_HI = ns["L2_LO_SER"], ns["L2_HI_SER"]
LN2_LO, LOG2E_LO = ns["LN2_LO"], ns["LOG2E_LO"]
A_YL, B_YL, DL_P, DR_P = ns["A_YL"], ns["B_YL"], ns["DL_P"], ns["DR_P"]
YL_ANCH = (ns["V0_UB"], ns["VH_UB"], ns["V1_UB"])
E20 = ns["E20"]
CB = 4
ok = True


def fe(x, d=4):
    return "%.*e" % (d, float(x))


def check(name, cond, detail=""):
    global ok
    print("  %-62s %s %s" % (name, "ok" if cond else "FAIL", detail))
    ok &= bool(cond)


def rejects(name, cond):
    global ok
    print("  [%s] rejected: %s" % (name, cond))
    ok &= bool(cond)


# ============================================================ [G] Lemma 3.1'
def split(U, sizes, S, search=True):
    """Canonical member: at each node, the least cyclic offset i whose window of the left children's total size w
    holds exactly w/2 elements of S. Returns the leaves, or None if some node has no balanced offset."""
    if len(sizes) == 1:
        return [U]
    h = len(sizes) // 2
    w, u = sum(sizes[:h]), len(U)
    for i in (range(u) if search else (0,)):
        win = [U[(i + j) % u] for j in range(w)]
        if 2 * sum(1 for c in win if c in S) == w:
            rest = [U[(i + w + j) % u] for j in range(u - w)]
            a = split(win, sizes[:h], S, search)
            b = split(rest, sizes[h:], S, search)
            return None if a is None or b is None else a + b
    return None


def splitter_exhaustive(sizes, search=True):
    n = sum(sizes)
    bad = 0
    for Sc in itertools.combinations(range(n), n // 2):
        S = set(Sc)
        leaves = split(list(range(n)), sizes, S, search)
        if leaves is None or any(2 * sum(1 for c in L if c in S) != len(L) for L in leaves):
            bad += 1
    return bad


def T_prod(m):  # prod over internal nodes of the leaf counts m_v, for the floor/ceil halving tree
    if m == 1:
        return 1
    return m * T_prod(m // 2) * T_prod(m - m // 2)


print("[G] Lemma 3.1' (halving splitter, canonical member)")
for sz in ((4, 4, 4), (4, 4, 4, 4), (6, 4, 2, 2), (8, 4, 2)):
    b = splitter_exhaustive(sz)
    check("every half-set balanced, leaves %s" % (sz,), b == 0, "(%d failures)" % b)
fam_ok = all((D * T_prod(D)) ** 4 <= 2 ** (9 * (D - 1)) for D in range(1, 401))
check("(D prod m_v)^4 <= 2^{9(D-1)} for D <= 400", fam_ok)
rejects("K3 offset 0 only", splitter_exhaustive((4, 4, 4), search=False) > 0)
rejects("K4 family bound with c = 2 at D = 3", not ((3 * T_prod(3)) <= 2 ** (2 * 2)))
rejects("K1 Lemma 3.1 at N0 = q", math.isqrt(10 ** 26 + 1) ** 2 != 10 ** 26 + 1)
# k(k+2) = N0 iff (k+1)^2 = N0 + 1, so no integer k exists unless N0 + 1 is a square.


# ============================================================ [V] certified anchors by concavity
def iadd(*xs):
    return (sum(x[0] for x in xs), sum(x[1] for x in xs))


def ineg(x):
    return (-x[1], -x[0])


def iscal(c, x):
    return (c * x[0], c * x[1]) if c >= 0 else (c * x[1], c * x[0])


def L2(x):
    lo, hi = ln_encl(F(x), 60)
    return (lo / (L2_HI if lo >= 0 else L2_LO), hi / (L2_LO if hi >= 0 else L2_HI))


def tlog(t):
    return (F(0), F(0)) if t == 0 else iscal(t, L2(t))


def hh(u, v):
    return iadd(tlog(u), ineg(tlog(v)), ineg(tlog(u - v)))


def f_and_grad(tau, a, b, mu, th):
    """Enclosures of f = tau l + (1-tau) r and of its gradient at (mu, th)."""
    l = iadd(hh(1 - b, mu), hh(2 * mu, th), (-4 * mu, -4 * mu))
    lm = iadd(L2((1 - b - mu) / mu), iscal(2, L2(2 * mu / (2 * mu - th))), (F(-4), F(-4)))
    lt = L2((2 * mu - th) / th)
    if tau == 1:
        return l, lm, lt
    r = iadd(hh(a, mu - a), hh(mu, th - mu))
    rm = iadd(L2((2 * a - mu) / (mu - a)), L2(mu / (2 * mu - th)), ineg(L2((2 * mu - th) / (th - mu))))
    rt = L2((2 * mu - th) / (th - mu))
    if tau == 0:
        return r, rm, rt
    return (iadd(iscal(tau, l), iscal(1 - tau, r)), iadd(iscal(tau, lm), iscal(1 - tau, rm)),
            iadd(iscal(tau, lt), iscal(1 - tau, rt)))


def newton_half(a, b):
    """Float Newton for the interior stationary point at tau = 1/2 (only picks x0; the bound is exact)."""
    a_q = F(a)
    a, c = float(a), float(1 - b)
    lg = math.log2

    def g(m, t):
        gm = lg((c - m) / m) + 2 * lg(2 * m / (2 * m - t)) - 4 + lg((2 * a - m) / (m - a)) + lg(m / (2 * m - t)) \
            - lg((2 * m - t) / (t - m))
        gt = lg((2 * m - t) / t) + lg((2 * m - t) / (t - m))
        return gm, gt
    m, t = 1.5 * a, 2.25 * a
    for _ in range(60):
        h = 1e-9 * a
        g0 = g(m, t)
        gmm = (g(m + h, t)[0] - g(m - h, t)[0]) / (2 * h)
        gmt = (g(m, t + h)[0] - g(m, t - h)[0]) / (2 * h)
        gtm = (g(m + h, t)[1] - g(m - h, t)[1]) / (2 * h)
        gtt = (g(m, t + h)[1] - g(m, t - h)[1]) / (2 * h)
        det = gmm * gtt - gmt * gtm
        dm = (g0[0] * gtt - g0[1] * gmt) / det
        dt = (gmm * g0[1] - gtm * g0[0]) / det
        m, t = m - dm, t - dt
        m = min(max(m, a * (1 + 1e-9)), 2 * a * (1 - 1e-9))
        t = min(max(t, m * (1 + 1e-9)), 2 * m * (1 - 1e-9))
    # Round to the grid a * 10^-15 (any interior x0 gives a valid bound; the gradient vanishes near the true
    # stationary point, so the rounding costs only a second-order amount).
    return F(round(m / a * 10 ** 15), 10 ** 15) * a_q, F(round(t / a * 10 ** 15), 10 ** 15) * a_q


def concave_max(tau, a, b, x0):
    """Upper bound on max_K f (f concave on K) and the enclosure of f(x0) (a feasible value)."""
    mu0, th0 = x0
    fv, gm, gt = f_and_grad(tau, a, b, mu0, th0)
    best = F(0)
    for vm, vt in ((a, a), (a, 2 * a), (2 * a, 2 * a), (2 * a, 4 * a)):
        dm, dt = vm - mu0, vt - th0
        lin = max(gm[0] * dm, gm[1] * dm) + max(gt[0] * dt, gt[1] * dt)
        best = max(best, lin)
    return fv[1] + best, fv


def anchors(a, b):
    """Upper bounds on V(0), V(1/2), V(1) (YL Sec. 3.5's V at the rational (a, b))."""
    Hb = H_encl(b)
    H4a = H_encl(4 * a)
    Hm = H_encl(2 * (1 - b - 2 * a))
    E1q_hi = Hb[1] - H4a[0] / 2 - Hm[0] / 2
    R0 = b - F(1, 2) + 2 * a
    x0s = {F(0): (5 * a / 3, 5 * a / 2), F(1, 2): newton_half(a, b), F(1): (2 * a, 2 * a)}
    out, feas = [], []
    for tau in (F(0), F(1, 2), F(1)):
        ub, fv = concave_max(tau, a, b, x0s[tau])
        out.append(up18(tau * E1q_hi + (1 - tau) * R0 + ub))
        feas.append(fv)
    m0, t0 = x0s[F(1, 2)]
    assert a < m0 < 2 * a and m0 < t0 < 2 * m0, "x0 at tau = 1/2 must lie inside K"
    return out, feas, x0s


def up18(x):
    """Round up to the grid 10^-18."""
    return F(-((-x.numerator * 10 ** 18) // x.denominator), 10 ** 18)


def hull_pair(U):
    """The line through the two crossings of Vbar (anchors U, no eps) with tau and (1-tau)/2, rounded up."""
    U0, Uh, U1 = U
    t1 = U0 / (1 + 2 * U0 - 2 * Uh)
    t2 = (F(1, 2) - 2 * Uh + U1) / (F(1, 2) + 2 * U1 - 2 * Uh)
    c1, c2 = t1, (1 - t2) / 2
    sl = (c2 - c1) / (t2 - t1)
    dR, dL = c1 - sl * t1, c1 + sl * (1 - t1)
    up = lambda x: F(-((-x.numerator * 10 ** 12) // x.denominator), 10 ** 12)
    dLp, dRp = up(dL), up(dR)
    xi = (F(1, 2) - dLp - dRp) / 2
    return dLp, dRp, F(int(xi * 10 ** 15), 10 ** 15)


print("[V] certified anchors by concavity")
U_yl, feas_yl, _ = anchors(A_YL, B_YL)
for i, nm in enumerate(("V(0)", "V(1/2)", "V(1)")):
    t = YL_ANCH[i] - E20
    check("Ye-Li (a,b): bound on %s >= table, within 2e-17" % nm, t <= U_yl[i] <= t + F(2, 10 ** 17),
          "(bound - table = %s)" % fe(U_yl[i] - t, 2))
QDES = {}
for tag, a, omb, q in (("D4", F(1, 2635), F(1, 110), 115940), ("q2664", F(1, 2664), F(1, 111), 2664)):
    b = 1 - omb
    U, feas, x0s = anchors(a, b)
    yc = ns["yl_conditions"](a, b)
    dLp, dRp, xi = hull_pair(U)
    qq = 4
    for den in (F(a).denominator, F(b).denominator):
        qq = qq * den // math.gcd(qq, den)
    print("  %s: a = 1/%d, 1-b = 1/%d, q = %d; anchors <= %.15f %.15f %.15f" % (tag, a.denominator, omb.denominator,
          qq, U[0], U[1], U[2]))
    check("%s: q = lcm(4, denominators) = %d" % (tag, q), qq == q)
    check("%s: YL params, E1(1/4) > 4a, h(1-b,2a) > 8a, H(b)<=1/10, 1-b<=1/100" % tag,
          yc["params"] and yc["dom1"] > 0 and yc["dom2"] > 0 and yc["e6"],
          "(margins %s, %s)" % (fe(yc["dom1"], 2), fe(yc["dom2"], 2)))
    check("%s: pair (%s, %s), xi'' = %s >= 2e-5" % (tag, dLp, dRp, fe(xi, 6)), xi >= F(2, 10 ** 5))
    QDES[tag] = dict(a=a, b=b, q=q, U=U, dL=dLp, dR=dRp, xi=xi, feas=feas, x0=x0s)
# K9: the bound at tau = 1/2 must be >= f at a feasible point (here x0 itself and a grid point)
d4 = QDES["D4"]
fg, _, _ = f_and_grad(F(1, 2), d4["a"], d4["b"], F(3, 2) * d4["a"], F(9, 4) * d4["a"])
ub_half = d4["U"][1] - F(1, 2) * (H_encl(d4["b"])[1] - H_encl(4 * d4["a"])[0] / 2
                                   - H_encl(2 * (1 - d4["b"] - 2 * d4["a"]))[0] / 2) - F(1, 2) * (d4["b"] - F(1, 2) + 2 * d4["a"])
rejects("K9 tau=1/2 bound below a feasible value", not (ub_half < fg[0]))
rejects("K6 xi'' >= 2.004e-5 at D4", not (d4["xi"] >= F(2004, 10 ** 8)))


# ============================================================ the design machinery
def structure(U, epsV, dL, dR):
    U0, Uh, U1 = (x + epsV for x in U)
    t1 = U0 / (1 + 2 * U0 - 2 * Uh)
    t2 = (F(1, 2) - 2 * Uh + U1) / (F(1, 2) + 2 * U1 - 2 * Uh)
    ok_s = (0 < t1 < F(1, 3) < t2 < 1) and 2 * Uh <= U0 + U1 and t2 >= F(1, 2)
    tau = [F(0), t1, t2, F(1)]
    cv = [F(0), t1, (1 - t2) / 2, F(0)]
    s = [None] + [(cv[i] - cv[i - 1]) / (tau[i] - tau[i - 1]) for i in (1, 2, 3)]
    ok_s = ok_s and s[1] > s[2] > s[3]
    line = lambda t: t * dL + (1 - t) * dR
    ok_sec = all(cv[i] <= line(tau[i]) + epsV for i in range(4))

    def v3(t):
        return U0 + 2 * t * (Uh - U0) if t <= F(1, 2) else Uh + 2 * (t - F(1, 2)) * (U1 - Uh)
    v = {1: lambda t: t, 2: v3, 3: lambda t: (1 - t) / 2}
    ends = {1: (0, 1), 2: (1, 2), 3: (2, 3)}
    dy = lambda x: F(math.floor(x * 2 ** 40), 2 ** 40)
    x1, x2 = dy((s[1] + s[2]) / 2), dy((s[2] + s[3]) / 2)
    ok_s = ok_s and abs(x1 - (s[1] + s[2]) / 2) <= (s[1] - s[2]) / 4 and abs(x2 - (s[2] + s[3]) / 2) <= (s[2] - s[3]) / 4
    ok_s = ok_s and all(v[t](tau[e]) <= cv[e] for t in (1, 2, 3) for e in ends[t])
    pairs = []
    for t in (1, 2, 3):
        lo_e, hi_e = ends[t]
        for j in range(4):
            if j in (lo_e, hi_e):
                continue
            if j > hi_e:
                xt = x1 if t == 1 else x2
                d = sum((tau[i] - tau[i - 1]) * (xt - s[i]) for i in range(hi_e + 1, j + 1))
            else:
                xt = x1 if t == 2 else x2
                d = sum((tau[i] - tau[i - 1]) * (s[i] - xt) for i in range(j + 1, lo_e + 1))
            pairs.append((t, j, d, v[t](tau[j]) - cv[j]))
    ok_s = ok_s and all(d > 0 for _, _, d, _ in pairs)
    dmin = min(d for _, _, d, _ in pairs)
    d1 = max(int(rr / d) + 1 for _, _, d, rr in pairs if rr > 0)
    S = sum(max([F(0)] + [rr - dd * d for _, _, d, rr in pairs]) for dd in range(1, d1 + 1))
    # E4 (single gap / single excess), for the Lean-checked accounting
    dmin_tau = min(t1, t2 - t1, 1 - t2)
    Delta = dmin_tau * min(s[1] - s[2], s[2] - s[3]) / 4
    rmax = max(max(t - c, (1 - t) / 2 - c, v3(t) - c) for t, c in zip(tau, cv))
    dstar = int(rmax / Delta) + 1
    return dict(ok_s=ok_s, ok_sec=ok_sec, t1=t1, t2=t2, pairs=pairs, dmin=dmin, d1=d1, S=S, U0=U0,
                Delta=Delta, LD=dstar * (rmax + 2) + 7, rmax=rmax)


def epsV_of(N, e, a, mode):
    J = J_of(e, N)
    if J is None or e > F(1, 20):
        return None
    ev = eps_win(e, a) + (5 + 15 * lg_up(N + 1)) / N
    if mode == "E3":
        ev += F(J, N)
    return ev, J


def best_e(N, a, mode):
    best = None
    for ex in range(1, 40):
        for m in (1, 2, 3, 5, 7):
            e = F(m, 10 ** ex)
            r = epsV_of(N, e, a, mode)
            if r is None:
                continue
            if mode == "E3" and 8 * r[1] > N:
                continue
            val = r[0] + (lg_up(r[1]) / N if mode == "POS" else 0)
            if best is None or val < best[0]:
                best = (val, e, r[0], r[1])
    return best


def eprime(N):
    """e' = 2^-s with s = floor((bitlen(N) - 1)/2), so that e'^2 N lies in [1, 4)."""
    return F(1, 2 ** ((int(N).bit_length() - 1) // 2))


def e6_ok(N, J, U0):  # Lemma E6's numeric hypotheses (U0 = Vbar(0) + eps_V)
    return 15 + 31 * lg_up(N + 1) + lg_up(J) <= F(49, 100) * N and U0 <= F(1, 2)


def s2_general(xi, eps):
    """S2 Lemma 6.1's exponent with general gamma, pi: gamma = 2(xi - 2 eps)/3, pi just below the balance."""
    gam = F(2, 3) * (xi - 2 * eps)
    if gam <= 0:
        return None
    pi = F(math.floor(F(3) / (12 + 2 * (xi - 2 * eps)) * 10 ** 13), 10 ** 13)
    if not (0 < pi <= F(1, 3) and pi <= F(2, 5)):
        return None
    t = [pi, 2 * pi, s2["LOG2_3_UP"] * pi, F(1, 4) + pi / 2, F(1, 4) + F(3, 4) * pi,
         F(1, 2) - gam * pi / 2, F(1, 2) - (xi - gam) * pi + 2 * eps * pi]
    return max(t), pi, gam


def n0_of(N0, g, log2C, build_extra=0):
    """n0 := max(2 (B + 1)/(1 - g), 2 (log2 C + 1)/g) with B = c_b N0 + build_extra. For n >= n0 the build,
    2^B, and the run, C 2^{(1/2 - g) n} poly(n, L), are each at most 2^{(1/2 - g/2) n - 1} poly(n, L)."""
    return max(2 * (CB * N0 + build_extra + 1) / (1 - g), 2 * (log2C + 1) / g)


def pad_bits(n_extra):  # each padded coordinate costs at most 2^{1/2} (max(dL', dR') + eps <= 1/2)
    return F(n_extra, 2)


def storage_bits(N0):
    return 4 + 2 * F(int(N0).bit_length())


# ============================================================ [A'] B17 at Ye-Li's (a, b), N0 = q = 10^26
print("[A'] B17 at Ye-Li's (a, b): N0 = q = 10^26, Lemma 3.1', E3 hole fixing")
N0 = 10 ** 26
check("q | N0, 4 | N0", N0 % ns["Q_YL"] == 0 and N0 % 4 == 0)
rejects("K2 q | N0 = q/2", (N0 // 2) % ns["Q_YL"] != 0)
yc = ns["yl_conditions"](A_YL, B_YL)
best = best_e(N0, A_YL, "E3")
_, eA, epsV, J = best
st = structure(YL_ANCH, epsV, DL_P, DR_P)
grp = (lg_up(N0) + F(9, 4)) / N0
epsL, epsR = epsV + grp, epsV
check("YL params, dominances, E6's H(b), 1-b", yc["params"] and yc["dom1"] > 0 and yc["dom2"] > 0 and yc["e6"])
check("eps' = %s, J = %s <= N0/8, E6 numeric" % (eA, fe(J, 3)), 8 * J <= N0 and e6_ok(N0, J, st["U0"]))
check("three-piece structure, dyadic thresholds, delta_{t,j} > 0", st["ok_s"])
check("secant domination with S2's pair (dL', dR')", st["ok_sec"])
check("N0 Delta >= 1 and N0 min delta >= 1", N0 * st["Delta"] >= 1 and N0 * st["dmin"] >= 1)
check("eps_V = %s; eps_L = %s, eps_R = %s <= 1e-9" % (fe(epsV, 3), fe(epsL, 3), fe(epsR, 3)),
      epsL <= F(1, 10 ** 9) and epsR <= F(1, 10 ** 9))
okB, EB = s2["check"](F(2499, 10 ** 4), s2["XI_STATED"], F(1, 10 ** 9), F("0.49999834"), xi_cap=s2["XI_STATED"])
gA = F(1, 2) - EB
check("S2 Certificate 7.2[B] verbatim: E <= %.10f" % float(EB), okB)
bitsE4 = st["LD"] * N0                       # E4, Lean-checked lemma: log2(8 D_inf) <= L_D N0
bitsB16 = st["S"] * N0 + 2 * st["d1"] + 6     # Sec. 12 (E4')
const = pad_bits(N0 + 1) + storage_bits(N0)
n0_E4 = n0_of(N0, gA, bitsE4 + const)
n0_B16 = n0_of(N0, gA, bitsB16 + const)
print("    L_D = %s (E4), S = %.6f (B16); padding <= (N0+1)/2 bits" % (st["LD"], float(st["S"])))
print("    n0 (E4 constant, [proof] + Lean-checked E4) <= %s;  n0 (B16 constant, [proof], Sec. 12) <= %s"
      % (fe(n0_E4, 3), fe(n0_B16, 3)))
check("n0 with E4 <= 5.84e35 and with B16 <= 1.20e32", n0_E4 <= F(584, 100) * 10 ** 35 and n0_B16 <= F(120, 100) * 10 ** 32)
print("    gain g = 1/2 - E >= %s; for n >= n0 the run time is below 2^{%.10f n} poly(n, L)" % (fe(gA, 4), 0.5 - float(gA) / 2))
RES = {"A'-E4": n0_E4, "A'-B16": n0_B16}
ROWS = {}


# ============================================================ [Q] small q
def ladder_bits(N0, q, a, U, st, epsV0, rho=F(3, 4)):
    """A19 (Sec. 13.6): tail template N_j = q floor(N0 rho^j / q) while E6's hypotheses hold, plus a level of
    length Delta in qZ cap [0, N0) above it; returns the constant bits (rebalancing + chain + union + padding)."""
    pairs = st["pairs"]
    tail, Nj, j = [], N0, 0
    while True:
        j += 1
        Nj = q * int(N0 * rho ** j / q)
        if Nj < q:
            break
        e = eprime(Nj)
        r = epsV_of(Nj, e, a, "POS")
        if r is None or not e6_ok(Nj, r[1], U[0] + r[0]) or r[0] > F(1, 100):
            break
        tail.append((Nj, r[0], r[1]))
    T0 = sum(x[0] for x in tail)
    bits = F(0)
    # tail levels, bottom-up: l_j = sum of the lengths at and below level j
    lrem = 0
    per = []
    for Nj, ev, J in reversed(tail):
        lrem += Nj
        om = max(F(0), ev - epsV0)          # piece 2 overshoot; pieces 1 and 3 are exact
        best_t = None
        for t in (1, 2, 3):
            A = Nj * om if t == 2 else F(0)
            ys = [Nj * (rr + (om if t == 2 else 0)) - lrem * d for (tt, _, d, rr) in pairs if tt == t]
            Y = max(ys) - A
            # log2(1 + 2 * 2^Y) <= 3 * 2^Y for Y <= -1 (and <= 2^-60 once Y <= -62); else <= Y^+ + 2
            extra = F(1, 2 ** 60) if Y <= -62 else (3 * F(2) ** math.ceil(Y) if Y <= -1 else max(Y, F(0)) + 2)
            val = A + extra
            best_t = val if best_t is None else max(best_t, val)
        bits += best_t + lg_up(J)                      # rebalancing factor and the POS union (both sides)
        per.append((Nj, lrem, best_t))
    # the Delta level (length Delta in [q, N0 - q], or absent), l = Delta + T0:
    #   Delta >= N_min: POS C3 at length Delta, e' = 2^{-s} with e'^2 Delta in [1, 4); overshoot bits
    #   <= W + 5 + 15 log2(N0+1); Delta < N_min: (I,M) in the role of piece 2, overshoot (1 - 3 tau1)/2 per coordinate.
    Nmin = tail[-1][0] if tail else N0
    W = 8 / (LN2_LO * F(99, 100)) + 4 * a / ((F(1, 4) - F(1, 20)) * (F(1, 4) - F(1, 20) - a) * LN2_LO)
    omb_big = W + 5 + 15 * lg_up(N0 + 1)
    # Switch length Nsw = 2^K: for Delta in [2^k, 2^{k+1}) with k >= K, eps_V(Delta) <= (W + 5 + 15 (k+2)) / 2^k,
    # which decreases in k; so one check at k = K covers every Delta >= Nsw. Below Nsw, (I,M) plays piece 2.
    K = 11
    while not ((W + 5 + 15 * (K + 2)) / F(2) ** K + U[0] <= F(1, 2)
               and 15 + 31 * (K + 2) + lg_up(3 * N0) <= F(49, 100) * 2 ** K):
        K += 1
    Nsw = 2 ** K
    omb_small = Nsw * (1 - 3 * st["t1"]) / 2
    om_bits = max(omb_big, omb_small)
    # off terms: Delta (r + omega) - (Delta + T0) delta <= max(N0 (r - delta), 0) - T0 delta + max(om_bits, Nsw/2)
    Yd = max(max(N0 * (rr - d), F(0)) - T0 * d + max(om_bits, F(Nsw, 2)) for (_, _, d, rr) in pairs)
    ok_d = Yd <= -1 and Nsw >= 1600
    bits += om_bits + 3 + lg_up(3 * N0)               # 3 * 2^{Yd} <= 3/2 bits, rounded up; union for Delta
    # main levels: l >= T0 + k N0, omega = 0 (any number of them, including none)
    y0 = max(N0 * rr - T0 * d for (_, _, d, rr) in pairs)
    ok_m = y0 <= -64 and N0 * st["dmin"] >= 1
    bits += 1 + 3                                     # main levels (< 1 bit) and the factor 8 of E4's degrees
    chain = (len(tail) + 2) * lg_up(5 * N0)            # tail chain of the splitter tree (Lemma 3.1')
    return dict(bits=bits + chain + pad_bits(q + 1) + storage_bits(N0), tail=tail, T0=T0, ok=ok_d and ok_m and T0 >= 2 * N0,
                parts=(bits, chain, pad_bits(q + 1)), okT=ok_d and ok_m and T0 >= 2 * N0, Nmin=Nmin, per=per, y0=y0)


def q_variant(tag, mode, ladder=False, js=range(4, 26)):
    d = QDES[tag]
    a, q, U = d["a"], d["q"], d["U"]
    best_row = None
    for j in js:
        N0 = q * 2 ** j
        be = best_e(N0, a, mode)
        if be is None:
            continue
        _, e, epsV, J = be
        st = structure(U, epsV, d["dL"], d["dR"])
        if not (st["ok_s"] and st["ok_sec"] and N0 * st["Delta"] >= 1 and N0 * st["dmin"] >= 1):
            continue
        if not e6_ok(N0, J, st["U0"]) or (mode == "E3" and 8 * J > N0):
            continue
        grp = (lg_up(N0) + F(9, 4)) / N0
        uni = lg_up(J) / N0 if mode == "POS" else F(0)
        em = max(epsV + grp + uni, epsV + uni)
        s = s2_general(d["xi"], em)
        if s is None:
            continue
        E, pi, gam = s
        g = F(1, 2) - E
        if g <= 0:
            continue
        if ladder:
            lb = ladder_bits(N0, q, a, U, st, epsV)
            if not lb["ok"]:
                continue
            log2C = lb["bits"]
            # build: 2^{c_b N0} for the main level, plus every tail and Delta circuit (lengths in qZ, below N0,
            # each at most 2^{c_b (N0 - q)} summed over two geometric series), all built once: at most 2^{c_b N0 + 1}.
            # Each PM length must hold the ladder: n' + 2 >= T0 + q, and n' > pi n - 2 (S2 Step 0, Lemma 3.2).
            n0 = max(n0_of(N0, g, log2C, build_extra=1), (lb["T0"] + q) / pi)
        else:
            lb = None
            log2C = st["S"] * N0 + 2 * st["d1"] + 6 + pad_bits(N0 + 1) + storage_bits(N0)
            n0 = n0_of(N0, g, log2C)
        if best_row is None or n0 < best_row["n0"]:
            best_row = dict(N0=N0, e=e, J=J, epsV=epsV, em=em, E=E, g=g, pi=pi, log2C=log2C, n0=n0, lb=lb)
    return best_row


print("[Q] small q (S2 Lemma 6.1 with general gamma; B16 constant unless ladder)")
for tag in ("D4", "q2664"):
    d = QDES[tag]
    if tag == "D4":
        stc = structure(d["U"], F(1, 10 ** 12), DL_P, DR_P)
        rejects("K5 S2's pair at the D4 anchors", not stc["ok_sec"])
    for mode, lad in (("E3", False), ("POS", False), ("POS", True)):
        # N0 = q 2^j; the j ranges bracket each optimum found by a wider search (any j gives a valid bound)
        js = {("D4", "E3"): range(19, 24), ("D4", "POS"): range(8, 13), ("q2664", "E3"): range(25, 30),
              ("q2664", "POS"): range(13, 18)}.get((tag, mode)) if not lad else \
            {"D4": range(13, 18), "q2664": range(15, 20)}[tag]
        row = q_variant(tag, mode, lad, js=js)
        name = "%s-%s%s" % (tag, mode, "-ladder" if lad else "")
        if row is None:
            check(name + ": some N0 gives a gain", False)
            continue
        extra = ""
        if lad:
            pr = row["lb"]["parts"]
            extra = ("\n%18s tail %d levels, N_min %s = %d q, T0/N0 %.2f; bits: rebalancing+union %s (%.3f N_min), "
                     "chain %s, padding %s; (T0 + q)/pi = %s") % (
                "", len(row["lb"]["tail"]), fe(row["lb"]["Nmin"], 2), row["lb"]["Nmin"] // d["q"],
                row["lb"]["T0"] / row["N0"], fe(pr[0], 2), float(pr[0] / row["lb"]["Nmin"]), fe(pr[1], 2),
                fe(pr[2], 2), fe((row["lb"]["T0"] + d["q"]) / row["pi"], 2))
        print("  %-16s N0 = %s, eps' = %s, eps_m = %s, E <= %.10f, g = %s, log2 C = %s, n0 <= %s, "
              "then time < 2^{%.10f n}%s"
              % (name, fe(row["N0"], 3), row["e"], fe(row["em"], 3), float(row["E"]), fe(row["g"], 4),
                 fe(row["log2C"], 3), fe(row["n0"], 3), 0.5 - float(row["g"]) / 2, extra))
        RES[name] = row["n0"]
        ROWS[name] = row
        if tag == "D4" and mode == "POS" and not lad:
            N0p = row["N0"]
            be = best_e(N0p, d["a"], "E3")
            st3 = structure(d["U"], be[2], d["dL"], d["dR"]) if be else None
            noE3 = be is None or s2_general(d["xi"], be[2] + (lg_up(N0p) + F(9, 4)) / N0p) is None \
                or F(1, 2) - s2_general(d["xi"], be[2] + (lg_up(N0p) + F(9, 4)) / N0p)[0] <= 0
            rejects("K7 E3 hole fixing at the POS design's N0 = %s" % fe(N0p, 2), noE3)
            stn = structure(d["U"], row["epsV"], d["dL"], d["dR"])
            single = stn["S"] * N0p
            rejects("K8 single scale claiming log2 C <= 0.1 N0", not (single <= F(1, 10) * N0p))
check("D4-POS-ladder n0 <= D4-POS n0 / 100", RES["D4-POS-ladder"] * 100 <= RES["D4-POS"])
# The (E, n0) pairs of proofs/stage2b-explicit.md Sec. 13's table, each certified as an upper bound.
TABLE = {"D4-E3": ("0.4999994073", "8.18e17"), "D4-POS": ("0.4999989913", "2.35e14"),
         "D4-POS-ladder": ("0.4999983549", "1.59e11"), "q2664-E3": ("0.4999992172", "9.11e17"),
         "q2664-POS": ("0.4999992295", "2.26e14"), "q2664-POS-ladder": ("0.4999985715", "4.90e10")}
for name, (Es, ns_) in TABLE.items():
    check("table row %s: E <= %s, n0 <= %s" % (name, Es, ns_), ROWS[name]["E"] <= F(Es) and ROWS[name]["n0"] <= F(ns_))
print("ALL PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
