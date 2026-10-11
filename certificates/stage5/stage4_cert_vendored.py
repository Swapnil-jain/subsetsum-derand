"""Stage 4 certificate: the deterministic exponent of Record 3's reduction, with the round-family loss lambda included.

Self-contained (standard library only). Three parts, each referenced from PROOF.md:
  [XI]  the circuit gain xi(s) at s = 1/8 and s = 11/100, by branch and bound over the colour polygon
        (PROOF.md Sec. 3.6), with the [F1] upper bracket and the must-fail controls C1, C2;
  [LAM] the round-family loss lambda at the explicit piece length N_b (PROOF.md Sec. 4.3), and the splitter count
        bound S(q) <= 3q - 3 - 2 log2 q checked for every q <= 2^14 (the proof is an induction, Lemma 4.2);
  [E]   the deterministic exponent E_det: every cost term of PROOF.md Sec. 5.3, sup over the layer range, with
        lambda added to every term that pays for the round family; and, for reference, the randomized exponent
        (needs A3, PROOF.md Sec. 6). Must-fail controls K1-K9.
Arithmetic: outward-rounded IEEE-754 intervals (one ulp per operation; libm log2 padded by four ulps), parameters as
exact Fractions. A claim passes only if the interval upper bound is below it.
Run: nice -n 15 /usr/bin/python3 -E cert_stage4.py            (about 20 s, < 60 MB)
     nice -n 15 /usr/bin/python3 -E cert_stage4.py --search   (also re-runs the float parameter search)
"""
import math
import sys
from fractions import Fraction as F

sys.setrecursionlimit(10000)

# ------------------------------------------------------------------ interval arithmetic
DN, UP = -math.inf, math.inf


def _dn(x, k=1):
    for _ in range(k):
        x = math.nextafter(x, DN)
    return x


def _up(x, k=1):
    for _ in range(k):
        x = math.nextafter(x, UP)
    return x


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if isinstance(lo, F) or isinstance(hi, F):
            lo, hi = _dn(float(lo)), _up(float(hi))
        self.lo, self.hi = float(lo), float(hi)
        assert self.lo <= self.hi, (self.lo, self.hi)

    @staticmethod
    def q(fr):
        fr = F(fr)
        return I(_dn(float(fr)), _up(float(fr)))

    def __add__(a, b):
        b = b if isinstance(b, I) else I.q(b)
        return I(_dn(a.lo + b.lo), _up(a.hi + b.hi))

    __radd__ = __add__

    def __neg__(a):
        return I(-a.hi, -a.lo)

    def __sub__(a, b):
        b = b if isinstance(b, I) else I.q(b)
        return I(_dn(a.lo - b.hi), _up(a.hi - b.lo))

    def __rsub__(a, b):
        return I.q(b) - a

    def __mul__(a, b):
        b = b if isinstance(b, I) else I.q(b)
        p = [a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi]
        return I(_dn(min(p)), _up(max(p)))

    __rmul__ = __mul__

    def __truediv__(a, b):
        b = b if isinstance(b, I) else I.q(b)
        assert b.lo > 0 or b.hi < 0, "division by an interval containing 0"
        p = [a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi]
        return I(_dn(min(p)), _up(max(p)))

    def __rtruediv__(a, b):
        return I.q(b) / a

    def mid(a):
        return 0.5 * (a.lo + a.hi)


def log2(a):
    assert a.lo > 0, "log2 of a non-positive interval"
    return I(_dn(math.log2(a.lo), 4), _up(math.log2(a.hi), 4))


def ln(a):
    assert a.lo > 0
    return I(_dn(math.log(a.lo), 4), _up(math.log(a.hi), 4))


def H(n, j):
    """Enclosure of n h(j/n) = j log2(n/j) + (n-j) log2(n/(n-j)) for point-like intervals, 0 <= j <= n."""
    out = I(0.0)
    if j.hi > 0:
        assert j.lo > 0
        out = out + j * log2(n / j)
    nj = n - j
    if nj.hi > 0:
        assert nj.lo > 0, "H: j > n"
        out = out + nj * log2(n / nj)
    return out


def h(x):
    return H(I(1.0), x)


def h_iv(X):
    """Enclosure of h over an interval X inside (0, 1) (h increases below 1/2 and decreases above)."""
    lo, hi = h(I(X.lo)), h(I(X.hi))
    if X.hi <= 0.5:
        return I(lo.lo, hi.hi)
    if X.lo >= 0.5:
        return I(hi.lo, lo.hi)
    return I(min(lo.lo, hi.lo), 1.0)


# ------------------------------------------------------------------ [XI] the colour landscape (PROOF.md Sec. 3.6)
class Land:
    """Central colour profile per coordinate (N = 1): k = s/2, m in [k, 2k], b = k + rho (m - k), m <= d <= b,
    R = H(k, m - k) + H(b - m, d - m), L = H(1/2, d) + H(1/2, b - d) - H(1 - m, b - m).
    The true left exponent is max(L, 0); we bound G = max(tau L + (1-tau) R, (1-tau) R) >= tau max(L,0) + (1-tau) R."""

    def __init__(self, s, rho):
        self.s, self.rho = s, rho
        self.k = s / 2
        self.kI, self.rI = I.q(self.k), I.q(rho)
        self.kf, self.rf = float(self.k), float(rho)

    def pieces(self, m, d):
        k, r = self.kI, self.rI
        b = k + r * (m - k)
        return dict(d=d, e=b - d, n3=1 - m, j3=(r - 1) * (m - k), j4=m - k, n5=(r - 1) * (m - k), j5=d - m, b=b)

    def point(self, mf, df, tau):
        P = self.pieces(I(mf), I(df))
        half = I(0.5)
        L = H(half, P["d"]) + H(half, P["e"]) - H(P["n3"], P["j3"])
        R = H(self.kI, P["j4"]) + H(P["n5"], P["j5"])
        return tau * L + (1 - tau) * R, R

    def ub_nat(self, m0, m1, d0, d1, tau):
        """Natural upper bound of G over a box (monotonicity of H(n, j) in n, and in j up to n/2)."""
        m, d = I(m0, m1), I(d0, d1)
        P = self.pieces(m, d)

        def UB(n, j):
            nh = n.hi
            jl, jh = max(j.lo, 0.0), min(j.hi, nh)
            if jl > jh:
                return None
            js = min(max(nh / 2, jl), jh)
            if 0 < js < 1e-200 <= nh / 2:
                js = 1e-200   # H increases in j below n/2, so a larger j is still an upper bound
            if 0 < nh - js < 1e-200:
                js = nh - 1e-200 if nh / 2 <= nh - 1e-200 else js
            return H(I(nh), I(js)).hi

        u1 = UB(I(0.5), P["d"])
        u2 = UB(I(0.5), P["e"])
        u4 = UB(self.kI, P["j4"])
        u5 = UB(P["n5"], P["j5"]) if P["n5"].hi > 0 else 0.0
        if None in (u1, u2, u4, u5):
            return -1e9   # the box misses the polygon
        n3, j3 = P["n3"], P["j3"]
        assert j3.hi <= n3.lo / 2
        l3 = H(I(n3.lo), I(max(j3.lo, 0.0))).lo
        L = I(u1) + I(u2) - I(l3)
        R = I(u4) + I(u5)
        return max((tau * L + (1 - tau) * R).hi, ((1 - tau) * R).hi)

    def ub_cen(self, m0, m1, d0, d1, tau):
        """Mean-value bound on boxes strictly inside the polygon; None where a derivative is unbounded."""
        m, d = I(m0, m1), I(d0, d1)
        P = self.pieces(m, d)
        k, r = self.kI, self.rI
        half = I(0.5)
        try:
            lgd = log2((half - P["d"]) / P["d"])
            lge = log2((half - P["e"]) / P["e"])
            n3, j3 = P["n3"], P["j3"]
            d3 = -log2(n3 / (n3 - j3)) + (r - 1) * log2((n3 - j3) / j3)
            d4 = log2((2 * k - m) / (m - k))
            n5, j5 = P["n5"], P["j5"]
            a5 = log2(n5 / (n5 - j5))
            b5 = log2((n5 - j5) / j5)
        except AssertionError:
            return None
        dLm, dLd = r * lge - d3, lgd - lge
        dRm, dRd = d4 + (r - 1) * a5 - b5, b5
        gm, gd = tau * dLm + (1 - tau) * dRm, tau * dLd + (1 - tau) * dRd
        mc, dc = 0.5 * (m0 + m1), 0.5 * (d0 + d1)
        g1c, Rc = self.point(mc, dc, tau)
        hm, hd = _up(0.5 * (m1 - m0)), _up(0.5 * (d1 - d0))
        sm, sd = max(abs(gm.lo), abs(gm.hi)), max(abs(gd.lo), abs(gd.hi))
        ub1 = (I(g1c.hi) + I(hm) * I(sm) + I(hd) * I(sd)).hi
        Rm, Rd = (1 - tau) * dRm, (1 - tau) * dRd
        ub2 = (I(((1 - tau) * Rc).hi) + I(hm) * I(max(abs(Rm.lo), abs(Rm.hi)))
               + I(hd) * I(max(abs(Rd.lo), abs(Rd.hi)))).hi
        return max(ub1, ub2), g1c

    def interior(self, m0, m1, d0, d1):
        k, r = self.kf, self.rf
        b0, b1 = k + r * (m0 - k), k + r * (m1 - k)
        return (m0 > k * (1 + 1e-9) and m1 < 2 * k * (1 - 1e-9) and d0 > m1 + 1e-12 and d1 < b0 - 1e-12
                and d1 < 0.5 - 1e-12 and d0 > b1 - 0.5 + 1e-12)

    def prove(self, tau, target, maxbox=400000):
        """Prove G <= target on the whole polygon at this tau. Returns (ok, boxes, best rigorous point found)."""
        k, r = self.kf, self.rf
        stack = [(k, 2 * k, k, min(k + r * k, 0.5))]
        boxes, best = 0, (-1e9, None)
        while stack:
            m0, m1, d0, d1 = stack.pop()
            boxes += 1
            if boxes > maxbox:
                return False, boxes, best
            if self.ub_nat(m0, m1, d0, d1, tau) <= target:
                continue
            if self.interior(m0, m1, d0, d1):
                cen = self.ub_cen(m0, m1, d0, d1, tau)
                if cen is not None:
                    ubc, g1c = cen
                    if g1c.lo > best[0]:
                        best = (g1c.lo, (0.5 * (m0 + m1), 0.5 * (d0 + d1)))
                    if g1c.lo > target:
                        return False, boxes, best
                    if ubc <= target:
                        continue
            if max(m1 - m0, d1 - d0) < 1e-12:
                return False, boxes, best
            if (m1 - m0) * 3 >= (d1 - d0):
                mm = 0.5 * (m0 + m1)
                stack += [(m0, mm, d0, d1), (mm, m1, d0, d1)]
            else:
                dm = 0.5 * (d0 + d1)
                stack += [(m0, m1, d0, dm), (m0, m1, dm, d1)]
        return True, boxes, best

    def refute(self, tau, target):
        """Find a colour whose RIGOROUS lower bound beats target at tau (B&B best point, polished locally)."""
        ok, _, (val, pt) = self.prove(tau, target)
        if ok or pt is None:
            return False, None, None
        step = 1e-4
        while val <= target and step > 1e-9:
            moved = False
            for dm, dd in ((step, 0), (-step, 0), (0, step), (0, -step), (step, step), (-step, -step),
                           (step, -step), (-step, step)):
                q = (pt[0] + dm, pt[1] + dd)
                if self.interior(q[0], q[0], q[1], q[1]):
                    v = self.point(q[0], q[1], tau)[0].lo
                    if v > val:
                        val, pt, moved = v, q, True
            if not moved:
                step /= 2
        return val > target, pt, val


# Contact data (rationals; any choice gives a valid bound, PROOF.md Sec. 3.6). t1, t2 pass; c1, c2 are one 1e-7 grid
# step past the contacts and must be refuted.
XI_DATA = {
    F(1, 8): dict(rho=F(27, 10), t1=F(798773, 2500000), t2=F(7218613, 10000000),
                  c1=F(3195091, 10000000), c2=F(3609307, 5000000)),
    F(11, 100): dict(rho=F(549, 200), t1=F(49989, 156250), t2=F(1850541, 2500000),
                     c1=F(639859, 2000000), c2=F(1480433, 2000000)),
}


def cert_xi(s, D):
    """Returns (ok, xi lower bound as a Fraction, upper bound on l = line(1) rounded up to 4 places, as a Fraction)."""
    Ld = Land(s, D["rho"])
    hs, sI = h(I.q(s)), I.q(s)
    t1, t2 = I.q(D["t1"]), I.q(D["t2"])
    A1, A2 = t1 * hs, (1 - t2) * (1 - sI)
    ok1, n1, _ = Ld.prove(t1, A1.lo)
    ok2, n2, _ = Ld.prove(t2, A2.lo)
    slope = (A2 - A1) / (t2 - t1)
    okS = slope.hi <= hs.lo and slope.lo >= -(1 - sI).lo   # tau h(s) <= line left of t1, (1-tau)(1-s) right of t2
    line = lambda t: A1 + slope * (I(t) - t1)
    l_, r_, half = line(1.0), line(0.0), line(0.5)
    okLR = l_.lo >= 0 and r_.lo >= 0
    xi_lo = ((hs - sI) * I(0.5) - half).lo
    xi_q = F(math.floor(xi_lo * 10 ** 10), 10 ** 10)
    ok = ok1 and ok2 and okS and okLR
    print(f"[XI] s={s} rho={D['rho']}: V(t1) <= t1 h(s): {ok1} ({n1} boxes); V(t2) <= (1-t2)(1-s): {ok2} ({n2} boxes);"
          f" slope l-r = {slope.mid():.6f} in (-(1-s), h(s)): {okS}; l = {l_.mid():.9f}, r = {r_.mid():.9f} >= 0: {okLR}")
    print(f"     xi(s) >= {xi_lo:.10f}  (rational xi' = {xi_q})")
    # must-fail controls C1, C2: one grid step past the contacts the claim is refuted by an explicit colour
    c1, c2 = I.q(D["c1"]), I.q(D["c2"])
    f1, p1, v1 = Ld.refute(c1, (c1 * hs).lo)
    f2, p2, v2 = Ld.refute(c2, ((1 - c2) * (1 - sI)).lo)
    print(f"     control C1 (tau = {D['c1']}): refuted {f1} at colour {p1};  C2 (tau = {D['c2']}): refuted {f2} at {p2}")
    ok_ctl = f1 and f2
    if ok_ctl:
        # [F1]: the witnesses make the trivial lines the minimum at c1 and c2 (V(c1) > c1 h(s), V(c2) > (1-c2)(1-s)),
        # so every valid line is above (c1, c1 h(s)) and (c2, (1-c2)(1-s)), and xi <= the chord value there.
        # Gotcha: the line need NOT pass above the witnesses' own values G(c1), G(c2): when the trivial disjunct
        # holds, only line(c1) >= c1 h(s) is known. Using G(c1) here gave a bracket too small by about 3e-8.
        B1, B2 = c1 * hs, (1 - c2) * (1 - sI)
        sl = (B2 - B1) / (c2 - c1)
        chord = B1 + sl * (I(0.5) - c1)
        print(f"     [F1] every line valid for this V has xi <= {((hs - sI) * I(0.5) - chord).hi:.10f}")
    l_q = F(math.ceil(l_.hi * 10 ** 4), 10 ** 4)
    return ok and ok_ctl, xi_q, l_q


# ------------------------------------------------------------------ [LAM] round-family loss (PROOF.md Sec. 4)
def splitter_S(qmax):
    """S(q) = log2 q + S(floor(q/2)) + S(ceil(q/2)), S(1) = 0; check S(q) <= 3q - 3 - 2 log2 q for 1 <= q <= qmax
    with intervals. (Lemma 4.2 proves it for every q by induction; this is a check of the arithmetic.)"""
    S = {1: I(0.0)}
    worst = -1e9
    for q in range(2, qmax + 1):
        S[q] = log2(I(float(q))) + S[q // 2] + S[q - q // 2]
        bound = I(float(3 * q - 3)) - 2 * log2(I(float(q)))
        worst = max(worst, (S[q] - bound).hi)
        if (S[q] - bound).hi > 1e-9:   # equality at q = 2, so the float check gets a 1e-9 tolerance
            return False, q
    return True, worst


def lam_bound(Nb, alpha):
    """lambda * N_b >= log2 N_b + 3 + log2(1 + N_b ln 2) + 2 log2((a_b + 1)(b_b + 1)), a_b = alpha N_b/2,
    b_b = (1 - alpha) N_b/2 (PROOF.md Lemma 4.4). Returns an upper bound on lambda as an interval's hi."""
    ab = F(Nb) * alpha / 2
    bb = F(Nb) / 2 - ab
    assert ab.denominator == 1 and bb.denominator == 1, "N_b must make a_b, b_b integers"
    NbI = I.q(Nb)
    tot = log2(NbI) + 3 + log2(1 + NbI * ln(I(2.0))) + 2 * log2(I.q((ab + 1) * (bb + 1)))
    return (tot / NbI).hi


# ------------------------------------------------------------------ [E] the exponent (PROOF.md Sec. 5.3)
def E_rig(s, a, mu, dl, xi, kap_lo, det=True, lam=0.0, pieces=6000, gen="ours"):
    """Rigorous upper bound on the exponent. kap_lo must satisfy h(kap_lo) < 1 - delta (checked), so the layer range
    lies inside [kap_lo, 1 - kap_lo]. Terms (per n; J, t as in PROOF.md Sec. 1.5):
      P1 mu(1-delta)        prefix sums up to T
      P2 1/2 - mu delta/2   few sums (AKKN)
      P3 mu(J+lam) + log|U| + deg(u) - (1-delta) mu      circuit on the kept records (closed form)
      P4 det: mu(J+lam) + 1/4 + mu log2(3)/4             kept-record generation and histograms, plain halves
         rand: mu J + log|U|/2                            balanced half-splits (A3)
      P5 2 mu (the sets C_k), Pscan mu(2 - delta) (prime scan), Kenum mu(2 + lam) (the sets S_{c,f}),
      P6 mu(2 - delta + J + lam) (the estimator).
    """
    sI, aI, muI, dI, xI, lamI = I.q(s), I.q(a), I.q(mu), I.q(dl), I.q(xi), I(lam)
    assert h(I.q(kap_lo)).hi < (1 - dI).lo, "kappa range certificate fails"
    k0 = I.q(kap_lo)
    assert (k0 - aI * 0.5).lo > 0, "layer range must lie inside (alpha/2, 1 - alpha/2)"
    hs = h(sI)
    terms = {"P1": (muI * (1 - dI)).hi, "P2": (0.5 - muI * dI * 0.5).hi}
    if det:
        terms["P5"] = (2 * muI).hi
        terms["Pscan"] = (muI * (2 - dI)).hi
        terms["Kenum"] = (muI * (2 + lamI)).hi
    P3 = P4 = P6 = -9.0
    tmin, tmax = 9.0, -9.0
    width = (1 - 2 * k0) * (1.0 / pieces)
    for i in range(pieces):
        K = I((k0 + width * i).lo, (k0 + width * (i + 1)).hi)
        T = (K - aI * 0.5) / (1 - aI)
        tmin, tmax = min(tmin, T.lo), max(tmax, T.hi)
        hk, ht = h_iv(K), h_iv(T)
        J = hk - aI * hs - (1 - aI) * ht
        p3 = 0.5 + muI * (hk - aI * xI - (1 - aI) * ht * 0.5 + (1 - aI) * 0.5 - 1 + dI + lamI)
        if det:
            p4 = muI * (J + lamI) + 0.25 + muI * (log2(I(3.0)) * 0.25)
        elif gen == "ours":
            mt = I(max(T.lo, 1 - T.hi), max(T.hi, 1 - T.lo))
            p4 = 0.25 + muI * (hk - aI * hs * 0.75 + aI * sI * 0.25 - (1 - aI) * ht * 0.75 + (1 - aI) * mt * 0.25)
        else:
            sb = aI * sI + (1 - aI) * 0.5
            sH, sHb = sb + K - 0.5, sb - K + 0.5
            g1, g2 = h_iv(sH) + sH, h_iv(sHb) + sHb
            p4 = muI * J + 0.25 + muI * 0.25 * I(max(g1.hi, g2.hi))
        P3, P4 = max(P3, p3.hi), max(P4, p4.hi)
        if det:
            P6 = max(P6, (muI * (2 - dI + J + lamI)).hi)
    terms["P3"], terms["P4"] = P3, P4
    if det:
        terms["P6"] = P6
        # Lemma 4.4's parity step needs t-bar +- 1/(2b) inside [1/3, 2/3]; b is huge, so a 0.01 margin suffices
        assert tmin > 1 / 3 + 0.01 and tmax < 2 / 3 - 0.01, (tmin, tmax)
    return max(terms.values()), terms


def kap_lo_for(dl):
    lo, hi = 1e-9, 0.5
    hf = lambda x: -x * math.log2(x) - (1 - x) * math.log2(1 - x)
    for _ in range(80):
        c = (lo + hi) / 2
        if hf(c) < 1 - float(dl):
            lo = c
        else:
            hi = c
    return F(math.floor(lo * 10 ** 9) - 1, 10 ** 9)


# ------------------------------------------------------------------ optional float search (pure Python)
def E_float(p, s, xi, det, lam):
    a, mu, dl = p
    if not (0.05 < a < 0.95 and 0.01 < mu <= 0.5 and 1e-5 < dl < 0.05):
        return 9.0
    hf = lambda x: 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)
    k0 = float(kap_lo_for(F(dl).limit_denominator(10 ** 9)))
    if k0 <= a / 2:
        return 9.0
    best = [mu * (1 - dl), 0.5 - mu * dl / 2] + ([2 * mu, mu * (2 + lam)] if det else [])
    for i in range(201):
        kap = k0 + (1 - 2 * k0) * i / 200
        t = (kap - a / 2) / (1 - a)
        J = hf(kap) - a * hf(s) - (1 - a) * hf(t)
        best.append(0.5 + mu * (hf(kap) - a * xi - (1 - a) * hf(t) / 2 + (1 - a) / 2 - 1 + dl + lam))
        if det:
            best += [mu * (J + lam) + 0.25 + mu * math.log2(3) / 4, mu * (2 - dl + J + lam)]
        else:
            best.append(0.25 + mu * (hf(kap) - 0.75 * a * hf(s) + 0.25 * a * s - 0.75 * (1 - a) * hf(t)
                                     + 0.25 * (1 - a) * max(t, 1 - t)))
    return max(best)


def nelder_mead(f, x0, steps, iters=3000):
    pts = [list(x0)] + [[x0[j] + (steps[j] if j == i else 0) for j in range(len(x0))] for i in range(len(x0))]
    vals = [f(p) for p in pts]
    for _ in range(iters):
        order = sorted(range(len(pts)), key=lambda i: vals[i])
        pts, vals = [pts[i] for i in order], [vals[i] for i in order]
        c = [sum(p[j] for p in pts[:-1]) / (len(pts) - 1) for j in range(len(x0))]
        refl = [c[j] + (c[j] - pts[-1][j]) for j in range(len(x0))]
        fr = f(refl)
        if fr < vals[0]:
            exp = [c[j] + 2 * (c[j] - pts[-1][j]) for j in range(len(x0))]
            fe = f(exp)
            pts[-1], vals[-1] = (exp, fe) if fe < fr else (refl, fr)
        elif fr < vals[-2]:
            pts[-1], vals[-1] = refl, fr
        else:
            con = [c[j] + 0.5 * (pts[-1][j] - c[j]) for j in range(len(x0))]
            fc = f(con)
            if fc < vals[-1]:
                pts[-1], vals[-1] = con, fc
            else:
                pts = [pts[0]] + [[pts[0][j] + 0.5 * (p[j] - pts[0][j]) for j in range(len(x0))] for p in pts[1:]]
                vals = [vals[0]] + [f(p) for p in pts[1:]]
    i = min(range(len(pts)), key=lambda i: vals[i])
    return pts[i], vals[i]


# ------------------------------------------------------------------ [K] hardcoding size (PROOF.md Cor. 3.8, Sec. 7)
def k0_for(s, lmax, eps):
    """least k, a multiple of den(s), meeting Cor. 3.8's two conditions (necessary, not sufficient):
       (a) (lmax + eps/4) c / k^2 <= eps/4 with c = den(s) ceil(k / (s den(s)))   (padding of Lemma 3.2),
       (b) log2(k + 1)/k <= eps/4                                                  (descriptions of Lemma 3.2)."""
    den = s.denominator

    def ok(k):
        c = den * -(-F(k) // (s * den))
        a = (lmax + eps / 4) * c <= eps / 4 * k * k
        b = (log2(I(float(k + 1))) / I(float(k))).hi <= float(eps) / 4
        return a and b
    hi = den
    while not ok(hi):
        hi *= 2
    lo = hi // 2
    while hi - lo > den:   # ok is monotone in k for these k
        mid = (lo + hi) // 2 // den * den
        if mid <= lo:
            break
        if ok(mid):
            hi = mid
        else:
            lo = mid
    k = max(den, lo // den * den)
    while not ok(k):
        k += den
    assert not ok(k - den) or k == den
    c = den * -(-F(k) // (s * den))
    return k, int(c), k * k + int(c)


# ------------------------------------------------------------------ the claimed data
NB = 8 * 10 ** 9   # the explicit piece length N_b (PROOF.md Sec. 4.3); a_b = alpha N_b/2 and s a_b are integers
# rational parameters (alpha, mu, delta) per (s, det); found by the float search, then certified as data
PARAMS = {
    (F(11, 100), True): (F(5571847, 10 ** 7), F(2193169, 10 ** 7), F(15323, 10 ** 7)),
    (F(1, 8), True): (F(223753, 400000), F(2215851, 10 ** 7), F(2969, 2000000)),
    (F(11, 100), False): (F(5158197, 10 ** 7), F(4757627, 10 ** 7), F(7541, 5000000)),
    (F(1, 8), False): (F(1303607, 2500000), F(2442283, 5000000), F(1831, 1250000)),
}
CLAIM = {(F(11, 100), True): 0.4998322132, (F(1, 8), True): 0.4998357367,
         (F(11, 100), False): 0.4996416844, (F(1, 8), False): 0.4996427665}


def main():
    fails = 0
    print("=== [XI] circuit gain ===")
    XI, LMAX = {}, {}
    for s, D in XI_DATA.items():
        ok, xq, lq = cert_xi(s, D)
        fails += not ok
        XI[s] = xq
        LMAX[s] = lq
    print("=== [LAM] splitter bound and lambda ===")
    okS, w = splitter_S(1 << 14)
    print(f"S(q) <= 3q - 3 - 2 log2 q for every q <= 2^14: {okS} (largest excess {w:.4f})")
    fails += not okS
    LAM = {}
    for key, (a, mu, dl) in PARAMS.items():
        if key[1]:
            LAM[key] = lam_bound(NB, a)
            print(f"s={key[0]}: N_b = {NB}, a_b = {F(NB) * a / 2}, s a_b = {key[0] * F(NB) * a / 2}: "
                  f"lambda <= {LAM[key]:.4e}, mu lambda <= {LAM[key] * float(mu):.4e}")
            fails += (key[0] * F(NB) * a / 2).denominator != 1
    if "--search" in sys.argv:
        print("=== float search (optional; data above is what is certified) ===")
        for (s, det), p in PARAMS.items():
            lam = LAM.get((s, det), 0.0)
            x, v = nelder_mead(lambda q: E_float(q, float(s), float(XI[s]), det, lam), [float(t) for t in p],
                               [0.01, 0.01, 1e-4])
            print(f"   s={s} det={det}: float optimum {v:.10f} at alpha={x[0]:.7f} mu={x[1]:.7f} delta={x[2]:.7f}")
    print("=== [K] hardcoded circuit size at eps = 1e-9 (necessary conditions only) ===")
    for s in XI_DATA:   # lmax: this s's own certified l, rounded up (any upper bound on l is valid here)
        k, cc, N0 = k0_for(s, LMAX[s], F(1, 10 ** 9))
        ex = len(str(N0)) - 1   # a lower bound must be rounded DOWN (float formatting would round 2.20358 up)
        lb = f"{N0 // 10 ** (ex - 4) // 10 ** 4}.{N0 // 10 ** (ex - 4) % 10 ** 4:04d}e{ex}"
        print(f"   s={s}: lmax = {LMAX[s]}, k_0 = {k}, padding c = {cc}, N0 = k_0^2 + c = {N0} (>= {lb})")
    print("=== [E] exponents ===")
    res = {}
    for (s, det), (a, mu, dl) in PARAMS.items():
        lam = LAM.get((s, det), 0.0)
        E, T = E_rig(s, a, mu, dl, XI[s], kap_lo_for(dl), det, lam)
        res[(s, det)] = E
        ok = E <= CLAIM[(s, det)]
        fails += not ok
        tt = ", ".join(f"{k} {v:.9f}" for k, v in sorted(T.items()))
        print(f"{'DET ' if det else 'RAND'} s={s} alpha={a} mu={mu} delta={dl}: E <= {E:.10f} "
              f"(claim {CLAIM[(s, det)]}: {ok})\n     [{tt}]")
    s = F(11, 100)
    a, mu, dl = PARAMS[(s, True)]
    lam, kl, xi, claim = LAM[(s, True)], kap_lo_for(dl), XI[s], CLAIM[(s, True)]
    print("=== must-fail controls (each must be REJECTED: rigorous bound above the claim) ===")
    c = []
    c.append(("K1 claim E_det - 1e-9", res[(s, True)] > claim - 1e-9))
    c.append(("K2 mu raised 1%", E_rig(s, a, mu * F(101, 100), dl, xi, kl, True, lam)[0] > claim))
    c.append(("K3 xi = 0 gives E >= 1/2", E_rig(s, a, mu, dl, 0, kl, True, lam)[0] >= 0.5))
    c.append(("K4 delta doubled", E_rig(s, a, mu, 2 * dl, xi, kap_lo_for(2 * dl), True, lam)[0] > claim))
    try:
        E_rig(s, a, mu, dl, xi, F(1, 2) - F(1, 1000), True, lam)
        c.append(("K5 kappa range cut to |kappa - 1/2| <= 1e-3", False))
    except AssertionError:
        c.append(("K5 kappa range cut to |kappa - 1/2| <= 1e-3 (range certificate rejects)", True))
    ra, rmu, rdl = PARAMS[(s, False)]
    c.append(("K6 deterministic claim at the randomized parameters (P6 too big)",
              E_rig(s, ra, rmu, rdl, xi, kap_lo_for(rdl), True, lam)[0] > claim))
    lam_small = lam_bound(2 * 10 ** 7, a) if (F(2 * 10 ** 7) * a / 2).denominator == 1 else lam_bound(10 ** 8, a)
    c.append((f"K7 N_b = 2e7 instead of 8e9 (lambda {lam_small:.2e})",
              E_rig(s, a, mu, dl, xi, kl, True, lam_small)[0] > claim))
    E0 = E_rig(s, a, mu, dl, xi, kl, True, 0.0)[0]
    c.append((f"K8 lambda dropped: the lambda-free bound {E0:.10f} is below the claim, so the claim includes lambda",
              E0 < claim and res[(s, True)] > E0))
    c.append(("K9 the randomized claim 0.4996417 made for the deterministic algorithm",
              E_rig(s, a, mu, dl, xi, kl, True, lam)[0] > CLAIM[(s, False)]))
    for name, ok in c:
        print(f"   {name}: {'rejected' if ok else 'NOT REJECTED'}")
        fails += not ok
    print("CERTIFICATE", "PASS" if fails == 0 else f"FAIL ({fails})")
    return fails


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
