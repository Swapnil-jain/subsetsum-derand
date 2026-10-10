"""Certificate for the Stage 1 exponent (PROOF.md, Sec. 6).

Exact rationals (fractions.Fraction) with outward rounding to a 2^-PREC grid; no floating point
enters any asserted inequality. Pure standard library, a few seconds.

Quantities (CJRS arXiv 2301.07134, Sec. 4; log = log2, H = binary entropy):
    beta(e2)        = 1 / H((1 + e2)/4)
    lambda0(e1, e2) = (1 - e1)/2 * beta * (1 - H((1 - e2)/2))
    delta(e1, e2)   = (1 - H((1 - e1)/2)) * beta                      (CJRS Lemma 6 with eps = e1)
    theta0(e1, e2)  = (1 - e1/2) * beta - 1 - lambda0
    g(e1, e2)       = min(lambda0/2, delta/2, theta0)                 (PROOF.md, Def. 6.1)
CJRS's roots solve (3) (1 - H((1-e1)/2)) / ((1-e1)/2) = 1 - H((1-e2)/2)
               and (4) 1 + e1 - 3 H((1-e1)/2) = -2 H((1+e2)/4).

Claims certified:
  [A] at the rational point P = (15792/10^5, 24267/10^5): g(P) > 0.0101, and the side conditions
      0 < e1, e2 < 1, theta0 > 0, lambda0 > 0. This alone gives Theorem 1 with gamma* >= 0.0101.
  [B] (3), (4) have a root (e1*, e2*) in an explicit box of width 2e-12 in e1; on that box every one
      of the three terms lies in [0.0101041782, 0.0101041783], so g(e1*, e2*) = 0.010104 (6 digits);
      also beta < 4/3 there and at P (used by Lemma 2.1(ii)).
  Must-fail controls (the same checker must reject):
  [C1] CJRS's printed rounding (0.1579, 0.2427): g > 0.0101 is false (certified g < 0.0101).
  [C2] at the root box: g > 0.010105 is false (certified g < 0.010105).
Exit code 0 iff [A], [B] hold and both controls are rejected.
"""
from fractions import Fraction as F
import sys

PREC = 256  # grid 2^-PREC for outward rounding
SCALE = 1 << PREC


def rdown(x):
    return F((x.numerator * SCALE) // x.denominator, SCALE)


def rup(x):
    return F(-((-x.numerator * SCALE) // x.denominator), SCALE)


class I:
    """Closed interval [lo, hi] of rationals; every operation rounds outward."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = rdown(lo), rup(hi)

    @staticmethod
    def _c(x):
        return x if isinstance(x, I) else I(x)

    def __add__(s, o):
        o = I._c(o); return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __sub__(s, o):
        o = I._c(o); return I(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return I._c(o) - s

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __mul__(s, o):
        o = I._c(o)
        p = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(min(p), max(p))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = I._c(o)
        assert o.lo > 0, "divisor interval must be positive"
        return s * I(1 / o.hi, 1 / o.lo)

    def __rtruediv__(s, o):
        return I._c(o) / s

    def __repr__(s):
        return f"[{float(s.lo):.12g}, {float(s.hi):.12g}]"


def ln_point(x):
    """Enclosure of ln(x) for a rational x > 0: ln x = 2 atanh(z), z = (x-1)/(x+1), |z| < 1.
    The series runs in integer fixed point (scale 2^PREC); every lower bound is floored and every
    upper bound ceiled, so [lo, hi] contains ln x."""
    x = F(x)
    assert x > 0
    z = (x - 1) / (x + 1)
    sgn, a = (1, z) if z >= 0 else (-1, -z)
    assert a < 1
    fl = lambda q: (q.numerator << PREC) // q.denominator
    ce = lambda q: -((-q.numerator << PREC) // q.denominator)
    a_lo, a_hi = fl(a), ce(a)
    a2_lo, a2_hi = (a_lo * a_lo) >> PREC, -((-a_hi * a_hi) >> PREC)
    assert a2_hi < SCALE
    s_lo = s_hi = 0
    p_lo, p_hi = a_lo, a_hi  # fixed-point bounds on a^(2k+1)
    k = 0
    while True:
        s_lo += p_lo // (2 * k + 1)
        s_hi += -(-p_hi // (2 * k + 1))
        p_lo, p_hi = (p_lo * a2_lo) >> PREC, -((-p_hi * a2_hi) >> PREC)
        k += 1
        # tail sum_{j>=k} a^(2j+1)/(2j+1) <= a^(2k+1) / ((2k+1)(1 - a^2))
        tail = -((-p_hi * SCALE) // ((2 * k + 1) * (SCALE - a2_hi)))
        if tail <= 1:
            break
    lo, hi = F(2 * s_lo, SCALE), F(2 * (s_hi + tail), SCALE)
    return I(lo, hi) if sgn > 0 else I(-hi, -lo)


LN2 = ln_point(2)


def log2_point(x):
    return ln_point(x) / LN2


def H_point(x):
    x = F(x)
    assert 0 < x < 1
    return -(x * log2_point(x)) - ((1 - x) * log2_point(1 - x))


def H(x):
    """H on an interval inside (0, 1/2], where H is increasing."""
    x = I._c(x)
    assert 0 < x.lo and x.hi <= F(1, 2), x
    return I(H_point(x.lo).lo, H_point(x.hi).hi)


def terms(e1, e2):
    e1, e2 = I._c(e1), I._c(e2)
    beta = 1 / H((1 + e2) / 4)
    lam0 = (1 - e1) / 2 * beta * (1 - H((1 - e2) / 2))
    delta = (1 - H((1 - e1) / 2)) * beta
    theta0 = (1 - e1 / 2) * beta - 1 - lam0
    return dict(beta=beta, lambda0=lam0, delta=delta, theta0=theta0,
                t1=lam0 / 2, t2=delta / 2, t3=theta0)


def g_lower(T):
    return min(T["t1"].lo, T["t2"].lo, T["t3"].lo)


def g_upper(T):
    return min(T["t1"].hi, T["t2"].hi, T["t3"].hi)


def certify_above(e1, e2, target):
    """True iff g(e1, e2) > target is certified (lower end of the enclosure above target)."""
    return g_lower(terms(e1, e2)) > F(target)


# Root enclosure for (3), (4). (4) gives H((1+e2)/4) = v(e1) := (3 H((1-e1)/2) - 1 - e1)/2, and H is
# increasing on [1/4, 1/2], so e2 = 4 H^{-1}(v) - 1 is a continuous function of e1. Substituting into (3)
# leaves one equation G(e1) = 0 with G continuous; a certified sign change of G on [a, b] gives a root.

def Hinv_enclose(v, lo=F(1, 4), hi=F(1, 2), steps=70):
    """Interval [u_lo, u_hi] containing every u in [1/4, 1/2] with H(u) in v."""
    assert H_point(lo).hi < v.lo, "v below H(1/4)"
    assert v.hi < 1, "v above H(1/2) = 1"
    ulo, uhi = lo, hi  # H(ulo) < v.lo and H(uhi) >= v.hi (H(1/2) = 1 exactly)
    for _ in range(steps):
        m = (ulo + uhi) / 2
        Hm = H_point(m)
        if Hm.hi < v.lo:
            ulo = m
        elif Hm.lo > v.hi:
            uhi = m
        else:
            break
    return I(ulo, uhi)


def e2_of(e1):
    e1 = I._c(e1)
    v = (3 * H((1 - e1) / 2) - 1 - e1) / 2
    return 4 * Hinv_enclose(v) - 1


def G(e1):
    e1 = I._c(e1)
    e2 = e2_of(e1)
    lhs = (1 - H((1 - e1) / 2)) / ((1 - e1) / 2)
    return lhs - (1 - H((1 - e2) / 2)), e2


def main():
    ok = True
    print(f"[setup] ln 2 in {LN2} (width {float(LN2.hi - LN2.lo):.1e})")

    # [A] rational point
    P = (F(15792, 10**5), F(24267, 10**5))
    TA = terms(*P)
    print(f"[A] P = (0.15792, 0.24267): beta {TA['beta']}  lambda0 {TA['lambda0']}  delta {TA['delta']}")
    print(f"    lambda0/2 {TA['t1']}  delta/2 {TA['t2']}  theta0 {TA['t3']}")
    a_ok = (0 < P[0] < 1 and 0 < P[1] < 1 and TA["theta0"].lo > 0 and TA["lambda0"].lo > 0
            and TA["beta"].lo > 1 and TA["beta"].hi < F(4, 3) and certify_above(*P, F(101, 10**4)))
    print(f"    certified g(P) >= {float(g_lower(TA)):.10f} > 0.0101: {a_ok}")
    ok &= a_ok

    # [B] root box
    a, b = F(157920369638, 10**12), F(157920369640, 10**12)
    Ga, e2a = G(a)
    Gb, e2b = G(b)
    print(f"[B] G(a) {Ga}  G(b) {Gb}  (a, b) = ({float(a):.12f}, {float(b):.12f})")
    sign_change = Ga.hi < 0 < Gb.lo
    E1 = I(a, b)
    E2 = e2_of(E1)
    TB = terms(E1, E2)
    print(f"    root box: e1 in {E1}, e2 in {E2}")
    print(f"    lambda0/2 {TB['t1']}  delta/2 {TB['t2']}  theta0 {TB['t3']}")
    lo_all = min(TB[k].lo for k in ("t1", "t2", "t3"))
    hi_all = max(TB[k].hi for k in ("t1", "t2", "t3"))
    b_ok = (sign_change and lo_all >= F(101041782, 10**10) and hi_all <= F(101041783, 10**10)
            and TB["beta"].hi < F(4, 3))
    print(f"    beta {TB['beta']} (< 4/3 needed by Lemma 2.1)")
    print(f"    sign change {sign_change}; all three terms in [{float(lo_all):.13f}, {float(hi_all):.13f}]"
          f" subset of [0.0101041782, 0.0101041783]: {b_ok}")
    ok &= b_ok

    # [C1] CJRS rounded point must fail
    TC = terms(F(1579, 10**4), F(2427, 10**4))
    c1_rejected = not certify_above(F(1579, 10**4), F(2427, 10**4), F(101, 10**4))
    c1_below = g_upper(TC) < F(101, 10**4)
    print(f"[C1] (0.1579, 0.2427): g in [{float(g_lower(TC)):.13f}, {float(g_upper(TC)):.13f}];"
          f" '> 0.0101' rejected: {c1_rejected}; certified below 0.0101: {c1_below}")
    ok &= c1_rejected and c1_below

    # [C2] overclaim at the root box must fail
    c2_rejected = not (g_lower(TB) > F(10105, 10**6))
    c2_below = g_upper(TB) < F(10105, 10**6)
    print(f"[C2] root box: '> 0.010105' rejected: {c2_rejected}; certified below 0.010105: {c2_below}")
    ok &= c2_rejected and c2_below

    print("CERTIFICATE", "PASS" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
