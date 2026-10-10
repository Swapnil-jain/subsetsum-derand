"""Generate SubsetsumLean/Stage1Points.lean, the kernel check of derand/stage1/cert_gamma.py.

Pure standard library. Every rational bound written into the Lean file is first checked here with the exact
formula Lean's kernel evaluates (`logOK` / `hbOK` of Basic.lean, replicated below in Fractions), so a bound that
Lean would reject is never emitted. The points are cert_gamma.py's own:
  [A]  P = (15792/10^5, 24267/10^5), claim g(P) > 0.0101 and the side conditions;
  [B]  the root box e1 in [0.157920369638, 0.157920369640] (cert_gamma.py's a, b), e2 in cert_gamma.py's enclosure
       e2_of(E1) rounded outward to 15 places; every term in (0.0101041782, 0.0101041783) on the whole box;
       the zero curve of (4) crosses the box (F4 < 0 on its lower edge, > 0 on its upper edge), and (3) changes
       sign between the slices e1 = a and e1 = b;
  [C1] (0.1579, 0.2427): g < 0.0101 (must fail);
  [C2] on the box: g < 0.010105, and the next-digit claims fail.
Run:  python3 gen_stage1.py            (writes SubsetsumLean/Stage1Points.lean, prints the controls it chose)
"""
from fractions import Fraction as F
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
STAGE1 = os.path.join(HERE, "..", "cert")
sys.path.insert(0, STAGE1)
import cert_gamma as CG  # noqa: E402  (only for the root enclosure e2_of, which the script certifies)

NTERMS = 60
DIG = 40  # decimal places of every emitted bound

# Basic.lean's log 2 bounds, verbatim.
L2lo = F(693147180559945309417232121458176568075500134, 10 ** 45) - F(1, 10 ** 42)
L2hi = F(693147180559945309417232121458176568075500134, 10 ** 45) + F(1, 10 ** 42)


def lsum(t, n):
    s = F(0)
    p = F(1)
    for i in range(n):
        p *= t
        s += p / (i + 1)
    return s


def lrem(t, n):
    return abs(t) ** (n + 1) / (1 - abs(t))


def log_series(x, k, n):
    """The enclosure of log x that Lean's logOK compares against (exactly the same formula)."""
    t = 1 - x / F(2) ** k
    assert abs(t) < 1
    s, r = lsum(t, n), lrem(t, n)
    return -s - r + min(k * L2lo, k * L2hi), -s + r + max(k * L2lo, k * L2hi)


def down(q, d=DIG):
    return F(math.floor(q * 10 ** d), 10 ** d)


def up(q, d=DIG):
    return F(math.ceil(q * 10 ** d), 10 ** d)


def best_k(x):
    """k with x / 2^k in [2/3, 4/3], so |t| <= 1/3."""
    k = 0
    while x / F(2) ** k > F(4, 3):
        k += 1
    while x / F(2) ** k < F(2, 3):
        k -= 1
    return k


def logOK(x, k, n, lo, hi):
    a, b = log_series(x, k, n)
    return 0 < x and abs(1 - x / F(2) ** k) < 1 and lo <= a and b <= hi


def hb_cert(x):
    """(k1, k2, l1, u1, l2, u2, lo, hi) with hbOK true; [lo, hi] encloses H(x) in bits."""
    k1, k2 = best_k(x), best_k(1 - x)
    a1, b1 = log_series(x, k1, NTERMS)
    a2, b2 = log_series(1 - x, k2, NTERMS)
    l1, u1, l2, u2 = down(a1), up(b1), down(a2), up(b2)
    nlo = -x * u1 - (1 - x) * u2
    nhi = -x * l1 - (1 - x) * l2
    lo, hi = down(nlo / L2hi), up(nhi / L2lo)
    ok = (logOK(x, k1, NTERMS, l1, u1) and logOK(1 - x, k2, NTERMS, l2, u2) and 0 < x < 1 and 0 <= lo and
          0 <= hi and lo * L2hi <= nlo and nhi <= hi * L2lo)
    assert ok, x
    return k1, k2, l1, u1, l2, u2, lo, hi


def _frac(x):
    """p/q text; a decimal fraction keeps its power-of-ten denominator, so literals read as in the scripts."""
    x = F(x)
    if x.denominator == 1:
        return f"{x.numerator}"
    for k in range(1, 61):
        if (x * 10 ** k).denominator == 1:
            return f"{x.numerator * 10 ** k // x.denominator}/{10 ** k}"
    return f"{x.numerator}/{x.denominator}"


def q(x):
    """Lean ℚ literal."""
    return f"({_frac(x)})"


def r(x):
    """Lean ℝ literal."""
    return f"({_frac(x)} : ℝ)"


class Pt:
    """Collects the Hb bounds one theorem needs and writes the `obtain` lines."""

    def __init__(self):
        self.lines, self.H = [], {}

    def need(self, expr, x):
        """expr: the real expression as Lean text (must match the lemma's syntactic form); x its exact value."""
        if expr in self.H:
            return self.H[expr]
        k1, k2, l1, u1, l2, u2, lo, hi = hb_cert(F(x))
        i = len(self.H)
        self.lines.append(
            f"  obtain ⟨h{i}l, h{i}h⟩ := Hb_mem {expr} {q(x)} ({k1}) ({k2}) {NTERMS} {q(l1)} {q(u1)} {q(l2)} {q(u2)} "
            f"{q(lo)} {q(hi)}\n    (by norm_num) (by decide +kernel)")
        self.H[expr] = (f"h{i}l", f"h{i}h", lo, hi)
        return self.H[expr]


def box_terms(a, b, c, d):
    """Python mirror of box_bounds: the rational interval of each term that the Lean lemma states."""
    P = Pt()
    A1 = P.need(f"((1 + {r(c)}) / 4)", (1 + c) / 4)
    A2 = P.need(f"((1 + {r(d)}) / 4)", (1 + d) / 4)
    B1 = P.need(f"((1 - {r(d)}) / 2)", (1 - d) / 2)
    B2 = P.need(f"((1 - {r(c)}) / 2)", (1 - c) / 2)
    C1 = P.need(f"((1 - {r(b)}) / 2)", (1 - b) / 2)
    C2 = P.need(f"((1 - {r(a)}) / 2)", (1 - a) / 2)
    Alo, Ahi, Blo, Bhi, Clo, Chi = A1[2], A2[3], B1[2], B2[3], C1[2], C2[3]
    T = dict(
        beta=(1 / Ahi, 1 / Alo),
        lam0=((1 - b) / 2 * (1 / Ahi) * (1 - Bhi), (1 - a) / 2 * (1 / Alo) * (1 - Blo)),
        delta=((1 - Chi) * (1 / Ahi), (1 - Clo) * (1 / Alo)),
    )
    T["theta0"] = ((1 - b / 2) * (1 / Ahi) - 1 - T["lam0"][1], (1 - a / 2) * (1 / Alo) - 1 - T["lam0"][0])
    T["t1"] = (T["lam0"][0] / 2, T["lam0"][1] / 2)
    T["t2"] = (T["delta"][0] / 2, T["delta"][1] / 2)
    T["t3"] = T["theta0"]
    call = (f"box_bounds (a := {r(a)}) (b := {r(b)}) (c := {r(c)}) (d := {r(d)}) {{E1}} {{E2}} {{E3}} {{E4}} "
            f"(by norm_num) (by norm_num) (by norm_num) (by norm_num) "
            f"{A1[0]} {A2[1]} {B1[0]} {B2[1]} {C1[0]} {C2[1]} (by norm_num) (by norm_num) (by norm_num)")
    return P, T, call


NORM = "\n  norm_num at be1 be2 la1 la2 de1 de2 th1 th2"
BOX_INTRO = """  obtain ⟨be1, be2, la1, la2, de1, de2, th1, th2⟩ := {call}"""


def point_cert(name, doc, e1, e2, s):
    """theorem name : Admissible e1 e2 s (the degenerate box a = b = e1, c = d = e2)."""
    P, T, call = box_terms(e1, e1, e2, e2)
    lo = min(T["t1"][0], T["t2"][0], T["t3"][0])
    assert lo > s and T["beta"][0] > 1 and T["beta"][1] < F(4, 3) and T["lam0"][0] > 0 and T["theta0"][0] > 0
    c = call.format(E1="le_rfl", E2="le_rfl", E3="le_rfl", E4="le_rfl")
    body = "\n".join(P.lines) + "\n" + BOX_INTRO.format(call=c) + NORM + """
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by linarith, by linarith, by linarith, by linarith,
    g_gt (by linarith) (by linarith) (by linarith)⟩"""
    return f"/-- {doc} -/\ntheorem {name} : Admissible {r(e1)} {r(e2)} {r(s)} := by\n{body}\n", T


def point_refute(name, doc, e1, e2, s, T=None):
    """theorem name : ¬ (s < g e1 e2): the binding term's upper bound is below s."""
    P, T, call = box_terms(e1, e1, e2, e2)
    k = min(("t1", "t2", "t3"), key=lambda k: T[k][1])
    assert T[k][1] < s, (name, float(T[k][1]), float(s))
    c = call.format(E1="le_rfl", E2="le_rfl", E3="le_rfl", E4="le_rfl")
    lem = {"t1": "g_le_lam", "t2": "g_le_delta", "t3": "g_le_theta"}[k]
    body = "\n".join(P.lines) + "\n" + BOX_INTRO.format(call=c) + NORM + f"""
  intro h
  have hu := lt_of_lt_of_le h {lem}
  linarith"""
    return f"/-- {doc} -/\ntheorem {name} : ¬ ({r(s)} < g {r(e1)} {r(e2)}) := by\n{body}\n", k


def box_cert(name, doc, a, b, c, d, L, U):
    P, T, call = box_terms(a, b, c, d)
    for k in ("t1", "t2", "t3"):
        assert T[k][0] > L and T[k][1] < U, (k, T[k])
    assert T["beta"][0] > 1 and T["beta"][1] < F(4, 3) and T["lam0"][0] > 0 and T["theta0"][0] > 0
    cl = call.format(E1="h1.1", E2="h1.2", E3="h2.1", E4="h2.2")
    body = "\n".join(P.lines) + f"""
  intro e1 h1 e2 h2
""" + BOX_INTRO.format(call=cl) + f"""
  have a1 : (0 : ℝ) < e1 := lt_of_lt_of_le (by norm_num) h1.1
  have a2 : e1 < 1 := lt_of_le_of_lt h1.2 (by norm_num)
  have a3 : (0 : ℝ) < e2 := lt_of_lt_of_le (by norm_num) h2.1
  have a4 : e2 < 1 := lt_of_le_of_lt h2.2 (by norm_num)""" + NORM + """
  exact ⟨⟨a1, a2, a3, a4, by linarith, by linarith, by linarith, by linarith,
    g_gt (by linarith) (by linarith) (by linarith)⟩, by linarith, by linarith, by linarith⟩"""
    stmt = (f"∀ e1 ∈ Set.Icc {r(a)} {r(b)}, ∀ e2 ∈ Set.Icc {r(c)} {r(d)},\n    Admissible e1 e2 {r(L)} ∧ "
            f"lam0 e1 e2 / 2 < {r(U)} ∧ delta e1 e2 / 2 < {r(U)} ∧ theta0 e1 e2 < {r(U)}")
    return f"/-- {doc} -/\ntheorem {name} :\n    {stmt} := by\n{body}\n", T


def curve_cert(name, doc, a, b, c, d):
    """∀ e1 ∈ [a, b], F4 e1 c < 0 ∧ 0 < F4 e1 d."""
    P = Pt()
    C1 = P.need(f"((1 - {r(b)}) / 2)", (1 - b) / 2)
    C2 = P.need(f"((1 - {r(a)}) / 2)", (1 - a) / 2)
    Ec = P.need(f"((1 + {r(c)}) / 4)", (1 + c) / 4)
    Ed = P.need(f"((1 + {r(d)}) / 4)", (1 + d) / 4)
    up_c = 1 + b - 3 * C1[2] + 2 * Ec[3]
    lo_d = 1 + a - 3 * C2[3] + 2 * Ed[2]
    assert up_c < 0 < lo_d, (float(up_c), float(lo_d))
    body = "\n".join(P.lines) + f"""
  intro e1 h1
  have hc := F4_bounds (e2 := {r(c)}) h1.1 h1.2 (by norm_num) (by norm_num) {C1[0]} {C2[1]} {Ec[0]} {Ec[1]}
  have hd := F4_bounds (e2 := {r(d)}) h1.1 h1.2 (by norm_num) (by norm_num) {C1[0]} {C2[1]} {Ed[0]} {Ed[1]}
  norm_num at hc hd
  exact ⟨by linarith [hc.2], by linarith [hd.1]⟩"""
    stmt = f"∀ e1 ∈ Set.Icc {r(a)} {r(b)}, F4 e1 {r(c)} < 0 ∧ 0 < F4 e1 {r(d)}"
    return f"/-- {doc} -/\ntheorem {name} : {stmt} := by\n{body}\n", (up_c, lo_d)


def slice_cert(name, doc, a, s1, s2, sign):
    """F4 a s1 < 0 < F4 a s2, and F3 a e2 < 0 (sign = -1) or > 0 (sign = +1) on [s1, s2]."""
    P = Pt()
    Ha = P.need(f"((1 - {r(a)}) / 2)", (1 - a) / 2)
    E1 = P.need(f"((1 + {r(s1)}) / 4)", (1 + s1) / 4)
    E2 = P.need(f"((1 + {r(s2)}) / 4)", (1 + s2) / 4)
    Q2 = P.need(f"((1 - {r(s2)}) / 2)", (1 - s2) / 2)
    Q1 = P.need(f"((1 - {r(s1)}) / 2)", (1 - s1) / 2)
    f4a = 1 + a - 3 * Ha[2] + 2 * E1[3]
    f4b = 1 + a - 3 * Ha[3] + 2 * E2[2]
    f3lo = (1 - Ha[3]) / ((1 - a) / 2) - 1 + Q2[2]
    f3hi = (1 - Ha[2]) / ((1 - a) / 2) - 1 + Q1[3]
    assert f4a < 0 < f4b, (float(f4a), float(f4b))
    assert (f3hi < 0) if sign < 0 else (f3lo > 0), (float(f3lo), float(f3hi))
    concl = "F3 " + r(a) + " e2 < 0" if sign < 0 else "0 < F3 " + r(a) + " e2"
    body = "\n".join(P.lines) + f"""
  have ha := F4_bounds (a := {r(a)}) (b := {r(a)}) (e2 := {r(s1)}) le_rfl le_rfl (by norm_num) (by norm_num)
    {Ha[0]} {Ha[1]} {E1[0]} {E1[1]}
  have hb := F4_bounds (a := {r(a)}) (b := {r(a)}) (e2 := {r(s2)}) le_rfl le_rfl (by norm_num) (by norm_num)
    {Ha[0]} {Ha[1]} {E2[0]} {E2[1]}
  norm_num at ha hb
  refine ⟨by linarith [ha.2], by linarith [hb.1], ?_⟩
  intro e2 h
  have hF := F3_bounds (a := {r(a)}) (by norm_num) (by norm_num) h.1 h.2 (by norm_num) (by norm_num)
    {Ha[0]} {Ha[1]} {Q2[0]} {Q1[1]}
  norm_num at hF
  linarith [hF.1, hF.2]"""
    stmt = (f"F4 {r(a)} {r(s1)} < 0 ∧ 0 < F4 {r(a)} {r(s2)} ∧\n    ∀ e2 ∈ Set.Icc {r(s1)} {r(s2)}, {concl}")
    return f"/-- {doc} -/\ntheorem {name} :\n    {stmt} := by\n{body}\n", (f4a, f4b, f3lo, f3hi)


def main():
    out = []
    a, b = F(157920369638, 10 ** 12), F(157920369640, 10 ** 12)
    E2 = CG.e2_of(CG.I(a, b))
    c, d = down(E2.lo, 15), up(E2.hi, 15)
    Sa, Sb = CG.e2_of(CG.I(a)), CG.e2_of(CG.I(b))
    sa1, sa2, sb1, sb2 = down(Sa.lo, 22), up(Sa.hi, 22), down(Sb.lo, 22), up(Sb.hi, 22)
    L, U = F(101041782, 10 ** 10), F(101041783, 10 ** 10)
    P = (F(15792, 10 ** 5), F(24267, 10 ** 5))

    t, TA = point_cert("stage1_A", "[A] cert_gamma.py: P = (0.15792, 0.24267) is admissible and g(P) > 0.0101.",
                       *P, F(101, 10 ** 4))
    out.append(t)
    sA = down(min(TA["t1"][0], TA["t2"][0], TA["t3"][0]), 11)
    t, _ = point_cert("stage1_A_sharp", f"[A] sharper: g(P) > {float(sA):.11f} (11 places, rounded down).", *P, sA)
    out.append(t)
    nA = sA + F(1, 10 ** 11)
    t, k = point_refute("stage1_A_fails_next", f"Control: g(P) > {float(nA):.11f} (next 11th-place unit) is false.",
                        *P, nA)
    out.append(t)
    print(f"[A] g(P) > {float(sA):.11f}; control {float(nA):.11f} refuted via {k}")

    t, TB = box_cert("stage1_box", "[B] cert_gamma.py: on the whole root box every point is admissible with "
                     "saving 0.0101041782, and each of the three terms is below 0.0101041783.", a, b, c, d, L, U)
    out.append(t)
    t, cv = curve_cert("stage1_curve", "[B] the zero curve of (4) crosses the box: F4 < 0 on the edge e2 = c and "
                       "> 0 on the edge e2 = d, for every e1 in [a, b].", a, b, c, d)
    out.append(t)
    t, sl = slice_cert("stage1_slice_a", "[B] slice e1 = a: (4) has its root in [s1, s2], and (3) is negative there.",
                       a, sa1, sa2, -1)
    out.append(t)
    t, sl2 = slice_cert("stage1_slice_b", "[B] slice e1 = b: (4) has its root in [s1, s2], and (3) is positive "
                        "there.", b, sb1, sb2, +1)
    out.append(t)
    print(f"[B] box e2 in [{c}, {d}]; slices a: [{sa1}, {sa2}], b: [{sb1}, {sb2}]")
    print(f"    F3 at a <= {float(sl[3]):.4e}, at b >= {float(sl2[2]):.4e}")

    t, k = point_refute("stage1_C1", "[C1] must fail: at CJRS's printed rounding (0.1579, 0.2427), g > 0.0101 is "
                        "false.", F(1579, 10 ** 4), F(2427, 10 ** 4), F(101, 10 ** 4))
    out.append(t)
    print(f"[C1] refuted via {k}")
    t, k = point_refute("stage1_C2", "[C2] must fail: at the box corner (a, c), g > 0.010105 is false.", a, c,
                        F(10105, 10 ** 6))
    out.append(t)
    t, k = point_refute("stage1_box_fails_U", "Control: at the box corner (a, c), g > 0.0101041783 (the box's upper "
                        "end) is false.", a, c, U)
    out.append(t)
    print(f"[C2] refuted; next-digit box control refuted via {k}")

    hdr = f"""import SubsetsumLean.Stage1Defs

/-!
# Kernel check of `derand/stage1/cert_gamma.py` (generated by `gen_stage1.py`; do not edit)

Each `Hb_mem` line bounds `H` at one rational point by the log series (`decide +kernel` on `hbOK`); the generic
lemmas of `Stage1Defs.lean` turn the corner bounds into bounds on every term, and `norm_num` closes the claims on
rational literals. Controls (`*_fails_*`, `stage1_C1`, `stage1_C2`) are claims that must be false, proved false.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS

"""
    path = os.path.join(HERE, "SubsetsumLean", "Stage1Points.lean")
    with open(path, "w") as f:
        f.write(hdr + "\n".join(out) + "\nend SS\n")
    print("wrote", path)


if __name__ == "__main__":
    main()
