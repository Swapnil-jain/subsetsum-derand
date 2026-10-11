"""Generate SubsetsumLean/Explicit.lean, the kernel check of certificates/cert_explicit.py.

Pure standard library. The design and its integer witnesses are read from cert_explicit.py itself (it is run,
and must exit 0). Every Hb_mem bound written into the Lean file is first checked here with the exact formula
Lean's kernel evaluates (logOK / hbOK of Basic.lean, replicated below in Fractions), so a bound that Lean would
reject is never emitted. Entropy is bounded at 8-digit rational points next to the true arguments, and
Hb_mono / Hb_symm carry the bound across (all arguments lie in [0, 1/2]).
Run:  python3 gen_explicit.py
"""
from fractions import Fraction as F
import contextlib
import io
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, "..", "certificates", "cert_explicit.py")

NTERMS = 40
DIG = 30
# Basic.lean's log 2 bounds, verbatim.
L2lo = F(693147180559945309417232121458176568075500134, 10 ** 45) - F(1, 10 ** 42)
L2hi = F(693147180559945309417232121458176568075500134, 10 ** 45) + F(1, 10 ** 42)


def lsum(t, n):
    s, p = F(0), F(1)
    for i in range(n):
        p *= t
        s += p / (i + 1)
    return s


def log_series(x, k, n):
    t = 1 - x / F(2) ** k
    assert abs(t) < 1
    s, r = lsum(t, n), abs(t) ** (n + 1) / (1 - abs(t))
    return -s - r + min(k * L2lo, k * L2hi), -s + r + max(k * L2lo, k * L2hi)


def down(q, d=DIG):
    return F(math.floor(q * 10 ** d), 10 ** d)


def up(q, d=DIG):
    return F(math.ceil(q * 10 ** d), 10 ** d)


def best_k(x):
    k = 0
    while x / F(2) ** k > F(4, 3):
        k += 1
    while x / F(2) ** k < F(2, 3):
        k -= 1
    return k


def hb_cert(x):
    """(k1, k2, l1, u1, l2, u2, lo, hi) with Lean's hbOK true; [lo, hi] encloses H(x) in bits."""
    k1, k2 = best_k(x), best_k(1 - x)
    a1, b1 = log_series(x, k1, NTERMS)
    a2, b2 = log_series(1 - x, k2, NTERMS)
    l1, u1, l2, u2 = down(a1), up(b1), down(a2), up(b2)
    nlo, nhi = -x * u1 - (1 - x) * u2, -x * l1 - (1 - x) * l2
    lo, hi = down(nlo / L2hi), up(nhi / L2lo)
    assert l1 <= a1 and b1 <= u1 and l2 <= a2 and b2 <= u2 and 0 < x < 1 and 0 <= lo <= hi
    assert lo * L2hi <= nlo and nhi <= hi * L2lo
    return k1, k2, l1, u1, l2, u2, lo, hi


def fr(x):
    x = F(x)
    if x.denominator == 1:
        return f"{x.numerator}"
    for k in range(1, 61):
        if (x * 10 ** k).denominator == 1:
            return f"{x.numerator * 10 ** k // x.denominator}/{10 ** k}"
    return f"{x.numerator}/{x.denominator}"


def R(x):
    return f"({fr(x)} : ℝ)"


def Q(x):
    return f"({fr(x)} : ℚ)"


def QR(x):
    return f"(({fr(x)} : ℚ) : ℝ)"


def hbmem(name, r):
    k1, k2, l1, u1, l2, u2, lo, hi = hb_cert(r)
    line = (f"  obtain ⟨{name}l, {name}h⟩ := Hb_mem {R(r)} {Q(r)} ({k1}) ({k2}) {NTERMS} {Q(l1)} {Q(u1)} {Q(l2)} "
            f"{Q(u2)} {Q(lo)} {Q(hi)}\n    (by norm_num) (by decide +kernel)\n")
    return line, lo, hi


def load_cert():
    ns = {"__name__": "cert"}
    buf = io.StringIO()
    rc = 0
    with contextlib.redirect_stdout(buf):
        try:
            exec(compile(open(CERT).read(), CERT, "exec"), ns)
        except SystemExit as e:
            rc = e.code
    assert rc == 0, "cert_explicit.py must pass"
    return ns


def design_lit(ns, k, e, a, J, dR=None):
    N = k * k + 2 * k
    dR = ns["DR_P"] if dR is None else dR
    d = ns["design"](k, e, a, dR=dR)
    dstar = d["dstar"] if d else 1
    return (f"{{ k := {k}, e := {Q(e)}, a := {Q(a)}, dL := dLp, dR := {Q(dR)}, J := {J}, lgN := {(N + 1).bit_length()}, "
            f"lgk := {(k + 1).bit_length()}, lgJ := {max(J, 1).bit_length()}, dstar := {dstar} }}"), d


def main():
    ns = CE = load_cert()
    A, B = CE["A_YL"], CE["B_YL"]
    r = CE["r"]
    kA, eA = CE["K_A"], CE["EPS_A"]
    assert CE["LN2_LO"] == F(6931, 10000) and CE["LOG2E_LO"] == F(14426, 10000)
    assert r["LD"] == 4855 and r["c"] == 4858 and r["rmax"] == 1
    dA, _ = design_lit(ns, kA, eA, A, r["J"])
    n0_bound = F(589, 100) * 10 ** 59
    assert 2 * r["c"] * r["N"] / CE["gain"](max(r["epsL"], r["epsR"])) <= n0_bound

    # entropy points (8 digits), outward
    one_b = 1 - B
    r_lo1b = F(math.floor(one_b * 10 ** 8), 10 ** 8)       # <= 1 - b: lower bound on H(b)
    r_hi1b = F(math.ceil(one_b * 10 ** 8), 10 ** 8)        # >= 1 - b: upper bound on H(b)
    r_4a = F(math.ceil(4 * A * 10 ** 8), 10 ** 8)
    r_mid = F(math.ceil(2 * (1 - B - 2 * A) * 10 ** 8), 10 ** 8)
    r_d2 = F(math.floor(2 * A / (1 - B) * 10 ** 8), 10 ** 8)
    l_b, lo_b, _ = hbmem("hb", r_lo1b)
    l_bu, _, hi_b = hbmem("hu", r_hi1b)
    l_4a, _, hi_4a = hbmem("h4", r_4a)
    l_mid, _, hi_mid = hbmem("hm", r_mid)
    l_d2, lo_d2, _ = hbmem("hd", r_d2)
    m1 = down(lo_b - hi_4a / 2 - hi_mid / 2 - 4 * A, 6)
    m2 = down((1 - B) * lo_d2 - 8 * A, 6)
    assert m1 >= F(381, 10 ** 5) and m2 >= F(726, 10 ** 6) and hi_b <= F(1, 10) and lo_b > F(7, 100)
    aR, bR = R(A), R(B)

    controls = []
    J1 = CE["J_of"](F(1, 1000), 115940 ** 2 + 2 * 115940)
    dC1, c1 = design_lit(ns, 115940, F(1, 1000), F(1, 2635), J1)
    J2 = CE["J_of"](F(1, 10 ** 4), r["N"])
    dC2, c2 = design_lit(ns, kA, F(1, 10 ** 4), A, J2)
    dC4, c4 = design_lit(ns, kA, eA, A, r["J"], dR=CE["DR_P"] - F(1, 10 ** 11))
    assert c1["epsL"] > F(1, 10 ** 9) and c2["epsL"] > F(1, 10 ** 9) and not c4["ok_sec"]
    e3 = F(1, 10 ** 27)
    assert 2 * e3 * e3 * r["N"] * F(3, 2) - 2 < 0

    out = f'''import SubsetsumLean.ExplicitDefs

/-!
# Kernel check of `certificates/cert_explicit.py` (generated by `gen_explicit.py`; do not edit)

`explicit_A` is Certificate [A]: every check of the design at k = {kA}, eps' = 10^-13 holds, with the property of
each integer witness stated in `DesignOK`. `ln2_bounds` proves the two analytic constants the formulas use.
`explicit_dom1`, `explicit_dom2` and `explicit_Hb` are Ye-Li's two dominance inequalities and Lemma E6's entropy
hypothesis, about the real binary entropy. Controls (`explicit_C1` to `explicit_C7`): the claims the script must
reject, proved false.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS

/-- The design of Certificate [A]. -/
def dA : Design := {dA}

/-- The designs of controls C1, C2 and C4. -/
def dC1 : Design := {dC1}
def dC2 : Design := {dC2}
def dC4 : Design := {dC4}

/-- [A] every check of Certificate [A]: k even, 10^26 | N0, the witnesses J, d*, log2 bounds, the three-piece
structure, the secant, N0 Delta >= 1, log2(8 D_inf)/N0 <= 4855, eps_L, eps_R <= 1e-9, the padding, Lemma E6's
numeric hypotheses, and c = L_D + 3 <= 4858. -/
theorem explicit_A : DesignOK dA (10 ^ 26) 4855 4858 where
  k_even := by decide +kernel
  q_dvd := by decide +kernel
  lgN := by decide +kernel
  lgk := by decide +kernel
  lgJ := by decide +kernel
  den_pos := by decide +kernel
  J_ok := by decide +kernel
  e_le := by decide +kernel
  struct := by decide +kernel
  slopes := by decide +kernel
  secant := by decide +kernel
  NDelta := by decide +kernel
  dstar_ok := by decide +kernel
  LD_le := by decide +kernel
  epsL_le := by decide +kernel
  epsR_le := by decide +kernel
  pad := by decide +kernel
  e6 := by decide +kernel
  c_le := by decide +kernel

/-- [A] the gain and n0: g > 0 and n0 = 2 c N0 / g <= 5.89e59. -/
theorem explicit_A_n0 : 0 < dA.gain ∧ 2 * dA.c * dA.Nq / dA.gain ≤ {Q(n0_bound)} := by decide +kernel

/-- The analytic constants: ln 2 >= 0.6931 and log2 e = 1 / ln 2 >= 1.4426 (and < 3/2, used by control C3). -/
theorem ln2_bounds : ((LN2lo : ℚ) : ℝ) ≤ log 2 ∧ ((LOG2Elo : ℚ) : ℝ) ≤ 1 / log 2 ∧ 1 / log 2 < 3 / 2 := by
  obtain ⟨l, u⟩ := log_two_mem
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  norm_num [L2lo, L2hi] at l u
  refine ⟨by norm_num [LN2lo]; linarith, ?_, ?_⟩
  · rw [le_div_iff₀ hL]; norm_num [LOG2Elo]; nlinarith
  · rw [div_lt_iff₀ hL]; linarith

/-- Ye-Li Sec. 3.5, first dominance inequality: E1(1/4) = h(b) - 2 h(1/4, a) - h(1/2, 1-b-2a) > 4a, with margin
{fr(m1)}. -/
theorem explicit_dom1 : 4 * {aR} + {R(m1)} <
    Hb {bR} - 2 * (1 / 4 * Hb (4 * {aR})) - 1 / 2 * Hb (2 * (1 - {bR} - 2 * {aR})) := by
{l_b}{l_4a}{l_mid}  have e1 : {QR(lo_b)} ≤ Hb {bR} := by
    rw [← Hb_symm]; exact Hb_ge_of (by norm_num) (by norm_num) (by norm_num) hbl
  have e2 : Hb (4 * {aR}) ≤ {QR(hi_4a)} := Hb_le_of (by norm_num) (by norm_num) (by norm_num) h4h
  have e3 : Hb (2 * (1 - {bR} - 2 * {aR})) ≤ {QR(hi_mid)} := Hb_le_of (by norm_num) (by norm_num) (by norm_num) hmh
  norm_num at e1 e2 e3 ⊢
  linarith

/-- Ye-Li Sec. 3.5, second dominance inequality: h(1-b, 2a) = (1-b) H(2a/(1-b)) > 8a, with margin {fr(m2)}. -/
theorem explicit_dom2 : 8 * {aR} + {R(m2)} < (1 - {bR}) * Hb (2 * {aR} / (1 - {bR})) := by
{l_d2}  have e1 : {QR(lo_d2)} ≤ Hb (2 * {aR} / (1 - {bR})) := Hb_ge_of (by norm_num) (by norm_num) (by norm_num) hdl
  have hpos : (0 : ℝ) < 1 - {bR} := by norm_num
  have := mul_le_mul_of_nonneg_left e1 hpos.le
  norm_num at this ⊢
  linarith

/-- Lemma E6's entropy hypothesis: H(b) <= 1/10 (and 1 - b <= 1/100, a rational fact checked in `explicit_params`). -/
theorem explicit_Hb : Hb {bR} ≤ 1 / 10 := by
{l_bu}  rw [← Hb_symm]
  have := Hb_le_of (x := 1 - {bR}) (by norm_num) (by norm_num) (by norm_num) huh
  norm_num at this ⊢
  linarith

/-- Ye-Li's parameter conditions of Sec. 3.5 / Sec. 4, and 1 - b <= 1/100 (Lemma E6). -/
theorem explicit_params : 0 < aYL ∧ aYL < 1 / 4 ∧ 4 * aYL ≤ 1 - bYL ∧ 1 - bYL < 1 / 2 + 2 * aYL ∧
    10 * aYL < 1 - bYL ∧ 1 - bYL ≤ 1 / 100 := by decide +kernel

/-- [C1] must fail: k = 115940 (grouping too costly): eps_L > 1e-9. -/
theorem explicit_C1 : 1 / 10 ^ 9 < dC1.epsL := by decide +kernel

/-- [C2] must fail: eps' = 1e-4 (window loss too large): eps_L > 1e-9. -/
theorem explicit_C2 : 1 / 10 ^ 9 < dC2.epsL := by decide +kernel

/-- [C3] must fail: eps' = 1e-27 leaves no valid J: 2 eps'^2 N0 log2 e - 2 < 0, even with log2 e < 3/2
(`ln2_bounds`). -/
theorem explicit_C3 : 2 * {Q(e3)} * {Q(e3)} * dA.Nq * (3 / 2) - 2 < 0 := by decide +kernel

/-- [C4] must fail: dR' lowered by 1e-11 below the secant. -/
theorem explicit_C4 : dC4.line dC4.t2 + dC4.epsV < dC4.c2 := by decide +kernel

/-- [C5] must fail: log2(8 D_inf)/N0 <= L_D - 50. -/
theorem explicit_C5 : ¬ dA.LD ≤ 4855 - 50 := by decide +kernel

/-- [C6] must fail: k = 10^25 (q does not divide N0). -/
theorem explicit_C6 : (10 ^ 25 * (10 ^ 25 + 2)) % 10 ^ 26 ≠ 0 := by decide +kernel

/-- [C7] must fail: H(b) <= 0.07. -/
theorem explicit_C7 : ¬ Hb {bR} ≤ 7 / 100 := by
{l_b}  have e1 : {QR(lo_b)} ≤ Hb {bR} := by
    rw [← Hb_symm]; exact Hb_ge_of (by norm_num) (by norm_num) (by norm_num) hbl
  norm_num at e1 ⊢
  linarith

end SS
'''
    path = os.path.join(HERE, "SubsetsumLean", "Explicit.lean")
    with open(path, "w") as fh:
        fh.write(out)
    print("wrote", path, "margins", float(m1), float(m2))


if __name__ == "__main__":
    main()
