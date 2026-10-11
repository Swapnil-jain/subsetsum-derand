"""Generate SubsetsumLean/Stage3.lean, the kernel check of cert_stage3.py (Stage 3).

Pure standard library. Every number is read from cert_stage3.py itself (in ../certificates), and every claim is first re-checked
here: the log enclosures are computed with the kernel's own
formulas (`lsum`, `lrem`, `logOK`, `entOK`, `hhOK`, `hbOK` of Basic.lean / Stage3Defs.lean) in exact rationals, so
each `decide +kernel` below is known to succeed before Lean runs. Ye-Li's table constants (fallback only) are
Lean variables, constrained only by the hypotheses each theorem states.
Run:  python3 gen_stage3.py
"""
from fractions import Fraction as F
import contextlib
import io
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "certificates"))
import cert_stage3 as C  # noqa: E402

L2C = F(693147180559945309417232121458176568075500134, 10 ** 45)
L2lo, L2hi = L2C - F(1, 10 ** 42), L2C + F(1, 10 ** 42)
NT = 60          # series terms in every log enclosure
DP = 40          # decimal places of the enclosure endpoints written into Stage3.lean


def lsum(t, n):
    s, p = F(0), F(1)
    for i in range(n):
        p *= t
        s += p / (i + 1)
    return s


def lrem(t, n):
    return abs(t) ** (n + 1) / (1 - abs(t))


def logOK(x, k, n, lo, hi):
    t = 1 - x / F(2) ** k
    if not (x > 0 and abs(t) < 1):
        return False
    S, Rm = lsum(t, n), lrem(t, n)
    return (lo <= -S - Rm + min(k * L2lo, k * L2hi)) and (-S + Rm + max(k * L2lo, k * L2hi) <= hi)


def log_enc(x):
    """(k, lo, hi): the kernel's enclosure of ln x, endpoints rounded outward to DP places."""
    x = F(x)
    k = 0
    while x / F(2) ** k > F(4, 3):
        k += 1
    while x / F(2) ** k < F(2, 3):
        k -= 1
    t = 1 - x / F(2) ** k
    S, Rm = lsum(t, NT), lrem(t, NT)
    lo, hi = C.dn(-S - Rm + min(k * L2lo, k * L2hi), DP), C.up(-S + Rm + max(k * L2lo, k * L2hi), DP)
    assert logOK(x, k, NT, lo, hi)
    return k, lo, hi


def q(x):
    x = F(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"


def r_(x):
    x = F(x)
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℝ)"


def z_(k):
    return f"({k})"


# ---------------------------------------------------------------- the kernel-side certificates
def ent_args(p, cp, cq):
    """Arguments of `entOK p k1 k2 NT l1 u1 l2 u2 cp cq`, checked here."""
    k1, l1, u1 = log_enc(p)
    k2, l2, u2 = log_enc(1 - p)
    assert 0 < p < 1 and cp >= 0 and cq >= 0 and -l1 <= cp * L2lo and -l2 <= cq * L2lo
    return f"{q(p)} {z_(k1)} {z_(k2)} {NT} {q(l1)} {q(u1)} {q(l2)} {q(u2)} {q(cp)} {q(cq)}"


def hh_args(c, x):
    """(lo, hi, args) of `hhOK c x kc kx ky NT lc uc lx ux ly uy lo hi`, checked here."""
    c, x = F(c), F(x)
    kc, lc, uc = log_enc(c)
    kx, lx, ux = log_enc(x)
    ky, ly, uy = log_enc(c - x)
    nlo = c * lc - x * ux - (c - x) * uy
    nhi = c * uc - x * lx - (c - x) * ly
    lo, hi = C.dn(nlo / L2hi, DP), C.up(nhi / L2lo, DP)
    assert 0 < x < c and 0 <= lo and 0 <= hi and lo * L2hi <= nlo and nhi <= hi * L2lo
    return lo, hi, (f"{q(c)} {q(x)} {z_(kc)} {z_(kx)} {z_(ky)} {NT} {q(lc)} {q(uc)} {q(lx)} {q(ux)} {q(ly)} {q(uy)}"
                    f" {q(lo)} {q(hi)}")


def hb_args(x):
    x = F(x)
    k1, l1, u1 = log_enc(x)
    k2, l2, u2 = log_enc(1 - x)
    nlo = -x * u1 - (1 - x) * u2
    nhi = -x * l1 - (1 - x) * l2
    lo, hi = C.dn(nlo / L2hi, DP), C.up(nhi / L2lo, DP)
    assert 0 < x < 1 and 0 <= lo and lo * L2hi <= nlo and nhi <= hi * L2lo
    return lo, hi, f"{q(x)} {z_(k1)} {z_(k2)} {NT} {q(l1)} {q(u1)} {q(l2)} {q(u2)} {q(lo)} {q(hi)}"


def main():
    with contextlib.redirect_stdout(io.StringIO()):
        assert C.main() == 0
        ok, dL, dR, xi_cert, xi_max = C.retune()
    assert ok
    A0, A1, OMB, R = C.A0, C.A1, C.OMB, C.R
    a0, a1, omb, r = r_(A0), r_(A1), r_(OMB), r_(R)
    T1, T2 = C.T1, C.T2
    t1, t2 = r_(T1), r_(T2)
    PAR = f"{a0} {a1} {omb} {r}"
    out = []
    w = out.append

    # ---- constants E1 and H(1/r)
    e1parts = [(1, 1 - OMB, "1", f"(1 - {omb})"), (F(1, 4), A0, "(1 / 4)", a0), (F(1, 4), A1, "(1 / 4)", a1),
               (F(1, 2), OMB - A0 - A1, "(1 / 2)", f"({omb} - {a0} - {a1})")]
    hs = [hh_args(c, x) for c, x, _, _ in e1parts]
    lo_e1 = hs[0][0] - hs[1][1] - hs[2][1] - hs[3][1]
    hi_e1 = hs[0][1] - hs[1][0] - hs[2][0] - hs[3][0]
    assert C.E1L <= lo_e1 and hi_e1 <= C.E1U
    lines = []
    for j, ((c, x, cs, xs), (lo, hi, args)) in enumerate(zip(e1parts, hs)):
        lines.append(f"  obtain ⟨l{j}, u{j}⟩ := hh_mem {cs} {xs} {args.split(' ', 2)[0]} {args.split(' ', 2)[1]}"
                     f" {args.split(' ', 2)[2]} (by norm_num) (by norm_num) (by decide +kernel)")
    w(f"""/-- `E1` of the re-tuned circuit, enclosed: `E1L ≤ E1 ≤ E1U`. -/
theorem s3_E1 : {r_(C.E1L)} ≤ E1 {a0} {a1} {omb} ∧ E1 {a0} {a1} {omb} ≤ {r_(C.E1U)} := by
""" + "\n".join(lines) + f"""
  push_cast at l0 u0 l1 u1 l2 u2 l3 u3
  unfold E1; constructor <;> linarith
""")
    lo_hr, hi_hr, ahr = hh_args(1, 1 / R)
    assert C.HRL <= lo_hr and hi_hr <= C.HRU
    sp = ahr.split(" ", 2)
    w(f"""/-- `H(1/r)` enclosed: `HRL ≤ H(1/r) ≤ HRU`. -/
theorem s3_Hr : {r_(C.HRL)} ≤ Hr {r} ∧ Hr {r} ≤ {r_(C.HRU)} := by
  obtain ⟨l, u⟩ := hh_mem 1 (1 / {r}) {sp[0]} {sp[1]} {sp[2]} (by norm_num) (by norm_num) (by decide +kernel)
  push_cast at l u
  unfold Hr; constructor <;> linarith
""")

    # ---- [P] parameters
    w(f"""/-- [P] the parameter conditions of the generalised Sec. 3.5: `0 < a0, a1 ≤ 1/4`, `0 ≤ 1-b-a0-a1 ≤ 1/2`,
`r ≥ 1`, `r (a0 + a1) ≤ 1 - b`, `(a0 + a1)/(1 - b) ≤ 1/2`. -/
theorem s3_params : 0 < {a0} ∧ {a0} ≤ 1 / 4 ∧ 0 < {a1} ∧ {a1} ≤ 1 / 4 ∧ 0 ≤ {omb} - {a0} - {a1} ∧
    {omb} - {a0} - {a1} ≤ 1 / 2 ∧ 1 ≤ {r} ∧ {r} * ({a0} + {a1}) ≤ {omb} ∧ ({a0} + {a1}) / {omb} ≤ 1 / 2 := by
  norm_num
""")

    # ---- [Apos]
    xb = A1 / OMB
    lo_b, hi_b, ab = hb_args(xb)
    apos = OMB * lo_b - R * (A0 + A1) * C.HRU
    assert apos > 0
    w(f"""/-- [Apos] `A(mu) = h(1-b, mu) - r mu H(1/r) > 0` on the polygon: `h(1-b, mu) = (1-b) H(mu/(1-b)) ≥
(1-b) H(a1/(1-b))` (H increases on `[0, 1/2]`) and `r mu H(1/r) ≤ r (a1 + a0) HRU`. -/
theorem s3_Apos : ∀ mu θ : ℝ, inPoly {a0} {a1} {r} mu θ → 0 < Aex {omb} {r} mu := by
  intro mu θ ⟨h1, h2, _, _⟩
  unfold Aex
  have e := hh_eq_mul_Hb (c := {omb}) (k := mu) (by linarith [(by norm_num : (0 : ℝ) < {a1})]) (by linarith [(by norm_num : {a1} + {a0} < {omb})])
  obtain ⟨hb, -⟩ := Hb_mem ({a1} / {omb}) {ab.split(' ', 1)[0]} {ab.split(' ', 1)[1]} (by norm_num) (by decide +kernel)
  have mono := Hb_mono (x := {a1} / {omb}) (y := mu / {omb}) (by norm_num)
    (div_le_div_of_nonneg_right h1 (by norm_num)) (by rw [div_le_iff₀ (by norm_num)]; linarith [(by norm_num : ({a1} + {a0}) ≤ 1 / 2 * {omb})])
  obtain ⟨hr0, hr1⟩ := s3_Hr
  have hm : mu * Hr {r} ≤ ({a1} + {a0}) * {r_(C.HRU)} :=
    mul_le_mul h2 hr1 (by linarith [(by norm_num : (0 : ℝ) ≤ {r_(C.HRL)})]) (by norm_num)
  have hom : {omb} * {r_(lo_b)} ≤ {omb} * Hb (mu / {omb}) :=
    mul_le_mul_of_nonneg_left (by push_cast at hb; linarith) (by norm_num)
  rw [e]
  nlinarith [hm, hom]
""")

    # ---- [U] six majorant bounds
    def ent_strings(n, k):
        """The Lean expressions of h's arguments, written exactly as `g_i` unfolds."""
        key = (n, k)
        table = {
            ((F(0), F(0), A0), (F(1), F(0), -A1)): (a0, f"mu - {a1}"),
            ((R - 1, F(0), F(0)), (F(-1), F(1), F(0))): (f"({r} - 1) * mu", "θ - mu"),
            ((R, F(0), F(0)), (F(0), F(1), F(0))): (f"{r} * mu", "θ"),
            ((F(0), F(0), OMB), (F(1), F(0), F(0))): (omb, "mu"),
        }
        return table[key]

    names = {}
    for key, tau, cexpr, cval in (("t1", T1, t1, T1), ("t2", T2, f"(1 - {t2}) / 2", (1 - T2) / 2)):
        for i in (1, 2, 3):
            M, data = C.majorant(i, tau, C.PTS[(i, key)])
            assert C.vmax(M) <= cval
            hs_ = []
            for j, (s, n, k, p, cp, cq) in enumerate(data):
                ns, ks = ent_strings(n, k)
                hs_.append(f"  have q{j} := ent_le ({ns}) ({ks}) {ent_args(p, cp, cq)} (by linarith) (by linarith)"
                           f" (by decide +kernel)")
            nm = f"s3_U{i}_{key}"
            names[(i, key)] = nm
            extra = ""
            if i in (2, 3):
                extra += f"  have hr : mu * {r_(C.HRL)} ≤ mu * Hr {r} := mul_le_mul_of_nonneg_left s3_Hr.1 (by linarith)\n"
            if i in (1, 3):
                extra += "  have he := s3_E1.2\n"
            w(f"""/-- [U] `g_{i}({key}) ≤ {'t1' if key == 't1' else '(1 - t2)/2'}` on the whole polygon (Gibbs majorant at a rational tangent point,
maximised at the four vertices). -/
theorem {nm} : ∀ mu θ : ℝ, inPoly {a0} {a1} {r} mu θ → g{i} {PAR} {t1 if key == 't1' else t2} mu θ ≤ {cexpr} := by
  intro mu θ ⟨h1, h2, h3, h4⟩
  have h0 : (0 : ℝ) < mu := by linarith [(by norm_num : (0 : ℝ) < {a1})]
  have hr1 : (0 : ℝ) ≤ ({r} - 1) * mu := by nlinarith [(by norm_num : (1 : ℝ) ≤ {r})]
""" + "\n".join(hs_) + "\n" + extra + f"""  have v := quad_le (A := {r_(M[0])}) (B := {r_(M[1])}) (C := {r_(M[2])}) (c := {cexpr}) (m0 := {a1})
    (m1 := {a1} + {a0}) (r := {r}) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3 h4
  unfold g{i} E0
  push_cast at *
  linarith
""")

    # ---- [L] the line, its pair, xi
    slope = ((1 - T2) / 2 - T1) / (T2 - T1)
    assert dL == T1 + (1 - T1) * slope and dR == T1 - T1 * slope
    w(f"""/-- [L] **Lemma 3.4's hypothesis for the re-tuned circuit**: for every `tau ∈ [0, 1]` and every colour of the
polygon, `min(tau L + (1 - tau) R, tau, (1 - tau)/2) ≤ line(tau)`, the line through `(t1, t1)` and
`(t2, (1 - t2)/2)`. -/
theorem s3_line : ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1 → ∀ mu θ : ℝ, inPoly {a0} {a1} {r} mu θ →
    min (tau * Lcol {PAR} mu θ + (1 - tau) * Rcol {PAR} mu θ) (min tau ((1 - tau) / 2)) ≤
      {r_(dR)} + tau * ({r_(dL)} - {r_(dR)}) := by
  intro tau h0 h1 mu θ hP
  have := line_of_U {PAR} {t1} {t2} (by norm_num) (by norm_num) (by norm_num) (by norm_num) s3_Apos {names[(1, 't1')]} {names[(2, 't1')]} {names[(3, 't1')]} {names[(1, 't2')]} {names[(2, 't2')]} {names[(3, 't2')]} tau h0 h1 mu θ hP
  have e : lineF {t1} {t2} tau = {r_(dR)} + tau * ({r_(dL)} - {r_(dR)}) := by unfold lineF; ring
  rw [e] at this; exact this

/-- [L] the line's pair: `dL = line(1)`, `dR = line(0)`, both `≥ 0`, and `xi_cert = 1/4 - (dL + dR)/2`. -/
theorem s3_xi : lineF {t1} {t2} 1 = {r_(dL)} ∧ lineF {t1} {t2} 0 = {r_(dR)} ∧ (0 : ℝ) ≤ {r_(dL)} ∧
    (0 : ℝ) ≤ {r_(dR)} ∧ 1 / 4 - ({r_(dL)} + {r_(dR)}) / 2 = {r_(xi_cert)} := by
  unfold lineF; norm_num
""")

    # ---- [F1]
    S1, S2 = C.S1, C.S2
    (m1, th1), (m2, th2) = C.F1PTS["s1"], C.F1PTS["s2"]
    chord = S1 + (F(1, 2) - S1) * ((1 - S2) / 2 - S1) / (S2 - S1)
    assert xi_max == F(1, 4) - chord

    def lb(s, m, th, tag):
        pts = [(OMB, m, omb, r_(m)), (R * m, th, f"{r} * {r_(m)}", r_(th)), (A0, m - A1, a0, f"{r_(m)} - {a1}"),
               ((R - 1) * m, th - m, f"({r} - 1) * {r_(m)}", f"{r_(th)} - {r_(m)}")]
        hl = []
        vals = []
        for j, (c, x, cs, xs) in enumerate(pts):
            lo, hi, args = hh_args(c, x)
            vals.append(lo)
            a = args.split(" ", 2)
            hl.append(f"    obtain ⟨l{j}, -⟩ := hh_mem ({cs}) ({xs}) {a[0]} {a[1]} {a[2]} (by norm_num) (by norm_num)"
                      f" (by decide +kernel)")
        Lv = C.E1L + vals[0] - R * m * C.HRU + vals[1] - R * m
        Rv = C.E0 + vals[2] + vals[3]
        assert s * Lv + (1 - s) * Rv > (s if tag == "s1" else (1 - s) / 2)
        return "\n".join(hl)
    w(f"""/-- [F1] **must-fail for xi**: every line `dr + tau (dl - dr)` that satisfies Lemma 3.4's hypothesis for
this circuit has `xi = 1/4 - (dl + dr)/2 ≤ xi_max`, because rigorous lower bounds give `V(s1) > s1` and
`V(s2) > (1 - s2)/2` at two explicit colours. And `xi_max < xi_cert (1 + 1e-4)`. -/
theorem s3_F1 (dl dr : ℝ) (hline : ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1 → ∀ mu θ : ℝ, inPoly {a0} {a1} {r} mu θ →
      min (tau * Lcol {PAR} mu θ + (1 - tau) * Rcol {PAR} mu θ) (min tau ((1 - tau) / 2)) ≤
        dr + tau * (dl - dr)) :
    1 / 4 - (dl + dr) / 2 ≤ {r_(xi_max)} ∧ {r_(xi_cert)} ≤ {r_(xi_max)} ∧
      {r_(xi_max)} < {r_(xi_cert)} * (1 + 1 / 10000) := by
  have hb1 : {r_(S1)} < {r_(S1)} * (E1 {a0} {a1} {omb} + Aex {omb} {r} {r_(m1)} + hh ({r} * {r_(m1)}) {r_(th1)} - {r} * {r_(m1)})
      + (1 - {r_(S1)}) * Rcol {PAR} {r_(m1)} {r_(th1)} := by
{lb(S1, m1, th1, "s1")}
    push_cast at l0 l1 l2 l3
    have := s3_E1.1; have := s3_Hr.2
    unfold Aex Rcol E0; nlinarith
  have hb2 : (1 - {r_(S2)}) / 2 < {r_(S2)} * (E1 {a0} {a1} {omb} + Aex {omb} {r} {r_(m2)} + hh ({r} * {r_(m2)}) {r_(th2)} - {r} * {r_(m2)})
      + (1 - {r_(S2)}) * Rcol {PAR} {r_(m2)} {r_(th2)} := by
{lb(S2, m2, th2, "s2")}
    push_cast at l0 l1 l2 l3
    have := s3_E1.1; have := s3_Hr.2
    unfold Aex Rcol E0; nlinarith
  refine ⟨?_, by norm_num, by norm_num⟩
  have := xi_le_of_F1 {PAR} {r_(S1)} {r_(S2)} dl dr {r_(m1)} {r_(th1)} {r_(m2)} {r_(th2)}
    (by unfold inPoly; norm_num) (by unfold inPoly; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hb1 hb2 hline
  have e : (1 : ℝ) / 4 - ({r_(S1)} + (1 / 2 - {r_(S1)}) * ((1 - {r_(S2)}) / 2 - {r_(S1)}) / ({r_(S2)} - {r_(S1)})) = {r_(xi_max)} := by
    norm_num
  linarith
""")

    # ---- [S3] the exponent
    eps = F(1, 10 ** 9)
    dLp, dRp = C.up(dL, 12), C.up(dR, 12)
    xi3 = (F(1, 2) - dLp - dRp) / 2
    pi3, _ = C.best_pi(xi3, eps)
    okE, E3 = C.check(pi3, xi3, eps, F(1, 2), dLp, dRp, dL, dR, xi_cert)
    E3c = C.up(E3, 12)
    assert okE and E3 <= E3c
    g = dRp - dLp
    n0, last = C.fit_n0(pi3, dLp, dRp)
    P3, X3, EP, B3 = r_(pi3), r_(xi3), r_(eps), r_(E3c)
    dl3, dr3 = r_(dLp), r_(dRp)

    def terms_tac():
        return ("s3Terms_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n"
                "      (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    w(f"""/-- [S3] **Theorem 3's certificate**: at pi = {C.dec(pi3, 8)}, xi' = (1/2 - dL' - dR')/2, eps = 1e-9, the rational pair
(dL', dR') = 12-place round-ups of the line's (dL, dR): Lemma 3.5's hypotheses, the fit, and every cost term is
`≤ E3 = {C.dec(E3c)}`. No Ye-Li table constant enters. -/
theorem s3_E3 : CertS3 {P3} {X3} {EP} {B3} {dl3} {dr3} {r_(dL)} {r_(dR)} {r_(xi_cert)} where
  pi_pos := by norm_num
  pi_le_third := by norm_num
  four_pi := by norm_num
  xi_nonneg := by norm_num
  xi_le := by norm_num
  dl_ge := by norm_num
  dr_ge := by norm_num
  dl_nonneg := by norm_num
  dr_nonneg := by norm_num
  pair := by norm_num
  g_lt := by norm_num
  fit_lo := by norm_num
  fit_hi := by norm_num
  terms_le := {terms_tac()}

/-- [S3] the gain: `1/2 - E3 ≥ 9.0779e-6`, and `E3 - 2 pi ≤ 2.1e-9` (pi is the grid point just below the balance point). -/
theorem s3_gain : (90779 / 10 ^ 10 : ℝ) ≤ 1 / 2 - {B3} ∧ {B3} - 2 * {P3} ≤ 21 / 10 ^ 10 := by norm_num

/-- [S3] the fit for large n (Lemma 3.3): for every `n ≥ {n0}` and `0 ≤ m ≤ pi n`, `(4 - f(0)) m ≤ n - 2` and
`(2 + f(1/2)) m ≤ n - 2`, with `g = dR' - dL'`. -/
theorem s3_fit_tail : ∀ n m : ℝ, {n0} ≤ n → m ≤ {P3} * n →
    (4 - 2 * ({dr3} - {dl3})) * m ≤ n - 2 ∧ (2 + (3 / 2 + ({dr3} - {dl3}))) * m ≤ n - 2 := by
  intro n m hn hm
  exact ⟨fit_tail (by norm_num) (by norm_num) (by norm_num) hn hm, fit_tail (by norm_num) (by norm_num) (by norm_num) hn hm⟩

/-- [S3] the fit for `{last + 1} ≤ n < {n0}`, at the algorithm's `m = 2 floor(pi n / 2)` (checked for each n). -/
theorem s3_fit_small : ∀ n : ℕ, n < {n0} → {last + 1} ≤ n →
    (4 - 2 * ({q(g)})) * ((2 * ({pi3.numerator} * n / (2 * {pi3.denominator})) : ℕ) : ℚ) ≤ (n : ℚ) - 2 ∧
    (2 + (3 / 2 + {q(g)})) * ((2 * ({pi3.numerator} * n / (2 * {pi3.denominator})) : ℕ) : ℚ) ≤ (n : ℚ) - 2 := by
  decide +kernel

/-- [S3] Cor. 3.2's block length for (dL', dR'): kappa_0 = 148444531984 meets both conditions (the second binds) and
kappa_0 - 2 fails the second. So N' = kappa_0^2 + 2 kappa_0 is as in Stage 2. -/
theorem s3_K : kcond1 {dl3} {dr3} {EP} (148444531984 : ℝ) ∧ kcond2 {EP} (148444531984 : ℝ) ∧
    ¬ kcond2 {EP} (148444531982 : ℝ) := by
  refine ⟨?_, stage2_K.2.1, stage2_K.2.2.1⟩
  unfold kcond1; rw [max_eq_right (by norm_num)]; norm_num
""")

    # ---- fallbacks
    E20 = C.E20
    xiA, xiB = F(20035, 10 ** 9), F(2, 10 ** 5)
    piA, _ = C.best_pi(xiA, eps)
    piB, _ = C.best_pi(xiB, eps)
    claimA, claimB = F("0.499994991801"), F("0.4999950006")
    assert C.check(piA, xiA, eps, claimA, C.DL_YL, C.DR_YL, C.DL_T + E20, C.DR_T + E20, C.XI_T)[0]
    assert C.check(piB, xiB, eps, claimB, C.DL_YL, C.DR_YL, C.DL_T + E20, C.DR_T + E20, xiB)[0]
    DLT, DRT, XIT, e20 = r_(C.DL_T), r_(C.DR_T), r_(C.XI_T), r_(E20)
    for nm, piX, xiX, cl, hx, xl, doc in (
            ("s3_FA", piA, xiA, claimA, f"(hx : {XIT} ≤ xiT)", "linarith [(by norm_num : " + r_(xiA) + " ≤ " + XIT + "), hx]",
             f"[FA] fallback (no re-tune; Ye-Li Prop. 4.2 and its table as in Stage 2): pi = {C.dec(piA, 8)}, xi' = 2.0035e-5, E <= 0.499994991801."),
            ("s3_FB", piB, xiB, cl if False else claimB, f"(hx : {r_(xiB)} < xiT)", "linarith [hx]",
             f"[FB] fallback from the statement xi > 0.00002 alone: pi = {C.dec(piB, 8)}, xi' = 2e-5, E <= 0.4999950006.")):
        w(f"""/-- {doc} -/
theorem {nm} (xiT dLT dRT : ℝ) {hx} (hl : dLT < {DLT} + {e20}) (hr : dRT < {DRT} + {e20}) :
    CertS3 {r_(piX)} {r_(xiX)} {EP} {r_(cl)} {r_(C.DL_YL)} {r_(C.DR_YL)} dLT dRT xiT where
  pi_pos := by norm_num
  pi_le_third := by norm_num
  four_pi := by norm_num
  xi_nonneg := by norm_num
  xi_le := by {xl}
  dl_ge := by linarith [(by norm_num : {DLT} + {e20} ≤ {r_(C.DL_YL)})]
  dr_ge := by linarith [(by norm_num : {DRT} + {e20} ≤ {r_(C.DR_YL)})]
  dl_nonneg := by norm_num
  dr_nonneg := by norm_num
  pair := by norm_num
  g_lt := by norm_num
  fit_lo := by norm_num
  fit_hi := by norm_num
  terms_le := {terms_tac()}
""")

    # ---- controls
    c = []
    c.append(f"""/-- [K1] must fail: every term `≤ E3 - 1e-12`. -/
theorem s3_K1 : ¬ ∀ t ∈ s3Terms {P3} {X3} {EP}, t ≤ {B3} - 1 / 10 ^ 12 := by
  intro h; have := h _ (s3_many_mem _ _ _); norm_num at this""")
    c.append(f"""/-- [K2] must fail: pi = 0.2501 (the four blocks do not fit, 4 pi > 1). -/
theorem s3_K2 : ∀ b dl dr a c x : ℝ, ¬ CertS3 (2501 / 10000) {X3} {EP} b dl dr a c x :=
  fun _ _ _ _ _ _ h => by have := h.four_pi; norm_num at this""")
    c.append(f"""/-- [K3] must fail: Ye-Li's prefix pi = 1/3. -/
theorem s3_K3 : ∀ b dl dr a c x : ℝ, ¬ CertS3 (1 / 3) {X3} {EP} b dl dr a c x :=
  fun _ _ _ _ _ _ h => by have := h.four_pi; norm_num at this""")
    c.append(f"""/-- [K4] must fail: xi' = 0. -/
theorem s3_K4 : ¬ ∀ t ∈ s3Terms {P3} 0 {EP}, t ≤ {B3} := by
  intro h; have := h _ (s3_many_mem _ _ _); norm_num at this""")
    c.append(f"""/-- [K5] must fail: eps = 1e-6. -/
theorem s3_K5 : ¬ ∀ t ∈ s3Terms {P3} {X3} (1 / 10 ^ 6), t ≤ {B3} := by
  intro h; have := h _ (s3_many_mem _ _ _); norm_num at this""")
    c.append(f"""/-- [K6] must fail: a one-sided dedupe (right list raw) at N = 1 costs more than 1/2. -/
theorem s3_K6 : ¬ ((1 : ℝ) / 2 + (1 - {X3}) * {P3} + 2 * {EP} * {P3} ≤ 1 / 2) := by norm_num""")
    c.append(f"""/-- [K7] must fail: pi one grid step (1e-8) above. -/
theorem s3_K7 : ¬ ∀ t ∈ s3Terms ({P3} + 1 / 10 ^ 8) {X3} {EP}, t ≤ {B3} := by
  intro h; have := h _ (s3_cover_mem _ _ _); norm_num at this""")
    c.append(f"""/-- [K8] must fail: dL' rounded below the line's dL. -/
theorem s3_K8 : ¬ CertS3 {P3} {X3} {EP} {B3} ({dl3} - 2 / 10 ^ 12) {dr3} {r_(dL)} {r_(dR)} {r_(xi_cert)} :=
  fun h => by have := h.dl_ge; norm_num at this""")
    c.append(f"""/-- [K9] must fail: xi' = xi_cert + 1e-12 with the rounded pair (even with no cap on xi'). -/
theorem s3_K9 : ∀ xc : ℝ, ¬ CertS3 {P3} ({r_(xi_cert)} + 1 / 10 ^ 12) {EP} {B3} {dl3} {dr3} {r_(dL)} {r_(dR)} xc :=
  fun _ h => by have := h.pair; norm_num at this""")
    c.append(f"""/-- [K10] must fail: the re-tuned xi' with Ye-Li's table pair (that pair has dL + dR = 0.499959929549). -/
theorem s3_K10 : ∀ a b xc : ℝ, ¬ CertS3 {P3} {X3} {EP} {B3} {r_(C.DL_YL)} {r_(C.DR_YL)} a b xc :=
  fun _ _ _ h => by have := h.pair; norm_num at this""")
    c.append(f"""/-- [K11] must fail: the fallback claim 1e-12 lower. -/
theorem s3_K11 : ¬ ∀ t ∈ s3Terms {r_(piA)} {r_(xiA)} {EP}, t ≤ {r_(claimA)} - 1 / 10 ^ 12 := by
  intro h; have := h _ (s3_many_mem _ _ _); norm_num at this""")
    c.append(f"""/-- [C3], [C4] must fail: r (a0 + a1) > 1 - b at 1 - b = 1/600, and r = 99/100 < 1. -/
theorem s3_C34 : ¬ ({r} * ({a0} + {a1}) ≤ 1 / 600) ∧ ¬ ((1 : ℝ) ≤ 99 / 100) := by norm_num""")

    head = f'''import SubsetsumLean.Stage3Defs
import SubsetsumLean.Stage2

/-!
# Kernel check of `cert_stage3.py` (generated by `gen_stage3.py`; do not edit)

The re-tuned Ye-Li Sec. 3.5 circuit at (a0, a1, 1-b, r) = ({A0}, {A1}, {OMB}, {R}):
- `s3_E1`, `s3_Hr`: rational enclosures of E1 and H(1/r); `s3_params`: [P]; `s3_Apos`: A(mu) > 0 ([Apos]);
- `s3_U*`: the six majorant bounds [U], each over the whole colour polygon;
- `s3_line`: Lemma 3.4's hypothesis, min(V, tau, (1-tau)/2) <= line on [0, 1] ([L]); `s3_xi`: its pair and xi;
- `s3_F1`: no valid line has xi > xi_max (refuted improvement).
Stage 3's exponent: `s3_E3` (Theorem 3, E3 <= {C.dec(E3c)}), `s3_gain`, `s3_fit_tail`, `s3_fit_small`, `s3_K`;
fallbacks `s3_FA` (E <= 0.499994991801), `s3_FB` (E <= 0.4999950006). Controls `s3_K1` to `s3_K11`, `s3_C34`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS

'''
    text = head + "\n".join(out) + "\n" + "\n\n".join(c) + "\n\nend SS\n"
    path = os.path.join(HERE, "SubsetsumLean", "Stage3.lean")
    with open(path, "w") as fh:
        fh.write(text)
    print("wrote", path, len(text), "bytes")


if __name__ == "__main__":
    main()
