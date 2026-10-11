"""Generate SubsetsumLean/Stage4ERows.lean and SubsetsumLean/Stage4.lean: the kernel check of every inequality of
derand/stage4/cert_stage4.py and cert_stage4plus.py except the cell trees (gen_stage4_cells.py).

Pure standard library. Every number is read from the two certificate scripts, and every claim is first re-checked
here in exact rationals with the kernel's own formulas (Basic.lean's `logOK`, `hbOK`, Stage3Defs' `hhOK`, and the
checkers of Stage4Check/Stage4ECheck), so each `decide +kernel` is known to succeed before Lean runs.
Run:  python3 gen_stage4.py   (after gen_stage4_cells.py; a few seconds)
"""
from fractions import Fraction as F
import contextlib
import io
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "certificates", "stage4"))
import gen_stage4_cells as G  # noqa: E402
import cert_stage4 as C4  # noqa: E402
import cert_stage4plus as C4P  # noqa: E402

L2lo, L2hi = G.L2lo, G.L2hi
NB = 50          # series terms of the point enclosures (Basic's logOK / hhOK / hbOK)
DP = 10 ** 30    # their endpoints, rounded outward


def q(x):
    x = F(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℚ)"


def r(x):
    x = F(x)
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"({x.numerator}/{x.denominator} : ℝ)"


def Qc(x):
    x = F(x)
    return f"(Q ({x.numerator}) {x.denominator})"


def z(k):
    return f"({k})"


def dn(x, d=DP):
    return F(math.floor(x * d), d)


def up(x, d=DP):
    return F(math.ceil(x * d), d)


# ------------------------------------------------------------------ Basic.lean's logOK, exactly
def enc(x, n=NB, d=DP):
    x = F(x)
    k = G.kfor(x)
    t = 1 - x / G.p2(k)
    S, R = G.lsum(t, n), G.lrem(t, n)
    lo, hi = dn(-S - R + min(k * L2lo, k * L2hi), d), up(-S + R + max(k * L2lo, k * L2hi), d)
    assert logOK(x, k, n, lo, hi)
    return k, lo, hi


def logOK(x, k, n, lo, hi):
    t = 1 - x / G.p2(k)
    if not (x > 0 and abs(t) < 1):
        return False
    S, R = G.lsum(t, n), G.lrem(t, n)
    return lo <= -S - R + min(k * L2lo, k * L2hi) and -S + R + max(k * L2lo, k * L2hi) <= hi


def log_mem(e_r, x):
    """`SS.log_mem` term: bounds lo ≤ log e ≤ hi, e_r the real expression equal to x."""
    k, lo, hi = enc(x)
    return (f"(SS.log_mem {e_r} {q(x)} {q(lo)} {q(hi)} {z(k)} {NB} _ _ (by norm_num) rfl rfl (by decide +kernel))",
            lo, hi)


def hb_mem(e_r, x, lo=None, hi=None, n=NB):
    x = F(x)
    k1, l1, u1 = enc(x, n, 10 ** 40)
    k2, l2, u2 = enc(1 - x, n, 10 ** 40)
    if lo is None:
        lo = max(F(0), dn((-x * u1 - (1 - x) * u2) / L2hi))
    if hi is None:
        hi = up((-x * l1 - (1 - x) * l2) / L2lo)
    assert 0 < x < 1 and lo >= 0 and hi >= 0
    assert lo * L2hi <= -x * u1 - (1 - x) * u2 and -x * l1 - (1 - x) * l2 <= hi * L2lo
    return (f"(SS.Hb_mem {e_r} {q(x)} {z(k1)} {z(k2)} {n} {q(l1)} {q(u1)} {q(l2)} {q(u2)} {q(lo)} {q(hi)} "
            f"(by norm_num) (by decide +kernel))", lo, hi)


def hh_mem(c_r, e_r, c, x, e_proof="(by norm_num)"):
    c, x = F(c), F(x)
    kc, lc, uc = enc(c)
    kx, lx, ux = enc(x)
    ky, ly, uy = enc(c - x)
    lo = max(F(0), dn((c * lc - x * ux - (c - x) * uy) / L2hi))
    hi = up((c * uc - x * lx - (c - x) * ly) / L2lo)
    assert 0 < x < c and lo * L2hi <= c * lc - x * ux - (c - x) * uy and c * uc - x * lx - (c - x) * ly <= hi * L2lo
    return (f"(SS.hh_mem {c_r} {e_r} {q(c)} {q(x)} {z(kc)} {z(kx)} {z(ky)} {NB} {q(lc)} {q(uc)} {q(lx)} {q(ux)} "
            f"{q(ly)} {q(uy)} {q(lo)} {q(hi)} (by norm_num) {e_proof} (by decide +kernel))", lo, hi)


# ------------------------------------------------------------------ light-module bounds (Stage4ECheck's HbU / HbL)
def hbU(x):
    x = F(x)
    k1, l1, _ = G.log_bounds(x)
    k2, l2, _ = G.log_bounds(1 - x)
    l1, l2 = G.dn(l1), G.dn(l2)
    hi = G.up((-x * l1 - (1 - x) * l2) / L2lo)
    assert G.logGe(x, k1, l1) and G.logGe(1 - x, k2, l2) and -x * l1 - (1 - x) * l2 <= hi * L2lo and hi >= 0
    return (k1, k2, l1, l2, hi)


def hbL(x):
    x = F(x)
    k1, _, u1 = G.log_bounds(x)
    k2, _, u2 = G.log_bounds(1 - x)
    u1, u2 = G.up(u1), G.up(u2)
    lo = max(F(0), G.dn((-x * u1 - (1 - x) * u2) / L2hi))
    assert G.logLe(x, k1, u1) and G.logLe(1 - x, k2, u2) and lo * L2hi <= -x * u1 - (1 - x) * u2
    return (k1, k2, u1, u2, lo)


def lean_hbU(e):
    return f"⟨{z(e[0])}, {z(e[1])}, {Qc(e[2])}, {Qc(e[3])}, {Qc(e[4])}⟩"


def lean_hbL(e):
    return f"⟨{z(e[0])}, {z(e[1])}, {Qc(e[2])}, {Qc(e[3])}, {Qc(e[4])}⟩"


# ------------------------------------------------------------------ the exponent rows
def tq(a, k):
    return (k - a / 2) / (1 - a)


def piece_ok(R, HK, HT, ta):
    a, mu, dl, xi, lam, cl = R["a"], R["mu"], R["dl"], R["xi"], R["lam"], R["claim"]
    ok = F(1, 2) + mu * (HK - a * xi - (1 - a) * HT / 2 + (1 - a) / 2 - 1 + dl + lam) <= cl
    J = HK - a * R["hsLo"] - (1 - a) * HT
    if R["det"]:
        return ok and mu * (J + lam) + F(1, 4) + mu * R["l3"] / 4 <= cl and mu * (2 - dl + J + lam) <= cl
    return ok and (F(1, 4) + mu * (HK - F(3, 4) * a * R["hsLo"] + a * R["s"] / 4 - F(3, 4) * (1 - a) * HT
                                   + (1 - a) * (1 - ta) / 4) <= cl)


def row_ok(R, klo):
    a, mu, dl, cl = R["a"], R["mu"], R["dl"], R["claim"]
    ok = 0 < a < 1 and mu > 0 and a / 2 < klo <= F(1, 2) and mu * (1 - dl) <= cl and F(1, 2) - mu * dl / 2 <= cl
    if R["det"]:
        ok = ok and 2 * mu <= cl and mu * (2 - dl) <= cl and mu * (2 + R["lam"]) <= cl
    return ok


def pieces(R):
    ka, out, w = R["klo"], [], F(1, 10 ** 7)
    while ka < F(1, 2):
        best = None
        w = max(w / 4, F(1, 10 ** 12))
        while True:
            kb = min(ka + w, F(1, 2))
            if kb < F(1, 2):
                kb = F(round(kb * 10 ** 12), 10 ** 12)
            if kb <= ka:
                kb = ka + F(1, 10 ** 12)
            u, l = hbU(kb), hbL(tq(R["a"], ka))
            if piece_ok(R, u[4], l[4], tq(R["a"], ka)):
                best = (kb, u, l)
                if kb == F(1, 2):
                    break
                w *= 2
            else:
                break
        assert best is not None, ("exponent piece stuck", float(ka))
        out.append(best)
        ka = best[0]
    return out


MARK = {}


def main():
    xi = {}
    with contextlib.redirect_stdout(io.StringIO()):
        for s, D in C4.XI_DATA.items():
            ok, xq, lq = C4.cert_xi(s, D)
            assert ok
            xi[s] = xq
    S11, S8 = F(11, 100), F(1, 8)
    HS = {s: G.hb_bounds(s) for s in (S11, S8)}
    # log2 3 <= l3
    k3, _, u3 = G.log_bounds(F(3))
    l3 = G.up(G.up(u3) / L2lo)
    assert G.logLe(F(3), k3, G.up(u3))
    LAMQ = F(23978, 10 ** 12)   # lambda' >= lambda (checked in Lean, lam_*)
    xi_plus = None
    out = []        # Stage4.lean body
    rows = []       # Stage4ERows.lean body

    # ---------------- Hb(s)
    out.append(f"""/-- `SS.log_two_mem` with the bounds as plain numerals. -/
lemma log2_bounds : {r(L2lo)} ≤ log 2 ∧ log 2 ≤ {r(L2hi)} := by
  have h := SS.log_two_mem
  simp only [SS.L2lo, SS.L2hi] at h
  push_cast at h
  constructor <;> linarith [h.1, h.2]
""")
    out.append("/-! ## H(s) -/\n")
    for s, tag in ((S11, "s11"), (S8, "s8")):
        lo, hi = HS[s]
        term, _, _ = hb_mem(r(s), s, lo, hi, 60)
        out.append(f"""/-- `H({s})` enclosed. -/
theorem hs_{tag} : {r(lo)} ≤ Hb {r(s)} ∧ Hb {r(s)} ≤ {r(hi)} := by
  have h := {term}
  push_cast at h
  exact h
""")

    # ---------------- the eight contact claims from the cell trees
    MARK["xi"] = len(out)
    out.append("/-! ## [XI] the contact claims, from the cell trees (`Stage4Cells_*`) -/\n")
    probs = {p[0]: p for p in G.problems()}
    for name, s, rho, tau, T, doc in G.problems():
        k = F(s) / 2
        out.append(f"""/-- [XI] {doc}: on the whole colour polygon. -/
theorem V_{name} : ∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} {r(tau)} m d ≤ {r(T)} := by
  have h := G4_le_of_cells P_{name} prob_{name} T_{name} _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) cells_{name}
  have e1 : P_{name}.k = {q(k)} := by decide +kernel
  have e2 : P_{name}.ρ = {q(rho)} := by decide +kernel
  have e3 : P_{name}.τ = {q(tau)} := by decide +kernel
  have e4 : P_{name}.T = {q(T)} := by decide +kernel
  rw [e1, e2, e3, e4] at h
  push_cast at h
  exact h
""")

    # ---------------- lines, xi, controls
    def refute_pt(s, rho, tau, target_float):
        Ld = C4.Land(F(s), F(rho))
        ok, pt, val = Ld.refute(C4.I.q(F(tau)), target_float)
        assert ok, ("no witness", s, rho, tau)
        return pt

    def witness(name, s, rho, tau, need):
        """A rational colour (m, d) inside the polygon whose rigorous G4 lower bound exceeds `need`."""
        k = F(s) / 2
        pt = refute_pt(s, rho, tau, float(need))
        for den in (10 ** 12, 10 ** 14, 10 ** 16):
            m, d = F(round(pt[0] * den), den), F(round(pt[1] * den), den)
            b = k + F(rho) * (m - k)
            assert k < m < 2 * k and m < d < b
            terms = [("a", "(1 / 2 : ℝ)", r(d), F(1, 2), d, 1),
                     ("b", "(1 / 2 : ℝ)", f"(bR {r(k)} {r(rho)} {r(m)} - {r(m) if False else r(d)})", F(1, 2), b - d, 1),
                     ("c", f"(1 - {r(m)})", f"(bR {r(k)} {r(rho)} {r(m)} - {r(m)})", 1 - m, b - m, 2),
                     ("e", r(k), f"({r(m)} - {r(k)})", k, m - k, 1),
                     ("f", f"(bR {r(k)} {r(rho)} {r(m)} - {r(m)})", f"({r(d)} - {r(m)})", b - m, d - m, 1)]
            bnd, lines = {}, []
            for key, c_r, e_r, c, x, side in terms:
                ep = "(by unfold bR; norm_num)" if "bR" in e_r else "(by norm_num)"
                cp = "(by unfold bR; norm_num)" if "bR" in c_r else "(by norm_num)"
                term, lo, hi = hh_mem(c_r, e_r, c, x, ep)
                term = term.replace(f"{q(x)} {z(G.kfor(c))}", f"{q(x)} {z(G.kfor(c))}", 1)
                term = term.replace("(by norm_num) " + ep + " (by decide", cp + " " + ep + " (by decide", 1)
                bnd[key] = lo if side == 1 else hi
                lines.append(f"  have h{key} := ({term}).{side}")
            glo = F(tau) * (bnd["a"] + bnd["b"] - bnd["c"]) + (1 - F(tau)) * (bnd["e"] + bnd["f"])
            if glo > need:
                break
        else:
            raise AssertionError(("witness too weak", name))
        txt = f"""/-- A colour of `{name}` at tau = {tau}: inside the polygon, with `G4 ≥ {float(glo):.12f}`. -/
theorem wp_{name} : Poly4 {r(k)} {r(rho)} {r(m)} {r(d)} := by unfold Poly4 bR; norm_num

theorem w_{name} : {r(glo)} ≤ G4 {r(k)} {r(rho)} {r(tau)} {r(m)} {r(d)} := by
""" + "\n".join(lines) + f"""
  push_cast at ha hb hc he hf
  have := G4_ge (k := {r(k)}) (ρ := {r(rho)}) (τ := {r(tau)}) (m := {r(m)}) (d := {r(d)}) (by norm_num) (by norm_num)
    ha hb hc he hf
  linarith
"""
        return txt, (m, d), glo

    def line_txt(tag, s, t1, t2, A1, A2):
        sig = f"({r(A2)} - {r(A1)}) / ({r(t2)} - {r(t1)})"
        return f"{r(A1)} + {sig} * (τ - {r(t1)})", sig

    # single circuits
    for s, tag in ((S11, "s11"), (S8, "s8")):
        D = C4.XI_DATA[s]
        rho, t1, t2, c1, c2 = D["rho"], D["t1"], D["t2"], D["c1"], D["c2"]
        hlo, hhi = HS[s]
        k = s / 2
        A1, A2 = t1 * hhi, (1 - t2) * (1 - s)
        sig = (A2 - A1) / (t2 - t1)
        assert sig <= hlo and sig >= -(1 - s)
        ell = lambda t: A1 + sig * (t - t1)
        l1, l0 = ell(F(1)), ell(F(0))
        xiq = (hlo - s) / 2 - (l1 + l0) / 2
        assert l0 >= 0 and l1 >= 0 and xiq >= xi[s], (float(xiq), float(xi[s]))
        lup, rup = up(l1, 10 ** 10), up(l0, 10 ** 10)
        line, sg = line_txt(tag, s, t1, t2, A1, A2)
        out.append(f"""/-! ### s = {s}, rho = {rho} -/

/-- Lemma 3.4's hypothesis at s = {s}: `min{{V, tau h(s), (1 - tau)(1 - s)}} ≤ line` (as a disjunction) for
every tau, with the line through `(t1, t1 hsHi)` and `(t2, (1 - t2)(1 - s))`. -/
theorem line_{tag} : ∀ τ : ℝ, (∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} τ m d ≤ {line}) ∨
    τ * Hb {r(s)} ≤ {line} ∨ (1 - τ) * (1 - {r(s)}) ≤ {line} := by
  have hs := hs_{tag}
  refine line_single {r(k)} {r(rho)} (Hb {r(s)}) {r(s)} {r(t1)} {r(t2)} {r(A1)} {r(A2)} (by norm_num)
    (by linarith [hs.2]) (by norm_num) (by have := hs.1; norm_num at this ⊢; linarith) (by norm_num)
    (fun m d hp => (V_{tag}_t1 m d hp).trans (by norm_num)) (fun m d hp => (V_{tag}_t2 m d hp).trans (by norm_num))

/-- The pair (l, r) = (line(1), line(0)) and xi = (h(s) - s)/2 - (l + r)/2 ≥ {xi[s]} (Prop. 3.7). -/
theorem xi_{tag} : {r(xi[s])} ≤ (Hb {r(s)} - {r(s)}) / 2 - ({r(A1)} + {sg} * (1 - {r(t1)}) + ({r(A1)} + {sg} * (0 - {r(t1)}))) / 2 ∧
    0 ≤ {r(A1)} + {sg} * (0 - {r(t1)}) ∧ 0 ≤ {r(A1)} + {sg} * (1 - {r(t1)}) ∧
    {r(A1)} + {sg} * (1 - {r(t1)}) ≤ {r(lup)} ∧ {r(A1)} + {sg} * (0 - {r(t1)}) ≤ {r(rup)} := by
  have hs := hs_{tag}.1
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  norm_num at hs ⊢
  linarith
""")
        # controls C1, C2 and [F1]
        w1, p1, g1 = witness(f"{tag}_C1", s, rho, c1, c1 * hhi)
        w2, p2, g2 = witness(f"{tag}_C2", s, rho, c2, (1 - c2) * (1 - s))
        out.append(w1)
        out.append(w2)
        # xi_max = alpha_F h + beta_F evaluated at hsHi
        alF = F(1, 2) - c1 + c1 * (F(1, 2) - c1) / (c2 - c1)
        beF = -s / 2 - ((1 - c2) * (1 - s)) * (F(1, 2) - c1) / (c2 - c1)
        assert alF > 0
        ximax = up(alF * hhi + beF, 10 ** 10)
        out.append(f"""/-- Control C1: one grid step past the left contact the claim `V(c1) ≤ c1 h(s)` is false. -/
theorem C1_{tag} : ¬ ∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} {r(c1)} m d ≤ {r(c1)} * Hb {r(s)} := by
  intro h
  have := h _ _ wp_{tag}_C1
  linarith [w_{tag}_C1, hs_{tag}.2]

/-- Control C2: one grid step past the right contact `V(c2) ≤ (1 - c2)(1 - s)` is false. -/
theorem C2_{tag} : ¬ ∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} {r(c2)} m d ≤ (1 - {r(c2)}) * (1 - {r(s)}) := by
  intro h
  have := h _ _ wp_{tag}_C2
  norm_num at this
  linarith [w_{tag}_C2]

/-- [F1]: every line valid for this V (in the sense of `line_{tag}`) has xi ≤ {ximax}. -/
theorem F1_{tag} : ∀ l r : ℝ, (∀ τ : ℝ, (∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} τ m d ≤ r + τ * (l - r)) ∨
    τ * Hb {r(s)} ≤ r + τ * (l - r) ∨ (1 - τ) * (1 - {r(s)}) ≤ r + τ * (l - r)) →
    (Hb {r(s)} - {r(s)}) / 2 - (l + r) / 2 ≤ {r(ximax)} := by
  intro l r hv
  have hs := hs_{tag}
  have w1 := w_{tag}_C1
  have w2 := w_{tag}_C2
  have h := F1_of (Hb {r(s)}) {r(s)} {r(c1)} {r(c2)} l r (G4 {r(k)} {r(rho)} {r(c1)} {r(p1[0])} {r(p1[1])})
    (G4 {r(k)} {r(rho)} {r(c2)} {r(p2[0])} {r(p2[1])}) (by norm_num) (by norm_num) (by linarith [hs.2])
    (by linarith) (by linarith [hs.2]) (by linarith [hs.1])
    ((hv {r(c1)}).imp_left (fun H => H _ _ wp_{tag}_C1)) ((hv {r(c2)}).imp_left (fun H => H _ _ wp_{tag}_C2))
  have key : (Hb {r(s)} - {r(s)}) / 2 - ({r(c1)} * Hb {r(s)} + ((1 - {r(c2)}) * (1 - {r(s)}) - {r(c1)} * Hb {r(s)}) *
      (1 / 2 - {r(c1)}) / ({r(c2)} - {r(c1)})) = {r(alF)} * Hb {r(s)} + {r(beF)} := by ring
  rw [key] at h
  linarith [hs.2]
""")
        globals()["XI_" + tag] = (k, rho, l1, l0)

    # family (Stage 4+)
    s = C4P.S
    hlo, hhi = HS[s]
    k = s / 2
    R1, R2 = C4P.R1, C4P.R2
    t1, t2, v, c1, c2 = (C4P.DATA[x] for x in ("t1", "t2", "v", "c1", "c2"))
    A1, A2 = t1 * hhi, (1 - t2) * (1 - s)
    sig = (A2 - A1) / (t2 - t1)
    assert sig <= hlo and sig >= -(1 - s)
    ell = lambda t: A1 + sig * (t - t1)
    assert ell(v) == probs["p1_v"][4] == probs["p2_v"][4]
    l1, l0 = ell(F(1)), ell(F(0))
    xi_plus = F(14072281, 2 * 10 ** 9)
    xiq = (hlo - s) / 2 - (l1 + l0) / 2
    assert l0 >= 0 and l1 >= 0 and xiq >= xi_plus
    line, sg = line_txt("plus", s, t1, t2, A1, A2)
    out.append(f"""/-! ### Stage 4+: the family rho = {R1}, {R2} at s = {s} -/

/-- Lemma 3.4's hypothesis for the family of two circuits (Sec. 8). -/
theorem line_plus : ∀ τ : ℝ, (∀ m d : ℝ, Poly4 {r(k)} {r(R1)} m d → G4 {r(k)} {r(R1)} τ m d ≤ {line}) ∨
    (∀ m d : ℝ, Poly4 {r(k)} {r(R2)} m d → G4 {r(k)} {r(R2)} τ m d ≤ {line}) ∨
    τ * Hb {r(s)} ≤ {line} ∨ (1 - τ) * (1 - {r(s)}) ≤ {line} := by
  have hs := hs_s11
  refine line_family {r(k)} {r(R1)} {r(R2)} (Hb {r(s)}) {r(s)} {r(t1)} {r(t2)} {r(v)} {r(A1)} {r(A2)} (by norm_num)
    (by linarith [hs.2]) (by norm_num) (by have := hs.1; norm_num at this ⊢; linarith) (by norm_num)
    (fun m d hp => (V_p1_t1 m d hp).trans (by norm_num)) (fun m d hp => (V_p1_v m d hp).trans (by norm_num))
    (fun m d hp => (V_p2_v m d hp).trans (by norm_num)) (fun m d hp => (V_p2_t2 m d hp).trans (by norm_num))

/-- The family's pair and xi ≥ {xi_plus}. -/
theorem xi_plus : {r(xi_plus)} ≤ (Hb {r(s)} - {r(s)}) / 2 - ({r(A1)} + {sg} * (1 - {r(t1)}) + ({r(A1)} + {sg} * (0 - {r(t1)}))) / 2 ∧
    0 ≤ {r(A1)} + {sg} * (0 - {r(t1)}) ∧ 0 ≤ {r(A1)} + {sg} * (1 - {r(t1)}) := by
  have hs := hs_s11.1
  refine ⟨?_, by norm_num, by norm_num⟩
  norm_num at hs ⊢
  linarith
""")
    ws = {}
    for key, rho, tau, need in (("C1a", R1, c1, c1 * hhi), ("C1b", R2, c1, c1 * hhi),
                                ("C2a", R1, c2, (1 - c2) * (1 - s)), ("C2b", R2, c2, (1 - c2) * (1 - s)),
                                ("C3a", R1, t2, A2), ("C3b", R2, t1, A1)):
        txt, pt, glo = witness(f"plus_{key}", s, rho, tau, need)
        out.append(txt)
        ws[key] = pt
    alF = F(1, 2) - c1 + c1 * (F(1, 2) - c1) / (c2 - c1)
    beF = -s / 2 - ((1 - c2) * (1 - s)) * (F(1, 2) - c1) / (c2 - c1)
    ximax = up(alF * hhi + beF, 10 ** 10)
    G1 = lambda rho, tau, pt: f"G4 {r(k)} {r(rho)} {r(tau)} {r(pt[0])} {r(pt[1])}"
    out.append(f"""/-- Stage 4+ controls C1, C2: one grid step past each contact both members beat the trivial line. -/
theorem C1_plus : (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R1)} m d → G4 {r(k)} {r(R1)} {r(c1)} m d ≤ {r(c1)} * Hb {r(s)}) ∧
    (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R2)} m d → G4 {r(k)} {r(R2)} {r(c1)} m d ≤ {r(c1)} * Hb {r(s)}) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h _ _ wp_plus_C1a; linarith [w_plus_C1a, hs_s11.2]
  · have := h _ _ wp_plus_C1b; linarith [w_plus_C1b, hs_s11.2]

theorem C2_plus : (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R1)} m d → G4 {r(k)} {r(R1)} {r(c2)} m d ≤ (1 - {r(c2)}) * (1 - {r(s)})) ∧
    (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R2)} m d → G4 {r(k)} {r(R2)} {r(c2)} m d ≤ (1 - {r(c2)}) * (1 - {r(s)})) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h _ _ wp_plus_C2a; norm_num at this; linarith [w_plus_C2a]
  · have := h _ _ wp_plus_C2b; norm_num at this; linarith [w_plus_C2b]

/-- Stage 4+ control C3: each member alone fails at the other's contact, so the family is needed. -/
theorem C3_plus : (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R1)} m d → G4 {r(k)} {r(R1)} {r(t2)} m d ≤ {r(A2)}) ∧
    (¬ ∀ m d : ℝ, Poly4 {r(k)} {r(R2)} m d → G4 {r(k)} {r(R2)} {r(t1)} m d ≤ {r(A1)}) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h _ _ wp_plus_C3a; linarith [w_plus_C3a]
  · have := h _ _ wp_plus_C3b; linarith [w_plus_C3b]

/-- Stage 4+ [F1]: every line valid for the family has xi ≤ {ximax}. -/
theorem F1_plus : ∀ l r : ℝ, (∀ τ : ℝ, (∀ m d : ℝ, Poly4 {r(k)} {r(R1)} m d → G4 {r(k)} {r(R1)} τ m d ≤ r + τ * (l - r)) ∨
    (∀ m d : ℝ, Poly4 {r(k)} {r(R2)} m d → G4 {r(k)} {r(R2)} τ m d ≤ r + τ * (l - r)) ∨
    τ * Hb {r(s)} ≤ r + τ * (l - r) ∨ (1 - τ) * (1 - {r(s)}) ≤ r + τ * (l - r)) →
    (Hb {r(s)} - {r(s)}) / 2 - (l + r) / 2 ≤ {r(ximax)} := by
  intro l r hv
  have hs := hs_s11
  have wa := w_plus_C1a
  have wb := w_plus_C1b
  have wc := w_plus_C2a
  have wd := w_plus_C2b
  have hl1 : min ({G1(R1, c1, ws['C1a'])}) ({G1(R2, c1, ws['C1b'])}) ≤ r + {r(c1)} * (l - r) ∨
      {r(c1)} * Hb {r(s)} ≤ r + {r(c1)} * (l - r) ∨ (1 - {r(c1)}) * (1 - {r(s)}) ≤ r + {r(c1)} * (l - r) := by
    rcases hv {r(c1)} with H | H | H | H
    · exact Or.inl ((min_le_left _ _).trans (H _ _ wp_plus_C1a))
    · exact Or.inl ((min_le_right _ _).trans (H _ _ wp_plus_C1b))
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr H)
  have hl2 : min ({G1(R1, c2, ws['C2a'])}) ({G1(R2, c2, ws['C2b'])}) ≤ r + {r(c2)} * (l - r) ∨
      {r(c2)} * Hb {r(s)} ≤ r + {r(c2)} * (l - r) ∨ (1 - {r(c2)}) * (1 - {r(s)}) ≤ r + {r(c2)} * (l - r) := by
    rcases hv {r(c2)} with H | H | H | H
    · exact Or.inl ((min_le_left _ _).trans (H _ _ wp_plus_C2a))
    · exact Or.inl ((min_le_right _ _).trans (H _ _ wp_plus_C2b))
    · exact Or.inr (Or.inl H)
    · exact Or.inr (Or.inr H)
  have h := F1_of (Hb {r(s)}) {r(s)} {r(c1)} {r(c2)} l r _ _ (by norm_num) (by norm_num)
    (le_min (by linarith [hs.2]) (by linarith [hs.2])) (le_min (by linarith) (by linarith))
    (by linarith [hs.2]) (by linarith [hs.1]) hl1 hl2
  have key : (Hb {r(s)} - {r(s)}) / 2 - ({r(c1)} * Hb {r(s)} + ((1 - {r(c2)}) * (1 - {r(s)}) - {r(c1)} * Hb {r(s)}) *
      (1 / 2 - {r(c1)}) / ({r(c2)} - {r(c1)})) = {r(alF)} * Hb {r(s)} + {r(beF)} := by ring
  rw [key] at h
  linarith [hs.2]
""")

    # ---------------- [LAM]
    MARK["e"] = len(out)
    out.append("/-! ## [LAM] the round-family loss lambda -/\n")
    lam_rows = {}
    for tag, a in (("s11", C4.PARAMS[(S11, True)][0]), ("s8", C4.PARAMS[(S8, True)][0]),
                   ("plus", C4P.PARAMS[0])):
        lam_rows[tag] = a
    nb = F(C4.NB)

    def lam_txt(tag, nbv, a, bound, upper=True):
        ab = nbv * a / 2
        bb = nbv / 2 - ab
        assert ab.denominator == 1 and bb.denominator == 1
        P = (ab + 1) * (bb + 1)
        X = 1 + nbv * (L2hi if upper else L2lo)
        t1, lo1, hi1 = log_mem(r(nbv), nbv)
        t2, lo2, hi2 = log_mem(f"(1 + {r(nbv)} * {r(L2hi if upper else L2lo)})", X)
        t3, lo3, hi3 = log_mem(r(P), P)
        if upper:
            val = (hi1 / L2lo + 3 + hi2 / L2lo + 2 * (hi3 / L2lo)) / nbv
            assert val <= bound, (float(val), float(bound))
        else:
            val = (lo1 / L2hi + 3 + lo2 / L2hi + 2 * (lo3 / L2hi)) / nbv
            assert val >= bound, (float(val), float(bound))
        rel = "≤" if upper else "≥"
        tL = "hi" if upper else "lo"
        return f"""/-- lambda at N_b = {nbv}, alpha = {a} (a_b = {ab}, b_b = {bb}): lambda {rel} {bound}. -/
theorem lam_{tag} : lamR {r(nbv)} {r(ab)} {r(bb)} {rel} {r(bound)} := by
  have h1 := {t1}
  have h2 := {t2}
  have h3 := {t3}
  have L := log2_bounds
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hx : (0 : ℝ) < 1 + {r(nbv)} * log 2 := by positivity
  push_cast at h1 h2 h3
  have m2 : {f"log (1 + {r(nbv)} * log 2) ≤ log (1 + {r(nbv)} * {r(L2hi)})" if upper else f"log (1 + {r(nbv)} * {r(L2lo)}) ≤ log (1 + {r(nbv)} * log 2)"} :=
    Real.log_le_log {'hx' if upper else '(by norm_num)'} (by {'linarith [L.2]' if upper else 'linarith [L.1]'})
  have p1 : (0 : ℝ) ≤ log {r(nbv)} := Real.log_nonneg (by norm_num)
  have p2 : (0 : ℝ) ≤ log (1 + {r(nbv)} * log 2) := Real.log_nonneg (by linarith [L.1])
  have p3 : (0 : ℝ) ≤ log {r(P)} := Real.log_nonneg (by norm_num)
  {lam_core(upper)}
"""

    def lam_core(upper):
        if upper:
            return """have d1 := div_le_div₀ (by linarith [h1.1, p1]) h1.2 (by norm_num) L.1
  have d2 := div_le_div₀ (by linarith [h2.1, p2, m2]) (m2.trans h2.2) (by norm_num) L.1
  have d3 := div_le_div₀ (by linarith [h3.1, p3]) h3.2 (by norm_num) L.1
  unfold lamR
  rw [div_le_iff₀ (by norm_num)]
  norm_num at d1 d2 d3 ⊢
  linarith"""
        return """have d1 := div_le_div₀ p1 h1.1 hL L.2
  have d2 := div_le_div₀ p2 (h2.1.trans m2) hL L.2
  have d3 := div_le_div₀ p3 h3.1 hL L.2
  unfold lamR
  rw [ge_iff_le, le_div_iff₀ (by norm_num)]
  norm_num at d1 d2 d3 ⊢
  linarith"""

    for tag, a in lam_rows.items():
        out.append(lam_txt(tag, nb, a, LAMQ))
    LAMLO = F(23976, 10 ** 12)
    out.append(lam_txt("s11_lower", nb, lam_rows["s11"], LAMLO, upper=False))
    nb7 = F(2 * 10 ** 7)
    with contextlib.redirect_stdout(io.StringIO()):
        lam7 = C4.lam_bound(2 * 10 ** 7, lam_rows["s11"])
    LAM7LO = dn(F(lam7) * F(999, 1000), 10 ** 12)
    out.append(lam_txt("K7_lower", nb7, lam_rows["s11"], LAM7LO, upper=False))

    # ---------------- [K]
    out.append("/-! ## [K] the hardcoded circuit size at eps = 1e-9 (necessary conditions of Cor. 3.8) -/\n")
    eps = F(1, 10 ** 9)
    with contextlib.redirect_stdout(io.StringIO()):
        for s, tag in ((S11, "s11"), (S8, "s8")):
            ok, xq, lq = C4.cert_xi(s, C4.XI_DATA[s])
            kk, cc, N0 = C4.k0_for(s, lq, eps)
            den = s.denominator
            kprev = kk - den
            assert (lq + eps / 4) * cc <= eps / 4 * kk * kk
            assert cc == den * -(-F(kk) // (s * den))
            tA, loA, hiA = log_mem(r(kk + 1), F(kk + 1))
            tB, loB, hiB = log_mem(r(kprev + 1), F(kprev + 1))
            assert hiA / L2lo <= eps / 4 * kk and loB / L2hi > eps / 4 * kprev
            ex = len(str(N0)) - 1
            lb = F(N0 // 10 ** (ex - 4), 10 ** 4) * 10 ** ex
            out.append(f"""/-- [K] at s = {s}: k_0 = {kk} (a multiple of {den}), c = {cc} = {den} ceil(k_0/({s} {den})) ≥ k_0/s,
condition (a) with lmax = {lq} (≥ this s's certified l), condition (b) log2(k_0 + 1)/k_0 ≤ eps/4, k_0 - {den} fails (b),
and N0 = k_0^2 + c = {N0} ≥ {lb}, but not ≥ {lb + F(10 ** (ex - 4))}. -/
theorem K_{tag} : ({r(lq)} + {r(eps)} / 4) * {r(cc)} ≤ {r(eps)} / 4 * {r(kk)} ^ 2 ∧ {r(kk)} / {r(s)} ≤ {r(cc)} ∧
    log {r(kk + 1)} / log 2 / {r(kk)} ≤ {r(eps)} / 4 ∧
    {r(eps)} / 4 < log {r(kprev + 1)} / log 2 / {r(kprev)} ∧
    ({kk} : ℕ) ^ 2 + {cc} = {N0} ∧ ({lb.numerator} : ℝ) ≤ {N0} ∧ ¬ (({(lb + F(10 ** (ex - 4))).numerator} : ℝ) ≤ {N0}) := by
  have hA := {tA}
  have hB := {tB}
  have L := log2_bounds
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  push_cast at hA hB
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · have d := div_le_div₀ (by norm_num) hA.2 (by norm_num) L.1
    have d' := div_le_div_of_nonneg_right d (by norm_num : (0 : ℝ) ≤ {r(kk)})
    exact d'.trans (by norm_num)
  · have d := div_le_div₀ (Real.log_nonneg (by norm_num)) hB.1 hL L.2
    have d' := div_le_div_of_nonneg_right d (by norm_num : (0 : ℝ) ≤ {r(kprev)})
    exact lt_of_lt_of_le (by norm_num) d'
""")

    # ---------------- [E]
    out.append("/-! ## [E] the exponents -/\n")
    t3, lo3, hi3 = log_mem("(3 : ℝ)", F(3))
    assert hi3 / L2lo <= l3
    out.append(f"""/-- `log2 3 ≤ {l3}`. -/
theorem log2_3_le : log 3 / log 2 ≤ {r(l3)} := by
  have h := {t3}
  have L := log2_bounds
  push_cast at h
  have d := div_le_div₀ (by linarith [h.1, Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]) h.2 (by norm_num) L.1
  norm_num at d ⊢
  linarith
""")
    rows.append("""import SubsetsumLean.Stage4ECheck

/-! The rows and pieces of Stage 4's [E] (generated by `gen_stage4.py`; do not edit). -/

namespace SS4
""")
    erows = []
    for (s, det), (a, mu, dl) in C4.PARAMS.items():
        tag = ("D" if det else "R") + ("11" if s == S11 else "8")
        erows.append((tag, s, det, a, mu, dl, xi[s], F(str(C4.CLAIM[(s, det)]))))
    a, mu, dl = C4P.PARAMS
    erows.append(("Dplus", S11, True, a, mu, dl, xi_plus, F(str(C4P.CLAIM))))
    for tag, s, det, a, mu, dl, xis, claim in erows:
        klo = C4.kap_lo_for(dl)
        R = dict(a=a, mu=mu, dl=dl, xi=xis, lam=LAMQ if det else F(0), hsLo=HS[s][0], l3=l3, det=det, s=s,
                 claim=claim, klo=klo)
        assert row_ok(R, klo)
        ps = pieces(R)
        hk = hbU(klo)
        assert hk[4] < 1 - dl
        if det:
            assert tq(a, klo) > F(1, 3) + F(1, 100)
        lam_name = {"D11": "s11", "D8": "s8", "Dplus": "plus"}.get(tag)
        rows.append(f"""/-- Row {tag}: s = {s}, {'deterministic' if det else 'randomized'}, claim {claim}. -/
def R_{tag} : ERow := ⟨{Qc(a)}, {Qc(mu)}, {Qc(dl)}, {Qc(xis)}, {Qc(R['lam'])}, {Qc(s)}, {Qc(HS[s][0])}, {Qc(l3)}, {'true' if det else 'false'}, {Qc(claim)}⟩
def klo_{tag} : ℚ := {Qc(klo)}
def PS_{tag} : List EP := [{", ".join(f"⟨{Qc(kb)}, {lean_hbU(u)}, {lean_hbL(l)}⟩" for kb, u, l in ps)}]
theorem rowok_{tag} : R_{tag}.ok klo_{tag} = true := by decide +kernel
theorem rowchk_{tag} : R_{tag}.chkE klo_{tag} PS_{tag} = true := by decide +kernel
/-- The layer-range certificate: `H(kappa_lo) < 1 - delta`. -/
theorem range_{tag} : HbU.ok klo_{tag} {lean_hbU(hk)} = true ∧ {Qc(hk[4])} < 1 - {Qc(dl)} := by decide +kernel
""")
        out.append(f"""/-- [E] row {tag} (s = {s}, {'deterministic' if det else 'randomized'}, claim {claim}): every cost term is at most
the claim for every kappa in [kappa_lo, 1 - kappa_lo] (kappa_lo = {klo}), which contains the layer range
(`range_{tag}`: H(kappa_lo) < 1 - delta). -/
theorem E_{tag} : (((R_{tag}.μ : ℚ) : ℝ) * (1 - R_{tag}.δ) ≤ R_{tag}.claim ∧ 1 / 2 - ((R_{tag}.μ : ℚ) : ℝ) * R_{tag}.δ / 2 ≤ R_{tag}.claim ∧
    (R_{tag}.det = true → 2 * ((R_{tag}.μ : ℚ) : ℝ) ≤ R_{tag}.claim ∧ ((R_{tag}.μ : ℚ) : ℝ) * (2 - R_{tag}.δ) ≤ R_{tag}.claim ∧
      ((R_{tag}.μ : ℚ) : ℝ) * (2 + R_{tag}.lam) ≤ R_{tag}.claim)) ∧
    ∀ κ : ℝ, ((klo_{tag} : ℚ) : ℝ) ≤ κ → κ ≤ 1 - ((klo_{tag} : ℚ) : ℝ) → ETerms R_{tag} κ := by
  have hs : ((R_{tag}.hsLo : ℚ) : ℝ) ≤ Hb (R_{tag}.s : ℚ) := by
    have e1 : R_{tag}.hsLo = {q(HS[s][0])} := by decide +kernel
    have e2 : R_{tag}.s = {q(s)} := by decide +kernel
    rw [e1, e2]; push_cast; exact hs_{"s11" if s == S11 else "s8"}.1
  have hl3 : log 3 / log 2 ≤ ((R_{tag}.l3 : ℚ) : ℝ) := by
    have e : R_{tag}.l3 = {q(l3)} := by decide +kernel
    rw [e]; push_cast; exact log2_3_le
  exact E_row R_{tag} klo_{tag} PS_{tag} rowok_{tag} rowchk_{tag} (by simp [PS_{tag}]) hs hl3
""")
        globals()["ROW_" + tag] = (R, klo, ps)
    for tag, title in (("D11", "Theorem 4 (s = 11/100)"), ("Dplus", "Theorem 4+ (the family)")):
        R, klo, _ = globals()["ROW_" + tag]
        a, mu, dl, xis, lam, s_, claim = R["a"], R["mu"], R["dl"], R["xi"], R["lam"], R["s"], R["claim"]
        out.append(f"""/-- {title}, every kappa-dependent cost term in plain numbers: for kappa in [kappa_lo, 1 - kappa_lo], P3, P4 and
P6 are at most {claim} (with xi ≥ {xis}, lambda ≤ {lam}); `E_{tag}` also bounds the constant terms. -/
theorem headline_{tag} : ∀ κ : ℝ, {r(klo)} ≤ κ → κ ≤ 1 - {r(klo)} →
    P3R {r(a)} {r(mu)} {r(dl)} {r(xis)} {r(lam)} κ ≤ {r(claim)} ∧ P4dR {r(a)} {r(mu)} {r(lam)} {r(s_)} κ ≤ {r(claim)} ∧
    P6R {r(a)} {r(mu)} {r(dl)} {r(lam)} {r(s_)} κ ≤ {r(claim)} := by
  intro κ h1 h2
  have ek : ((klo_{tag} : ℚ) : ℝ) = {r(klo)} := by simp only [klo_{tag}, Q]; push_cast; ring
  obtain ⟨h3, hd, -⟩ := E_{tag}.2 κ (by rw [ek]; exact h1) (by rw [ek]; exact h2)
  obtain ⟨h4, h6⟩ := hd rfl
  simp only [R_{tag}, Q] at h3 h4 h6
  push_cast at h3 h4 h6
  exact ⟨h3, h4, h6⟩
""")
    # ---------------- the exponent controls (cert_stage4.py K1-K9, cert_stage4plus.py K1-K4)
    out.append("/-! ## The exponent controls: each is refuted (proved false) -/\n")
    hl11, hh11 = HS[S11]

    def p6_lo(a, mu, dl, lam, hbk_lo, hbt_hi, hs_hi):
        return mu * (2 - dl + hbk_lo - a * hs_hi - (1 - a) * hbt_hi + lam)

    def p3_lo(a, mu, dl, xi_, lam, hbk_lo, hbt_hi):
        return F(1, 2) + mu * (hbk_lo - a * xi_ - (1 - a) * hbt_hi / 2 + (1 - a) / 2 - 1 + dl + lam)

    def at_klo(tag, a, mu, dl, xi_, lam_lo, claim, lam_expr, kname):
        """Refute 'every term <= claim - g' (or '<= claim' when g = 0) at kappa = kappa_lo. Returns Lean text."""
        klo = C4.kap_lo_for(dl)
        L = hbL(klo)
        U = hbU(tq(a, klo))
        v6 = p6_lo(a, mu, dl, lam_lo, L[4], U[4], hh11)
        v3 = p3_lo(a, mu, dl, xi_, lam_lo, L[4], U[4])
        rows.append(f"theorem kb_{kname} : HbL.ok {Qc(klo)} {lean_hbL(L)} = true ∧ HbU.ok (tq {Qc(a)} {Qc(klo)}) {lean_hbU(U)} = true := by decide +kernel")
        return klo, L, U, v6, v3

    def klo_proof(kname, a, klo, term):
        return f"""  intro h
  have hk := h {r(klo)} le_rfl (by norm_num)
  have a := HbL.sound _ _ kb_{kname}.1
  have b := HbU.sound _ _ kb_{kname}.2
  rw [tR_cast] at b
  simp only [Q] at a b
  push_cast at a b
  have hs := hs_s11
  unfold {term} at hk
{"  unfold JR at hk" if term == "P6R" else "  -- P3 has no J term"}
  linarith [hs.1, hs.2]"""

    def half_proof(term):
        return f"""  intro h
  have hk := h (1 / 2) (by norm_num) (by norm_num)
  have hs := hs_s11
  unfold {term} at hk
{"  unfold JR at hk" if term == "P6R" else "  -- P3 has no J term"}
  rw [tR_half _ (by norm_num), Hb_half] at hk
  linarith [hs.1, hs.2]"""

    def ctl_row(prefix, a, mu, dl, xi_, claim, lam_name, gs):
        klo = C4.kap_lo_for(dl)
        # K1: the bound cannot be lowered by g at these parameters
        kl, L, U, v6, v3 = at_klo(prefix, a, mu, dl, xi_, LAMQ if False else LAMLO, claim, None, f"{prefix}_K1")
        g = next(g for g in gs if max(v6, v3) > claim - g)
        term = "P6R" if v6 > claim - g else "P3R"
        stmt = (f"P6R {r(a)} {r(mu)} {r(dl)} {r(LAMLO)} {r(S11)} κ" if term == "P6R"
                else f"P3R {r(a)} {r(mu)} {r(dl)} {r(xi_)} {r(LAMLO)} κ")
        out.append(f"""/-- {prefix} K1: even with lambda at its lower bound, the claim minus {g} fails at kappa_lo ({term}). -/
theorem Kc1_{prefix} : ¬ ∀ κ : ℝ, {r(kl)} ≤ κ → κ ≤ 1 - {r(kl)} → {stmt} ≤ {r(claim - g)} := by
{klo_proof(f"{prefix}_K1", a, kl, term)}
""")
        # K2: mu raised 1% (kappa = 1/2, P6)
        mu2 = mu * F(101, 100)
        v = mu2 * (2 - dl + a * (1 - hh11) + LAMLO)
        assert v > claim
        out.append(f"""/-- {prefix} K2: mu raised 1% breaks the claim (P6 at kappa = 1/2). -/
theorem Kc2_{prefix} : ¬ ∀ κ : ℝ, {r(klo)} ≤ κ → κ ≤ 1 - {r(klo)} → P6R {r(a)} {r(mu2)} {r(dl)} {r(LAMLO)} {r(S11)} κ ≤ {r(claim)} := by
{half_proof("P6R")}
""")
        # delta doubled (P3 at 1/2)
        kl2 = C4.kap_lo_for(2 * dl)
        v = F(1, 2) + mu * (2 * dl - a * xi_ + LAMLO)
        assert v > claim
        out.append(f"""/-- {prefix} {'K4' if prefix == 'D11' else 'K3'}: delta doubled breaks the claim (P3 at kappa = 1/2). -/
theorem Kc_delta_{prefix} : ¬ ∀ κ : ℝ, {r(kl2)} ≤ κ → κ ≤ 1 - {r(kl2)} → P3R {r(a)} {r(mu)} {r(2 * dl)} {r(xi_)} {r(LAMLO)} κ ≤ {r(claim)} := by
{half_proof("P3R")}
""")
        return klo

    gs = [F(i, 10 ** 7) for i in range(1, 8)]
    a, mu, dl = C4.PARAMS[(S11, True)]
    claim = F(str(C4.CLAIM[(S11, True)]))
    klo = ctl_row("D11", a, mu, dl, xi[S11], claim, "s11", gs)
    # K3: xi = 0 gives E >= 1/2
    out.append(f"""/-- K3: with xi = 0 the exponent is at least 1/2 (P3 at kappa = 1/2). -/
theorem Kc3_D11 : 1 / 2 ≤ P3R {r(a)} {r(mu)} {r(dl)} 0 {r(LAMLO)} (1 / 2) := by
  unfold P3R
  rw [tR_half _ (by norm_num), Hb_half]
  norm_num
""")
    # K5: the kappa range cut to |kappa - 1/2| <= 1e-3: the range certificate refuses, H(1/2 - 1e-3) >= 1 - delta
    x5 = F(1, 2) - F(1, 1000)
    L5 = hbL(x5)
    assert L5[4] >= 1 - dl
    rows.append(f"theorem kb_K5 : HbL.ok {Qc(x5)} {lean_hbL(L5)} = true := by decide +kernel")
    out.append(f"""/-- K5: cutting the layer range to |kappa - 1/2| ≤ 1e-3 is refused: H(1/2 - 1e-3) ≥ 1 - delta. -/
theorem Kc5_D11 : ¬ (Hb {r(x5)} < 1 - {r(dl)}) := by
  have a := HbL.sound _ _ kb_K5
  simp only [Q] at a
  push_cast at a
  linarith
""")
    # K6: the deterministic claim at the randomized parameters (P6 at 1/2)
    ra, rmu, rdl = C4.PARAMS[(S11, False)]
    v = rmu * (2 - rdl + ra * (1 - hh11) + LAMLO)
    assert v > claim
    rk = C4.kap_lo_for(rdl)
    out.append(f"""/-- K6: the deterministic claim at the randomized optimum's parameters fails (P6 at kappa = 1/2). -/
theorem Kc6_D11 : ¬ ∀ κ : ℝ, {r(rk)} ≤ κ → κ ≤ 1 - {r(rk)} → P6R {r(ra)} {r(rmu)} {r(rdl)} {r(LAMLO)} {r(S11)} κ ≤ {r(claim)} := by
{half_proof("P6R")}
""")
    # K7: N_b = 2e7 (lambda >= LAM7LO) breaks the claim at kappa_lo (P6)
    kl, L, U, v6, v3 = at_klo("K7", a, mu, dl, xi[S11], LAM7LO, claim, None, "D11_K7")
    assert v6 > claim, float(v6 - claim)
    out.append(f"""/-- K7: with N_b = 2e7 (lambda ≥ {LAM7LO}, `lam_K7_lower`) the claim fails at kappa_lo (P6). -/
theorem Kc7_D11 : ¬ ∀ κ : ℝ, {r(kl)} ≤ κ → κ ≤ 1 - {r(kl)} →
    P6R {r(a)} {r(mu)} {r(dl)} (lamR {r(nb7)} {r(nb7 * a / 2)} {r(nb7 / 2 - nb7 * a / 2)}) {r(S11)} κ ≤ {r(claim)} := by
  intro h
  have hk := h {r(kl)} le_rfl (by norm_num)
  have a := HbL.sound _ _ kb_D11_K7.1
  have b := HbU.sound _ _ kb_D11_K7.2
  rw [tR_cast] at b
  simp only [Q] at a b
  push_cast at a b
  have hs := hs_s11
  have hl := lam_K7_lower
  unfold P6R JR at hk
  linarith [hs.1, hs.2]
""")
    out.append(f"""/-- K8: lambda is a real cost: lambda ≥ {LAMLO} at N_b = 8e9, so every term that pays for rounds carries
mu lambda ≥ {mu * LAMLO}. -/
theorem Kc8_D11 : {r(mu * LAMLO)} ≤ {r(mu)} * lamR {r(nb)} {r(nb * a / 2)} {r(nb / 2 - nb * a / 2)} := by
  have := lam_s11_lower
  linarith
""")
    rclaim = F(str(C4.CLAIM[(S11, False)]))
    assert F(1, 2) - mu * dl / 2 > rclaim
    out.append(f"""/-- K9: the randomized claim {rclaim} is false for the deterministic algorithm (P2 alone exceeds it). -/
theorem Kc9_D11 : ¬ (1 / 2 - {r(mu)} * {r(dl)} / 2 ≤ {r(rclaim)}) := by norm_num
""")
    # Stage 4+: K1-K4
    a, mu, dl = C4P.PARAMS
    pclaim = F(str(C4P.CLAIM))
    ctl_row("Dplus", a, mu, dl, xi_plus, pclaim, "plus", gs)
    xs = F(22424519, 5 * 10 ** 9)
    v = F(1, 2) + mu * (dl - a * xs + LAMLO)
    assert v > pclaim
    kp = C4.kap_lo_for(dl)
    out.append(f"""/-- Stage 4+ K4: the single-circuit xi = {xs} at these parameters breaks the claim (P3 at kappa = 1/2). -/
theorem Kc4_Dplus : ¬ ∀ κ : ℝ, {r(kp)} ≤ κ → κ ≤ 1 - {r(kp)} → P3R {r(a)} {r(mu)} {r(dl)} {r(xs)} {r(LAMLO)} κ ≤ {r(pclaim)} := by
{half_proof("P3R")}
""")
    rows.append("end SS4\n")

    with open(os.path.join(HERE, "SubsetsumLean", "Stage4ERows.lean"), "w") as f:
        f.write("\n".join(rows))
    parts = {"Stage4Base": (BASE_HEAD, out[:MARK["xi"]]), "Stage4XI": (XI_HEAD, out[MARK["xi"]:MARK["e"]]),
             "Stage4E": (E_HEAD, out[MARK["e"]:])}
    for mod, (head, body) in parts.items():
        with open(os.path.join(HERE, "SubsetsumLean", mod + ".lean"), "w") as f:
            f.write(head + "\n".join(body) + "\nend SS4\n")
    with open(os.path.join(HERE, "SubsetsumLean", "Stage4.lean"), "w") as f:
        f.write(STAGE4_TOP)
    print("wrote Stage4ERows, Stage4Base, Stage4XI, Stage4E, Stage4")


BASE_HEAD = """import SubsetsumLean.Stage4EDefs

/-!
# Stage 4 kernel check, shared part (generated by `gen_stage4.py`; do not edit)

`Hb_half`, `tR_half`, the splitter bound `splitter_S` (Lemma 4.2, for every q), `lamR`, `log2_bounds`, `hs_*`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS4

open SS

lemma Hb_half : Hb (1 / 2) = 1 := by
  have e : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
  have hL : log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold Hb
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, e]
  field_simp
  norm_num

lemma tR_half (α : ℝ) (h : α < 1) : tR α (1 / 2) = 1 / 2 := by
  unfold tR
  have : (1 : ℝ) - α ≠ 0 := by linarith
  field_simp

/-! ## The splitter bound (Lemma 4.2), for every q -/

/-- `S(q) = log2 q + S(floor(q/2)) + S(ceil(q/2))`, `S(1) = 0` (PROOF.md Lemma 4.2). -/
noncomputable def Ssp : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | n + 2 => log ((n + 2 : ℕ) : ℝ) / log 2 + Ssp ((n + 2) / 2) + Ssp ((n + 2) - (n + 2) / 2)
termination_by n => n
decreasing_by all_goals omega

lemma cube_le (q : ℕ) (hq : 2 ≤ q) : q ^ 3 ≤ 8 * ((q / 2) * (q - q / 2)) ^ 2 := by
  rcases Nat.even_or_odd' q with ⟨a, rfl | rfl⟩
  · have h1 : 2 * a / 2 = a := by omega
    have h2 : 2 * a - a = a := by omega
    rw [h1, h2]
    have ha : 1 ≤ a := by omega
    have : a ^ 3 ≤ a ^ 3 * a := Nat.le_mul_of_pos_right _ ha
    calc (2 * a) ^ 3 = 8 * a ^ 3 := by ring
      _ ≤ 8 * (a ^ 3 * a) := by omega
      _ = 8 * (a * a) ^ 2 := by ring
  · have h1 : (2 * a + 1) / 2 = a := by omega
    have h2 : 2 * a + 1 - a = a + 1 := by omega
    rw [h1, h2]
    have ha : 1 ≤ a := by omega
    nlinarith [Nat.mul_le_mul ha ha, Nat.mul_le_mul (Nat.mul_le_mul ha ha) ha]

/-- Lemma 4.2: `S(q) ≤ 3q - 3 - 2 log2 q` for every `q ≥ 1` (the certificate checks `q ≤ 2^14` in floats). -/
theorem splitter_S : ∀ q : ℕ, 1 ≤ q → Ssp q ≤ 3 * q - 3 - 2 * (log q / log 2) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    rcases q with _ | _ | n
    · omega
    · simp [Ssp]
    · rw [Ssp.eq_3]
      have h1 : 1 ≤ (n + 2) / 2 := by omega
      have h2 : 1 ≤ (n + 2) - (n + 2) / 2 := by omega
      have i1 := ih ((n + 2) / 2) (by omega) h1
      have i2 := ih ((n + 2) - (n + 2) / 2) (by omega) h2
      have hsum : (((n + 2) / 2 : ℕ) : ℝ) + (((n + 2) - (n + 2) / 2 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by
        rw [← Nat.cast_add]; congr 1; omega
      have hp1 : (0 : ℝ) < (((n + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast h1
      have hp2 : (0 : ℝ) < (((n + 2) - (n + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast h2
      have hp : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      have cube : ((n + 2 : ℕ) : ℝ) ^ 3 ≤ 8 * ((((n + 2) / 2 : ℕ) : ℝ) * (((n + 2) - (n + 2) / 2 : ℕ) : ℝ)) ^ 2 := by
        exact_mod_cast cube_le (n + 2) (by omega)
      have key := Real.log_le_log (by positivity) cube
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        Real.log_mul hp1.ne' hp2.ne'] at key
      have e8 : log (8 : ℝ) = 3 * log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      rw [e8] at key
      have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
      have hinv : log 2 * (log 2)⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
      have k2 := mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hL.le)
      simp only [div_eq_mul_inv] at i1 i2 ⊢
      push_cast at k2 i1 i2 hsum ⊢
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      nlinarith [k2, hinv, i1, i2, hsum]

/-- lambda of PROOF.md Lemma 4.4, per N_b. -/
noncomputable def lamR (Nb ab bb : ℝ) : ℝ :=
  (log Nb / log 2 + 3 + log (1 + Nb * log 2) / log 2 + 2 * (log ((ab + 1) * (bb + 1)) / log 2)) / Nb

"""

XI_HEAD = """import SubsetsumLean.Stage4Base
import SubsetsumLean.Stage4Cells_s11_t1
import SubsetsumLean.Stage4Cells_s11_t2
import SubsetsumLean.Stage4Cells_s8_t1
import SubsetsumLean.Stage4Cells_s8_t2
import SubsetsumLean.Stage4Cells_p1_t1
import SubsetsumLean.Stage4Cells_p2_t2
import SubsetsumLean.Stage4Cells_p1_v
import SubsetsumLean.Stage4Cells_p2_v

/-!
# Stage 4 kernel check of [XI] (generated by `gen_stage4.py`; do not edit)

`V_*`: the eight contact claims over the whole colour polygon (cell trees); `line_s11`, `line_s8`, `line_plus`:
Lemma 3.4's hypothesis on [0, 1]; `xi_*`: the pairs and xi; `C1_*`, `C2_*`, `C3_plus`: must-fail controls with
explicit colours; `F1_*`: no valid line has a larger xi.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS4

open SS

"""

E_HEAD = """import SubsetsumLean.Stage4Base
import SubsetsumLean.Stage4ERows

/-!
# Stage 4 kernel check of [LAM], [K], [E] and the exponent controls (generated by `gen_stage4.py`)

`lam_*`: lambda at N_b = 8e9 (and lower bounds for K7, K8); `K_*`: [K]; `E_*`: every row of [E]; `headline_*`:
Theorems 4 and 4+ in plain numbers; `Kc*`: the controls K1-K9 of `cert_stage4.py` and K1-K4 of `cert_stage4plus.py`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS4

open SS

"""

STAGE4_TOP = """import SubsetsumLean.Stage4XI
import SubsetsumLean.Stage4E

/-! Stage 4: the kernel check of `derand/stage4/cert_stage4.py` and `cert_stage4plus.py` (see LEAN_SCOPE.md). -/
"""


if __name__ == "__main__":
    main()
