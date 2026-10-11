"""Generate SubsetsumLean/ExplicitAnchors.lean and SubsetsumLean/ExplicitN0.lean, the kernel check of
cert_explicit_b16.py (proofs/stage2b-explicit.md Sec. 12) and cert_explicit_b17.py (proofs/stage2b-explicit.md Sec. 13).

Pure standard library. Both certificates are run first (each must exit 0); only their inputs are read from them:
the rounded-up anchors, the points x0 of Lemma V, and each row's N0 and window half-width e. Lean recomputes every
other number from these (ExplicitN0Defs.lean). For the real-valued anchor theorems, every log2 and entropy
enclosure written into the Lean file is first checked here with the exact formula Lean's kernel evaluates
(logOK / lgOK / hbOK), and the linear combination that linarith must find is evaluated here exactly against the
anchor, so a bound Lean would reject is never emitted.
Run:  python3 gen_explicit_n0.py
"""
from collections import defaultdict
from fractions import Fraction as F
import contextlib
import io
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
CERT_DIR = os.path.join(HERE, "..", "certificates")

NTERMS = 60
DIG = 34
L2lo = F(693147180559945309417232121458176568075500134, 10 ** 45) - F(1, 10 ** 42)
L2hi = F(693147180559945309417232121458176568075500134, 10 ** 45) + F(1, 10 ** 42)


# ---------------------------------------------------------------- Lean's log machinery, replicated exactly
def lsum(t, n):
    s, p = F(0), F(1)
    for i in range(n):
        p *= t
        s += p / (i + 1)
    return s


def log_series(x, k, n):
    """Lean's logOK enclosure of ln x: -S -/+ R + k ln 2 (k ln 2 by the L2lo/L2hi bounds)."""
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


def lg_cert(x):
    """(k, lo, hi) with Lean's lgOK x k NTERMS lo hi true; then lo <= log2 x <= hi."""
    assert x > 0
    k = best_k(x)
    a1, b1 = log_series(x, k, NTERMS)
    lo = down(a1 / (L2hi if a1 >= 0 else L2lo))
    hi = up(b1 / (L2lo if b1 >= 0 else L2hi))
    clo = lo * (L2hi if lo >= 0 else L2lo)
    chi = hi * (L2lo if hi >= 0 else L2hi)
    assert clo <= a1 and b1 <= chi, "lgOK would fail"
    return k, lo, hi


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


# ---------------------------------------------------------------- printing
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


def load(name):
    path = os.path.join(CERT_DIR, name)
    ns = {"__name__": "cert", "__file__": path}
    rc = 0
    with contextlib.redirect_stdout(io.StringIO()):
        try:
            exec(compile(open(path).read(), path, "exec"), ns)
        except SystemExit as e:
            rc = e.code
    assert rc == 0, name + " must pass"
    return ns


# ---------------------------------------------------------------- Lemma V's tangent bound, as a linear form
def tan_lin(tau, a, b, m0, t0, vm, vt):
    """tanBound (ExplicitN0Defs.lean) = C + sum_x L[x] lg x + sum_y H[y] Hb y, exactly."""
    C = F(0)
    L, H = defaultdict(F), defaultdict(F)

    def lg(x, c):
        if c == 0:
            return
        assert x > 0
        L[x] += c

    def hB(u, v, c):
        lg(u, c * u)
        lg(v, -c * v)
        lg(u - v, -c * (u - v))

    H[b] += tau
    H[4 * a] -= tau / 2
    H[2 * (1 - b - 2 * a)] -= tau / 2
    C += (1 - tau) * (b - F(1, 2) + 2 * a)
    hB(1 - b, m0, tau)
    hB(2 * m0, t0, tau)
    C -= tau * 4 * m0
    hB(a, m0 - a, 1 - tau)
    hB(m0, t0 - m0, 1 - tau)
    cm, ct = vm - m0, vt - t0
    k = tau * cm
    lg(1 - b - m0, k); lg(m0, -k); lg(2 * m0, 2 * k); lg(2 * m0 - t0, -2 * k); C -= 4 * k
    k = (1 - tau) * cm
    lg(2 * a - m0, k); lg(m0 - a, -k); lg(m0, k); lg(2 * m0 - t0, -k); lg(2 * m0 - t0, -k); lg(t0 - m0, k)
    k = tau * ct
    lg(2 * m0 - t0, k); lg(t0, -k)
    k = (1 - tau) * ct
    lg(2 * m0 - t0, k); lg(t0 - m0, -k)
    return C, {x: c for x, c in L.items() if c != 0}, {y: c for y, c in H.items() if c != 0}


def upper(C, L, H, lgb, hbb):
    return C + sum(c * (lgb[x][2] if c > 0 else lgb[x][1]) for x, c in L.items()) \
        + sum(c * (hbb[y][7] if c > 0 else hbb[y][6]) for y, c in H.items())


UNFOLD = "tanBound, E1q, fL, fR, hB, gLm, gLt, gRm, gRt"


def bound_lines(L, H, lgb, hbb, tag):
    lines, names = [], []
    for i, x in enumerate(sorted(L)):
        k, lo, hi = lgb[x]
        lines.append(f"  obtain ⟨{tag}g{i}l, {tag}g{i}h⟩ := lg_mem {R(x)} {Q(x)} {Q(lo)} {Q(hi)} ({k}) {NTERMS} "
                     f"(by norm_num) (by decide +kernel)\n")
        names += [f"{tag}g{i}l", f"{tag}g{i}h"]
    for i, y in enumerate(sorted(H)):
        k1, k2, l1, u1, l2, u2, lo, hi = hbb[y]
        lines.append(f"  obtain ⟨{tag}h{i}l, {tag}h{i}h⟩ := Hb_mem {R(y)} {Q(y)} ({k1}) ({k2}) {NTERMS} {Q(l1)} {Q(u1)} "
                     f"{Q(l2)} {Q(u2)} {Q(lo)} {Q(hi)}\n    (by norm_num) (by decide +kernel)\n")
        names += [f"{tag}h{i}l", f"{tag}h{i}h"]
    return "".join(lines), names


def certs_for(L, H, lgb, hbb):
    for x in L:
        if x not in lgb:
            lgb[x] = lg_cert(x)
    for y in H:
        if y not in hbb:
            hbb[y] = hb_cert(y)


def main():
    b16 = load("cert_explicit_b16.py")
    b17 = load("cert_explicit_b17.py")
    A_YL, B_YL = b17["A_YL"], b17["B_YL"]
    U_yl, _, x0_yl = b17["anchors"](A_YL, B_YL)
    tags = {"YL": dict(a=A_YL, b=B_YL, U=U_yl, x0=x0_yl)}
    for t in ("D4", "q2664"):
        d = b17["QDES"][t]
        tags[t] = dict(a=d["a"], b=d["b"], U=d["U"], x0=d["x0"], q=d["q"], xi=d["xi"], dL=d["dL"], dR=d["dR"])
    rows = b17["ROWS"]

    # ------------------------------------------------------------ ExplicitAnchors.lean
    lgb, hbb = {}, {}
    taus = ((F(0), "0", 0), (F(1, 2), "h", 1), (F(1), "1", 2))
    data, thms = [], []
    for tg, d in tags.items():
        a, b = d["a"], d["b"]
        for i, nm in enumerate(("0", "h", "1")):
            data.append(f"def U_{tg}_{nm} : ℚ := {fr(d['U'][i])}\n")
        verts = ((a, a), (a, 2 * a), (2 * a, 2 * a), (2 * a, 4 * a))
        for tau, nm, i in taus:
            m0, t0 = d["x0"][tau]
            lins = [tan_lin(tau, a, b, m0, t0, vm, vt) for vm, vt in verts]
            Lall, Hall = {}, {}
            for _, L, H in lins:
                Lall.update(L)
                Hall.update(H)
            certs_for(Lall, Hall, lgb, hbb)
            for C, L, H in lins:
                assert upper(C, L, H, lgb, hbb) <= d["U"][i], (tg, nm)
            bl, names = bound_lines(Lall, Hall, lgb, hbb, "")
            stmt = " ∧\n    ".join(f"tanBound {R(tau)} {R(a)} {R(b)} {R(m0)} {R(t0)} {R(vm)} {R(vt)} ≤ ((U_{tg}_{nm} : ℚ) : ℝ)"
                                   for vm, vt in verts)
            thms.append(f"""/-- Lemma V's bound for V({ {'0': '0', 'h': '1/2', '1': '1'}[nm] }) at {tg}'s (a, b), at all four vertices of K (x0 = ({fr(m0)}, {fr(t0)})). -/
theorem anchor_{tg}_{nm} :
    {stmt} := by
{bl}  norm_num at {' '.join(names)}
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [{UNFOLD}, U_{tg}_{nm}]
    norm_num
    linarith
""")
    # K9: the tau = 1/2 anchor at D4 is not below the value of V's expression at a feasible point of K
    d = tags["D4"]
    a, b = d["a"], d["b"]
    p1, p2 = F(3, 2) * a, F(9, 4) * a
    C, L, H = tan_lin(F(1, 2), a, b, p1, p2, p1, p2)
    certs_for(L, H, lgb, hbb)
    assert upper(C, L, H, lgb, hbb) <= d["U"][1]
    bl, names = bound_lines(L, H, lgb, hbb, "")
    thms.append(f"""/-- [K9] must fail: the tau = 1/2 anchor at D4 below tau E1(1/4) + (1 - tau)(b - 1/2 + 2a) + f_tau at the
feasible point (3a/2, 9a/4) of K, which is at most V(1/2). (At v = x0 the tangent bound is that value.) -/
theorem anchor_K9 : ¬ ((U_D4_h : ℚ) : ℝ) < tanBound (1/2 : ℝ) {R(a)} {R(b)} {R(p1)} {R(p2)} {R(p1)} {R(p2)} := by
{bl}  norm_num at {' '.join(names)}
  rw [not_lt]
  simp only [{UNFOLD}, U_D4_h]
  norm_num
  linarith
""")
    # Ye-Li's parameter conditions, both dominances and Lemma E6's entropy hypothesis, at D4 and q = 2664
    for tg in ("D4", "q2664"):
        d = tags[tg]
        a, b = d["a"], d["b"]
        for y in (b, 4 * a, 2 * (1 - b - 2 * a), 2 * a / (1 - b)):
            if y not in hbb:
                hbb[y] = hb_cert(y)
        hb, h4, hm, hd = hbb[b], hbb[4 * a], hbb[2 * (1 - b - 2 * a)], hbb[2 * a / (1 - b)]
        m1 = down(hb[6] - h4[7] / 2 - hm[7] / 2 - 4 * a, 6)
        m2 = down((1 - b) * hd[6] - 8 * a, 6)
        assert m1 > 0 and m2 > 0 and hb[7] <= F(1, 10)
        bl1, n1 = bound_lines({}, {b: 1, 4 * a: 1, 2 * (1 - b - 2 * a): 1}, lgb, hbb, "")
        bl2, n2 = bound_lines({}, {2 * a / (1 - b): 1}, lgb, hbb, "")
        bl3, n3 = bound_lines({}, {b: 1}, lgb, hbb, "")
        thms.append(f"""/-- {tg}: Ye-Li's first dominance inequality, E1(1/4) > 4a, with margin {fr(m1)}. -/
theorem dom1_{tg} : 4 * {R(a)} + {R(m1)} < E1q {R(a)} {R(b)} := by
{bl1}  norm_num at {' '.join(n1)}
  simp only [E1q]
  norm_num
  linarith

/-- {tg}: Ye-Li's second dominance inequality, h(1-b, 2a) = (1-b) H(2a/(1-b)) > 8a, with margin {fr(m2)}. -/
theorem dom2_{tg} : 8 * {R(a)} + {R(m2)} < (1 - {R(b)}) * Hb (2 * {R(a)} / (1 - {R(b)})) := by
{bl2}  norm_num at {' '.join(n2)} ⊢
  linarith

/-- {tg}: Lemma E6's entropy hypothesis H(b) <= 1/10. -/
theorem hb_{tg} : Hb {R(b)} ≤ 1 / 10 := by
{bl3}  norm_num at {' '.join(n3)} ⊢
  linarith
""")
    anchors = f'''import SubsetsumLean.ExplicitN0Defs

/-!
# Lemma V's anchors, kernel-checked (generated by `gen_explicit_n0.py`; do not edit)

For Ye-Li's (a, b), D4 (a = 1/2635, 1-b = 1/110) and q = 2664 (a = 1/2664, 1-b = 1/111), and tau = 0, 1/2, 1:
the concavity bound `tanBound` of `cert_explicit_b17.py` (tau E1(1/4) + (1-tau)(b - 1/2 + 2a) + f_tau(x0) +
grad f_tau(x0) . (v - x0)) is at most the certificate's anchor U (rounded up to 10^-18), at each of the four
vertices v of K, with the real log and the real binary entropy. Lemma V (paper: f_tau is concave on K, and a linear
function on a polygon peaks at a vertex) then gives V(tau) <= U. `anchor_K9` is the must-fail control K9.
`dom1_*`, `dom2_*`, `hb_*`: Ye-Li's two dominance inequalities and Lemma E6's H(b) <= 1/10 at D4 and q = 2664
(at Ye-Li's own (a, b) they are `explicit_dom1`, `explicit_dom2`, `explicit_Hb`).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Real

namespace SS
namespace N0

/-- The certified anchors (upper bounds on V(0), V(1/2), V(1)), rounded up to the grid 10^-18. -/
{"".join(data)}
{chr(10).join(thms)}
end N0
end SS
'''
    with open(os.path.join(HERE, "SubsetsumLean", "ExplicitAnchors.lean"), "w") as fh:
        fh.write(anchors)

    # ------------------------------------------------------------ ExplicitN0.lean
    def tag_lit(tg):
        d = tags[tg]
        return f"⟨{Q(d['a'])}, {d['q']}, U_{tg}_0, U_{tg}_h, U_{tg}_1⟩"

    TABLE = b17["TABLE"]
    row_defs, row_thms = [], []
    for name, (Es, ns_) in TABLE.items():
        tg, rest = name.split("-", 1)
        pos = rest.startswith("POS")
        lad = rest.endswith("ladder")
        r = rows[name]
        q = tags[tg]["q"]
        j = int(math.log2(r["N0"] // q))
        assert q * 2 ** j == r["N0"]
        ident = name.replace("-", "_")
        row_defs.append(f"/-- Sec. 13 table row {name}: N0 = {q} * 2^{j}, e' = {fr(r['e'])}. -/\n"
                        f"def row_{ident} : Row := qRow tag{tg} ({q} * 2 ^ {j}) {Q(r['e'])} {str(pos).lower()} {str(lad).lower()}\n")
        row_thms.append(f"""/-- Sec. 13 table row {name}: every check of `q_variant` holds, E <= {Es}, n0 <= {ns_}, and every S2 cost
term (real log2 3) is at most E. -/
theorem row_{ident}_ok : row_{ident}.ok = true ∧ row_{ident}.E ≤ {Q(F(Es))} ∧ row_{ident}.n0 ≤ {Q(F(ns_))} ∧
    ∀ t ∈ s2TermsG row_{ident}.pi row_{ident}.xi row_{ident}.em row_{ident}.gam, t ≤ (row_{ident}.E : ℝ) :=
  Row.s2_real _ _ _ (by decide +kernel)
""")
    # [A'] values
    best = b17["best_e"](10 ** 26, A_YL, "E3")
    eA = best[1]
    n0E4, n0B16 = b17["n0_E4"], b17["n0_B16"]
    assert n0E4 <= F(584, 100) * 10 ** 35 and n0B16 <= F(120, 100) * 10 ** 32
    # K7's grid of window half-widths (best_e's grid)
    grid = [F(m, 10 ** ex) for ex in range(1, 40) for m in (1, 2, 3, 5, 7)]
    gridlit = ", ".join(fr(e) for e in grid)
    K7N0 = rows["D4-POS"]["N0"]
    K7j = int(math.log2(K7N0 // 115940))
    assert 115940 * 2 ** K7j == K7N0
    n16 = b16["n0"]
    assert n16 <= F(121, 100) * 10 ** 56 and b16["d1"] == 3

    n0file = f'''import SubsetsumLean.ExplicitAnchors
import SubsetsumLean.Explicit

/-!
# Kernel check of `cert_explicit_b16.py` and `cert_explicit_b17.py` (generated by `gen_explicit_n0.py`; do not edit)

PROOF Sec. 12 (B16, at Certificate [A]'s design `dA`) and Sec. 13 (B17 at N0 = q = 10^26, the small-q rows, the
POS union and the ladder). Every number is recomputed by `ExplicitN0Defs.lean` from the inputs; `decide +kernel`
evaluates it. The anchors of the small-q rows are those of `ExplicitAnchors.lean`, whose real-valued bounds are
kernel-checked there. Controls: B16's D1, D2 and B17's K1, K2, K4 to K9 (K3 and K9: see LEAN_SCOPE.md), each
proved false.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open Real

namespace SS
namespace N0

/-! ## Sec. 12 (lead B16) at Certificate [A]'s design -/

/-- The three-piece structure at design [A]: Ye-Li's anchors (table + 1e-20), eps_V of `dA`, S2's pair. -/
def stB16 : St := mkSt V0u Vhu V1u dA.epsV dLp dRp
/-- log2 C <= S N0 + 2 d1 + 6 + (k^2 + 2)/2 + 2 bitlen(N0) + 4 (rebalancing, padding, storage). -/
def log2CB16 : ℚ := stB16.S * dA.Nq + 2 * stB16.d1 + 6 + ((dA.k : ℚ) * dA.k + 2) / 2 + 2 * lgUp dA.N + 4
def n0B16 : ℚ := max (2 * (4 * dA.Nq + 1) / (1 - dA.gain)) (2 * (log2CB16 + 1) / dA.gain)

/-- [B16] dyadic thresholds within a quarter of the slope gaps, no excess at the endpoints, all six gaps
delta_(t,j) > 0, N0 min delta >= 1, d1 = 3, S <= 0.4967 (so log2(8 D_inf) <= S N0 + 2 d1 + 6), and
n0 = max(2 (c_b N0 + 1)/(1-g), 2 (log2 C + 1)/g) <= 1.21e56. -/
theorem explicit_B16 : stB16.okS = true ∧ 1 ≤ dA.Nq * stB16.dmin ∧ stB16.d1 = 3 ∧ stB16.S ≤ 4967 / 10000 ∧
    0 < dA.gain ∧ n0B16 ≤ 121 / 100 * 10 ^ 56 := by decide +kernel

/-- [D1] must fail: S <= 0.49. -/
theorem B16_D1 : ¬ stB16.S ≤ 49 / 100 := by decide +kernel

/-- [D2] must fail: thresholds at the slopes themselves (x1 = s2, x2 = s3) leave some gap delta_(t,j) <= 0. -/
theorem B16_D2 : ¬ (pairsOf stB16.U0 stB16.Uh stB16.U1 stB16.t1 stB16.t2 stB16.s1 stB16.s2 stB16.s3 stB16.s2 stB16.s3).all
    (fun p => decide (0 < p.d)) = true := by decide +kernel

/-! ## Sec. 13.1 (Lemma 3.1'), numeric parts -/

/-- prod over the internal nodes of the floor/ceil halving tree of the leaf counts m_v. -/
def Tprod : ℕ → ℕ → ℕ
  | 0, _ => 1
  | f + 1, m => if m ≤ 1 then 1 else m * Tprod f (m / 2) * Tprod f (m - m / 2)

/-- Lemma 3.1'(b) for D <= 400, as the integer inequality (D prod m_v)^4 <= 2^(9(D-1)). -/
theorem splitter_family : (List.range 400).all
    (fun i => decide (((i + 1) * Tprod 20 (i + 1)) ^ 4 ≤ 2 ^ (9 * i))) = true := by decide +kernel

/-- [K4] must fail: the family bound with 2 in place of 9/4, at D = 3. -/
theorem K4 : ¬ (3 * Tprod 20 3 ≤ 2 ^ (2 * 2)) := by decide +kernel

/-- [K1] must fail: Lemma 3.1 at N0 = q = 10^26 needs N0 = k(k+2), and no natural k has it. -/
theorem K1 : ∀ k : ℕ, k * (k + 2) ≠ 10 ^ 26 := by
  intro k hk
  have e : (k + 1) * (k + 1) = 10 ^ 26 + 1 := by nlinarith
  rcases Nat.lt_or_ge k (10 ^ 13) with h | h
  · have : (k + 1) * (k + 1) ≤ 10 ^ 13 * 10 ^ 13 := Nat.mul_le_mul h h
    omega
  · have : (10 ^ 13 + 1) * (10 ^ 13 + 1) ≤ (k + 1) * (k + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- [K2] must fail: q = 10^26 divides N0 = q/2. -/
theorem K2 : (10 ^ 26 / 2) % 10 ^ 26 ≠ 0 := by decide +kernel

/-! ## Sec. 13.4 (small q): the hull pairs, xi'', and the match with Ye-Li's table -/

def tagD4 : Tag := {tag_lit("D4")}
def tagq2664 : Tag := {tag_lit("q2664")}

/-- At Ye-Li's (a, b), each certified anchor is >= the table's truncation and within 2e-17 of it. -/
theorem yl_match : V0u - 1 / 10 ^ 20 ≤ U_YL_0 ∧ U_YL_0 ≤ V0u - 1 / 10 ^ 20 + 2 / 10 ^ 17 ∧
    Vhu - 1 / 10 ^ 20 ≤ U_YL_h ∧ U_YL_h ≤ Vhu - 1 / 10 ^ 20 + 2 / 10 ^ 17 ∧
    V1u - 1 / 10 ^ 20 ≤ U_YL_1 ∧ U_YL_1 ≤ V1u - 1 / 10 ^ 20 + 2 / 10 ^ 17 := by decide +kernel

/-- D4: q = lcm(4, 2635, 110) = 115940, Ye-Li's parameter conditions, 1 - b <= 1/100, the pair
(dL'', dR'') = ({fr(tags['D4']['dL'])}, {fr(tags['D4']['dR'])}) and xi'' = {fr(tags['D4']['xi'])} >= 2e-5. -/
theorem hull_D4 : Nat.lcm 4 (Nat.lcm 2635 110) = 115940 ∧ (hull U_D4_0 U_D4_h U_D4_1).dL = {Q(tags['D4']['dL'])} ∧
    (hull U_D4_0 U_D4_h U_D4_1).dR = {Q(tags['D4']['dR'])} ∧ (hull U_D4_0 U_D4_h U_D4_1).xi = {Q(tags['D4']['xi'])} ∧ 2 / 10 ^ 5 ≤ (hull U_D4_0 U_D4_h U_D4_1).xi ∧
    (0 : ℚ) < 1 / 2635 ∧ (1 : ℚ) / 2635 < 1 / 4 ∧ 4 * (1 / 2635 : ℚ) ≤ 1 / 110 ∧ (1 / 110 : ℚ) < 1 / 2 + 2 / 2635 ∧
    10 * (1 / 2635 : ℚ) < 1 / 110 ∧ (1 / 110 : ℚ) ≤ 1 / 100 := by decide +kernel

/-- q = 2664: q = lcm(4, 2664, 111) = 2664, the parameter conditions and xi'' = {fr(tags['q2664']['xi'])} >= 2e-5. -/
theorem hull_q2664 : Nat.lcm 4 (Nat.lcm 2664 111) = 2664 ∧ (hull U_q2664_0 U_q2664_h U_q2664_1).dL = {Q(tags['q2664']['dL'])} ∧
    (hull U_q2664_0 U_q2664_h U_q2664_1).dR = {Q(tags['q2664']['dR'])} ∧ (hull U_q2664_0 U_q2664_h U_q2664_1).xi = {Q(tags['q2664']['xi'])} ∧ 2 / 10 ^ 5 ≤ (hull U_q2664_0 U_q2664_h U_q2664_1).xi ∧
    (0 : ℚ) < 1 / 2664 ∧ (1 : ℚ) / 2664 < 1 / 4 ∧ 4 * (1 / 2664 : ℚ) ≤ 1 / 111 ∧ (1 / 111 : ℚ) < 1 / 2 + 2 / 2664 ∧
    10 * (1 / 2664 : ℚ) < 1 / 111 ∧ (1 / 111 : ℚ) ≤ 1 / 100 := by decide +kernel

/-- [K5] must fail: S2's pair (dL', dR') is admissible for the D4 anchors (the secant check, eps_V = 1e-12). -/
theorem K5 : ¬ (mkSt U_D4_0 U_D4_h U_D4_1 (1 / 10 ^ 12) dLp dRp).okSec = true := by decide +kernel

/-- [K6] must fail: xi'' >= 2.004e-5 at D4. -/
theorem K6 : ¬ 2004 / 10 ^ 8 ≤ (hull U_D4_0 U_D4_h U_D4_1).xi := by decide +kernel

/-! ## Sec. 13.3: B17 at Ye-Li's (a, b), N0 = q = 10^26, E3 hole fixing (Certificate [A']) -/

def NA : ℕ := 10 ^ 26
def eA : ℚ := {Q(eA)}
def epsJA : ℚ × ℕ := (epsVOf NA eA aYL true).getD (1, 0)
def stA : St := mkSt V0u Vhu V1u epsJA.1 dLp dRp
def epsLA : ℚ := epsJA.1 + (lgUp NA + 9 / 4) / NA
/-- S2 Certificate 7.2[B]'s exponent: the largest cost term at pi = 0.2499, xi' = 2e-5, eps = 1e-9. -/
def EB : ℚ := lmax (s2TermsQ (2499 / 10000) (2 / 10 ^ 5) (1 / 10 ^ 9) (2 / 3 * (2 / 10 ^ 5)))
def constA : ℚ := ((NA : ℚ) + 1) / 2 + storageBits NA
def n0A_E4 : ℚ := n0Of NA (1 / 2 - EB) (stA.LD * NA + constA) 0
def n0A_B16 : ℚ := n0Of NA (1 / 2 - EB) (stA.S * NA + 2 * stA.d1 + 6 + constA) 0

/-- [A'] q | N0 and 4 | N0, J <= N0/8, Lemma E6's numeric hypotheses, the structure, the dyadic thresholds and
all delta_(t,j) > 0, the secant with S2's pair, N0 Delta >= 1, N0 min delta >= 1, eps_L, eps_R <= 1e-9 (so S2
Certificate 7.2 applies: `stage2_B`), L_D = 4855, S <= 0.4967, d1 = 3, E <= 0.4999983345, and n0 <= 5.84e35 with
E4's constant, n0 <= 1.20e32 with B16's. -/
theorem explicit_Aprime : NA % 10 ^ 26 = 0 ∧ NA % 4 = 0 ∧ (epsVOf NA eA aYL true).isSome = true ∧
    8 * epsJA.2 ≤ NA ∧ e6ok NA epsJA.2 stA.U0 = true ∧ stA.okS = true ∧ stA.okSec = true ∧
    1 ≤ (NA : ℚ) * stA.Delta ∧ 1 ≤ (NA : ℚ) * stA.dmin ∧ epsLA ≤ 1 / 10 ^ 9 ∧ epsJA.1 ≤ 1 / 10 ^ 9 ∧
    stA.LD = 4855 ∧ stA.S ≤ 4967 / 10000 ∧ stA.d1 = 3 ∧ EB ≤ 4999983345 / 10 ^ 10 ∧
    n0A_E4 ≤ 584 / 100 * 10 ^ 35 ∧ n0A_B16 ≤ 120 / 100 * 10 ^ 32 := by decide +kernel

/-- [A'] every S2 cost term at [B] (real log2 3, gamma = 2 xi'/3) is at most EB, the exponent used for the gain. -/
theorem explicit_Aprime_s2 : ∀ t ∈ s2TermsG (2499 / 10000 : ℚ) (2 / 10 ^ 5 : ℚ) (1 / 10 ^ 9 : ℚ)
    (2 / 3 * (2 / 10 ^ 5) : ℚ), t ≤ (EB : ℝ) := s2G_le _ _ _ _ _ (by decide +kernel)

/-! ## Sec. 13 table: the small-q rows -/

{"".join(row_defs)}
{chr(10).join(row_thms)}
/-- The ladder gains a factor >= 100 in n0 over the POS row at D4. -/
theorem ladder_gain_D4 : row_D4_POS_ladder.n0 * 100 ≤ row_D4_POS.n0 := by decide +kernel

/-- [K7] must fail: E3 hole fixing at the D4 POS design's N0 = 115940 * 2^{K7j}: for every e' in the
certificate's grid, E3 is unusable (no J, J > N0/8, no S2 point) or gives no gain. -/
theorem K7 : ([{gridlit}] : List ℚ).all (fun e =>
    match epsVOf (115940 * 2 ^ {K7j}) e (1 / 2635) true with
    | none => true
    | some (ev, J) => decide (115940 * 2 ^ {K7j} < 8 * J) ||
        match s2General (hull U_D4_0 U_D4_h U_D4_1).xi (ev + (lgUp (115940 * 2 ^ {K7j}) + 9 / 4) / (115940 * 2 ^ {K7j} : ℕ)) with
        | none => true
        | some s => decide (1 / 2 - s.E ≤ 0)) = true := by decide +kernel

/-- [K8] must fail: the single-scale constant at the D4 POS design is not <= 0.1 N0 (its S is above 1/10). -/
theorem K8 : ¬ (mkSt U_D4_0 U_D4_h U_D4_1 row_D4_POS.epsV (hull U_D4_0 U_D4_h U_D4_1).dL
    (hull U_D4_0 U_D4_h U_D4_1).dR).S ≤ 1 / 10 := by decide +kernel

end N0
end SS
'''
    with open(os.path.join(HERE, "SubsetsumLean", "ExplicitN0.lean"), "w") as fh:
        fh.write(n0file)
    print("wrote ExplicitAnchors.lean (%d log, %d entropy enclosures) and ExplicitN0.lean (%d rows)"
          % (len(lgb), len(hbb), len(row_defs)))


if __name__ == "__main__":
    main()
