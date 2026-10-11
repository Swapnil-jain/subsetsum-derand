"""Generate the Stage 5 kernel check except the cell trees (gen_stage5_cells.py): the circuit and row data, the exponent
pieces, the must-fail refutations, and the analysis modules Stage5XI, Stage5Ctl, Stage5E, Stage5, Stage5Axioms.

Pure standard library. Every number comes from derand/stage5/cert_stage5.py (MENU_DATA, ROWS, the controls) or from
Stage 4's Lean data, and every claim is first re-checked here by an exact mirror of the Lean checkers
(Stage5ECheck.lean: `Row.pieceOK`, `Row.refOne`), so each `decide +kernel` is known to succeed before Lean runs.
Run:  python3 gen_stage5.py   (after gen_stage5_cells.py; about 3 min; writes stage5_light_modules.txt)
"""
from fractions import Fraction as F
import contextlib
import io
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "certificates", "stage5"))
import gen_stage4_cells as G  # noqa: E402
import gen_stage4 as G4  # noqa: E402
import gen_stage5_cells as G5C  # noqa: E402
import cert_stage5 as C5  # noqa: E402

L2lo, L2hi = G.L2lo, G.L2hi
q, r, Qc = G4.q, G4.r, G4.Qc
LEAN = os.path.join(HERE, "SubsetsumLean")
HD = 10 ** 15            # H(s) bounds in the light data, rounded outward to multiples of 1/HD
LRD = 10 ** 13           # line values l, r rounded up to multiples of 1/LRD
LAMQ = F(23983, 10 ** 12)  # lambda <= LAMQ for every design at N_b = 8e9 (Lean: lam5)
K1_DELTA = F(2, 10 ** 6)   # K1 is refuted at claim - K1_DELTA (the true sup is within ~1.3e-6 of each claim)
CH_PIECES = 60           # pieces per light module
CH_DESIGNS = 160         # refutation designs per light module


def dnq(x, d):
    return F(math.floor(x * d), d)


def upq(x, d):
    return F(math.ceil(x * d), d)


def hf(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


# ------------------------------------------------------------------ circuits
class Circ:
    def __init__(self, tag, s, rho, t1, t2, family=None):
        self.tag, self.s, self.rho, self.t1, self.t2, self.family = tag, F(s), F(rho), F(t1), F(t2), family
        lo, hi = G.hb_bounds(self.s)
        self.hlo30, self.hhi30 = lo, hi
        self.hsLo, self.hsHi = dnq(lo, HD), upq(hi, HD)
        A1, A2 = self.t1 * hi, (1 - self.t2) * (1 - self.s)
        sig = (A2 - A1) / (self.t2 - self.t1)
        assert sig <= lo and sig >= -(1 - self.s)
        self.A1, self.A2, self.sig = A1, A2, sig
        self.lq, self.rq = A1 + sig * (1 - self.t1), A1 - sig * self.t1
        assert self.lq >= 0 and self.rq >= 0
        self.l, self.r = upq(self.lq, LRD), upq(self.rq, LRD)
        self.xi = dnq((lo - self.s) / 2 - (self.lq + self.rq) / 2, 10 ** 10)

    def tup(self):
        return (self.s, self.hsLo, self.hsHi, self.l, self.r)

    def lean(self):
        return f"⟨{Qc(self.s)}, {Qc(self.hsLo)}, {Qc(self.hsHi)}, {Qc(self.l)}, {Qc(self.r)}⟩"


def make_cname(single, menu, fam, sfam):
    """Lean names of the circuits, by object identity."""
    return {id(c): "C_" + (c.tag if c is not sfam else "s11f") for c in [single] + menu + [fam, sfam]}


def circuits():
    S4 = C5.XI_DATA[F(11, 100)]
    single = Circ("s11", F(11, 100), S4["rho"], S4["t1"], S4["t2"])
    menu = [Circ(G5C.tag_of(s) if s != F(1, 8) else "s8", s, rho, t1, t2) for s, rho, t1, t2 in G5C.menu()]
    fam = Circ("plus", F(11, 100), F(49, 20), F(1531131, 5 * 10 ** 6), F(7403119, 10 ** 7), family=(F(49, 20), F(11, 4)))
    # the single-circuit data with the family's s, as in control K7
    sfam = Circ("s11", F(11, 100), S4["rho"], S4["t1"], S4["t2"])
    return single, menu, fam, sfam


# ------------------------------------------------------------------ exact mirrors of Stage5ECheck.lean
def hbU_ok(x, e):
    k1, k2, l1, l2, hi = e
    return (0 < x < 1 and G.logGe(x, k1, l1) and G.logGe(1 - x, k2, l2) and hi >= 0
            and -x * l1 - (1 - x) * l2 <= hi * L2lo)


def hbL_ok(x, e):
    k1, k2, u1, u2, lo = e
    return (0 < x < 1 and G.logLe(x, k1, u1) and G.logLe(1 - x, k2, u2) and lo >= 0
            and lo * L2hi <= -x * u1 - (1 - x) * u2)


def t5(a, s1, s2, k):
    return (k - a * (s1 + 1 - s2) / 2) / (1 - a)


class Row:
    def __init__(self, name, mu, j, claim, sym, alphas, circs, osv=F(0), lam=LAMQ):
        self.name, self.mu, self.j, self.claim, self.sym = name, F(mu), j, F(claim), sym
        self.alphas, self.circs, self.osv, self.lam = [F(a) for a in alphas], circs, F(osv), F(lam)

    def designs(self):
        out = []
        for a in self.alphas:
            for c1 in self.circs:
                for c2 in self.circs:
                    if self.sym and c1.tup() != c2.tup():
                        continue
                    out.append((a, c1, c2))
        return out


L3Q = None


def terms_ok(R, a, c1, c2, w, B, Jq, HK):
    mu, j = R.mu, R.j
    g = (j - 1) * mu * (1 - HK)
    u = F(1, 2) + mu * (B + a / 2 * (c1.s - c2.hsLo + c1.r + c2.l)) + (1 - mu) * w - g
    v = F(1, 2) + mu * (B + a / 2 * (c2.s - c1.hsLo + c1.l + c2.r)) - (1 - mu) * w + R.osv - g
    p4 = mu * (Jq + R.lam) + mu * (L3Q + 1) / 4 + max(mu, (1 - mu) * (F(1, 2) + abs(w)) - mu)
    p6 = mu * (1 + HK + Jq + R.lam)
    return u <= R.claim and v <= R.claim and p4 <= R.claim and p6 <= R.claim


def piece_ok(R, ka, p):
    kb, ia, i1, i2, w, hk, ta, tb = p
    if not (ia < len(R.alphas) and i1 < len(R.circs) and i2 < len(R.circs)):
        return False
    a, c1, c2 = R.alphas[ia], R.circs[i1], R.circs[i2]
    if R.sym and not (i1 == i2 and w == 0):
        return False
    if not (0 <= a < 1 and R.j >= 1 and R.j * R.mu <= (1 - R.mu) * (F(1, 2) - abs(w))):
        return False
    if not (0 <= ka <= kb <= F(1, 2) and hbU_ok(kb, hk)):
        return False
    HK = hk[4]
    if a == 0:
        return terms_ok(R, a, c1, c2, w, HK / 2 - F(1, 2) + R.lam, F(0), HK)
    if not (hbL_ok(t5(a, c1.s, c2.s, ka), ta) and hbL_ok(t5(a, c1.s, c2.s, kb), tb)):
        return False
    HT = min(ta[4], tb[4])
    return terms_ok(R, a, c1, c2, w, HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1 + R.lam,
                    HK - a / 2 * (c1.hsLo + c2.hsLo) - (1 - a) * HT, HK)


def row_ok(R):
    return (0 < R.mu < 1 and R.lam >= 0 and R.mu <= R.claim and 2 * R.mu <= R.claim
            and R.mu * (2 + R.lam) <= R.claim)


def ref_core(R, kap, HK, d, HT):
    a, c1, c2 = d
    mu, j = R.mu, R.j
    B = HK / 2 - F(1, 2) if a == 0 else HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1
    Jq = F(0) if a == 0 else HK - a / 2 * (c1.hsHi + c2.hsHi) - (1 - a) * HT
    u = F(1, 2) + mu * (B + a / 2 * (c1.s - c2.hsHi + c1.r + c2.l))
    v = F(1, 2) + mu * (B + a / 2 * (c2.s - c1.hsHi + c1.l + c2.r)) + R.osv
    g = (j - 1) * mu * (1 - HK)
    return 0 <= a < 1 and (R.claim < (u + v) / 2 - g or R.claim < max(u, v) - (1 - mu) * (F(1, 2) - j * mu / (1 - mu)) - g
                           or R.claim < mu * (1 + HK + Jq))


def ref_one(R, kap, HK, d, ht):
    a, c1, c2 = d
    t = t5(a, c1.s, c2.s, kap)
    if a != 0 and (t <= 0 or t >= 1):
        return True
    if ht is None:
        return ref_core(R, kap, HK, d, F(1))
    return hbU_ok(t, ht) and ref_core(R, kap, HK, d, ht[4])


# ------------------------------------------------------------------ float evaluation (design choice only)
def fl_val(R, a, c1, c2, ka, kb):
    """A float estimate of the piece's worst term for design (a, c1, c2), with w balancing the two lines."""
    mu, j, lam = float(R.mu), R.j, float(R.lam)
    a_ = float(a)
    HK = hf(float(kb)) + 1e-13
    if a == 0:
        B = HK / 2 - 0.5 + lam
        Jq = 0.0
    else:
        ta, tb = float(t5(a, c1.s, c2.s, ka)), float(t5(a, c1.s, c2.s, kb))
        if not (ta > 1e-9 and tb < 1 - 1e-9):
            return None
        HT = min(hf(ta), hf(tb)) - 1e-13
        B = HK - (1 - a_) * HT / 2 + (1 - a_) / 2 - 1 + lam
        Jq = HK - a_ / 2 * (float(c1.hsLo) + float(c2.hsLo)) - (1 - a_) * HT
    u0 = 0.5 + mu * (B + a_ / 2 * float(c1.s - c2.hsLo + c1.r + c2.l))
    v0 = 0.5 + mu * (B + a_ / 2 * float(c2.s - c1.hsLo + c1.l + c2.r)) + float(R.osv)
    W = 0.5 - j * mu / (1 - mu)
    if W < 0:
        return None
    if R.sym:
        w = 0.0
    else:
        w = max(-W, min(W, (v0 - u0) / (2 * (1 - mu))))
    g = (j - 1) * mu * (1 - HK)
    p3 = max(u0 + (1 - mu) * w, v0 - (1 - mu) * w) - g
    p4 = mu * (Jq + lam) + mu * (float(L3Q) + 1) / 4 + max(mu, (1 - mu) * (0.5 + abs(w)) - mu)
    p6 = mu * (1 + HK + Jq + lam)
    return max(p3, p4, p6), w


def make_piece(R, ka, kb, d):
    """The exact piece (or None) for design d = (ia, i1, i2) on [ka, kb], w chosen by floats then rounded."""
    ia, i1, i2 = d
    a, c1, c2 = R.alphas[ia], R.circs[i1], R.circs[i2]
    fv = fl_val(R, a, c1, c2, ka, kb)
    if fv is None:
        return None
    w = F(0) if R.sym else F(round(fv[1] * 10 ** 9), 10 ** 9)
    hk = G4.hbU(kb)
    if a == 0:
        ta = tb = (0, 0, F(0), F(0), F(0))
    else:
        ta, tb = G4.hbL(t5(a, c1.s, c2.s, ka)), G4.hbL(t5(a, c1.s, c2.s, kb))
    p = (kb, ia, i1, i2, w, hk, ta, tb)
    return p if piece_ok(R, ka, p) else None


def design_idx(R):
    out = []
    for ia, a in enumerate(R.alphas):
        if a == 0:
            out.append((ia, 0, 0))
            continue
        for i1 in range(len(R.circs)):
            for i2 in range(len(R.circs)):
                if R.sym and i1 != i2:
                    continue
                out.append((ia, i1, i2))
    return out


def best_designs(R, ka, kb, D, n=4):
    vals = []
    for d in D:
        a, c1, c2 = R.alphas[d[0]], R.circs[d[1]], R.circs[d[2]]
        fv = fl_val(R, a, c1, c2, ka, kb)
        if fv is not None:
            vals.append((fv[0], d))
    vals.sort(key=lambda x: x[0])
    return [d for v, d in vals[:n] if v <= float(R.claim)]


def pieces(R, lo=F(2, 5)):
    """Pieces of [0, 1/2]: the core-free tail [0, lo], then greedy maximal pieces up to 1/2."""
    D = design_idx(R)
    ia0 = R.alphas.index(F(0))
    out = []
    p = make_piece(R, F(0), lo, (ia0, 0, 0))
    assert p is not None, ("tail fails", R.name)
    out.append(p)
    ka, w = lo, F(1, 10 ** 4)
    while ka < F(1, 2):
        best = None
        w = max(w / 4, F(1, 10 ** 12))
        while True:
            kb = min(ka + w, F(1, 2))
            if kb < F(1, 2):
                kb = F(round(kb * 10 ** 12), 10 ** 12)
            if kb <= ka:
                kb = ka + F(1, 10 ** 12)
            got = None
            for d in best_designs(R, ka, kb, D):
                got = make_piece(R, ka, kb, d)
                if got is not None:
                    break
            if got is None:
                if best is None and w > F(1, 10 ** 12):
                    w /= 4          # the first width tried was too wide: shrink before giving up
                    continue
                break
            best = got
            if kb == F(1, 2):
                break
            w *= 2
        assert best is not None, ("piece stuck", R.name, float(ka))
        out.append(best)
        ka = best[0]
    return out


def chk_mirror(R, ka, kend, ps):
    for p in ps:
        if not piece_ok(R, ka, p):
            return False
        ka = p[0]
    return ka == kend


# ------------------------------------------------------------------ refutations
def fl_lower(R, a, c1, c2, kap):
    """Float version of refCore's best lower bound (max of the three tests), or +inf if the design is invalid."""
    mu, j = float(R.mu), R.j
    a_ = float(a)
    t = float(t5(a, c1.s, c2.s, kap))
    if a != 0 and (t <= 0 or t >= 1):
        return float("inf")
    HK = hf(float(kap))
    HT = hf(t) if a != 0 else HK
    B = HK / 2 - 0.5 if a == 0 else HK - (1 - a_) * HT / 2 + (1 - a_) / 2 - 1
    Jq = 0.0 if a == 0 else HK - a_ / 2 * (float(c1.hsHi) + float(c2.hsHi)) - (1 - a_) * HT
    u = 0.5 + mu * (B + a_ / 2 * float(c1.s - c2.hsHi + c1.r + c2.l))
    v = 0.5 + mu * (B + a_ / 2 * float(c2.s - c1.hsHi + c1.l + c2.r)) + float(R.osv)
    g = (j - 1) * mu * (1 - HK)
    return max((u + v) / 2 - g, max(u, v) - (1 - mu) * (0.5 - j * mu / (1 - mu)) - g, mu * (1 + HK + Jq))


def fl_min(R, kap):
    return min(fl_lower(R, a, c1, c2, kap) for a, c1, c2 in R.designs())


def best_kappa(R, lo=0.40, hi=0.5):
    N = 2000
    vals = [(fl_min(R, F(lo + (hi - lo) * i / N)), lo + (hi - lo) * i / N) for i in range(N + 1)]
    v, k0 = max(vals)
    a_, b_ = k0 - (hi - lo) / N, k0 + (hi - lo) / N
    for _ in range(3):
        M = 200
        vals = [(fl_min(R, F(a_ + (b_ - a_) * i / M)), a_ + (b_ - a_) * i / M) for i in range(M + 1)]
        v, k0 = max(vals)
        st = (b_ - a_) / M
        a_, b_ = k0 - st, k0 + st
    return F(round(k0 * 10 ** 9), 10 ** 9), v


def refutation(R, kap):
    """(hk, hts) with Row.refute R kap hk hts = true, checked exactly."""
    hk = G4.hbL(kap)
    HK = hk[4]
    hts = []
    for d in R.designs():
        if ref_one(R, kap, HK, d, None):
            hts.append(None)
            continue
        a, c1, c2 = d
        e = G4.hbU(t5(a, c1.s, c2.s, kap))
        assert ref_one(R, kap, HK, d, e), ("design not refuted", R.name, float(kap), float(a), float(c1.s), float(c2.s))
        hts.append(e)
    assert 0 < R.mu < 1 and R.j >= 1 and hbL_ok(kap, hk)
    return hk, hts


# ------------------------------------------------------------------ Lean text
def lean_row(R, cname):
    al = ", ".join(Qc(a) for a in R.alphas)
    cs = ", ".join(cname[id(c)] for c in R.circs)
    return (f"⟨{Qc(R.mu)}, {R.j}, {Qc(R.lam)}, {Qc(L3Q)}, {Qc(R.claim)}, {'true' if R.sym else 'false'}, "
            f"{Qc(R.osv)}, [{al}], [{cs}]⟩")


def lean_piece(p):
    kb, ia, i1, i2, w, hk, ta, tb = p
    return (f"⟨{Qc(kb)}, {ia}, {i1}, {i2}, {Qc(w)}, {G4.lean_hbU(hk)}, {G4.lean_hbL(ta)}, {G4.lean_hbL(tb)}⟩")


def write(name, text):
    with open(os.path.join(LEAN, name + ".lean"), "w") as f:
        f.write(text)


def main():
    global L3Q
    k3, _, u3 = G.log_bounds(F(3))
    L3Q = G.up(G.up(u3) / L2lo)
    assert L3Q == F(39624062518029, 25 * 10 ** 12)     # Stage 4's log2_3_le bound
    single, menu, fam, sfam = circuits()
    with contextlib.redirect_stdout(io.StringIO()):
        lam_py = C5.lam_max(C5.NB)
    assert lam_py <= float(LAMQ)
    rows = {
        "R1": Row("R1", C5.ROWS["R1"]["mu"], 1, C5.ROWS["R1"]["claim"], True, C5.ROWS["R1"]["alphas"], [single]),
        "R1b": Row("R1b", C5.ROWS["R1b"]["mu"], 2, C5.ROWS["R1b"]["claim"], True, C5.ROWS["R1b"]["alphas"], [single]),
        "R2": Row("R2", C5.ROWS["R2"]["mu"], 1, C5.ROWS["R2"]["claim"], False, C5.ROWS["R2"]["alphas"], menu),
        "R3": Row("R3", C5.ROWS["R3"]["mu"], 1, C5.ROWS["R3"]["claim"], False, C5.ROWS["R3"]["alphas"], menu + [fam]),
    }
    for R in rows.values():
        R.claim = F(repr(C5.ROWS[R.name]["claim"]))      # the printed decimal, exactly
        assert float(R.claim) == C5.ROWS[R.name]["claim"]
        assert row_ok(R)
    R2, R1, R3 = rows["R2"], rows["R1"], rows["R3"]
    ctl = {
        "K1_R1": Row("K1_R1", R1.mu, 1, R1.claim - K1_DELTA, True, R1.alphas, R1.circs),
        "K1_R1b": Row("K1_R1b", rows["R1b"].mu, 2, rows["R1b"].claim - K1_DELTA, True, rows["R1b"].alphas, R1.circs),
        "K1_R2": Row("K1_R2", R2.mu, 1, R2.claim - K1_DELTA, False, R2.alphas, menu),
        "K1_R3": Row("K1_R3", R3.mu, 1, R3.claim - K1_DELTA, False, R3.alphas, menu + [fam]),
        "K2": Row("K2", R2.mu * F(101, 100), 1, R2.claim, False, R2.alphas, menu),
        "K4": Row("K4", R2.mu, 1, F(1, 2), False, R2.alphas, menu, osv=R2.mu),
        "K5": Row("K5", R2.mu, 1, R2.claim, False, [F(0), F(97, 100)], menu),
        "K5b": Row("K5b", F(1, 5), 1, F(49919788, 10 ** 8), False, [F(0), F(9, 10)], menu),
        "K6": Row("K6", R1.mu, 1, F(1, 2) - R1.mu * F(19, 20) * single.xi, True, R1.alphas, [single]),
        "K6b": Row("K6b", R1.mu, 1, R1.claim, True, [F(0), F(19, 20)], [single]),
        "K7": Row("K7", R3.mu, 1, R3.claim, False, R3.alphas, menu + [sfam]),
    }
    # K6's target is A39's ceiling with our certified xi (xi_true >= xi_lo makes the true ceiling no larger)
    assert single.xi == F(22424519, 5 * 10 ** 9) or single.xi >= F(22424519, 5 * 10 ** 9)
    allc = [single] + menu + [fam, sfam]
    cname = make_cname(single, menu, fam, sfam)
    print("circuits:", ", ".join(f"{c.tag} l {float(c.l):.10f} r {float(c.r):.10f} xi {float(c.xi):.10f}" for c in allc))

    # ---------------- data module
    data = ["import SubsetsumLean.Stage5ECheck", "",
            "/-! Stage 5 data: the circuits and rows of `cert_stage5.py` and its controls (generated by `gen_stage5.py`; do "
            "not edit). -/", "", "namespace SS5", "", "open SS4", ""]
    seen = set()
    for c in allc:
        n = cname[id(c)]
        if n in seen:
            continue
        seen.add(n)
        doc = "Stage 4+ family" if c.family else f"rho = {c.rho}, t1 = {c.t1}, t2 = {c.t2}"
        if c is sfam:
            doc = "control K7: the single 11/100 circuit's (l, r) in place of the family point"
        data.append(f"/-- s = {c.s} ({doc}): hsLo <= H(s) <= hsHi, l >= line(1), r >= line(0). -/")
        data.append(f"def {n} : Circ := {c.lean()}")
    data.append("")
    for name, R in list(rows.items()) + list(ctl.items()):
        data.append(f"def R_{name} : Row := {lean_row(R, cname)}")
    for name in rows:
        data.append(f"theorem rowok_{name} : R_{name}.ok = true := by decide +kernel")
    data += ["", "end SS5", ""]
    write("Stage5Data", "\n".join(data))
    mods = ["Stage5Data"]

    # ---------------- exponent rows
    chunks = {}
    for name, R in rows.items():
        ps = pieces(R)
        assert chk_mirror(R, F(0), F(1, 2), ps)
        ncore = sum(1 for p in ps if R.alphas[p[1]] != 0)
        print(f"{name}: {len(ps)} pieces ({ncore} cored)", flush=True)
        parts, ka = [], F(0)
        for i in range(0, len(ps), CH_PIECES):
            sub = ps[i:i + CH_PIECES]
            parts.append((ka, sub[-1][0], sub))
            ka = sub[-1][0]
        chunks[name] = parts
        for i, (a, b, sub) in enumerate(parts):
            mod = f"Stage5Rows_{name}_{i}"
            mods.append(mod)
            write(mod, f"""import SubsetsumLean.Stage5Data

/-! Stage 5 row {name}, pieces {i * CH_PIECES} to {i * CH_PIECES + len(sub) - 1} (generated by `gen_stage5.py`; do not edit). -/

namespace SS5

open SS4

def PS_{name}_{i} : List EP := [{", ".join(lean_piece(p) for p in sub)}]

theorem ne_{name}_{i} : PS_{name}_{i} ≠ [] := by simp [PS_{name}_{i}]

theorem chk_{name}_{i} : R_{name}.chk {Qc(b)} {Qc(a)} PS_{name}_{i} = true := by decide +kernel

end SS5
""")

    # ---------------- refutations (one alpha per sub-row; several alphas per module)
    refs = {}
    for name, R in ctl.items():
        kap, v = best_kappa(R) if name != "K4" else (F(1, 2), fl_min(R, F(1, 2)))
        print(f"{name}: kappa* = {kap} ({float(kap):.9f}), float min lower bound {v:.10f} vs target "
              f"{float(R.claim):.10f}", flush=True)
        assert v > float(R.claim)
        subs = []
        for ia, a in enumerate(R.alphas):
            Rs = Row(R.name, R.mu, R.j, R.claim, R.sym, [a], R.circs, R.osv, R.lam)
            hk, hts = refutation(Rs, kap)
            subs.append((ia, a, hk, hts))
        refs[name] = (kap, subs)
        groups, cur, n = [], [], 0
        for sb in subs:
            if cur and n + len(sb[3]) > CH_DESIGNS:
                groups.append(cur)
                cur, n = [], 0
            cur.append(sb)
            n += len(sb[3])
        if cur:
            groups.append(cur)
        for gi, grp in enumerate(groups):
            mod = f"Stage5Refs_{name}_{gi}"
            mods.append(mod)
            body = []
            for ia, a, hk, hts in grp:
                hl = ", ".join("none" if e is None else f"some {G4.lean_hbU(e)}" for e in hts)
                body.append(f"""/-- {name}, alpha = {a}: at kappa = {kap} every design fails the target. -/
theorem ref_{name}_{ia} : ({{ R_{name} with alphas := [{Qc(a)}] }} : Row).refute {Qc(kap)} {G4.lean_hbL(hk)} [{hl}] = true := by
  decide +kernel
""")
            write(mod, f"""import SubsetsumLean.Stage5Data

/-! Stage 5 must-fail control {name}, part {gi} (generated by `gen_stage5.py`; do not edit). -/

namespace SS5

open SS4

""" + "\n".join(body) + "\nend SS5\n")
    with open(os.path.join(HERE, "stage5_light_modules.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    print("light modules:", len(mods))
    return single, menu, fam, sfam, rows, ctl, chunks, refs, cname


# ------------------------------------------------------------------ heavy modules (analysis imported)
HEAD = """set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS5

open SS SS4

"""


def witness(name, s, rho, tau, need):
    """A rational colour (m, d) inside the polygon whose rigorous G4 lower bound exceeds `need` (as gen_stage4.py)."""
    k = F(s) / 2
    Ld = C5.C4.Land(F(s), F(rho))
    ok, pt, val = Ld.refute(C5.C4.I.q(F(tau)), float(need))
    assert ok, ("no witness", name)
    for den in (10 ** 12, 10 ** 14, 10 ** 16):
        m, d = F(round(pt[0] * den), den), F(round(pt[1] * den), den)
        b = k + F(rho) * (m - k)
        assert k < m < 2 * k and m < d < b
        terms = [("a", "(1 / 2 : ℝ)", r(d), F(1, 2), d, 1),
                 ("b", "(1 / 2 : ℝ)", f"(bR {r(k)} {r(rho)} {r(m)} - {r(d)})", F(1, 2), b - d, 1),
                 ("c", f"(1 - {r(m)})", f"(bR {r(k)} {r(rho)} {r(m)} - {r(m)})", 1 - m, b - m, 2),
                 ("e", r(k), f"({r(m)} - {r(k)})", k, m - k, 1),
                 ("f", f"(bR {r(k)} {r(rho)} {r(m)} - {r(m)})", f"({r(d)} - {r(m)})", b - m, d - m, 1)]
        bnd, lines = {}, []
        for key, c_r, e_r, c, x, side in terms:
            ep = "(by unfold bR; norm_num)" if "bR" in e_r else "(by norm_num)"
            cp = "(by unfold bR; norm_num)" if "bR" in c_r else "(by norm_num)"
            term, lo, hi = G4.hh_mem(c_r, e_r, c, x, ep)
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
    return txt


def line_exprs(c):
    sig = f"({r(c.A2)} - {r(c.A1)}) / ({r(c.t2)} - {r(c.t1)})"
    L1 = f"{r(c.A1)} + {sig} * (1 - {r(c.t1)})"
    L0 = f"{r(c.A1)} + {sig} * (0 - {r(c.t1)})"
    return sig, L1, L0


def cfield(n, f, v):
    return f"have e_{f} : {n}.{f} = {q(v)} := by decide +kernel"


def write_heavy(single, menu, fam, sfam, rows, ctl, chunks, refs, cname):
    cname = make_cname(single, menu, fam, sfam)
    new = [c for c in menu if c.tag != "s8"]
    allc = [single] + menu + [fam, sfam]
    names = {}
    for c in allc:
        names.setdefault(cname[id(c)], c)
    S4HS = {"s11": "hs_s11", "s8": "hs_s8", "plus": "hs_s11", "s11f": "hs_s11"}
    # ---------------- Stage5Base: H(s) and the circuit data facts, log2 3
    out = ["import SubsetsumLean.Stage4Base", "import SubsetsumLean.Stage5Data", "",
           "/-!\n# Stage 5 kernel check, shared part (generated by `gen_stage5.py`; do not edit)\n\n"
           "`hs_*`: H(s) of the six new menu densities (60-term series); `hb_C_*`: every circuit's `hsLo ≤ H(s) ≤ hsHi`;"
           "\n`log2_3_le5`: `log2 3 ≤ l3`.\n-/", "", HEAD]
    for c in new:
        term, _, _ = G4.hb_mem(r(c.s), c.s, c.hlo30, c.hhi30, 60)
        out.append(f"""/-- `H({c.s})` enclosed. -/
theorem hs_{c.tag} : {r(c.hlo30)} ≤ Hb {r(c.s)} ∧ Hb {r(c.s)} ≤ {r(c.hhi30)} := by
  have h := {term}
  push_cast at h
  exact h
""")
    for n, c in names.items():
        hs = S4HS.get(n[2:], f"hs_{c.tag}")
        out.append(f"""/-- The data of `{n}`: `hsLo ≤ H(s) ≤ hsHi`. -/
theorem hb_{n} : (({n}.hsLo : ℚ) : ℝ) ≤ Hb (({n}.s : ℚ) : ℝ) ∧ Hb (({n}.s : ℚ) : ℝ) ≤ (({n}.hsHi : ℚ) : ℝ) := by
  {cfield(n, "s", c.s)}
  {cfield(n, "hsLo", c.hsLo)}
  {cfield(n, "hsHi", c.hsHi)}
  rw [e_s, e_hsLo, e_hsHi]
  have h := {hs}
  push_cast
  constructor <;> linarith [h.1, h.2]
""")
    out.append("""/-- `log2 3 ≤ 39624062518029/25000000000000` (as Stage 4). -/
theorem log2_3_le5 : log 3 / log 2 ≤ (39624062518029/25000000000000 : ℝ) := by
  have h := (SS.log_mem (3 : ℝ) (3 : ℚ) (549306144334054845697622618461/500000000000000000000000000000 : ℚ) (1098612288668109691395245236923/1000000000000000000000000000000 : ℚ) (2) 50 _ _ (by norm_num) rfl rfl (by decide +kernel))
  have L := log2_bounds
  push_cast at h
  have d := div_le_div₀ (by linarith [h.1, Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]) h.2 (by norm_num) L.1
  norm_num at d ⊢
  linarith
""")
    out.append("end SS5\n")
    write("Stage5Base", "\n".join(out))

    # ---------------- Stage5XI: contacts, lines, xi, and the (l, r) data
    out = ["import SubsetsumLean.Stage5Base", "import SubsetsumLean.Stage4XI"]
    out += [f"import SubsetsumLean.Stage5Cells_{c.tag}_{t}" for c in new for t in ("t1", "t2")]
    out += ["", "/-!\n# Stage 5 kernel check of the menu circuits (generated by `gen_stage5.py`; do not edit)\n\n"
            "`V_*`: the twelve new contact claims over the whole colour polygon (cell trees, Stage 4's method); `line_*`:\n"
            "Lemma 3.4's hypothesis on [0, 1]; `xi_*`: the pairs and xi, and `line(1) ≤ C.l`, `line(0) ≤ C.r` for the row data;\n"
            "`lr_s11`, `lr_s8`, `lr_plus`: the same bounds on Stage 4's own lines (`SS4.line_s11`, `line_s8`, `line_plus`).\n-/",
            "", HEAD]
    for c in new:
        k = c.s / 2
        for tt, tau, T, doc in (("t1", c.t1, c.t1 * c.hlo30, "V(t1) <= t1 hsLo"),
                                ("t2", c.t2, (1 - c.t2) * (1 - c.s), "V(t2) <= (1-t2)(1-s)")):
            nm = f"{c.tag}_{tt}"
            out.append(f"""/-- [XI] {doc} at s = {c.s}: on the whole colour polygon. -/
theorem V_{nm} : ∀ m d : ℝ, Poly4 {r(k)} {r(c.rho)} m d → G4 {r(k)} {r(c.rho)} {r(tau)} m d ≤ {r(T)} := by
  have h := G4_le_of_cells P_{nm} prob_{nm} T_{nm} _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) cells_{nm}
  have e1 : P_{nm}.k = {q(k)} := by decide +kernel
  have e2 : P_{nm}.ρ = {q(c.rho)} := by decide +kernel
  have e3 : P_{nm}.τ = {q(tau)} := by decide +kernel
  have e4 : P_{nm}.T = {q(T)} := by decide +kernel
  rw [e1, e2, e3, e4] at h
  push_cast at h
  exact h
""")
        sig, L1, L0 = line_exprs(c)
        line = f"{r(c.A1)} + {sig} * (τ - {r(c.t1)})"
        n = cname[id(c)]
        out.append(f"""/-- Lemma 3.4's hypothesis at s = {c.s}, rho = {c.rho}: `min{{V, tau h(s), (1 - tau)(1 - s)}} ≤ line` for every
tau, with the line through `(t1, t1 hsHi)` and `(t2, (1 - t2)(1 - s))`. -/
theorem line_{c.tag} : ∀ τ : ℝ, (∀ m d : ℝ, Poly4 {r(k)} {r(c.rho)} m d → G4 {r(k)} {r(c.rho)} τ m d ≤ {line}) ∨
    τ * Hb {r(c.s)} ≤ {line} ∨ (1 - τ) * (1 - {r(c.s)}) ≤ {line} := by
  have hs := hs_{c.tag}
  refine line_single {r(k)} {r(c.rho)} (Hb {r(c.s)}) {r(c.s)} {r(c.t1)} {r(c.t2)} {r(c.A1)} {r(c.A2)} (by norm_num)
    (by linarith [hs.2]) (by norm_num) (by have := hs.1; norm_num at this ⊢; linarith) (by norm_num)
    (fun m d hp => (V_{c.tag}_t1 m d hp).trans (by norm_num)) (fun m d hp => (V_{c.tag}_t2 m d hp).trans (by norm_num))

/-- The pair (l, r) = (line(1), line(0)), xi = (h(s) - s)/2 - (l + r)/2 ≥ {c.xi}, and the row data `{n}` bounds l, r. -/
theorem xi_{c.tag} : {r(c.xi)} ≤ (Hb {r(c.s)} - {r(c.s)}) / 2 - ({L1} + ({L0})) / 2 ∧
    0 ≤ {L0} ∧ 0 ≤ {L1} ∧ {L1} ≤ (({n}.l : ℚ) : ℝ) ∧ {L0} ≤ (({n}.r : ℚ) : ℝ) := by
  {cfield(n, "l", c.l)}
  {cfield(n, "r", c.r)}
  rw [e_l, e_r]
  have hs := hs_{c.tag}.1
  refine ⟨?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  norm_num at hs ⊢
  linarith
""")
    for c, base in ((single, "s11"), (menu[[m.tag for m in menu].index("s8")], "s8"), (fam, "plus")):
        sig, L1, L0 = line_exprs(c)
        n = cname[id(c)]
        out.append(f"""/-- The row data `{n}` bounds Stage 4's line `SS4.line_{base}`: line(1) ≤ l, line(0) ≤ r. -/
theorem lr_{base} : {L1} ≤ (({n}.l : ℚ) : ℝ) ∧ {L0} ≤ (({n}.r : ℚ) : ℝ) := by
  {cfield(n, "l", c.l)}
  {cfield(n, "r", c.r)}
  rw [e_l, e_r]
  constructor <;> norm_num
""")
    out.append("end SS5\n")
    write("Stage5XI", "\n".join(out))

    # ---------------- Stage5Ctl_*: controls C1, C2 for the seven menu circuits (one 1e-4 step past each contact)
    groups = [menu[:4], menu[4:]]
    for gi, grp in enumerate(groups):
        out = ["import SubsetsumLean.Stage5Base", "", f"/-! Stage 5 controls C1, C2 for menu circuits {', '.join(str(c.s) for c in grp)} "
               "(generated by `gen_stage5.py`; do not edit). -/", "", HEAD]
        for c in grp:
            k = c.s / 2
            c1, c2 = c.t1 - C5.CTL_STEP, c.t2 + C5.CTL_STEP
            hs = "hs_s8" if c.tag == "s8" else f"hs_{c.tag}"
            out.append(witness(f"{c.tag}_C1", c.s, c.rho, c1, c1 * c.hhi30))
            out.append(witness(f"{c.tag}_C2", c.s, c.rho, c2, (1 - c2) * (1 - c.s)))
            out.append(f"""/-- Control C1 at s = {c.s}: one step (1e-4) past the left contact, `V(c1) ≤ c1 h(s)` is false. -/
theorem C1_{c.tag} : ¬ ∀ m d : ℝ, Poly4 {r(k)} {r(c.rho)} m d → G4 {r(k)} {r(c.rho)} {r(c1)} m d ≤ {r(c1)} * Hb {r(c.s)} := by
  intro h
  have := h _ _ wp_{c.tag}_C1
  linarith [w_{c.tag}_C1, {hs}.2]

/-- Control C2 at s = {c.s}: one step past the right contact, `V(c2) ≤ (1 - c2)(1 - s)` is false. -/
theorem C2_{c.tag} : ¬ ∀ m d : ℝ, Poly4 {r(k)} {r(c.rho)} m d → G4 {r(k)} {r(c.rho)} {r(c2)} m d ≤ (1 - {r(c2)}) * (1 - {r(c.s)}) := by
  intro h
  have := h _ _ wp_{c.tag}_C2
  norm_num at this
  linarith [w_{c.tag}_C2]
""")
        out.append("end SS5\n")
        write(f"Stage5Ctl_{gi}", "\n".join(out))

    # ---------------- Stage5E: [LAM], the rows, the exponent controls
    out = ["import SubsetsumLean.Stage5Base", "import SubsetsumLean.Stage5EDefs"]
    for name, parts in chunks.items():
        out += [f"import SubsetsumLean.Stage5Rows_{name}_{i}" for i in range(len(parts))]
    ref_mods = sorted(m for m in os.listdir(LEAN) if m.startswith("Stage5Refs_"))
    out += [f"import SubsetsumLean.{m[:-5]}" for m in ref_mods]
    out += ["", "/-!\n# Stage 5 kernel check of [LAM], the exponent rows R1, R1b, R2, R3 and the controls K1-K8 "
            "(generated by `gen_stage5.py`)\n\n"
            "`E_*`: every layer kappa in [0, 1] is served by a menu design whose P3, P4, P6 are at most the claim, and the\n"
            "constant terms are too; `K*`: the must-fail controls of `cert_stage5.py`, each proved false.\n-/", "", HEAD]
    # [LAM]
    nb = F(C5.NB)
    half = nb / 4 + 1
    t1, lo1, hi1 = G4.log_mem(r(nb), nb)
    X = 1 + nb * L2hi
    t2, lo2, hi2 = G4.log_mem(f"(1 + {r(nb)} * {r(L2hi)})", X)
    t3, lo3, hi3 = G4.log_mem(r(half), half)
    val = (hi1 / L2lo + 3 + hi2 / L2lo + 4 * (hi3 / L2lo)) / nb
    assert val <= LAMQ, float(val)
    out.append(f"""/-! ## [LAM] lambda for every design -/

/-- DERIVATION Lemma 3.3: for every core size, `(a_b + 1)(b_b + 1) ≤ (N_b/4 + 1)^2` when `a_b + b_b = N_b/2`, so
lambda ≤ {LAMQ} at N_b = {nb} for every design (the core-free one included). -/
theorem lam5 : ∀ ab bb : ℝ, 0 ≤ ab → 0 ≤ bb → ab + bb = {r(nb / 2)} → lamR {r(nb)} ab bb ≤ {r(LAMQ)} := by
  intro ab bb ha hb hsum
  have hP : (ab + 1) * (bb + 1) ≤ {r(half)} ^ 2 := by nlinarith [sq_nonneg (ab - bb)]
  have hpos : 0 < (ab + 1) * (bb + 1) := by positivity
  have hl : log ((ab + 1) * (bb + 1)) ≤ 2 * log {r(half)} := by
    have := Real.log_le_log hpos hP
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have h1 := {t1}
  have h2 := {t2}
  have h3 := {t3}
  have L := log2_bounds
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hx : (0 : ℝ) < 1 + {r(nb)} * log 2 := by positivity
  push_cast at h1 h2 h3
  have m2 : log (1 + {r(nb)} * log 2) ≤ log (1 + {r(nb)} * {r(L2hi)}) :=
    Real.log_le_log hx (by linarith [L.2])
  have p1 : (0 : ℝ) ≤ log {r(nb)} := Real.log_nonneg (by norm_num)
  have p2 : (0 : ℝ) ≤ log (1 + {r(nb)} * log 2) := Real.log_nonneg (by linarith [L.1])
  have p3 : (0 : ℝ) ≤ log {r(half)} := Real.log_nonneg (by norm_num)
  have d1 := div_le_div₀ (by linarith [h1.1, p1]) h1.2 (by norm_num) L.1
  have d2 := div_le_div₀ (by linarith [h2.1, p2, m2]) (m2.trans h2.2) (by norm_num) L.1
  have d3 : log ((ab + 1) * (bb + 1)) / log 2 ≤ (2 * {r(hi3)}) / {r(L2lo)} :=
    div_le_div₀ (by norm_num) (hl.trans (by linarith [h3.2])) (by norm_num) L.1
  unfold lamR
  rw [div_le_iff₀ (by norm_num)]
  norm_num at d1 d2 d3 ⊢
  linarith
""")
    # integrality and the window
    all_alpha = sorted(set(a for R in rows.values() for a in R.alphas))
    al = ", ".join(Qc(a) for a in all_alpha)
    cs = ", ".join(cname[id(c)] for c in [single] + menu)
    for a in all_alpha:
        ab = nb * a / 2
        assert ab.denominator == 1 and all((ab * c.s).denominator == 1 for c in [single] + menu)
    out.append(f"""/-- Every alpha of every row makes `a_b = alpha N_b/2` and `s a_b` integral for every circuit (Lemma 3.3). -/
theorem ab_integral : ∀ a ∈ [{al}], ((8000000000 : ℚ) * a / 2).den = 1 ∧
    ∀ c ∈ [{cs}], ((8000000000 : ℚ) * a / 2 * c.s).den = 1 := by decide +kernel

/-- Lemma 3.5''s window `s rho < 1/2` for all seven menu circuits and both family rho values. -/
theorem window : ∀ p ∈ [{", ".join(f"({Qc(c.s)}, {Qc(c.rho)})" for c in menu)}, ({Qc(fam.s)}, {Qc(F(49, 20))}), ({Qc(fam.s)}, {Qc(F(11, 4))})],
    p.1 * p.2 < 1 / 2 := by decide +kernel
""")
    # circuit lists
    def circ_facts(nm, R, side):
        lst = [cname[id(c)] for c in R.circs]
        alts = " | ".join("rfl" for _ in lst)
        if side == "lo":
            st = f"∀ c ∈ R_{nm}.circs, ((c.hsLo : ℚ) : ℝ) ≤ Hb ((c.s : ℚ) : ℝ)"
            ex = ", ".join(f"hb_{x}.1" for x in lst)
        else:
            st = f"∀ c ∈ R_{nm}.circs, Hb ((c.s : ℚ) : ℝ) ≤ ((c.hsHi : ℚ) : ℝ)"
            ex = ", ".join(f"hb_{x}.2" for x in lst)
        return f"""theorem hs{side}_{nm} : {st} := by
  intro c hc
  have e : R_{nm}.circs = [{", ".join(lst)}] := rfl
  rw [e] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with {alts}
  exacts [{ex}]
"""
    out.append("/-! ## The exponent rows -/\n")
    for nm, R in rows.items():
        out.append(circ_facts(nm, R, "lo"))
        parts = chunks[nm]
        lines = [f"""/-- Row {nm}: pieces of [0, 1/2]. -/
theorem half_{nm} : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 2 → Covered R_{nm} κ := by
  intro κ h0 h1
  have hl3 : log 3 / log 2 ≤ ((R_{nm}.l3 : ℚ) : ℝ) := by
    have e : R_{nm}.l3 = (39624062518029/25000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; exact log2_3_le5
  have e0 : ((Q 0 1 : ℚ) : ℝ) = 0 := by norm_num [Q]
  have e1 : ((Q 1 2 : ℚ) : ℝ) = 1 / 2 := by norm_num [Q]"""]
        for i, (a, b, sub) in enumerate(parts):
            lines.append(f"  have c{i} := chk_sound R_{nm} hslo_{nm} hl3 rowok_{nm} {Qc(b)} PS_{nm}_{i} {Qc(a)} chk_{nm}_{i} ne_{nm}_{i}")
        n = len(parts)
        prev = "(by rw [e0]; exact h0)"
        for i in range(n - 1):
            b = parts[i][1]
            lines.append(f"  rcases le_total κ (({Qc(b)} : ℚ) : ℝ) with hc{i} | hc{i}")
            lines.append(f"  · exact c{i} κ {prev} hc{i}")
            prev = f"hc{i}"
        lines.append(f"  exact c{n - 1} κ {prev} (by rw [e1]; exact h1)")
        out.append("\n".join(lines) + "\n")
        out.append(f"""/-- [E] row {nm} (claim {R.claim} = {float(R.claim):.10f}): P1 = mu, P5 = Pscan = 2 mu, Kenum = mu (2 + lambda) are
at most the claim, and every layer kappa in [0, 1] has a menu design with P3, P4, P6 at most the claim. -/
theorem E_{nm} : ((R_{nm}.μ : ℚ) : ℝ) ≤ R_{nm}.claim ∧ 2 * ((R_{nm}.μ : ℚ) : ℝ) ≤ R_{nm}.claim ∧
    ((R_{nm}.μ : ℚ) : ℝ) * (2 + R_{nm}.lam) ≤ R_{nm}.claim ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → Covered R_{nm} κ := by
  have h := rowok_{nm}
  simp only [Row.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, c1⟩, c2⟩, c3⟩ := h
  refine ⟨by exact_mod_cast c1, by exact_mod_cast c2, by exact_mod_cast c3, ?_⟩
  exact row_covered R_{nm} (by decide +kernel) (by decide +kernel) half_{nm}
""")
    # controls
    out.append("/-! ## The exponent controls: each is refuted (proved false) -/\n")
    out.append("""/-- The rows a control is compared with: same menu and parameters except the stated change. -/
theorem same_ctl : R_K1_R1.alphas = R_R1.alphas ∧ R_K1_R1.circs = R_R1.circs ∧ R_K1_R1.μ = R_R1.μ ∧
    R_K1_R1b.alphas = R_R1b.alphas ∧ R_K1_R1b.circs = R_R1b.circs ∧ R_K1_R1b.μ = R_R1b.μ ∧ R_K1_R1b.j = R_R1b.j ∧
    R_K1_R2.alphas = R_R2.alphas ∧ R_K1_R2.circs = R_R2.circs ∧ R_K1_R2.μ = R_R2.μ ∧
    R_K1_R3.alphas = R_R3.alphas ∧ R_K1_R3.circs = R_R3.circs ∧ R_K1_R3.μ = R_R3.μ ∧
    R_K2.alphas = R_R2.alphas ∧ R_K2.circs = R_R2.circs ∧ R_K2.μ = R_R2.μ * (101 / 100) ∧ R_K2.claim = R_R2.claim ∧
    R_K4.alphas = R_R2.alphas ∧ R_K4.circs = R_R2.circs ∧ R_K4.μ = R_R2.μ ∧ R_K4.osv = R_R2.μ ∧
    R_K5.circs = R_R2.circs ∧ R_K5.μ = R_R2.μ ∧ R_K5.claim = R_R2.claim ∧ R_K5b.circs = R_R2.circs ∧
    R_K6.alphas = R_R1.alphas ∧ R_K6.circs = R_R1.circs ∧ R_K6.μ = R_R1.μ ∧
    R_K6b.circs = R_R1.circs ∧ R_K6b.μ = R_R1.μ ∧ R_K6b.claim = R_R1.claim ∧
    R_K7.alphas = R_R3.alphas ∧ R_K7.μ = R_R3.μ ∧ R_K7.claim = R_R3.claim := by decide +kernel
""")
    docs = {
        "K1_R1": f"R1's claim minus {K1_DELTA} fails", "K1_R1b": f"R1b's claim minus {K1_DELTA} fails",
        "K1_R2": f"R2's claim minus {K1_DELTA} fails", "K1_R3": f"R3's claim minus {K1_DELTA} fails",
        "K2": "R2 with mu raised 1% fails R2's claim",
        "K4": "one-sided dedupe (the v-list not deduped: v-line + mu) gives no saving: E > 1/2",
        "K5": "A39's own design set {0, 97/100} at R2's point fails R2's claim",
        "K5b": "A39's printed D1 point (alpha 9/10, mu 1/5, designs {0, 9/10}) fails A39's 0.49919788",
        "K6": "R1 does not reach A39's ceiling 1/2 - mu (19/20) xi (xi = our certified lower bound, so the true ceiling is no larger)",
        "K6b": "R1 with one fixed alpha 19/20 (and core-free elsewhere) fails R1's claim",
        "K7": "R3 with the family point replaced by the single 11/100 circuit's (l, r) fails R3's claim",
    }
    for nm, R in ctl.items():
        out.append(circ_facts(nm, R, "hi"))
        kap, subs = refs[nm]
        al = ", ".join(Qc(a) for a in R.alphas)
        alts = " | ".join("rfl" for _ in R.alphas)
        ex = ", ".join(f"⟨_, _, ref_{nm}_{ia}⟩" for ia, *_ in subs)
        out.append(f"""/-- {nm}: {docs[nm]} (target {R.claim} = {float(R.claim):.10f}); at kappa = {kap} no design of the
menu meets it, for any w and any lambda ≥ 0. -/
theorem {nm} : ∀ lam : ℝ, 0 ≤ lam → ¬ ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → CoveredL R_{nm} lam κ := by
  intro lam hlam h
  refine refute_alphas R_{nm} hshi_{nm} {Qc(kap)} ?_ lam hlam (h _ (by norm_num [Q]) (by norm_num [Q]))
  intro a ha
  have e : R_{nm}.alphas = [{al}] := by decide +kernel
  rw [e] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with {alts}
  exacts [{ex}]
""")
    out.append(f"""/-- Control K3: no cores anywhere (the dedupe alone): at kappa = 1/2 every core-free design has P3 ≥ 1/2, for any
lambda ≥ 0, w and circuits. -/
theorem K3 : ∀ lam : ℝ, 0 ≤ lam → ∀ (c1 c2 : Circ) (w : ℝ), 1 / 2 ≤ P3v R_R2.μ lam R_R2.j R_R2.osv ((0 : ℚ) : ℝ) c1.s c1.l c1.r
    c2.s c2.l c2.r w (Hb (1 / 2)) (Hb (t5R ((0 : ℚ) : ℝ) c1.s c2.s (1 / 2))) (Hb c1.s) (Hb c2.s) := by
  intro lam hlam c1 c2 w
  have e1 : R_R2.μ = (201/1000 : ℚ) := by decide +kernel
  have e2 : R_R2.osv = (0 : ℚ) := by decide +kernel
  rw [Rat.cast_zero, t5R_zero, Hb_half]
  exact P3v_half_ge _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [e1]; norm_num) hlam (by rw [e2]; norm_num)

/-- Control K8: R1b's two blocks per side no longer fit at mu = 201/1000: `j mu ≤ (1 - mu)(1/2 - |w|)` fails for every w. -/
theorem K8 : ∀ w : ℝ, ¬ ((2 : ℝ) * (201 / 1000) ≤ (1 - 201 / 1000) * (1 / 2 - |w|)) := by
  intro w h
  have := abs_nonneg w
  nlinarith
""")
    out.append("end SS5\n")
    write("Stage5E", "\n".join(out))
    write("Stage5", """import SubsetsumLean.Stage5XI
import SubsetsumLean.Stage5Ctl_0
import SubsetsumLean.Stage5Ctl_1
import SubsetsumLean.Stage5E

/-! Stage 5: the kernel check of `derand/stage5/cert_stage5.py` (see LEAN_SCOPE.md). -/
""")
    # axioms audit
    thms = []
    for c in new:
        thms += [f"hs_{c.tag}", f"V_{c.tag}_t1", f"V_{c.tag}_t2", f"line_{c.tag}", f"xi_{c.tag}"]
    thms += [f"hb_{n}" for n in names] + ["lr_s11", "lr_s8", "lr_plus", "log2_3_le5"]
    for c in menu:
        thms += [f"C1_{c.tag}", f"C2_{c.tag}"]
    thms += ["lam5", "ab_integral", "window"] + [f"E_{n}" for n in rows] + list(ctl) + ["K3", "K8", "same_ctl"]
    thms += ["chk_sound", "row_covered", "refute_sound", "refute_alphas"]
    write("Stage5Axioms", "import SubsetsumLean.Stage5\n\n/-! The axioms of every Stage 5 theorem (expect propext, Classical.choice, Quot.sound only). -/\n\n"
          + "\n".join(f"#print axioms SS5.{t}" for t in thms) + "\n")
    print("heavy modules written;", len(thms), "theorems in the axioms audit")


if __name__ == "__main__":
    cache = os.environ.get("GEN5_CACHE")       # development only: reuse the light-module results from a pickle
    if cache and os.path.exists(cache):
        import pickle
        args = pickle.load(open(cache, "rb"))
        k3, _, u3 = G.log_bounds(F(3))
        L3Q = G.up(G.up(u3) / L2lo)
    else:
        args = main()
        if cache:
            import pickle
            pickle.dump(args, open(cache, "wb"))
    write_heavy(*args)
