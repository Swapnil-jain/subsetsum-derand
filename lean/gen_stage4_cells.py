"""Generate the cell certificates for Stage 4's [XI] (SubsetsumLean/Stage4Cells*.lean), checked by the kernel.

Pure standard library. The Python certificate (certificates/stage4/cert_stage4.py, cert_stage4plus.py) proves each contact
claim V(tau) <= target by branch and bound with natural interval bounds, thousands of boxes and float logs. That is
not a shape Lean can check cheaply, so this file builds a different certificate for the SAME claims:

  - the colour polygon {k <= m <= 2k, m <= d <= b(m)}, b(m) = k + rho (m - k), k = s/2, is covered by a binary tree of
    boxes (each node clips its d-range to [max(d0, m0), min(d1, b(m1))], then splits m or d at the midpoint);
  - on a leaf box, each of the four entropy terms entering with a plus sign is bounded above by Gibbs' inequality
    h(n, j) <= j (-log2 p) + (n - j)(-log2 (1 - p)) at a rational tangent point p (an affine function of (m, d)), and
    the one minus-sign term h(1 - m, b(m) - m) is bounded below by its chord on [m0, m1] (h is jointly concave);
  - so tau L + (1 - tau) R and (1 - tau) R are below affine functions of (m, d), and those are checked at the four box
    corners against the target, in exact rationals.

Every number written is first checked here by an exact mirror of the Lean checker `SS4.chk` (Stage4Check.lean), so
each `decide +kernel` is known to succeed before Lean runs. Logs use the series of Basic.lean (NT terms).
Run:  python3 gen_stage4_cells.py   (writes Stage4Probs.lean and the Stage4Cells_* modules, listed in stage4_modules.txt)
"""
from fractions import Fraction as F
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
L2C = F(693147180559945309417232121458176568075500134, 10 ** 45)
L2lo, L2hi = L2C - F(1, 10 ** 42), L2C + F(1, 10 ** 42)
NT = 26           # series terms (|t| <= 1/3 gives a tail below 2e-13)
PD = 10 ** 12     # tangent points p are multiples of 1/PD
LD = 10 ** 14     # log and coefficient bounds are multiples of 1/LD, rounded outward
CH = 40           # at most this many leaves per generated module (keeps each build under 3 GB)


def p2(k):
    return F(2) ** k if k >= 0 else F(1) / F(2) ** (-k)


def lsum(t, n):
    s, p = F(0), F(1)
    for i in range(n):
        p *= t
        s += p / (i + 1)
    return s


def lrem(t, n):
    return abs(t) ** (n + 1) / (1 - abs(t))


def kfor(x):
    k = 0
    while x / p2(k) > F(4, 3):
        k += 1
    while x / p2(k) < F(2, 3):
        k -= 1
    return k


LOGC = {}


def log_bounds(x):
    """(k, lower, upper) of the kernel's series bound on ln x (exact; cached)."""
    if x not in LOGC:
        k = kfor(x)
        t = 1 - x / p2(k)
        S, R = lsum(t, NT), lrem(t, NT)
        LOGC[x] = (k, -S - R + min(k * L2lo, k * L2hi), -S + R + max(k * L2lo, k * L2hi))
    return LOGC[x]


def dn(x):
    return F(math.floor(x * LD), LD)


def up(x):
    return F(math.ceil(x * LD), LD)


# ------------------------------------------------------------------ exact mirror of Stage4Check.lean
def logGe(x, k, l):
    if not (x > 0 and abs(1 - x / p2(k)) < 1):
        return False
    t = 1 - x / p2(k)
    return l <= -lsum(t, NT) - lrem(t, NT) + min(k * L2lo, k * L2hi)


def logLe(x, k, u):
    if not (x > 0 and abs(1 - x / p2(k)) < 1):
        return False
    t = 1 - x / p2(k)
    return -lsum(t, NT) + lrem(t, NT) + max(k * L2lo, k * L2hi) <= u


def gib_ok(g):
    p, k1, k2, l1, l2, cp, cq = g
    return (0 < p < 1 and logGe(p, k1, l1) and logGe(1 - p, k2, l2) and cp >= 0 and cq >= 0
            and -l1 <= cp * L2lo and -l2 <= cq * L2lo)


def hlo_ok(c, x, e):
    kc, kx, ky, lc, ux, uy, lo = e
    if x == 0:
        return lo <= 0
    return (0 < x < c and logGe(c, kc, lc) and logLe(x, kx, ux) and logLe(c - x, ky, uy) and lo >= 0
            and lo * L2hi <= c * lc - x * ux - (c - x) * uy)


def bq(P, m):
    return P["k"] + P["rho"] * (m - P["k"])


def Uq(P, g, e0, e1, m0, m1, m, d):
    gA, gB, gC, gD = g
    k, tau, b = P["k"], P["tau"], bq(P, m)
    L = ((d * gA[5] + (F(1, 2) - d) * gA[6]) + ((b - d) * gB[5] + (F(1, 2) - (b - d)) * gB[6])
         - (e0 + (e1 - e0) * (m - m0) / (m1 - m0)))
    R = ((m - k) * gC[5] + (k - (m - k)) * gC[6]) + ((d - m) * gD[5] + ((b - m) - (d - m)) * gD[6])
    return tau * L + (1 - tau) * R, (1 - tau) * R


def leaf_ok(P, m0, m1, d0, d1, g, h0, h1):
    k, rho, T = P["k"], P["rho"], P["T"]
    if not (k <= m0 < m1 <= 2 * k):
        return False
    if not all(gib_ok(x) for x in g):
        return False
    if not (hlo_ok(1 - m0, (rho - 1) * (m0 - k), h0) and hlo_ok(1 - m1, (rho - 1) * (m1 - k), h1)):
        return False
    for m in (m0, m1):
        for d in (d0, d1):
            u, r = Uq(P, g, h0[6], h1[6], m0, m1, m, d)
            if u > T or r > T:
                return False
    return True


def prob_ok(P):
    return P["k"] > 0 and P["rho"] >= 1 and 0 <= P["tau"] <= 1 and bq(P, 2 * P["k"]) <= F(1, 2)


def chk(P, t, m0, m1, d0, d1):
    a, c = max(d0, m0), min(d1, bq(P, m1))
    if t[0] == "none":
        return c < a
    if t[0] == "leaf":
        return leaf_ok(P, m0, m1, a, c, t[1], t[2], t[3])
    if t[0] == "sm":
        mm = (m0 + m1) / 2
        return chk(P, t[1], m0, mm, a, c) and chk(P, t[2], mm, m1, a, c)
    dm = (a + c) / 2
    return chk(P, t[1], m0, m1, a, dm) and chk(P, t[2], m0, m1, dm, c)


# ------------------------------------------------------------------ building the tree
def gib_at(pf):
    """Gibbs data at the tangent point nearest pf (a float in (0, 1))."""
    p = F(min(max(round(pf * PD), 1), PD - 1), PD)
    k1, lo1, _ = log_bounds(p)
    k2, lo2, _ = log_bounds(1 - p)
    l1, l2 = dn(lo1), dn(lo2)
    cp, cq = up(-l1 / L2lo), up(-l2 / L2lo)
    g = (p, k1, k2, l1, l2, max(cp, F(0)), max(cq, F(0)))
    assert gib_ok(g)
    return g


HLC = {}


def hlo_at(P, m):
    c, x = 1 - m, (P["rho"] - 1) * (m - P["k"])
    key = (c, x)
    if key not in HLC:
        if x == 0:
            HLC[key] = (0, 0, 0, F(0), F(0), F(0), F(0))
        else:
            kc, lc, _ = log_bounds(c)
            kx, _, ux = log_bounds(x)
            ky, _, uy = log_bounds(c - x)
            lc, ux, uy = dn(lc), up(ux), up(uy)
            lo = max(F(0), dn((c * lc - x * ux - (c - x) * uy) / L2hi))
            HLC[key] = (kc, kx, ky, lc, ux, uy, lo)
        assert hlo_ok(c, x, HLC[key]), (c, x)
    return HLC[key]


def clampf(x):
    return min(max(x, 1e-9), 1 - 1e-9)


def build(P, m0, m1, d0, d1, depth=0):
    a, c = max(d0, m0), min(d1, bq(P, m1))
    if c < a:
        return ("none",)
    k, rho = float(P["k"]), float(P["rho"])
    mc, dc = float(m0 + m1) / 2, float(a + c) / 2
    bc = k + rho * (mc - k)
    dc = min(max(dc, mc), bc)
    n5 = (rho - 1) * (mc - k)
    g = (gib_at(clampf(2 * dc)), gib_at(clampf(2 * (bc - dc))), gib_at(clampf((mc - k) / k)),
         gib_at(clampf((dc - mc) / n5) if n5 > 0 else 0.5))
    h0, h1 = hlo_at(P, m0), hlo_at(P, m1)
    if leaf_ok(P, m0, m1, a, c, g, h0, h1):
        return ("leaf", g, h0, h1)
    assert depth < 60, "cell tree too deep: the claim may be false"
    if (m1 - m0) * 3 >= (c - a):
        mm = (m0 + m1) / 2
        return ("sm", build(P, m0, mm, a, c, depth + 1), build(P, mm, m1, a, c, depth + 1))
    dm = (a + c) / 2
    return ("sd", build(P, m0, m1, a, dm, depth + 1), build(P, m0, m1, dm, c, depth + 1))


def count(t):
    if t[0] in ("none", "leaf"):
        return (t[0] == "leaf", t[0] == "none", 0)
    a, b = count(t[1]), count(t[2])
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2] + 1)


# ------------------------------------------------------------------ Lean output
def q(x):
    x = F(x)
    return f"(Q ({x.numerator}) {x.denominator})"


def lean_tree(t, out):
    if t[0] == "none":
        out.append("CT.none")
        return
    if t[0] == "leaf":
        gs = " ".join("⟨" + ", ".join([q(g[0]), f"({g[1]})", f"({g[2]})"] + [q(v) for v in g[3:]]) + "⟩"
                      for g in t[1])
        hs = " ".join("⟨" + ", ".join([f"({e[0]})", f"({e[1]})", f"({e[2]})"] + [q(v) for v in e[3:]]) + "⟩"
                      for e in (t[2], t[3]))
        out.append(f"(CT.leaf {gs} {hs})")
        return
    out.append(f"(CT.{t[0]} ")
    lean_tree(t[1], out)
    out.append(" ")
    lean_tree(t[2], out)
    out.append(")")


def problems():
    """The eight contact claims: (name, s, rho, tau, target, doc)."""
    sys.path.insert(0, os.path.join(HERE, "..", "certificates", "stage4"))
    import cert_stage4 as C4
    import cert_stage4plus as C4P
    out = []
    for s, D in C4.XI_DATA.items():
        hlo, hhi = hb_bounds(s)
        tag = "s8" if s == F(1, 8) else "s11"
        out.append((f"{tag}_t1", s, D["rho"], D["t1"], D["t1"] * hlo, "V(t1) <= t1 hsLo"))
        out.append((f"{tag}_t2", s, D["rho"], D["t2"], (1 - D["t2"]) * (1 - s), "V(t2) <= (1-t2)(1-s)"))
    s = C4P.S
    hlo, hhi = hb_bounds(s)
    t1, t2, v = C4P.DATA["t1"], C4P.DATA["t2"], C4P.DATA["v"]
    A1, A2 = t1 * hhi, (1 - t2) * (1 - s)
    lv = A1 + (A2 - A1) / (t2 - t1) * (v - t1)
    out.append(("p1_t1", s, C4P.R1, t1, t1 * hlo, "rho1 at t1"))
    out.append(("p2_t2", s, C4P.R2, t2, A2, "rho2 at t2"))
    out.append(("p1_v", s, C4P.R1, v, lv, "rho1 at v"))
    out.append(("p2_v", s, C4P.R2, v, lv, "rho2 at v"))
    return out


HB_DIG = 10 ** 30


def hb_bounds(s):
    """Rational bounds hsLo <= H(s) <= hsHi (bits), from 60-term log bounds (Lean re-checks with Hb_mem)."""
    s = F(s)
    k1 = kfor(s)
    k2 = kfor(1 - s)
    lo, hi = None, None
    t1, t2 = 1 - s / p2(k1), 1 - (1 - s) / p2(k2)
    S1, R1 = lsum(t1, 60), lrem(t1, 60)
    S2, R2 = lsum(t2, 60), lrem(t2, 60)
    a1, b1 = -S1 - R1 + min(k1 * L2lo, k1 * L2hi), -S1 + R1 + max(k1 * L2lo, k1 * L2hi)
    a2, b2 = -S2 - R2 + min(k2 * L2lo, k2 * L2hi), -S2 + R2 + max(k2 * L2lo, k2 * L2hi)
    lo = F(math.floor((-s * b1 - (1 - s) * b2) / L2hi * HB_DIG), HB_DIG)
    hi = F(math.ceil((-s * a1 - (1 - s) * a2) / L2lo * HB_DIG), HB_DIG)
    return lo, hi


def chunks(t, box, P, path, out):
    """Cut the tree into subtrees of at most CH leaves. Returns the skeleton: ('chunk', i) or (op, left, right)
    together with the boxes the checker passes down (exactly as `chk` computes them)."""
    m0, m1, d0, d1 = box
    if count(t)[0] <= CH or t[0] in ("none", "leaf"):
        out.append((t, box))
        return ("chunk", len(out) - 1, box)
    a, c = max(d0, m0), min(d1, bq(P, m1))
    if t[0] == "sm":
        mm = (m0 + m1) / 2
        return ("sm", box, (mm, a, c), chunks(t[1], (m0, mm, a, c), P, path + "l", out),
                chunks(t[2], (mm, m1, a, c), P, path + "r", out))
    dm = (a + c) / 2
    return ("sd", box, (a, c, dm), chunks(t[1], (m0, m1, a, dm), P, path + "l", out),
            chunks(t[2], (m0, m1, dm, c), P, path + "r", out))


def skel_term(sk, name):
    if sk[0] == "chunk":
        return f"T_{name}_{sk[1]}"
    return f"(CT.{sk[0]} {skel_term(sk[3], name)} {skel_term(sk[4], name)})"


def skel_proof(sk, name, P, ind):
    """A proof term of `chk P (skeleton) box = true` from the chunk theorems."""
    if sk[0] == "chunk":
        return f"c_{name}_{sk[1]}"
    m0, m1, d0, d1 = sk[1]
    pre = " " * ind
    if sk[0] == "sm":
        mm, a, c = sk[2]
        eqs = (f"(by decide +kernel : ({q(m0)} + {q(m1)}) / 2 = {q(mm)}) "
               f"(by decide +kernel : max {q(d0)} {q(m0)} = {q(a)}) "
               f"(by decide +kernel : min {q(d1)} (P_{name}.bq {q(m1)}) = {q(c)})")
        return (f"(chk_sm P_{name} _ _ {q(m0)} {q(m1)} {q(d0)} {q(d1)} {q(mm)} {q(a)} {q(c)} {eqs}\n{pre}  "
                f"{skel_proof(sk[3], name, P, ind + 2)}\n{pre}  {skel_proof(sk[4], name, P, ind + 2)})")
    a, c, dm = sk[2]
    eqs = (f"(by decide +kernel : max {q(d0)} {q(m0)} = {q(a)}) "
           f"(by decide +kernel : min {q(d1)} (P_{name}.bq {q(m1)}) = {q(c)}) "
           f"(by decide +kernel : ({q(a)} + {q(c)}) / 2 = {q(dm)})")
    return (f"(chk_sd P_{name} _ _ {q(m0)} {q(m1)} {q(d0)} {q(d1)} {q(a)} {q(c)} {q(dm)} {eqs}\n{pre}  "
            f"{skel_proof(sk[3], name, P, ind + 2)}\n{pre}  {skel_proof(sk[4], name, P, ind + 2)})")


MODS = []


def main():
    blocks = []
    summary = []
    for name, s, rho, tau, T, doc in problems():
        k = F(s) / 2
        P = dict(k=k, rho=F(rho), tau=F(tau), T=F(T))
        assert prob_ok(P)
        root = (k, 2 * k, k, bq(P, 2 * k))
        t = build(P, *root)
        assert chk(P, t, *root)
        nl, nn, ns = count(t)
        summary.append(f"{name}: {nl} leaves, {nn} empty, {ns} splits")
        blocks.append((name, s, rho, tau, T, doc, P, t, root))
        print(summary[-1], flush=True)
    probs = ["import SubsetsumLean.Stage4Check", "",
             "/-! The eight contact problems of Stage 4's [XI] (generated by `gen_stage4_cells.py`; do not edit). -/",
             "", "namespace SS4", ""]
    for name, s, rho, tau, T, doc, P, t, root in blocks:
        probs += [f"/-- {doc}: s = {s}, rho = {rho}, tau = {tau}, target = {T}. -/",
                  f"def P_{name} : Prob := ⟨{q(P['k'])}, {q(P['rho'])}, {q(P['tau'])}, {q(P['T'])}⟩",
                  f"theorem prob_{name} : P_{name}.ok = true := by decide +kernel", ""]
        parts = []
        sk = chunks(t, root, P, "", parts)
        mods = []
        for i, (sub, box) in enumerate(parts):
            out = []
            lean_tree(sub, out)
            mod = f"Stage4Cells_{name}_{i}"
            mods.append(mod)
            with open(os.path.join(HERE, "SubsetsumLean", mod + ".lean"), "w") as f:
                f.write(f"""import SubsetsumLean.Stage4Probs

/-! Cell certificate `{name}`, part {i} of {len(parts)} (generated by `gen_stage4_cells.py`; do not edit). -/

namespace SS4

def T_{name}_{i} : CT := {"".join(out)}

theorem c_{name}_{i} : chk P_{name} T_{name}_{i} {" ".join(q(x) for x in box)} = true := by
  decide +kernel

end SS4
""")
        MODS.extend(mods)
        root_q = " ".join(q(x) for x in root)
        with open(os.path.join(HERE, "SubsetsumLean", f"Stage4Cells_{name}.lean"), "w") as f:
            f.write("\n".join(f"import SubsetsumLean.{m}" for m in mods) + f"""

/-! Cell certificate `{name}` assembled from its {len(parts)} parts ({doc}; generated by `gen_stage4_cells.py`). -/

namespace SS4

def T_{name} : CT := {skel_term(sk, name)}

theorem cells_{name} : chk P_{name} T_{name} {root_q} = true :=
  {skel_proof(sk, name, P, 2)}

end SS4
""")
        MODS.append(f"Stage4Cells_{name}")
    probs.append("end SS4")
    with open(os.path.join(HERE, "SubsetsumLean", "Stage4Probs.lean"), "w") as f:
        f.write("\n".join(probs) + "\n")
    with open(os.path.join(HERE, "stage4_modules.txt"), "w") as f:
        f.write("\n".join(["Stage4Check", "Stage4Probs"] + MODS) + "\n")
    print("\n".join(summary))


if __name__ == "__main__":
    main()
