"""Stage 5b certificate: rho-FAMILIES at every density of Stage 5's circuit menu, inside Stage 5's deterministic
exponent. proofs/stage5b.md has the statements.

Self-contained, standard library only. Two vendored files, both verbatim and hash-checked against their sources when
those exist:
  stage4_cert_vendored.py = certificates/stage4/cert_stage4.py (the CURRENT one, with the corrected [F1] brackets):
                            interval arithmetic I, h, and the colour-landscape prover Land;
  stage5_cert_vendored.py = certificates/stage5/cert_stage5.py: the per-layer terms and E_row, used UNCHANGED.

Family circuit at density s with members rho_1, ..., rho_J (Stage 4 Lemma 3.4 with P = J; proofs/stage5b.md Lemma 5b.1):
  g(tau) := min{tau h(s), V_rho1(tau), ..., V_rhoJ(tau), (1 - tau)(1 - s)} <= line(tau) := r + (l - r) tau on [0, 1].
Proof data: breakpoints 0 < v_0 < ... < v_J < 1 and pieces P_0 = tau h(s) on [0, v_0], P_i = V_rho_i on
[v_{i-1}, v_i], P_{J+1} = (1 - tau)(1 - s) on [v_J, 1]. Each piece is convex (V_rho is a max of affine functions of tau,
the trivial pieces are affine), so it lies under the line on its interval iff it does at both ends:
  P_0: r >= 0 and v_0 h(s) <= line(v_0);   P_i: V_rho_i(v_{i-1}), V_rho_i(v_i) <= line (Stage 4's prover);
  P_{J+1}: (1 - v_J)(1 - s) <= line(v_J) and l >= 0.
The intervals cover [0, 1], so g <= line everywhere and (l, r) is in K(s). Then (s, l, r) enters E_row exactly as
Stage 5's family point does (rig_terms reads only s, l, r).
GOTCHA (breaking site: the breakpoints). The middle member's interval is narrow (about 0.013 wide around tau = 1/2). A
breakpoint outside the overlap of two adjacent pieces' valid ranges makes the prover FAIL (never pass wrongly), so
moving FAM_DATA's breakpoints is safe but may need the margin in the line raised.

Must-fail controls (each must be REJECTED; any failure fails the certificate):
  [F1]  rigorous lower bounds on g at the breakpoints bound the xi of ANY valid line for this family from above; the
        line with (l, r) lowered by 1e-5 is then refuted.
  [NEED] each member is needed for the certified line: somewhere in its own interval every OTHER piece (the other
        members by an explicit colour, the trivial lines exactly) is rigorously above the line.
  K1 claim - 1e-9 for every row;  K2 mu + 1%;  K7' every family replaced by the single circuit at its s;
  KF(s) each family of R4b-min alone replaced by its single circuit (each is needed);  K9 every (l, r) + 0.01.
  K2, K7', K9 and KF are run on R4b-min, the row of Theorem 5b-F.
Run: nice -n 15 /usr/bin/python3 -B -E cert_stage5b.py      (about 4-6 min, < 100 MB)
"""
import hashlib
import math
import os
import sys
import time
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stage5_cert_vendored as C5  # noqa: E402   (imports stage4_cert_vendored from HERE)
from stage4_cert_vendored import I, h, Land, NB  # noqa: E402

FAILS = []


def check(ok, msg):
    if not ok:
        FAILS.append(msg)
        print("   FAIL:", msg, flush=True)
    return ok


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def vendor_check():
    src = {"stage4_cert_vendored.py": os.path.join(HERE, "..", "stage4", "cert_stage4.py"),
           "stage5_cert_vendored.py": os.path.join(HERE, "..", "stage5", "cert_stage5.py")}
    for mine, theirs in src.items():
        a = sha(os.path.join(HERE, mine))
        if os.path.exists(theirs):
            same = a == sha(theirs)
            print(f"   {mine}: sha256 {a[:16]}..., identical to {os.path.relpath(theirs, HERE)}: {same}")
            check(same, f"vendored {mine} differs from its source")
        else:
            print(f"   {mine}: sha256 {a[:16]}... (source not present; not compared)")


# ------------------------------------------------------------------ family data (from a [float] search)
# Members, the line (r = line(0), l = line(1)) and the J + 1 breakpoints, per menu density. Any data that passes the
# [iv] checks below gives a valid (l, r); the search that produced it plays no role in the proof.
FAM_DATA = {
    F(2, 25): dict(rhos=(F(47, 20), F(5, 2), F(14, 5)), r=F(34085267, 500000000), l=F(240685651, 1000000000),
                   bps=(F(148409, 500000), F(7699, 15625), F(255379, 500000), F(780429, 1000000))),
    F(19, 200): dict(rhos=(F(12, 5), F(51, 20), F(14, 5)), r=F(16691369, 200000000), l=F(13021319, 50000000),
                     bps=(F(60343, 200000), F(495413, 1000000), F(511053, 1000000), F(94997, 125000))),
    F(13, 125): dict(rhos=(F(12, 5), F(51, 20), F(11, 4)), r=F(18349349, 200000000), l=F(67888743, 250000000),
                     bps=(F(151519, 500000), F(247273, 500000), F(254107, 500000), F(149527, 200000))),
    F(111, 1000): dict(rhos=(F(12, 5), F(51, 20), F(11, 4)), r=F(98101829, 1000000000), l=F(279562383, 1000000000),
                       bps=(F(76003, 250000), F(49387, 100000), F(101491, 200000), F(92389, 125000))),
    F(59, 500): dict(rhos=(F(12, 5), F(51, 20), F(11, 4)), r=F(104404771, 1000000000), l=F(287019137, 1000000000),
                     bps=(F(152473, 500000), F(493211, 1000000), F(126677, 250000), F(91357, 125000))),
    F(1, 8): dict(rhos=(F(12, 5), F(51, 20), F(11, 4)), r=F(27659599, 250000000), l=F(293978793, 1000000000),
                  bps=(F(152921, 500000), F(61569, 125000), F(253, 500), F(361417, 500000))),
    F(29, 200): dict(rhos=(F(49, 20), F(13, 5), F(14, 5)), r=F(130510881, 1000000000), l=F(772347, 2500000),
                     bps=(F(310451, 1000000), F(494561, 1000000), F(31717, 62500), F(701931, 1000000))),
    F(11, 100): dict(rhos=(F(12, 5), F(51, 20), F(11, 4)), r=F(97196311, 1000000000), l=F(139226901, 500000000),
                     bps=(F(75969, 250000), F(19759, 40000), F(126893, 250000), F(92539, 125000))),
}


def line_iv(r, l, tau):
    return I.q(r) + (I.q(l) - I.q(r)) * tau


def hf(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def colour_lb(Ld, tau, G=240):
    """A rigorous LOWER bound on V_rho(tau): a float search for a good colour (m, d), then Land.point's interval value
    at that colour. Only the final interval evaluation matters for rigour."""
    k, rho = Ld.kf, Ld.rf
    t = float(tau)

    def fv(m, d):
        b = k + rho * (m - k)
        L = 0.5 * hf(2 * d) + 0.5 * hf(2 * (b - d)) - (1 - m) * hf((b - m) / (1 - m))
        R = k * hf((m - k) / k) + (b - m) * hf((d - m) / (b - m))
        return t * L + (1 - t) * R

    best = (-1e9, None)
    for i in range(1, G):
        m = k + k * i / G
        b = k + rho * (m - k)
        dlo, dhi = max(m, b - 0.5), min(b, 0.5)
        for j in range(1, G):
            d = dlo + (dhi - dlo) * j / G
            if Ld.interior(m, m, d, d):
                v = fv(m, d)
                if v > best[0]:
                    best = (v, (m, d))
    (val, (m, d)), step = best, 1e-4
    while step > 1e-11:
        moved = False
        for dm, dd in ((step, 0), (-step, 0), (0, step), (0, -step), (step, step), (-step, -step), (step, -step),
                       (-step, step)):
            q = (m + dm, d + dd)
            if Ld.interior(q[0], q[0], q[1], q[1]):
                v2 = fv(*q)
                if v2 > val:
                    val, m, d, moved = v2, q[0], q[1], True
        if not moved:
            step /= 2
    return Ld.point(m, d, I.q(tau))[0].lo


def cert_fam(s, D):
    """Lemma 5b.1's statements for one family, then the controls [F1] and [NEED]. Returns (s, l_hi, r_hi, xi_lo)."""
    rhos, r, l, bps = D["rhos"], D["r"], D["l"], D["bps"]
    J = len(rhos)
    assert len(bps) == J + 1 and list(bps) == sorted(set(bps)) and 0 < bps[0] and bps[-1] < 1
    for rho in rhos:   # Stage 4 Lemma 3.5' (window): b <= k1 + rho k0 <= s rho + 2 eps' < 1/2 needs s rho < 1/2
        assert rho > 1 and s * rho < F(1, 2), ("Lemma 3.5' needs rho > 1 and s rho < 1/2", s, rho)
    sI, hs = I.q(s), h(I.q(s))
    Ls = {rho: Land(s, rho) for rho in rhos}
    st = [("r >= 0 and l >= 0", r >= 0 and l >= 0)]
    v0, vJ = I.q(bps[0]), I.q(bps[-1])
    st.append(("v0 h(s) <= line(v0)", (v0 * hs).hi <= line_iv(r, l, v0).lo))
    st.append(("(1 - vJ)(1 - s) <= line(vJ)", ((1 - vJ) * (1 - sI)).hi <= line_iv(r, l, vJ).lo))
    boxes = 0
    for i, rho in enumerate(rhos):
        for v in (bps[i], bps[i + 1]):
            ok, nb, _ = Ls[rho].prove(I.q(v), line_iv(r, l, I.q(v)).lo)
            boxes += nb
            st.append((f"V_{rho}({v}) <= line", ok))
    xi = ((hs - sI) * 0.5 - (I.q(r) + I.q(l)) * 0.5).lo
    good = all(ok for _, ok in st)
    print(f"   s = {str(s):9s} rho = {', '.join(str(x) for x in rhos)} (max s rho = {float(s * max(rhos)):.4f}): "
          f"{len(st)} statements {'all hold' if good else [n for n, ok in st if not ok]} ({boxes} boxes); "
          f"l <= {I.q(l).hi:.10f}, r <= {I.q(r).hi:.10f}, xi >= {xi:.10f}", flush=True)
    check(good, f"family s = {s}")
    # [F1] every valid line passes above g at each breakpoint; g >= min of the pieces' lower bounds there
    gl = []
    for v in bps:
        vI = I.q(v)
        gl.append(min([(vI * hs).lo, ((1 - vI) * (1 - sI)).lo] + [colour_lb(Ls[rho], v) for rho in rhos]))
    xi_up = 9.0
    for i in range(len(bps)):
        for j in range(len(bps)):
            if bps[i] < F(1, 2) < bps[j]:
                c1, c2 = I.q(bps[i]), I.q(bps[j])
                chord = I(gl[i]) + (I(gl[j]) - I(gl[i])) / (c2 - c1) * (I(0.5) - c1)
                xi_up = min(xi_up, ((hs - sI) * 0.5 - chord).hi)
    dl = F(1, 10 ** 5)
    xi_better = ((hs - sI) * 0.5 - (I.q(r - dl) + I.q(l - dl)) * 0.5).lo
    f1 = xi_up >= xi and xi_better > xi_up
    # [NEED] member i: at some tau inside [v_{i-1}, v_i], every other piece is rigorously above the line
    need = []
    for i, rho in enumerate(rhos):
        a, b = bps[i], bps[i + 1]
        hit = None
        for frac in (F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4)):
            tau = a + (b - a) * frac
            tI = I.q(tau)
            ln_hi = line_iv(r, l, tI).hi
            others = [(tI * hs).lo, ((1 - tI) * (1 - sI)).lo] + [colour_lb(Ls[q], tau) for q in rhos if q != rho]
            if min(others) > ln_hi:
                hit = tau
                break
        need.append(hit is not None)
    print(f"      [F1] any valid line for this family has xi <= {xi_up:.10f} (gap {xi_up - xi:.2e}); (l, r) - 1e-5 "
          f"refuted {xi_better > xi_up};  [NEED] each member needed {need}", flush=True)
    check(f1 and all(need), f"family controls s = {s}")
    return (s, I.q(l).hi, I.q(r).hi, xi)


# ------------------------------------------------------------------ rows
R3_ALPHAS = [F(m, 10) for m in range(10)] + [F(23, 25)]
R4_ALPHAS = [F(m, 10) for m in range(10)] + [F(97, 100)]
R4B_ALPHAS = [F(m, 10) for m in range(10)] + [F(m, 100) for m in (93, 95, 96, 97, 98, 99)]
CLAIMS = {"R3": 0.4989524521, "R4": 0.4986354853, "R4b": 0.4986298176, "R4b-min": 0.4986298176}
MU = {"R3": F(1, 5), "R4": F(1, 5), "R4b": F(199, 1000), "R4b-min": F(199, 1000)}
ALPHAS = {"R3": R3_ALPHAS, "R4": R4_ALPHAS, "R4b": R4B_ALPHAS, "R4b-min": R4B_ALPHAS}
# R4b-min, the row of Theorem 5b-F: families only where they are needed. In R4b (all eight families) replacing the
# family at 2/25, 19/200, 1/8 or 29/200 ALONE by its single circuit leaves the bound unchanged, but those are
# substitutes: replacing all four at once costs 2.2e-4 (binding moves off-centre to the pair (13/125, 29/200)).
# A greedy pass (drop in the order 2/25, 19/200, 1/8, 29/200, then the rest; keep a drop only if the bound is unchanged)
# leaves the six densities below; 2/25 and 19/200 keep Stage 5's single circuits. Control KF checks that each of the
# six remaining families is needed.
FAMILY_DENSITIES = (F(13, 125), F(111, 1000), F(59, 500), F(1, 8), F(29, 200), F(11, 100))


def main():
    t0 = time.time()
    print("Stage 5b certificate")
    vendor_check()
    print("[XI] Stage 5's seven single menu circuits, Stage 4's single 11/100 circuit and the Stage 4+ pair, re-proved "
          "with Stage 5's own functions:", flush=True)
    menu = [C5.cert_single(*m, controls=False) for m in C5.MENU_DATA]
    X = C5.XI_DATA[F(11, 100)]
    single11 = C5.cert_single(F(11, 100), X["rho"], X["t1"], X["t2"], controls=False)
    fam11 = C5.cert_family()
    print("[XI-FAM] triple families at every menu density and at 11/100 (Lemma 5b.1; controls [F1], [NEED]):",
          flush=True)
    fams = [cert_fam(s, D) for s, D in FAM_DATA.items()]
    print(f"   circuits done [{time.time() - t0:.0f}s]", flush=True)
    lam = C5.lam_max(NB)
    print(f"[LAM] N_b = {NB}: lambda <= {lam:.4e} for every design")
    singles = {c[0]: c for c in menu + [single11]}
    check(set(singles) == set(FAM_DATA), "every family density has a certified single circuit")
    rmin = [c if c[0] in FAMILY_DENSITIES else singles[c[0]] for c in fams]
    rowcirc = {"R3": menu + [fam11], "R4": fams, "R4b": fams, "R4b-min": rmin}
    res = {}
    for name in ("R3", "R4", "R4b", "R4b-min"):
        circ, mu, al = rowcirc[name], MU[name], ALPHAS[name]
        for a in al:   # Stage 5 Lemma 3.3: a_b = alpha N_b/2 and s a_b integral for every s used
            ab = F(NB) * a / 2
            assert ab.denominator == 1 and all((ab * c[0]).denominator == 1 for c in circ), (name, a)
        E, _ = C5.E_row(name, circ, mu, al, 1, False, lam)
        res[name] = E
        check(E <= CLAIMS[name], f"{name}: {E} > claim {CLAIMS[name]}")
        print(f"      claim E <= {CLAIMS[name]}: {E <= CLAIMS[name]}   [{time.time() - t0:.0f}s]", flush=True)
    print("Must-fail controls on the rows (each must be REJECTED):", flush=True)
    ctl = [(f"sanity: R3 re-run equals Stage 5's certified 0.4989524520 (|diff| < 1e-10)",
            abs(res["R3"] - 0.4989524520) < 1e-10)]
    for name in res:
        ctl.append((f"K1 {name}: claim - 1e-9 rejected", res[name] > CLAIMS[name] - 1e-9))
    mu, al, cl = MU["R4b-min"], ALPHAS["R4b-min"], CLAIMS["R4b-min"]
    e = C5.E_row("K2", rmin, mu * F(101, 100), al, 1, False, lam, verbose=False)[0]
    ctl.append((f"K2 R4b-min with mu raised 1% gives {e:.10f} > claim", e > cl))
    e = C5.E_row("K7'", [singles[c[0]] for c in fams], mu, al, 1, False, lam, verbose=False)[0]
    ctl.append((f"K7' R4b-min with every family replaced by the single circuit at its s gives {e:.10f} > claim", e > cl))
    e = C5.E_row("K9", [(c[0], c[1] + 0.01, c[2] + 0.01, c[3] - 0.01) for c in rmin], mu, al, 1, False, lam,
                 verbose=False)[0]
    ctl.append((f"K9 R4b-min with every circuit's (l, r) raised by 0.01 gives {e:.10f} > claim", e > cl))
    for c in [x for x in rmin if x[0] in FAMILY_DENSITIES]:
        circ = [singles[c[0]] if x[0] == c[0] else x for x in rmin]
        e = C5.E_row("KF", circ, mu, al, 1, False, lam, verbose=False)[0]
        ctl.append((f"KF R4b-min with the family at s = {c[0]} replaced by its single circuit gives {e:.10f} "
                    f"(+{e - res['R4b-min']:.2e}) > claim", e > cl))
        print(f"   ... KF s = {c[0]} done [{time.time() - t0:.0f}s]", flush=True)
    for name, ok in ctl:
        print(f"   {name}: {'pass' if ok else 'FAIL'}", flush=True)
        check(ok, name)
    print(f"STAGE 5b CERTIFICATE", "PASS" if not FAILS else f"FAIL ({len(FAILS)}): {FAILS}",
          f"[{time.time() - t0:.0f}s]")
    return len(FAILS)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
