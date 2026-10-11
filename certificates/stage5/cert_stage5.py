"""Stage 5 certificate: the deterministic exponent of Record 3's route with A22's outer-sum dedupe (lead A39), alone and
combined with the kappa-adaptive core menu (A38) and with the Stage 4+ two-circuit family. PROOF.md is DERIVATION.md here.

Rows (all deterministic, D1 = Stage 4's residue estimator, so P6 is included):
  R1   A39 alone: Stage 4's own round design (one circuit, s = 11/100, symmetric cores, x' = x + sigma, equal outer
       halves), the core fraction alpha chosen PER LAYER from a finite menu (the core-free design alpha = 0 included).
  R1b  R1 with two dedupe blocks per outer side (DERIVATION Sec. 5; ours, not in A39).
  R2   A39 + A38: per layer a menu pair (s1, s2) of certified circuits, alpha from the menu, rational outer split w.
  R3   R2 + the Stage 4+ family point (s = 11/100, rho = 49/20 and 11/4) added to the menu.
Every term is DERIVATION Sec. 4's: per layer kappa and design,
  u-line = 1/2 + mu[h(k) - (1-a) h(t)/2 + (1-a)/2 - 1 + lam + (a/2)(s1 - h(s2) + r1 + l2)] + (1 - mu) w
  v-line = 1/2 + mu[h(k) - (1-a) h(t)/2 + (1-a)/2 - 1 + lam + (a/2)(s2 - h(s1) + l1 + r2)] - (1 - mu) w
  P3 = max(u-line, v-line) - (j - 1) mu (1 - h(k))          (j = dedupe blocks per side; d >= 1 - h(k))
  P4 = mu(J + lam) + mu (log2 3 + 1)/4 + max(mu, (1 - mu)(1/2 + |w|) - mu)
  P6 = mu(1 + h(k) + J + lam),  J = h(k) - (a/2)(h(s1) + h(s2)) - (1 - a) h(t)
  with t = (1 + D)/2, D = (2k - a(s1 + 1 - s2))/(1 - a) - 1 (a = 0: t = k); plus P1 = (2j+1)-block sums mu, P5 = 2 mu,
  Kenum = mu(2 + lam), Pscan <= 2 mu. Side condition (1 - mu)(1/2 - |w|) >= j mu.
GOTCHA (breaking site: the kappa range). Without the few/many dichotomy the layer range is NOT cut by delta: an instance
with deficiency d could own layers down to h(kappa) = 1 - d (a case the proof cannot exclude; random instances are in
fact all served by the central layer), and d is anything in [0, 1]. So the sup runs over ALL kappa, as a conservative bound,
and symmetric cores pay the curvature (1 - a)(1 - h(t))/2 off-centre. That is why R1 saves only ~ mu xi/2 (binding
at alpha = 1/2 near kappa = 0.47), not A39's ceiling mu alpha xi; control K6 rejects the ceiling for R1. And A39's
design set {0, alpha} leaves a gap just outside the last feasible menu pair (control K5): intermediate alphas are needed.
Arithmetic: stage4_cert_vendored.py (a verbatim copy of certificates/stage4/cert_stage4.py): outward-rounded intervals and the colour-landscape prover Land.
Run: nice -n 15 /usr/bin/python3 -B -E cert_stage5.py        (about 3-6 min under load, < 100 MB)
"""
import hashlib
import math
import os
import sys
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stage4_cert_vendored as C4  # noqa: E402
from stage4_cert_vendored import I, h, h_iv, log2, ln, Land, XI_DATA, NB  # noqa: E402

FAILS = []


def check(ok, msg):
    if not ok:
        FAILS.append(msg)
        print("   FAIL:", msg)
    return ok


# ------------------------------------------------------------------ circuits: (s, l_hi, r_hi, xi_lo)
# A38's menu contact data (lane A run 14, a36_menu.py `cert`), re-proved here with Stage 4's prover.
MENU_DATA = [
    (F(2, 25), F(57, 20), F(3212279, 10 ** 7), F(1562577, 2 * 10 ** 6)),
    (F(19, 200), F(14, 5), F(3207417, 10 ** 7), F(7599759, 10 ** 7)),
    (F(13, 125), F(11, 4), F(3194763, 10 ** 7), F(7476349, 10 ** 7)),
    (F(111, 1000), F(11, 4), F(200169, 625000), F(1847779, 2500000)),
    (F(59, 500), F(27, 10), F(398447, 1250000), F(1824717, 2500000)),
    (F(1, 8), F(27, 10), F(798773, 2500000), F(7218613, 10 ** 7)),
    (F(29, 200), F(53, 20), F(3193069, 10 ** 7), F(3495099, 5 * 10 ** 6)),
]
CTL_STEP = F(1, 10 ** 4)   # must-fail: the contact moved this far outward must be refuted by an explicit colour


def line_lr(s, t1, t2):
    hs, sI = h(I.q(s)), I.q(s)
    T1, T2 = I.q(t1), I.q(t2)
    A1, A2 = T1 * hs, (1 - T2) * (1 - sI)
    slope = (A2 - A1) / (T2 - T1)
    r_ = A1 - slope * T1
    l_ = r_ + slope
    ok = slope.hi <= hs.lo and slope.lo >= -(1 - sI).lo and l_.lo >= 0 and r_.lo >= 0
    xi = ((hs - sI) * 0.5 - (r_ + slope * 0.5)).lo
    return ok, l_.hi, r_.hi, xi, A1, A2, slope


def cert_single(s, rho, t1, t2, controls=True):
    Ld = Land(s, rho)
    ok, l_, r_, xi, A1, A2, slope = line_lr(s, t1, t2)
    ok1 = Ld.prove(I.q(t1), A1.lo)[0]
    ok2 = Ld.prove(I.q(t2), A2.lo)[0]
    ctl = ""
    if controls:
        hs, sI = h(I.q(s)), I.q(s)
        c1, c2 = I.q(t1 - CTL_STEP), I.q(t2 + CTL_STEP)
        f1 = Ld.refute(c1, (c1 * hs).lo)[0]
        f2 = Ld.refute(c2, ((1 - c2) * (1 - sI)).lo)[0]
        ctl = f"; controls C1/C2 (contacts moved {float(CTL_STEP):.0e} outward) refuted: {f1} {f2}"
        check(f1 and f2, f"menu control at s = {s}")
    good = ok and ok1 and ok2
    print(f"   s = {str(s):9s} rho = {str(rho):6s}: V(t1) <= t1 h(s) {ok1}, V(t2) <= (1-t2)(1-s) {ok2}, slope/l/r ok {ok};"
          f" l <= {l_:.10f}, r <= {r_:.10f}, xi >= {xi:.10f}{ctl}", flush=True)
    check(good, f"menu point s = {s}")
    return (s, l_, r_, xi)


def cert_family():
    """Stage 4+ (PROOF.md Sec. 8): the same five statements as cert_stage4plus.py, re-proved here."""
    S, R1, R2 = F(11, 100), F(49, 20), F(11, 4)
    t1, t2, v = F(1531131, 5 * 10 ** 6), F(7403119, 10 ** 7), F(5037, 10 ** 4)
    L1, L2 = Land(S, R1), Land(S, R2)
    ok, l_, r_, xi, A1, A2, slope = line_lr(S, t1, t2)
    lv = A1 + slope * (I.q(v) - I.q(t1))
    oks = [L1.prove(I.q(t1), A1.lo)[0], L2.prove(I.q(t2), A2.lo)[0], L1.prove(I.q(v), lv.lo)[0],
           L2.prove(I.q(v), lv.lo)[0], ok]
    g1 = L1.refute(I.q(t2), A2.lo)[0]
    g2 = L2.refute(I.q(t1), A1.lo)[0]
    print(f"   family s = 11/100, rho = 49/20 + 11/4: five statements {oks}; l <= {l_:.10f}, r <= {r_:.10f}, "
          f"xi >= {xi:.10f}; control C3 (each member alone fails at the other's contact): {g1} {g2}", flush=True)
    check(all(oks) and g1 and g2, "Stage 4+ family")
    return (S, l_, r_, xi)


# ------------------------------------------------------------------ [LAM]
def lam_max(Nb):
    """Stage 4 Lemma 4.4's lambda for ANY core size: (a_b + 1)(b_b + 1) <= (N_b/4 + 1)^2 since a_b + b_b = N_b/2.
    The asymmetric (A38) and core-free designs have the same per-piece loss (DERIVATION Lemma 3.3)."""
    NbI = I.q(Nb)
    tot = log2(NbI) + 3 + log2(1 + NbI * ln(I(2.0))) + 4 * log2(NbI * 0.25 + 1)
    return (tot / NbI).hi


# ------------------------------------------------------------------ the per-layer terms
L3F = (math.log2(3) + 1) / 4
L3I = (log2(I(3.0)) + 1) * 0.25


def hf(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def float_terms(k, a, c1, c2, mu, lam, j, sym):
    s1, l1, r1 = float(c1[0]), c1[1], c1[2]
    s2, l2, r2 = float(c2[0]), c2[1], c2[2]
    a = float(a)
    D = (2 * k - a * (s1 + 1 - s2)) / (1 - a) - 1 if a > 0 else 2 * k - 1
    if abs(D) >= 0.998:
        return None
    t = (1 + D) / 2
    hk, ht = hf(k), hf(t)
    base = hk - (1 - a) * ht / 2 + (1 - a) / 2 - 1 + lam
    u = 0.5 + mu * (base + a / 2 * (s1 - hf(s2) + r1 + l2))
    v = 0.5 + mu * (base + a / 2 * (s2 - hf(s1) + l1 + r2))
    w = 0.0 if sym else (v - u) / (2 * (1 - mu))
    if (1 - mu) * (0.5 - abs(w)) < j * mu:
        return None
    J = hk - a / 2 * (hf(s1) + hf(s2)) - (1 - a) * ht
    P3 = max(u + (1 - mu) * w, v - (1 - mu) * w) - (j - 1) * mu * (1 - hk)
    P4 = mu * (J + lam) + mu * L3F + max(mu, (1 - mu) * (0.5 + abs(w)) - mu)
    P6 = mu * (1 + hk + J + lam)
    return max(P3, P4, P6), w


def rig_terms(K, a, c1, c2, w, mu, lam, j, onesided=False):
    """Rigorous upper bounds (P3, P4, P6) on the layer piece K for one design, or None if the design is invalid on K."""
    s1, l1, r1 = c1[0], c1[1], c1[2]
    s2, l2, r2 = c2[0], c2[1], c2[2]
    if (1 - mu) * (F(1, 2) - abs(w)) < j * mu:
        return None
    aI, muI, wI, lamI = I.q(a), I.q(mu), I.q(w), I(lam)
    if a > 0:
        D = (K * 2 - aI * (I.q(s1) + 1 - I.q(s2))) / (1 - aI) - 1
    else:
        D = K * 2 - 1
    T = (D + 1) * 0.5
    if not (T.lo > 1e-3 and T.hi < 1 - 1e-3):    # local counts x_i, x'_i strictly inside (0, b_b): DERIVATION Lemma 3.3
        return None
    hK, hT = h_iv(K), h_iv(T)
    hs1, hs2 = h(I.q(s1)), h(I.q(s2))
    base = hK - (1 - aI) * hT * 0.5 + (1 - aI) * 0.5 - 1 + lamI
    u = 0.5 + muI * (base + aI * 0.5 * (I.q(s1) - hs2 + I(r1) + I(l2))) + (1 - muI) * wI
    v = 0.5 + muI * (base + aI * 0.5 * (I.q(s2) - hs1 + I(l1) + I(r2))) - (1 - muI) * wI
    if onesided:          # control: the v-list NOT deduped; the worst instance has d = 1 (N = 1)
        v = v + muI
    gain = (muI * (j - 1) * (1 - hK)).lo if j > 1 else 0.0
    P3 = max(u.hi, v.hi) - gain
    J = hK - aI * 0.5 * (hs1 + hs2) - (1 - aI) * hT
    side = max(muI.hi, ((1 - muI) * (I.q(F(1, 2)) + I.q(abs(w))) - muI).hi)
    P4 = (muI * (J + lamI) + muI * L3I + I(side)).hi
    P6 = (muI * (1 + hK + J + lamI)).hi
    return P3, P4, P6


def tail_terms(lo, mu, lam, j, onesided=False):
    """kappa in [0, lo] (and its mirror): the core-free design, symmetric, w = 0. There J = 0 and
    P3 = 1/2 - mu(1 - h(k))/2 - (j - 1) mu (1 - h(k)) [+ mu if one-sided], which is increasing in h(k), so its sup over
    [0, lo] is at k = lo (lo < 1/2); the one-sided control's sup is 1/2 + mu/2 at any k."""
    muI, lamI, hl = I.q(mu), I(lam), h(I.q(lo))
    P3 = (0.5 - muI * (1 - hl) * 0.5 - muI * (j - 1) * (1 - hl) + muI * lamI).hi
    if onesided:
        P3 = (0.5 + muI * 0.5).hi
    P4 = (muI * lamI + muI * L3I + I(max(muI.hi, ((1 - muI) * 0.5 - muI).hi))).hi
    P6 = (muI * (1 + hl + lamI)).hi
    return P3, P4, P6


def E_row(name, circ, mu, alphas, j=1, sym=False, lam=0.0, lo=F(2, 5), pieces=6000, grid=1200, onesided=False,
          cores=True, verbose=True):
    """Rigorous upper bound on the deterministic exponent of one row. Designs are chosen per piece by a float search
    on a grid (rigour does not depend on the choice: every piece's design is re-evaluated in intervals)."""
    if not cores:
        alphas = [F(0)]
    pairs = [(c, c) for c in circ] if sym else [(c1, c2) for c1 in circ for c2 in circ]
    designs = [(a, c1, c2) for a in alphas for (c1, c2) in (pairs if a > 0 else pairs[:1])]
    flo, fmu = float(lo), float(mu)
    gk = [flo + (1 - 2 * flo) * g / grid for g in range(grid + 1)]
    top = []
    for k in gk:
        vals = []
        for d in designs:
            r = float_terms(k, d[0], d[1], d[2], fmu, lam, j, sym)
            if r is not None:
                vals.append((r[0], d, r[1]))
        vals.sort(key=lambda x: x[0])
        top.append(vals[:2])
    worst = {"P3": -9.0, "P4": -9.0, "P6": -9.0}
    argw = None
    width = (1 - 2 * lo) / pieces
    used = set()
    for p in range(pieces):
        klo, khi = lo + width * p, lo + width * (p + 1)
        K = I(I.q(klo).lo, I.q(khi).hi)
        g0 = min(int((klo - lo) / (1 - 2 * lo) * grid), grid - 1)
        cands = [c for c in top[g0] + top[g0 + 1]]
        best = None
        for _, d, wf in cands:
            a, c1, c2 = d
            w = F(0) if sym else F(round(wf * 10 ** 7), 10 ** 7)
            r = rig_terms(K, a, c1, c2, w, mu, lam, j, onesided)
            if r is not None and (best is None or max(r) < max(best[0])):
                best = (r, (str(a), str(c1[0]), str(c2[0])))
        if best is None:      # fall back to the core-free design, valid wherever t = k is inside (0, 1)
            r = rig_terms(K, F(0), circ[0], circ[0], F(0), mu, lam, j, onesided)
            assert r is not None, f"no valid design on piece {p}"
            best = (r, ("0", "-", "-"))
        used.add(best[1])
        for key, val in zip(("P3", "P4", "P6"), best[0]):
            worst[key] = max(worst[key], val)
        if argw is None or max(best[0]) > argw[0]:
            argw = (max(best[0]), float(K.mid()), best[1])
    t3, t4, t6 = tail_terms(lo, mu, lam, j, onesided)
    worst = {k: max(v, t) for (k, v), t in zip(worst.items(), (t3, t4, t6))}
    muI = I.q(mu)
    terms = dict(worst, P1=muI.hi, P5=(2 * muI).hi, Kenum=(muI * (2 + I(lam))).hi)
    E = max(terms.values())
    if verbose:
        print(f"[E] {name}: mu = {mu}, j = {j}, alpha menu {[str(a) for a in alphas]}: E_det <= {E:.10f} "
              f"(saving >= {0.5 - E:.4e}); " + ", ".join(f"{k} {v:.9f}" for k, v in terms.items()))
        print(f"      binding piece kappa ~ {argw[1]:.5f}, design (alpha, s1, s2) = {argw[2]}; {len(used)} designs used",
              flush=True)
    return E, terms


# ------------------------------------------------------------------ rows and claims
ALPHA_MENU = [F(m, 20) for m in range(0, 20)]                 # 0, 1/20, ..., 19/20
ROWS = {
    "R1": dict(mu=F(2215, 10000), alphas=ALPHA_MENU, j=1, sym=True, claim=0.4995054714),
    "R1b": dict(mu=F(1999, 10000), alphas=ALPHA_MENU, j=2, sym=True, claim=0.4993293934),
    "R2": dict(mu=F(201, 1000), alphas=[F(m, 10) for m in range(10)] + [F(97, 100)], j=1, sym=False,
               claim=0.4991541425),
    "R3": dict(mu=F(1, 5), alphas=[F(m, 10) for m in range(10)] + [F(23, 25)], j=1, sym=False, claim=0.4989524521),
}


def main():
    sha = hashlib.sha256(open(os.path.join(HERE, "stage4_cert_vendored.py"), "rb").read()).hexdigest()[:16]
    print(f"Stage 5 certificate (uses stage4_cert_vendored.py = copy of certificates/stage4/cert_stage4.py, sha256 {sha}...)")
    print("[XI] circuits (Stage 4's branch-and-bound prover):")
    s4 = XI_DATA[F(11, 100)]
    single = cert_single(F(11, 100), s4["rho"], s4["t1"], s4["t2"], controls=False)
    menu = [cert_single(*m) for m in MENU_DATA]
    for m in MENU_DATA + [(F(11, 100), F(49, 20), None, None), (F(11, 100), F(11, 4), None, None)]:
        assert m[0] * m[1] < F(1, 2), ("Lemma 3.5' window s*rho < 1/2 fails", m[:2])   # (s, rho, ...) of every circuit
    print("      Lemma 3.5' window s*rho < 1/2 holds for all seven menu circuits and both family rho values")
    fam = cert_family()
    lam = lam_max(NB)
    print(f"[LAM] N_b = {NB}: lambda <= {lam:.4e} for every design (any a_b; the core-free design included)")
    for a in set(ALPHA_MENU) | set(ROWS["R2"]["alphas"]) | set(ROWS["R3"]["alphas"]):
        ab = F(NB) * a / 2
        assert ab.denominator == 1 and all((ab * c[0]).denominator == 1 for c in menu + [single]), a
    print("      every alpha in every menu makes a_b = alpha N_b/2 and s a_b integral for every menu s")
    circ = {"R1": [single], "R1b": [single], "R2": menu, "R3": menu + [fam]}
    res = {}
    for name, R in ROWS.items():
        E, T = E_row(name, circ[name], R["mu"], R["alphas"], R["j"], R["sym"], lam)
        res[name] = (E, T)
        check(E <= R["claim"], f"{name}: {E} > claim {R['claim']}")
        print(f"      claim E <= {R['claim']}: {E <= R['claim']}")
    print("Must-fail controls (each must be REJECTED):")
    ctl = []
    for name, R in ROWS.items():
        ctl.append((f"K1 {name}: claim - 1e-9", res[name][0] > R["claim"] - 1e-9))
    R = ROWS["R2"]
    e = E_row("K2 R2 mu + 1%", circ["R2"], R["mu"] * F(101, 100), R["alphas"], 1, False, lam, verbose=False)[0]
    ctl.append((f"K2 R2 with mu raised 1% gives {e:.10f} > claim", e > R["claim"]))
    e = E_row("K3", circ["R2"], R["mu"], R["alphas"], 1, False, lam, cores=False, verbose=False)[0]
    ctl.append((f"K3 no cores anywhere (dedupe alone) gives {e:.10f} >= 1/2", e >= 0.5))
    e = E_row("K4", circ["R2"], R["mu"], R["alphas"], 1, False, lam, onesided=True, verbose=False)[0]
    ctl.append((f"K4 one-sided dedupe (v-list raw) gives {e:.10f} > 1/2", e > 0.5))
    e = E_row("K5", circ["R2"], R["mu"], [F(0), F(97, 100)], 1, False, lam, verbose=False)[0]
    ctl.append((f"K5 A39's own design set {{0, alpha}} at R2's point gives {e:.10f} > R2 claim", e > R["claim"]))
    e = E_row("K5b", circ["R2"], F(1, 5), [F(0), F(9, 10)], 1, False, lam, verbose=False)[0]
    ctl.append((f"K5b A39's printed D1 point (alpha 0.90, mu 0.200, designs {{0, 0.90}}) gives {e:.10f} > A39's "
                f"0.49919788", e > 0.49919788))
    R1 = ROWS["R1"]
    ceil = 0.5 - float(R1["mu"]) * 0.95 * single[3]
    ctl.append((f"K6 R1 at A39's ceiling 1/2 - mu alpha xi = {ceil:.10f} (alpha 0.95)", res["R1"][0] > ceil))
    e = E_row("K6b", circ["R1"], R1["mu"], [F(0), F(19, 20)], 1, True, lam, verbose=False)[0]
    ctl.append((f"K6b R1 with one fixed alpha (19/20) and core-free elsewhere gives {e:.10f} > R1 claim",
                e > R1["claim"]))
    R3 = ROWS["R3"]
    sfam = (fam[0], single[1], single[2], single[3])
    e = E_row("K7", menu + [sfam], R3["mu"], R3["alphas"], 1, False, lam, verbose=False)[0]
    ctl.append((f"K7 R3 with the family point replaced by the single 11/100 circuit gives {e:.10f} > R3 claim",
                e > R3["claim"]))
    R1b = ROWS["R1b"]
    e = E_row("K8", circ["R1b"], F(201, 1000), R1b["alphas"], 2, True, lam, verbose=False)[0] \
        if (1 - F(201, 1000)) / 2 >= 2 * F(201, 1000) else 9.0
    ctl.append((f"K8 R1b at mu = 0.201 (two blocks per side no longer fit): {e}", e > 1))
    for name, ok in ctl:
        print(f"   {name}: {'rejected' if ok else 'NOT REJECTED'}")
        check(ok, name)
    print("STAGE 5 CERTIFICATE", "PASS" if not FAILS else f"FAIL ({len(FAILS)}): {FAILS}")
    return len(FAILS)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
