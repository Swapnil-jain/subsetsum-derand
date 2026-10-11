"""Stage 4+ certificate (separate, optional; PROOF.md Sec. 8): a FAMILY of two Record 3 circuits, rho = 49/20 and 11/4,
offered together to the density-s rebalancing (Lemma 3.4 with a finite family), at s = 11/100.

Claim [XI+]: min{tau h(s), V_{49/20}(tau), V_{11/4}(tau), (1 - tau)(1 - s)} <= line(tau) on [0, 1], where the line runs
through (t1, t1 h(s)) and (t2, (1 - t2)(1 - s)). Proof data:
  - V_{49/20}(t1) <= t1 h(s) and V_{11/4}(t2) <= (1 - t2)(1 - s)              (branch and bound, as cert_stage4.py);
  - at a middle vertex v: V_{49/20}(v) <= line(v) and V_{11/4}(v) <= line(v)  (branch and bound);
  - slope of the line in (-(1 - s), h(s)).
  V_rho is convex in tau (a max of affine functions), so V_{49/20} <= line on [t1, v] and V_{11/4} <= line on [v, t2];
  tau h(s) <= line on [0, t1] and (1 - tau)(1 - s) <= line on [t2, 1] by the slope.
Then the deterministic exponent at this xi, with the same lambda and terms as cert_stage4.py.
Controls: C1/C2 one grid step past the contacts (refuted for BOTH members, which also gives the [F1] bracket);
C3: each member alone fails at the other member's contact; K1-K4 on the exponent.
Run: nice -n 15 /usr/bin/python3 -E cert_stage4plus.py   (about 10 s, < 60 MB)
"""
import sys
from fractions import Fraction as F

from cert_stage4 import I, h, Land, E_rig, lam_bound, kap_lo_for, NB

S = F(11, 100)
R1, R2 = F(49, 20), F(11, 4)
DATA = dict(t1=F(1531131, 5000000), t2=F(7403119, 10 ** 7), v=F(5037, 10 ** 4),
            c1=F(3062261, 10 ** 7), c2=F(7403120, 10 ** 7))
PARAMS = (F(5564102, 10 ** 7), F(2192909, 10 ** 7), F(24022, 10 ** 7))   # alpha, mu, delta
CLAIM = 0.4997369618   # the Stage 4+ deterministic exponent claimed in PROOF.md Sec. 8


def main(search=False):
    fails = 0
    L1, L2 = Land(S, R1), Land(S, R2)
    hs, sI = h(I.q(S)), I.q(S)
    if search:
        bracket(L1, L2, hs, sI)
    t1, t2, v = I.q(DATA["t1"]), I.q(DATA["t2"]), I.q(DATA["v"])
    A1, A2 = t1 * hs, (1 - t2) * (1 - sI)
    slope = (A2 - A1) / (t2 - t1)
    line = lambda t: A1 + slope * (t - t1)
    ok1 = L1.prove(t1, A1.lo)[0]
    ok2 = L2.prove(t2, A2.lo)[0]
    okv1 = L1.prove(v, line(v).lo)[0]
    okv2 = L2.prove(v, line(v).lo)[0]
    okS = slope.hi <= hs.lo and slope.lo >= -(1 - sI).lo
    l_, r_ = line(I(1.0)), line(I(0.0))
    okLR = l_.lo >= 0 and r_.lo >= 0
    xi_lo = ((hs - sI) * I(0.5) - line(I(0.5))).lo
    print(f"[XI+] s={S}, family rho = {R1}, {R2}: V_{R1}(t1) <= t1 h(s) {ok1}; V_{R2}(t2) <= (1-t2)(1-s) {ok2}; "
          f"middle vertex v={DATA['v']}: V_{R1}(v) <= line {okv1}, V_{R2}(v) <= line {okv2}; slope {slope.mid():.6f} "
          f"ok {okS}; l = {l_.mid():.9f}, r = {r_.mid():.9f} >= 0 {okLR}")
    ok = ok1 and ok2 and okv1 and okv2 and okS and okLR
    fails += not ok
    xi = F(int(xi_lo * 10 ** 10), 10 ** 10)
    print(f"      CERTIFIED family xi(11/100) >= {xi_lo:.10f} (rational {xi}); single circuit: 0.0044849038")
    # controls
    c1, c2 = I.q(DATA["c1"]), I.q(DATA["c2"])
    f11, p11, _ = L1.refute(c1, (c1 * hs).lo)
    f21, p21, _ = L2.refute(c1, (c1 * hs).lo)
    f12, p12, _ = L1.refute(c2, ((1 - c2) * (1 - sI)).lo)
    f22, p22, _ = L2.refute(c2, ((1 - c2) * (1 - sI)).lo)
    print(f"      C1 (tau = {DATA['c1']}): both members exceed tau h(s): {f11 and f21};  "
          f"C2 (tau = {DATA['c2']}): both exceed (1-tau)(1-s): {f12 and f22}")
    fails += not (f11 and f21 and f12 and f22)
    if f11 and f21 and f12 and f22:   # [F1]: g(c1) = c1 h(s), g(c2) = (1-c2)(1-s), so every valid line is above both
        B1, B2 = c1 * hs, (1 - c2) * (1 - sI)
        sl = (B2 - B1) / (c2 - c1)
        print(f"      [F1] every line valid for this family's V has xi <= "
              f"{((hs - sI) * I(0.5) - (B1 + sl * (I(0.5) - c1))).hi:.10f}")
    g1, _, _ = L1.refute(t2, A2.lo)
    g2, _, _ = L2.refute(t1, A1.lo)
    print(f"      C3 each member alone fails at the other's contact: rho {R1} at t2 {g1}, rho {R2} at t1 {g2}")
    fails += not (g1 and g2)
    # exponent
    a, mu, dl = PARAMS
    lam = lam_bound(NB, a)
    assert (S * F(NB) * a / 2).denominator == 1
    E, T = E_rig(S, a, mu, dl, xi, kap_lo_for(dl), True, lam)
    claim = CLAIM
    fails += not (E <= claim)
    tt = ", ".join(f"{k} {w:.9f}" for k, w in sorted(T.items()))
    print(f"[E+] DET s={S} alpha={a} mu={mu} delta={dl}, lambda <= {lam:.3e}: E_det <= {E:.10f}  "
          f"(claim {claim}: {E <= claim}); gain {0.5 - E:.4e}\n      [{tt}]")
    Esingle = E_rig(S, a, mu, dl, F(22424519, 5 * 10 ** 9), kap_lo_for(dl), True, lam)[0]
    c = [("K1 claim - 1e-9", E > claim - 1e-9),
         ("K2 mu raised 1%", E_rig(S, a, mu * F(101, 100), dl, xi, kap_lo_for(dl), True, lam)[0] > claim),
         ("K3 delta doubled", E_rig(S, a, mu, 2 * dl, xi, kap_lo_for(2 * dl), True, lam)[0] > claim),
         (f"K4 single-circuit xi at these parameters gives {Esingle:.10f} > claim", Esingle > claim)]
    for name, okc in c:
        print(f"   {name}: {'rejected' if okc else 'NOT REJECTED'}")
        fails += not okc
    print("STAGE 4+ CERTIFICATE", "PASS" if fails == 0 else f"FAIL ({fails})")
    return fails


def bracket(L1, L2, hs, sI):
    """optional: re-derive t1, t2 on the 1e-7 grid with the prover itself (bisection)."""
    def bis(Ld, lo, hi, side):
        tgt = (lambda t: (I.q(t) * hs).lo) if side == 1 else (lambda t: ((1 - I.q(t)) * (1 - sI)).lo)
        good, bad = (hi, lo) if side == 1 else (lo, hi)
        for _ in range(26):
            mid = F(round((good + bad) / 2 * 10 ** 7), 10 ** 7)
            if mid in (good, bad):
                break
            if Ld.prove(I.q(mid), tgt(mid))[0]:
                good = mid
            else:
                bad = mid
        return good, bad
    print("   t1 bracket (rho1):", bis(L1, F(29, 100), F(33, 100), 1))
    print("   t2 bracket (rho2):", bis(L2, F(71, 100), F(77, 100), 2))


if __name__ == "__main__":
    sys.exit(1 if main("--search" in sys.argv) else 0)
