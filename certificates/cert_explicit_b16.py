"""Improvement certificate (lead B16): a sharper rebalancing constant for the explicit Stage 2 (proofs/stage2b-explicit.md Sec. 12).

Separate from cert_explicit.py, which certifies Theorem E as stated (c = 4858). Both are kernel-checked in Lean
(this one by lean/SubsetsumLean/ExplicitN0.lean, theorems explicit_B16, B16_D1, B16_D2). Exact rationals only; it reuses cert_explicit.py's design [A] (run first, must
exit 0).

What it certifies, at design [A] (k = 10045215487480163574218750, eps' = 1e-13):
  * dyadic thresholds x1, x2 (denominator 2^40) within a quarter of the slope gap of the midpoints, as E4's rule
    requires;
  * for every piece t and every off point tau_j of A, the gap delta_{t,j} > 0 (the least value over piece t's
    threshold region of the chord sum between tau_j and the nearer endpoint) and the excess
    r_{t,j} = v_t(tau_j) - c(tau_j); and v_t <= c at piece t's own endpoints;
  * d1 := max over pairs with r > 0 of floor(r/delta) + 1, N0 * min delta >= 1, and
    S := sum_{d=1}^{d1} max_{t,j} (r_{t,j} - d delta_{t,j})^+, so that log2(8 D_inf) <= S N0 + 2 d1 + 6
    (PROOF Lemma E4');
  * the run-time constant log2 C <= S N0 + 2 d1 + 6 + (k^2 + 2)/2 + log2(12 N0^2) (padding at most 2^{1/2} per
    padded coordinate, storage by binary search), and the threshold
    n0 := max(2 (c_b N0 + 1)/(1 - g), 2 (log2 C + 1)/g), with c_b = 4 (Lemma E6, additive and paid once). For
    n >= n0 the build and the run are each at most 2^{(1/2 - g/2) n - 1} poly(n, L), so the run time is below
    2^{(1/2 - g/2) n} poly(n, L). (Same definition as proofs/stage2b-explicit.md Sec. 13 and cert_explicit_b17.py.)
Must-fail controls: [D1] the claim S <= 0.49; [D2] thresholds at the slopes themselves (x1 = s2, x2 = s3), where
some gap delta_{t,j} is 0.
Exit 0 iff every check holds and both controls are rejected.
"""
from fractions import Fraction as F
import contextlib
import io
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ns = {"__name__": "cert"}
with contextlib.redirect_stdout(io.StringIO()):
    try:
        exec(compile(open(os.path.join(HERE, "cert_explicit.py")).read(), "cert_explicit.py", "exec"), ns)
    except SystemExit as e:
        assert e.code == 0, "cert_explicit.py must pass"
r = ns["r"]
N, k = r["N"], ns["K_A"]
epsV = r["epsV"]
U0, Uh, U1 = ns["V0_UB"] + epsV, ns["VH_UB"] + epsV, ns["V1_UB"] + epsV
t1, t2 = r["t1"], r["t2"]
tau = [F(0), t1, t2, F(1)]
cv = [F(0), t1, (1 - t2) / 2, F(0)]
s = [None] + [(cv[i] - cv[i - 1]) / (tau[i] - tau[i - 1]) for i in (1, 2, 3)]

def v3(t):
    return U0 + 2 * t * (Uh - U0) if t <= F(1, 2) else Uh + 2 * (t - F(1, 2)) * (U1 - Uh)
# pieces: 1 = (M,I) on [tau0, tau1], 2 = C3 on [tau1, tau2], 3 = (I,M) on [tau2, tau3]
v = {1: lambda t: t, 2: v3, 3: lambda t: (1 - t) / 2}
ends = {1: (0, 1), 2: (1, 2), 3: (2, 3)}

def dyadic(x, bits=40):
    return F(int(x * 2 ** bits) if x >= 0 else -int(-x * 2 ** bits) - 1, 2 ** bits)  # floor to 2^-bits

def analyse(x1, x2):
    """Per-pair gaps and excesses for thresholds x1 (between pieces 1 and 2) and x2 (between 2 and 3)."""
    pairs = []
    for t in (1, 2, 3):
        lo_e, hi_e = ends[t]
        for j in range(4):
            if j in (lo_e, hi_e):
                continue
            if j > hi_e:      # right of the piece: nearer endpoint tau_{hi_e}; ell >= x_t on piece t
                xt = x1 if t == 1 else x2
                d = sum((tau[i] - tau[i - 1]) * (xt - s[i]) for i in range(hi_e + 1, j + 1))
            else:             # left of the piece: nearer endpoint tau_{lo_e}; ell < x_{t-1} on piece t
                xt = x1 if t == 2 else x2
                d = sum((tau[i] - tau[i - 1]) * (s[i] - xt) for i in range(j + 1, lo_e + 1))
            pairs.append((t, j, d, v[t](tau[j]) - cv[j]))
    return pairs

m1, m2 = (s[1] + s[2]) / 2, (s[2] + s[3]) / 2
x1, x2 = dyadic(m1), dyadic(m2)
ok = abs(x1 - m1) <= (s[1] - s[2]) / 4 and abs(x2 - m2) <= (s[2] - s[3]) / 4
ok &= all(v[t](tau[e]) <= cv[e] for t in (1, 2, 3) for e in ends[t])   # endpoints carry no excess
pairs = analyse(x1, x2)
ok &= all(d > 0 for _, _, d, _ in pairs)
dmin = min(d for _, _, d, _ in pairs)
d1 = max(int(rr / d) + 1 for _, _, d, rr in pairs if rr > 0)
ok &= N * dmin >= 1
S = sum(max([F(0)] + [rr - dd * d for _, _, d, rr in pairs]) for dd in range(1, d1 + 1))
log2_8Dinf = S * N + 2 * d1 + 6
log2C = log2_8Dinf + F(k * k + 2, 2) + 2 * N.bit_length() + 4
g = ns["gain"](max(r["epsL"], r["epsR"]))
CB = 4
n0 = max(2 * (CB * N + 1) / (1 - g), 2 * (log2C + 1) / g)
ok &= S <= F(4967, 10000) and n0 <= F(121, 100) * 10 ** 56
print("[B16] thresholds x1 = %.6f, x2 = %.6f (dyadic, 2^-40), within a quarter of the slope gaps" % (float(x1), float(x2)))
for t, j, d, rr in pairs:
    print("  piece %d, off point tau_%d: delta = %.6f, r = %.6f, r/delta = %.3f" % (t, j, float(d), float(rr), float(rr / d)))
print("  d1 = %d, N0 * min delta = %.3e >= 1; S = %.6f, so log2(8 D_inf) <= %.6f N0 + %d (was 4855 N0)"
      % (d1, float(N * dmin), float(S), float(S), 2 * d1 + 6))
print("  log2 C <= %.6f N0 (rebalancing + padding 1/2 + storage); c_b = 4 is additive" % float(log2C / N))
print("  n0 = max(2 (c_b N0 + 1)/(1-g), 2 (log2 C + 1)/g) <= %.3e (was 5.88e59)  -> %s" % (float(n0), "PASS" if ok else "FAIL"))
print("  gain g >= %.4e; for n >= n0 the run time is below 2^{%.10f n} poly(n, L)" % (float(g), 0.5 - float(g) / 2))

def rejects(name, cond):
    global ok
    print("  [%s] rejected: %s" % (name, cond))
    ok &= cond
rejects("D1 S <= 0.49", not S <= F(49, 100))
rejects("D2 x = slopes", not all(d > 0 for _, _, d, _ in analyse(s[2], s[3])))
print("ALL PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
