"""Certificate for the explicit Stage 2 (proofs/stage2b-explicit.md). Exact rationals only (fractions.Fraction).

Irrational inputs, all bounded outward and checked here:
  * Ye-Li v1 Sec. 4 table: 20-place truncations t, so t <= true < t + 1e-20 (used as upper bounds only);
  * ln 2: the series ln 2 = sum_{i>=1} 2^-i / i, whose partial sums are lower bounds and whose tail after n
    terms is at most 2^-n / (n+1). This certifies ln 2 >= 0.6931 and log2 e = 1/ln 2 >= 1.4426;
  * ln x for a rational x > 0: x = 2^k (1 - t) with 0 <= t < 1/2, and -S - R <= ln(1 - t) <= -S, where S is
    the 40-term series and R = t^41 / (41 (1 - t)). Binary entropy H is then enclosed by exact rationals;
  * log2 x <= bitlength(x) for integers x >= 1, and 48 (N+1)^14 <= 2^5 (N+1)^15 since 48 <= 32 (N+1).

[A] Explicit design at Ye-Li's own (a, b), q = lcm(4, 10^26) = 10^26. k = 10045215487480163574218750 is the least
    even k with q | N0 = k(k+2) (CRT: 5^26 | k/2 and 2^24 | k/2 + 1). Window half-width eps' = 10^-13.
    Certifies:
      q | N0 and k even;
      Ye-Li's parameter conditions and both dominance inequalities of Sec. 3.5 (PROOF E2(v)):
        E1(1/4) = h(b) - 2 h(1/4, a) - h(1/2, 1-b-2a) > 4a  and  h(1-b, 2a) > 8a;
      the preprocessing hypotheses of PROOF Lemma E6: H(b) <= 1/10, 1 - b <= 1/100, J <= N0/8,
        15 + 31 log2(N0+1) + log2 J <= 0.49 N0 and Vbar(0) + eps_V <= 1/2;
      eps_V = eps_win + J/N0 + eps_poly          (PROOF Lemma E2 + E3: volume loss per coordinate)
      the three-piece structure of Cbar (PROOF Lemma E4 hypotheses), secant domination at its division
      points with Stage 2's rational pair (dL', dR'), the gap Delta, N0 Delta >= 1, and log2(8 D_inf)/N0 <= L_D;
      eps_L, eps_R <= 1e-9 (PROOF Lemma E5), so Stage 2's Certificate 7.2 applies verbatim;
      the constant (proofs/stage2b-explicit.md Sec. 7): padding k^2 + 2 <= N0, c = L_D + 1 (padding) + 1 (storage) + 1 (additive
      preprocessing, c_b = 4 <= L_D + 2), and n0 = 2 c N0 / g.
[T] Trade-off table (exact bounds, printed): for a grid of k, the best eps' on a grid,
    eps_m = max(eps_L, eps_R), the balanced gain g = (xi' - 2 eps_m) / (12 + 2(xi' - 2 eps_m)), and
    n0 = 2 c N0 / g, beyond which the constant 2^{c N0} costs at most half the gain.
    Rows marked D4 use a = 1/2635, 1-b = 1/110 (q = 115940, k a multiple of q); their xi is NOT certified
    (CONDITIONAL).
Must-fail controls: [C1] k = 115940 at eps' tuned (grouping too costly for 1e-9); [C2] eps' = 1e-4
(window loss too big); [C3] eps' = 1e-27 (hole fixing has no valid J); [C4] dR' lowered by 1e-11 below
the secant; [C5] claim log2 D_inf / N0 <= L_D - 50; [C6] k = 10^25: q does not divide N0; [C7] claim
H(b) <= 0.07 (true value 0.0745).
Exit 0 iff [A] holds and every control is rejected. Pure standard library, < 2 s.
"""
from fractions import Fraction as F
import sys

E20 = F(1, 10 ** 20)
V0_UB = F("0.49268569663735450584") + E20
VH_UB = F("0.24997913372377961141") + E20
V1_UB = F("0.00757766963945240565") + E20
A_YL = F("0.00037954865735953624129927")
B_YL = F("0.99094548027616196930017929")
Q_YL = 10 ** 26                                           # lcm(4, denominators of a and b)
DL_P, DR_P = F("0.007275870560"), F("0.492684058989")   # Stage 2 Sec. 4 rational pair
XI_B = F(2, 10 ** 5)                                      # Prop. 4.2 statement: xi > 0.00002
LN2_LO, LOG2E_LO = F("0.6931"), F("1.4426")
K_A = 10045215487480163574218750
EPS_A = F(1, 10 ** 13)

# ---------------- exact enclosures of ln 2, ln x and binary entropy
def lsum(t, n):          # sum_{i=1}^{n} t^i / i
    s, p = F(0), F(1)
    for i in range(1, n + 1):
        p *= t
        s += p / i
    return s

L2_S = lsum(F(1, 2), 60)
L2_LO_SER, L2_HI_SER = L2_S, L2_S + F(1, 2 ** 60 * 61)   # tail sum_{i>60} 2^-i/i <= 2^-60/61
LN2_CHECK = LN2_LO <= L2_LO_SER and L2_HI_SER * LOG2E_LO <= 1  # ln 2 >= 0.6931; 1/ln 2 >= 1.4426

def ln_encl(x, n=40):
    """[lo, hi] with lo <= ln x <= hi, for rational x > 0."""
    assert x > 0
    k = 0
    while x / F(2) ** k > 1:
        k += 1
    while x / F(2) ** k <= F(1, 2):
        k -= 1
    t = 1 - x / F(2) ** k                    # 0 <= t < 1/2
    S = lsum(t, n)
    R = t ** (n + 1) / ((n + 1) * (1 - t))
    lo, hi = -S - R, -S
    if k >= 0:
        return lo + k * L2_LO_SER, hi + k * L2_HI_SER
    return lo + k * L2_HI_SER, hi + k * L2_LO_SER

def H_encl(x):
    """[lo, hi] with lo <= H(x) <= hi (bits), for rational 0 < x < 1."""
    l1, u1 = ln_encl(x)
    l2, u2 = ln_encl(1 - x)
    nlo, nhi = -x * u1 - (1 - x) * u2, -x * l1 - (1 - x) * l2
    assert nlo >= 0
    return nlo / L2_HI_SER, nhi / L2_LO_SER

def yl_conditions(a, b):
    """Ye-Li's parameter conditions, the two dominance inequalities, and Lemma E6's hypotheses."""
    Hb_lo, Hb_hi = H_encl(b)
    _, H4a_hi = H_encl(4 * a)
    _, Hm_hi = H_encl(2 * (1 - b - 2 * a))
    Hd_lo, _ = H_encl(2 * a / (1 - b))
    E1_lo = Hb_lo - H4a_hi / 2 - Hm_hi / 2             # E1(1/4) = h(b) - 2 (1/4) H(4a) - (1/2) H(2(1-b-2a))
    dom1 = E1_lo - 4 * a
    dom2 = (1 - b) * Hd_lo - 8 * a                     # h(1-b, 2a) = (1-b) H(2a/(1-b))
    params = 0 < a < F(1, 4) and 4 * a <= 1 - b < F(1, 2) + 2 * a and 1 - b > 10 * a
    return dict(params=params, dom1=dom1, dom2=dom2, Hb_hi=Hb_hi, Hb_lo=Hb_lo,
                e6=Hb_hi <= F(1, 10) and 1 - b <= F(1, 100))

# ---------------- the design
def lg_up(x):  # log2 upper bound for integer x >= 1
    return F(int(x).bit_length())

def eps_win(e, a):
    # row weight: 1 - h(1/2 + e) <= (2e)^2 / (2 ln2 (1 - (2e)^2)); query type: second-order Taylor term
    row = (2 * e) ** 2 / (2 * LN2_LO * (1 - (2 * e) ** 2))
    qry = e * e * a / ((F(1, 4) - e) * (F(1, 4) - e - a) * LN2_LO)
    return row + qry

def J_of(e, N):
    # need J * (2 - 2 e^2 N log2 e) + 2.5 N < 0  (pair miss prob <= 4 exp(-2 e^2 N), |X||Y| <= 2^{2.5N})
    den = 2 * e * e * N * LOG2E_LO - 2
    if den <= 0:
        return None
    return int(F(5, 2) * N / den) + 1

def design(k, e, a, dL=DL_P, dR=DR_P):
    N = k * k + 2 * k
    J = J_of(e, N)
    if J is None:
        return None
    epsV = eps_win(e, a) + F(J, N) + (5 + 15 * lg_up(N + 1)) / N
    U0, Uh, U1 = V0_UB + epsV, VH_UB + epsV, V1_UB + epsV
    t1 = U0 / (1 + 2 * U0 - 2 * Uh)                       # segment 1 meets tau
    t2 = (F(1, 2) - 2 * Uh + U1) / (F(1, 2) + 2 * U1 - 2 * Uh)  # segment 2 meets (1 - tau)/2
    if t2 < F(1, 2):                                       # large eps_V: the crossing is on segment 1
        t2 = (F(1, 2) - U0) / (2 * (Uh - U0) + F(1, 2))
    # pieces: tau on [0,t1], Vbar+eps_V on [t1,t2], (1-tau)/2 on [t2,1]; Vbar convex (Uh <= (U0+U1)/2)
    ok_struct = (0 < t1 < F(1, 3) < t2 < 1) and 2 * Uh <= U0 + U1 and t1 <= F(1, 2)
    line = lambda t: t * dL + (1 - t) * dR
    c1, c2 = t1, (1 - t2) / 2
    ok_sec = c1 <= line(t1) + epsV and c2 <= line(t2) + epsV
    # rebalancing constant (PROOF Lemma E4): chord slopes, gap Delta (per coordinate), ratio exponent r_max
    s1, s2, s3 = c1 / t1, (c2 - c1) / (t2 - t1), -c2 / (1 - t2)
    ok_struct = ok_struct and s1 > s2 > s3
    dmin = min(t1, t2 - t1, 1 - t2)
    # Delta = dmin * min slope gap / 4: the dyadic thresholds lie within a quarter of the slope gap of the
    # midpoints, so each comparison keeps a quarter of the gap (PROOF Lemma E4).
    Delta = dmin * min(s1 - s2, s2 - s3) / 4
    # r_max = max over pieces t and A-points of v_t(tau) - c(tau); v1 = tau, v2 = (1-tau)/2, v3 = Vbar + epsV
    def v3(t):
        return U0 + 2 * t * (Uh - U0) if t <= F(1, 2) else Uh + 2 * (t - F(1, 2)) * (U1 - Uh)
    Apts = [(F(0), F(0)), (t1, c1), (t2, c2), (F(1), F(0))]
    rmax = max(max(t - c, (1 - t) / 2 - c, v3(t) - c) for t, c in Apts)
    if not ok_struct or N * Delta < 1:   # the D_inf bound below needs N0 * Delta >= 1
        ok_struct, Delta = False, F(1)
    dstar = int(rmax / Delta) + 1
    LD = dstar * (rmax + 2) + 4 + 3      # log2 (8 D_inf) <= N0 * LD
    epsL = 2 * dL / k + (1 + F(2, k)) * epsV + lg_up(k + 1) / k
    epsR = 2 * dR / k + (1 + F(2, k)) * epsV
    c = LD + 3                           # + padding 2^{k^2+2} <= 2^{N0}, storage 2^{N0}, additive preprocessing
    return dict(N=N, J=J, epsV=epsV, t1=t1, t2=t2, ok_struct=ok_struct, ok_sec=ok_sec,
                Delta=Delta, rmax=rmax, dstar=dstar, LD=LD, c=c, epsL=epsL, epsR=epsR,
                pad_ok=k * k + 2 <= N,
                # Lemma E6's numeric hypotheses: J <= N/8, 2^15 (N+1)^31 J <= 2^{0.49 N}, Vbar(0) + eps_V <= 1/2
                e6num=8 * J <= N and 15 + 31 * lg_up(N + 1) + lg_up(J) <= F(49, 100) * N and U0 <= F(1, 2))

def gain(em):
    return (XI_B - 2 * em) / (12 + 2 * (XI_B - 2 * em))

def f(x, d=6):
    return "%.*e" % (d, float(x))

ok = True
# ---------------- [A]
yc = yl_conditions(A_YL, B_YL)
r = design(K_A, EPS_A, A_YL)
LD_A = r["LD"]
gA = gain(max(r["epsL"], r["epsR"]))
n0A = 2 * r["c"] * r["N"] / gA
A_ok = (LN2_CHECK and K_A % 2 == 0 and r["N"] % Q_YL == 0 and yc["params"] and yc["dom1"] > 0 and yc["dom2"] > 0
        and yc["e6"] and r["e6num"] and r["ok_struct"] and r["ok_sec"] and r["pad_ok"]
        and r["epsL"] <= F(1, 10 ** 9) and r["epsR"] <= F(1, 10 ** 9)
        and r["LD"] <= 4855 and r["c"] <= 4858 and n0A <= F(59, 10 ** 2) * 10 ** 60)
print("[A] ln2 >= 0.6931 and log2 e >= 1.4426: %s;  k=%d even, 10^26 | N0: %s" % (LN2_CHECK, K_A, r["N"] % Q_YL == 0))
print("    YL params %s; E1(1/4)-4a >= %s; h(1-b,2a)-8a >= %s; H(b) <= %s (Lemma E6: <= 1/10, 1-b <= 1/100: %s)"
      % (yc["params"], f(yc["dom1"], 3), f(yc["dom2"], 3), f(yc["Hb_hi"], 4), yc["e6"]))
print("    N0=%s J=%s eps_V<=%s tau1=%.9f tau2=%.9f Delta=%s r_max=%s d*=%d log2(8 D_inf)/N0<=%d"
      % (f(r["N"], 4), f(r["J"], 3), f(r["epsV"]), float(r["t1"]), float(r["t2"]), f(r["Delta"]), f(r["rmax"], 3),
         r["dstar"], r["LD"]))
print("    eps_L<=%s eps_R<=%s  structure %s  secant %s  padding %s  Lemma E6 numeric hypotheses %s"
      % (f(r["epsL"]), f(r["epsR"]), r["ok_struct"], r["ok_sec"], r["pad_ok"], r["e6num"]))
print("    c = L_D + 3 = %d;  gain g >= %s;  n0 = 2 c N0 / g <= %s  -> %s" % (r["c"], f(gA, 5), f(n0A, 3),
      "PASS" if A_ok else "FAIL"))
ok &= A_ok

# ---------------- controls
def rejects(name, cond):
    global ok
    print("  [%s] rejected: %s" % (name, cond))
    ok &= cond

A_D4 = F(1, 2635)
c1 = design(115940, F(1, 1000), A_D4)
rejects("C1 k=115940", c1["epsL"] > F(1, 10 ** 9))
c2 = design(K_A, F(1, 10 ** 4), A_YL)
rejects("C2 eps'=1e-4", c2["epsL"] > F(1, 10 ** 9))
rejects("C3 eps'=1e-27", design(K_A, F(1, 10 ** 27), A_YL) is None)
c4 = design(K_A, EPS_A, A_YL, dR=DR_P - F(1, 10 ** 11))
rejects("C4 dR' - 1e-11", not c4["ok_sec"])
rejects("C5 L_D - 50", not (LD_A <= LD_A - 50))
rejects("C6 k=10^25", (10 ** 25 * (10 ** 25 + 2)) % Q_YL != 0)
rejects("C7 H(b)<=0.07", yc["Hb_lo"] > F(7, 100))

# ---------------- [T] trade-off table (printed; not asserted)
def best(k, a):
    bestr = None
    for ex in range(2, 40):
        for m in (1, 2, 5):
            e = F(m, 10 ** ex)
            if e >= F(1, 20):
                continue
            d = design(k, e, a)
            if d is None or not (d["ok_struct"] and d["ok_sec"]):
                continue
            em = max(d["epsL"], d["epsR"])
            if bestr is None or em < bestr[0]:
                bestr = (em, e, d)
    return bestr

print("[T] trade-off (exact bounds; D4 rows CONDITIONAL on certifying xi at a=1/2635, 1-b=1/110)")
print("    %-6s %-10s %-10s %-11s %-11s %-12s %-5s %s" % ("param", "k", "N0", "eps'", "eps_m", "gain", "c",
      "n0 = 2 c N0 / g"))
rows = [("D4", j * 115940, A_D4) for j in (1, 4, 8, 16, 19, 32, 64, 128)] + [("YL", K_A, A_YL), ("YL", 10 ** 30, A_YL)]
for tag, k, a in rows:
    em, e, d = best(k, a)
    g = gain(em)
    n0 = "none (no gain)" if g <= 0 else f(2 * d["c"] * d["N"] / g, 2)
    print("    %-6s %-10s %-10s %-11s %-11s %-12s %-5d %s" % (tag, f(k, 3), f(d["N"], 3), f(e, 1), f(em, 3),
          f(g, 4) if g > 0 else "<= 0", d["c"], n0))
g_lim = XI_B / (12 + 2 * XI_B)
print("    limit eps_m -> 0: gain -> xi'/(12+2xi') = %s, exponent -> %.12f (growing N0, PROOF Sec. 8)" % (f(g_lim, 8), 0.5 - float(g_lim)))
print("ALL PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
