"""Numerical test of the rebalancing statement Ye-Li use (Sec. 3.4, Lemma 3.4, from Alman-Li arXiv 2509.14489 Thm B.2).

Lists (a_ij, b_ij) with entries >= 1, Upsilon(tau) = min_i sum_j a^tau b^(1-tau),
F_0(l) = 1 + l, F_d(l) = min_i sum_j a_ij F_{d-1}(l b_ij / a_ij).
Claim: F_d(l) <= 2^{o(d)} max_tau Upsilon(tau)^d l^(1-tau), given the two trivial lists (K,1) and (1,K').
Weak duality (AL Thm B.1, corrected exponents) gives the matching lower bound F_d >= Upsilon(tau)^d l^(1-tau).
We take a = 2^alpha, b = 2^beta with integer alpha, beta and l = 2^t on the integer lattice, so the
recursion is evaluated exactly on the lattice (log domain, float). Rate r_d = log2 F_d(2^{round(d kappa)}) / d,
bound B(kappa) = max_tau [log2 Upsilon(tau) + (1 - tau) kappa] on a 20001-point tau grid.
Pass: r_d - B -> 0 (gap at d = 256 below 0.02 and below the gap at d = 32) for every family and kappa,
and r_d >= B - 1e-6 - 1/d (weak duality, lattice rounding of t). Exit 0 = pass.
Families: YL-shaped (trivial lists + one multi-colour list with b > a everywhere) and random families
whose lists straddle (some a > b, some a < b), which AL's theorem also covers.
"""
import sys, math, random

def lse2(xs):  # log2 sum 2^x
    m = max(xs)
    return m + math.log2(sum(2.0 ** (x - m) for x in xs))

def bound(fam, kappa, G=20000):
    best = -1e18
    for g in range(G + 1):
        tau = g / G
        ups = min(lse2([tau * al + (1 - tau) * be for al, be in lst]) for lst in fam)
        best = max(best, ups + (1 - tau) * kappa)
    return best

def rates(fam, kappas, dmax):
    S = max(abs(be - al) for lst in fam for al, be in lst)
    T = int(dmax * (S + max(abs(k) for k in kappas))) + 10
    lo, hi = -T - dmax * S, T + dmax * S
    g = {t: math.log2(1 + 2.0 ** t) if t < 1000 else t + math.log2(1 + 2.0 ** -t) for t in range(lo, hi + 1)}
    out = {}
    for d in range(1, dmax + 1):
        lo += S; hi -= S
        g = {t: min(lse2([al + g[t + be - al] for al, be in lst]) for lst in fam) for t in range(lo, hi + 1)}
        for k in kappas:
            out[d, k] = g[round(d * k)] / d
    return out

def test(name, fam, kappas, dmax=256):
    ok = True
    r = rates(fam, kappas, dmax)
    for k in kappas:
        B = bound(fam, k)
        gaps = {d: r[d, k] - B for d in (8, 32, 128, 256)}
        lowok = all(r[d, k] >= B - 1e-6 - 1.0 / d for d in (8, 32, 128, 256))
        good = gaps[256] < 0.02 and gaps[256] <= gaps[32] + 1e-12 and lowok
        ok &= good
        print("%-10s kappa=%6.2f  B=%.4f  gap d=8 %.4f  32 %.4f  128 %.4f  256 %.4f  %s"
              % (name, k, B, gaps[8], gaps[32], gaps[128], gaps[256], "ok" if good else "FAIL"))
    return ok

if __name__ == "__main__":
    ok = True
    # YL-shaped: (M,I) = (2^13, 1), (I,M) = (1, 2^8), colored circuit with deg_R > deg_L in every colour
    yl = [[(13, 0)], [(0, 8)], [(0, 5), (1, 5)]]
    ok &= test("YL-shape", yl, [-6.0, -4.5, -3.0, -1.0, 0.0, 2.0])
    rng = random.Random(7)
    for f in range(4):
        fam = [[(6, 0)], [(0, 6)]]
        for _ in range(3):
            lst = [(rng.randint(0, 4), rng.randint(0, 4)) for _ in range(rng.randint(1, 3))]
            fam.append(lst)
        ok &= test("random%d" % f, fam, [-3.0, -1.0, 0.0, 1.0, 3.0])
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
