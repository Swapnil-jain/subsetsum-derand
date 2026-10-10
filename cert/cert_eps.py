"""Certificate for the Stage 2 exponent (PROOF.md, Sec. 7).

Exact rationals (fractions.Fraction) only; no floating point enters any asserted inequality (the one
exception is the kappa bisection, done in 60-digit decimals, with a wide margin). The two
irrational inputs are handled by outward bounds:
  * Ye-Li's table values (arXiv 2610.10446v1, Sec. 4) are 20-place truncations t, so t <= true < t + 10^-20;
  * log2(3) < 1.585 is certified by the integer comparison 3^200 < 2^317.
Printed decimals are rounded outward (lower bounds down, upper bounds up). Pure standard library, < 1 s.

Cost terms, as exponents of 2 per unit n, at prefix m = pi n (PROOF.md Lemma 6.1; every term carries an
additional 2^{o(n)} factor, which the strict margin below absorbs):
  T_prefix  = pi                      enumerate the 2^m prefix subset sums
  T_prime   = 2 pi                    prime scan, N^2 (b+1) poly          (Lemma 2.3(ii))
  T_layers  = 2 pi                    all layer sets K(c, j) mod p         (Step 3)
  T_cover   = 2 pi                    greedy coverings, |R| 2^m p polylog  (Lemma 2.1(iv))
  T_hist    = log2(3) pi              right prefix histogram over 3^m vectors; the other histograms and the
                                      convolutions are dominated by T_left, T_right, T_prefix
  T_left    = 1/4 + pi/2              left partial lists                   (Lemma 6.1)
  T_right   = 1/4 + 3 pi/4            right partial lists (JUDGE fix S2)   (Lemma 6.1)
  T_few     = 1/2 - gamma pi/2        few-sums branch, N <= 2^{(1-gamma) m}
  T_many    = 1/2 - (xi' - gamma) pi + 2 eps_PM pi      many-sums branch, filtered partial match
with gamma = 2 xi'/3, xi' a rational LOWER bound on Ye-Li's xi, eps_PM the slack of Def. 2.1.
Side conditions (PROOF.md Lemma 3.5): pi <= 1/3 (so l >= 0) and pi <= 2/5 (so l <= n - m); the rational
pair (dL', dR') is >= Ye-Li's pair termwise and dL' + dR' <= 1/2 - 2 xi' (admissible by upward closure).

Claims certified:
  [A] pi = 2499/10^4, xi' = 2.0035e-5 (<= the table's xi), eps_PM = 10^-9: max term E < 0.49999834,
      so the gain 1/2 - E >= 1.66e-6.
  [B] the same with xi' = 2e-5, using from Prop. 4.2 only the STATEMENT xi > 0.00002 for xi. YL's table is
      used in [B] ONLY as upper bounds on the two degree exponents dL and dR (these two numbers are not in the
      statement, so there is no other source for them): dL <= DL_UB, dR <= DR_UB. The pair used by the
      algorithm is the rational (dL', dR') just above those upper bounds, and [B] checks dL' + dR' <=
      1/2 - 2 xi' with xi' = 2e-5 against nothing from the table. The table's xi is not read in [B].
Must-fail controls (the same checker must reject each):
  [C1] at the parameters of [A], claim E <= 0.49999833 (one unit lower in the 8th place): rejected.
  [C2] prefix pi = 1/4 (the covering then costs 2^{n/2}): rejected.
  [C3] Ye-Li's own prefix pi = 1/3 (their randomized split; the covering costs 2^{2n/3}): rejected.
  [C4] slack eps_PM = 10^-6: rejected.
  [C5] xi' = 0 (Prop. 4.2 false): rejected.
  [C6] a pair rounded DOWN below Ye-Li's table: the admissibility check rejects it.
  [C7] in [B], claim xi' = 2.0035e-5 from the statement alone (the statement gives only 2e-5): rejected.
  [C8] in [B], a pair rounded DOWN below the upper bounds on dL, dR: rejected.
Also printed: Cor. 3.2's block length kappa for the rational pair, from BOTH of its conditions, and N'.
Exit code 0 iff [A], [B], the kappa computation hold and every control is rejected.
"""
from fractions import Fraction as F
from decimal import Decimal, getcontext
import sys

E20 = F(1, 10 ** 20)
# Ye-Li v1, Sec. 4 table (20-place truncations of the exact values).
DL_T = F("0.00727587055962990941")
DR_T = F("0.49268405898808998771")
XI_T = F("0.00002003522614005143")
# log2(3) < 1.585, certified by integers.
assert 3 ** 200 < 2 ** 317
LOG2_3_UP = F(317, 200)

# Rational pair used by the algorithm (12-place round-ups of the table).
DL_P = F("0.007275870560")
DR_P = F("0.492684058989")


def dec(x, places=12, up=True):
    """Outward decimal string: rounded up if up, else down."""
    s = 10 ** places
    q = -((-x.numerator * s) // x.denominator) if up else (x.numerator * s) // x.denominator
    sign = "-" if q < 0 else ""
    q = abs(q)
    return f"{sign}{q // s}.{q % s:0{places}d}"


def terms(pi, xi, eps):
    gamma = F(2, 3) * xi
    return {
        "T_prefix": pi,
        "T_prime": 2 * pi,
        "T_layers": 2 * pi,
        "T_cover": 2 * pi,
        "T_hist": LOG2_3_UP * pi,
        "T_left": F(1, 4) + pi / 2,
        "T_right": F(1, 4) + F(3, 4) * pi,
        "T_few": F(1, 2) - gamma * pi / 2,
        "T_many": F(1, 2) - (xi - gamma) * pi + 2 * eps * pi,
    }


# Upper bounds on Ye-Li's true dL and dR (truncation + 10^-20). They are the ONLY table input of [B].
DL_UB = DL_T + E20
DR_UB = DR_T + E20
# Lower bound on xi that Prop. 4.2 STATES (xi > 0.00002); the xi input of [B]. [B] is no weaker in assumptions
# than [A] (dL, dR still come from the table, which already implies xi' = 2.00352e-5); it checks xi_cap bookkeeping.
XI_STATED = F(2, 10 ** 5)


def admissible(dl, dr, xi):
    """dl, dr >= the upper bounds on Ye-Li's pair, and dl + dr <= 1/2 - 2 xi."""
    return dl >= DL_UB and dr >= DR_UB and dl + dr <= F(1, 2) - 2 * xi


def check(pi, xi, eps, bound, dl=DL_P, dr=DR_P, verbose=False, xi_cap=XI_T):
    """True iff every side condition holds and every cost term is < bound.
    xi_cap is the largest xi' we may assume: the table's xi for [A], the STATED 2e-5 for [B]."""
    if not (0 < pi <= F(1, 3) and pi <= F(2, 5)):
        return False, None
    if not (0 <= xi <= xi_cap):       # xi' must be a lower bound on Ye-Li's xi
        return False, None
    if not admissible(dl, dr, xi):
        return False, None
    t = terms(pi, xi, eps)
    E = max(t.values())
    if verbose:
        for k, v in t.items():
            print(f"    {k:9s} <= {dec(v)}")
        arg = max(t, key=t.get)
        print(f"    max E    <= {dec(E)}  ({arg});  gain 1/2 - E >= {dec(F(1, 2) - E, up=False)}")
        print(f"    margin to {dec(bound, 8)}: {dec(bound - E, up=False)}")
    return E < bound, E


def main():
    ok = True
    pi = F(2499, 10 ** 4)
    eps = F(1, 10 ** 9)
    bound = F("0.49999834")

    print("[A] pi = 0.2499, xi' = 2.0035e-5 (table), eps_PM = 1e-9")
    a, EA = check(pi, F("0.000020035"), eps, bound, verbose=True)
    a = a and F(1, 2) - EA >= F("0.00000166")
    print("   ", "PASS" if a else "FAIL")
    ok &= a

    print("[B] pi = 0.2499, xi' = 2e-5 (same dL, dR table bounds as [A]; only checks the xi_cap bookkeeping), eps_PM = 1e-9")
    b, EB = check(pi, XI_STATED, eps, bound, verbose=True, xi_cap=XI_STATED)
    b = b and F(1, 2) - EB >= F("0.00000166")
    print("   ", "PASS" if b else "FAIL")
    ok &= b

    print("    pair used: dL' + dR' =", dec(DL_P + DR_P), "<= 1/2 - 2 xi' =", dec(F(1, 2) - 2 * F("0.000020035"), up=False))
    # informational: the balanced prefix pi* = 3/(12 + 2 xi) of AUDIT.md, with the table's xi
    pstar = F(3) / (12 + 2 * XI_T)
    print("    info: pi* = 3/(12+2xi) =", dec(pstar), "; there 2 pi* = 1/2 - xi pi*/3 =", dec(2 * pstar))
    # Cor. 3.2's block length for the RATIONAL pair (dL', dR'): both conditions of the corollary, restated with
    # dL', dR' in place of dL, dR (Cor. 3.2 needs (dL, dR) in K(1/2); the proof of Prop. 4.2 gives this for Ye-Li's pair and K is upward closed):
    #   (1) (2/kappa)(max(dL', dR') + eps/4) <= eps/4      i.e.  kappa >= 8 (dR' + eps/4)/eps
    #   (2) log2(kappa + 1)/kappa <= eps/4
    # (2) is monotone for kappa >= 1, so the least admissible kappa is found by bisection (60-digit decimals).
    getcontext().prec = 60
    k1 = 8 * (max(DL_P, DR_P) + eps / 4) / eps
    ln2 = Decimal(2).ln()
    e4 = Decimal(eps.numerator) / Decimal(eps.denominator) / 4

    def cond2(k):
        return (Decimal(k + 1).ln() / ln2) / Decimal(k) <= e4
    lo, hi = 10 ** 6, 10 ** 15
    assert cond2(hi) and not cond2(lo)
    while lo < hi:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if cond2(mid) else (mid + 1, hi)
    k2 = lo + (lo % 2)               # kappa must be an even integer
    kmin = max(-((-k1.numerator) // k1.denominator), k2)
    kmin += kmin % 2
    assert cond2(kmin) and not cond2(kmin - 4) and kmin >= k1 and kmin - 2 < max(k1, k2) + 2
    Np = kmin * kmin + 2 * kmin
    print(f"    Cor. 3.2: condition (1) gives kappa >= {float(k1):.4e}; condition (2) gives kappa >= {k2:.4e}"
          f" (binding); least even kappa = {kmin}; N' = kappa^2 + 2 kappa = {Np:.4e} (>= 2.2e22)")
    ok &= Np >= 22 * 10 ** 21 and k2 > k1
    # informational (kept for continuity): the old, first-condition-only bound
    print(f"    info: condition (1) alone would give N' >= {float(k1 * k1):.2e} (not tight)")

    controls = [
        ("[C1] claim E <= 0.49999833 at [A]", lambda: check(pi, F("0.000020035"), eps, F("0.49999833") + F(1, 10 ** 30))[0]),
        ("[C2] prefix pi = 1/4", lambda: check(F(1, 4), F("0.000020035"), eps, bound)[0]),
        ("[C3] prefix pi = 1/3 (Ye-Li's split)", lambda: check(F(1, 3), F("0.000020035"), eps, bound)[0]),
        ("[C4] eps_PM = 1e-6", lambda: check(pi, F("0.000020035"), F(1, 10 ** 6), bound)[0]),
        ("[C5] xi' = 0", lambda: check(pi, F(0), eps, bound)[0]),
        ("[C6] pair rounded down", lambda: check(pi, F("0.000020035"), eps, bound,
                                                 dl=F("0.007275870559"), dr=F("0.492684058988"))[0]),
        # A true must-fail: with the cap lifted, xi' = 2.1e-5 is still refused because the rational pair no
        # longer satisfies dL' + dR' <= 1/2 - 2 xi'. (xi' = 2.0035e-5 itself is TRUE for that pair, so the
        # xi_cap in [B] is only bookkeeping, not an extra assumption; see PROOF Sec. 7 [B].)
        ("[C7] [B] claiming xi' = 2.1e-5 (pair too large for it)",
         lambda: check(pi, F("0.000021"), eps, bound, xi_cap=F(1, 10 ** 4))[0]),
        ("[C8] [B] with a pair rounded down below the upper bounds",
         lambda: check(pi, XI_STATED, eps, bound, dl=F("0.007275870559"), dr=F("0.492684058988"),
                       xi_cap=XI_STATED)[0]),
    ]
    for name, f in controls:
        r = f()
        print(f"{name}: {'accepted (CONTROL FAILED)' if r else 'rejected (ok)'}")
        ok &= not r

    print("CERTIFICATE PASS" if ok else "CERTIFICATE FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
