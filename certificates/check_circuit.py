"""Gate-level check of the generalised Ye-Li Sec. 3.5 circuit (PROOF.md Sec. 2.1): a0 != a1 outside counts and
lookup sets of size q(u) != 2u. Self-contained (standard library only).

Adapted from proofs/ye-li-audit/yl_circuit.py (ours). Generalisation:
  D(y): B-subset leaving exactly A0 zeros and A1 ones of y outside D;
  U ranges over A1(y) <= U <= A1(y) u A0(y), u = |U| in [A1, A1 + A0], sign (-1)^{u - A1};
  calQ[D,u]: q(u)-subsets of comp(D) covering every u-subset (greedy); Q(U) = first member containing U.
Checks (exit 0 = pass):
  1. (L R)[x,y] = f_y(x) over Z for every row and every (or sampled) central query;
  2. per colour (u, w = #1(sigma|Q)): right degree <= 2^{stars in D} C(A0, u - A1) C(q(u) - u, w - u),
     signs uniform per colour;
  3. negative control 'drop' (remove one needed lookup set) must FAIL check 1.
Run: nice -n 15 python3 -I check_circuit.py   (< 2 min, < 200 MB)
"""
import sys, random
from itertools import combinations
from math import comb


def popc(v): return bin(v).count("1")


def subsets(pos, k):
    for c in combinations(pos, k):
        m = 0
        for i in c: m |= 1 << i
        yield m


def bits(m):
    i = 0
    while m:
        if m & 1: yield i
        m >>= 1; i += 1


def greedy_cover(universe, cands, covers):
    left = set(universe); out = []
    cov = {c: {e for e in universe if covers(c, e)} for c in cands}
    while left:
        c = max(cands, key=lambda c: (len(cov[c] & left), -c))
        got = cov[c] & left
        assert got, "cover impossible"
        out.append(c); left -= got
    return out


def build(n, A0, A1, B, q):
    full = (1 << n) - 1
    queries = [(z, o) for z in subsets(range(n), n // 4)
               for o in subsets([i for i in range(n) if not z >> i & 1], n // 4)]
    ok_D = lambda D, y: popc(y[0] & full & ~D) == A0 and popc(y[1] & full & ~D) == A1
    calD = greedy_cover(queries, list(subsets(range(n), B)), ok_D)
    calQ = {}
    for D in calD:
        comp = [i for i in range(n) if not D >> i & 1]
        for u in range(A1, A1 + A0 + 1):
            assert q(u) <= len(comp)
            calQ[D, u] = greedy_cover(list(subsets(comp, u)), list(subsets(comp, q(u))), lambda Q, U: U & Q == U)
    return queries, calD, calQ


def right_column(y, n, A0, A1, calD, calQ, drop=False):
    full = (1 << n) - 1; z, o = y
    D = next(D for D in calD if popc(z & full & ~D) == A0 and popc(o & full & ~D) == A1)
    Ao, Az = o & ~D, z & ~D
    starsD = list(bits(D & ~(z | o)))
    col = {}
    for k in range(A0 + 1):
        for W in subsets(list(bits(Az)), k):
            U = Ao | W; u = popc(U); sign = (-1) ** (u - A1)
            Qs = [Q for Q in calQ[D, u] if U & Q == U][:1]
            if drop and Qs and Qs[0] == calQ[D, u][-1]: Qs = []
            for Q in Qs:
                free = list(bits(Q & ~U))
                for kk in range(len(free) + 1):
                    for F in subsets(free, kk):
                        for s in range(len(starsD) + 1):
                            for S in subsets(starsD, s):
                                g = (D, u, Q, o & D | S | U | F)
                                col[g] = col.get(g, 0) + sign
    return D, {g: c for g, c in col.items() if c}


def mismatches(n, A0, A1, qs, calD, calQ, drop=False):
    bad = 0
    for y in qs:
        z, o = y
        D, col = right_column(y, n, A0, A1, calD, calQ, drop)
        byQ = {}
        for (Dg, u, Q, sig), c in col.items():
            byQ.setdefault((u, Q), {})[sig] = c
        for x in range(1 << n):
            val = sum(tab.get(x & (D | Q), 0) for (u, Q), tab in byQ.items())
            bad += val != (1 if (x & o) == o and (x & z) == 0 else 0)
    return bad


def run(n, A0, A1, B, q, sample, label):
    queries, calD, calQ = build(n, A0, A1, B, q)
    qs = queries if sample is None else random.Random(1).sample(queries, sample)
    bad = mismatches(n, A0, A1, qs, calD, calQ)
    starsD = n // 2 - (n - B - A0 - A1)
    worst = 0
    for y in qs:
        D, col = right_column(y, n, A0, A1, calD, calQ)
        cnt = {}
        for (Dg, u, Q, sig), c in col.items():
            assert (c > 0) == ((u - A1) % 2 == 0), "sign not uniform in colour"
            w = popc(sig & Q); cnt[u, w] = cnt.get((u, w), 0) + 1
        for (u, w), k in cnt.items():
            bd = 2 ** starsD * comb(A0, u - A1) * comb(q(u) - u, w - u)
            assert k <= bd, (u, w, k, bd)
            worst = max(worst, k / bd)
    ctrl = mismatches(n, A0, A1, qs, calD, calQ, drop=True)
    ok = bad == 0 and ctrl > 0
    print(f"{label}: n={n} A0={A0} A1={A1} B={B} q={[q(u) for u in range(A1, A1 + A0 + 1)]} |calD|={len(calD)} "
          f"queries {len(qs)} x rows {1 << n}: mismatches {bad}; right-degree ratio max {worst:.3f}; "
          f"control drop {ctrl} -> {'PASS' if ok else 'FAIL'}")
    return ok


if __name__ == "__main__":
    r17 = lambda u: max(u + 1, round(1.7 * u))
    ok = run(8, 1, 1, 4, lambda u: 2 * u, None, "YL r=2 (control)")
    ok &= run(12, 2, 1, 6, r17, 300, "a0>a1, r~1.7")
    ok &= run(12, 1, 2, 6, r17, 300, "a1>a0, r~1.7")
    ok &= run(12, 2, 1, 5, lambda u: u + 1, 300, "a0>a1, q=u+1")
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
