"""Exact check of the Ye-Li Sec. 3.5 EXACT_Z circuit (arXiv 2610.10446v1) at small n, our reimplementation.

Rows x in {0,1}^n; queries y with #0 = #1 = n/4, n/2 stars; f_y(x) = 1 iff x matches y on S(y).
Parameters as integers: A = an, B = bn. The random orderings of the paper are replaced by deterministic
greedy covers (this also shows the covers can be found without randomness, at cost poly(2^n)):
  calD     : B-subsets D; D(y) = first D in calD leaving exactly A zeros and A ones of y outside D.
  calQ[D,u]: 2u-subsets of comp(D) covering every u-subset of comp(D), u = |U| in [A, 2A];
             Q(U) = first member of calQ[D,u] containing U.
Gates (D,Q,sigma), sigma in {0,1}^{D u Q}:  L[x,g] = [x|_{DuQ} = sigma],
  R[g,y] = [D = D(y)] f_{y|D}(sigma|D) * sum_{U: A1 <= U <= A1 u A0, Q(U)=Q} (-1)^{|U|-A} prod_{i in U} sigma_i.
Checks (exit 0 = all pass):
  1. (L R)[x,y] = f_y(x) over Z, evaluated gate by gate from the sparse L and R (all rows; all queries at
     n = 8, a fixed sample of queries at n = 12);
  2. per colour (u, w = #1(sigma|Q)): actual right degree <= 2^{stars in D} C(A,u-A) C(u,w-u) (paper's bound),
     and all nonzero right coefficients of a colour have sign (-1)^{u-A};
  3. negative controls must FAIL check 1: 'double' assigns each U to every covering Q (double counting),
     'drop' removes one lookup set that some U needs.
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
    """Deterministic greedy set cover; covers(c, e) -> bool. Returns ordered list of chosen candidates."""
    left = set(universe); out = []
    cov = {c: {e for e in universe if covers(c, e)} for c in cands}
    while left:
        c = max(cands, key=lambda c: (len(cov[c] & left), -c))
        got = cov[c] & left
        assert got, "cover impossible"
        out.append(c); left -= got
    return out

def build(n, A, B):
    full = (1 << n) - 1
    queries = []
    for z in subsets(range(n), n // 4):
        rest = [i for i in range(n) if not z >> i & 1]
        for o in subsets(rest, n // 4):
            queries.append((z, o))
    def ok_D(D, y):
        z, o = y; out = full & ~D
        return popc(z & out) == A and popc(o & out) == A
    calD = greedy_cover(queries, list(subsets(range(n), B)), ok_D)
    calQ = {}
    for D in calD:
        comp = [i for i in range(n) if not D >> i & 1]
        for u in range(A, 2 * A + 1):
            if 2 * u > len(comp): continue
            us = list(subsets(comp, u))
            calQ[D, u] = greedy_cover(us, list(subsets(comp, 2 * u)), lambda Q, U: U & Q == U)
    return queries, calD, calQ

def D_of(y, calD, n, A):
    full = (1 << n) - 1; z, o = y
    for D in calD:
        out = full & ~D
        if popc(z & out) == A and popc(o & out) == A: return D
    raise AssertionError("query not covered")

def right_column(y, n, A, calD, calQ, mode="ok"):
    """Sparse R column: {(D,Q,sigma): coef}. sigma stored as the bitmask of ones inside D u Q."""
    full = (1 << n) - 1; z, o = y
    D = D_of(y, calD, n, A)
    A1, A0 = o & ~D, z & ~D
    starsD = [i for i in bits(D & ~(z | o))]
    col = {}
    for W in (w for k in range(A + 1) for w in subsets(list(bits(A0)), k)):
        U = A1 | W; u = popc(U); sign = (-1) ** (u - A)
        Qs = [Q for Q in calQ[D, u] if U & Q == U]
        if mode == "double": targets = Qs
        else: targets = Qs[:1]
        if mode == "drop" and targets and targets[0] == calQ[D, u][-1]: targets = []
        for Q in targets:
            free = [i for i in bits(Q & ~U)]
            for k in range(len(free) + 1):
                for F in subsets(free, k):
                    for s in range(len(starsD) + 1):
                        for S in subsets(starsD, s):
                            sigma = o & D | S | U | F       # ones: y's ones in D, chosen stars, U, extra
                            g = (D, Q, sigma)
                            col[g] = col.get(g, 0) + sign
    return D, {g: c for g, c in col.items() if c}

def check_product(n, A, queries, calD, calQ, mode):
    """Return number of (x,y) entries where (LR)[x,y] != f_y(x)."""
    bad = 0
    for y in queries:
        z, o = y
        D, col = right_column(y, n, A, calD, calQ, mode)
        byQ = {}
        for (Dg, Q, sigma), c in col.items():
            byQ.setdefault(Q, {})[sigma] = c
        for x in range(1 << n):
            # gates incident to x with D = D(y): (D, Q, x|_{DuQ}) for every Q; others have R = 0
            val = sum(tab.get(x & (D | Q), 0) for Q, tab in byQ.items())
            f = 1 if (x & o) == o and (x & z) == 0 else 0
            if val != f: bad += 1
    return bad

def run(n, A, B, sample):
    ok = True
    queries, calD, calQ = build(n, A, B)
    qs = queries if sample is None else random.Random(1).sample(queries, sample)
    bad = check_product(n, A, qs, calD, calQ, "ok")
    print("n=%d A=%d B=%d |calD|=%d  queries checked %d x rows %d: mismatches %d"
          % (n, A, B, len(calD), len(qs), 1 << n, bad))
    ok &= bad == 0
    # degrees and signs per colour
    starsD = n // 2 - (n - B - 2 * A)
    worst = 0
    for y in qs:
        D, col = right_column(y, n, A, calD, calQ)
        cnt = {}
        for (Dg, Q, sigma), c in col.items():
            u = popc(Q) // 2; w = popc(sigma & Q)
            assert (c > 0) == ((u - A) % 2 == 0), "sign not uniform in colour"
            cnt[u, w] = cnt.get((u, w), 0) + 1
        for (u, w), k in cnt.items():
            bound = 2 ** starsD * comb(A, u - A) * comb(u, w - u)
            assert k <= bound, (u, w, k, bound)
            worst = max(worst, k / bound)
    print("  right degree <= paper bound for every colour (max ratio %.3f); colour signs uniform" % worst)
    # 'double' can only bite if some U lies in two lookup sets of its list (not the case at n = 8,
    # where the greedy lists are partitions); then it is reported but not required.
    multi = any(sum(1 for Q in lst if U & Q == U) > 1
                for (D, u), lst in calQ.items()
                for U in subsets([i for i in range(n) if not D >> i & 1], u))
    for mode in ("double", "drop"):
        b2 = check_product(n, A, qs, calD, calQ, mode)
        need = mode == "drop" or multi
        print("  control %-6s mismatches %d (%s)" % (mode, b2, "must be > 0" if need else "vacuous: lists are partitions"))
        ok &= b2 > 0 or not need
    return ok

if __name__ == "__main__":
    ok = run(8, 1, 4, None)          # a = 1/8, b = 1/2: 4a <= 1-b < 1/2 + 2a
    ok &= run(12, 1, 6, 400)         # a = 1/12, b = 1/2
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
