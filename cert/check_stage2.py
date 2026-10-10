"""Brute-force check of the deterministic wrapper DET2 of PROOF.md (Sec. 4) on small n.

Logic check only, not asymptotics. Written from PROOF.md; imports nothing from the other scripts and
runs no third-party code. Pure standard library, single core, well under 1 GB, about a minute.

STAND-IN FOR THE HARDCODED CIRCUIT. The real partial-match algorithm of Ye-Li (Def. 2.1, Prop. 4.2)
hardcodes a circuit that is only shown to exist (PROOF.md Sec. 8), so it cannot be run. Here the keyed
partial-match count is done through the same label-sum interface as Ye-Li Cor. 3.3, but with the TRIVIAL
exact circuit (exponent pair (0, 1/2)): a row x has the single gate x, a query y has one gate per
completion of its wildcards. Its count is exact, which is all DET2's correctness uses; its speed is not
the one Prop. 4.2 gives, which only the running time uses. Every count is cross-checked by direct
arithmetic (a + b in {0,1}^m on the prefix), which also checks the dummy padding (Lemma 3.2).

Asserted on every instance (exit 1 on any failure):
  * DET2 answers exactly as brute force; both branches (few sums, many sums) are run on every instance
    and each must agree with brute force; a found solution is verified;
  * Lemma 3.3: every c_pre has a layer j <= m/2 with |K(c_pre, j)| >= N/(m+2);
  * Lemma 3.4: |K mod p| >= |K|^2/(|K| + coll_p) for every (c_pre, j); with coll_p <= 3N, >= |K|^2/(4N);
  * Step 3: the layer families T_j (defined by '>= D residues') cover every c_pre;
  * Lemma 2.1: each R_j covers T_j x Z_p, exhaustively, and |R_j| <= ceil((p/D) ln|U|);
  * Lemma 2.2: the averaging bound p * sum_{r in C_j} w(r) <= |R_j| * sum_r w(r), in integers;
  * the class sizes from the convolution route of Step 4 equal the direct histograms;
  * Step 5: the MITM generation produces exactly the records whose key residue is in C_j (as multisets);
  * Lemma 5.2 directly: for every solution c and every layer j with c_pre in T_j, a correct pair of c is kept;
  * run 1 only (the true prime range P0 = N(b+1)): the prime has coll_p <= 3N, and the number of primes
    in [P0, 2 P0] with coll_p > 3N is below the counting bound N(b+1)/(3 log2 P0) of Lemma 2.3.
Negative controls (each must fail somewhere):
  * 'sigma'   : one covering of the translates of Sigma mod p, reused in every layer (ignores c_pre): misses;
  * 'single'  : only the cheapest residue class per layer, no covering: misses;
  * 'nocompat': the count ignores compatibility (equal keys only): false positives.
Run 1 (n=10, m=4) and run 2 (n=13, m=6) have m > n/3, outside Lemma 3.5's hypothesis: they are LOGIC-ONLY runs.
Run 3 (n=18, m=6) is inside the hypothesis, uses the proof's prime range and must filter at least one layer.
Also: Lemma 9.1 at gate level on P_{4,1/2} and P_{6,1/2}: a real depth-2 window circuit (gates = strings,
R[gate, q] = gate completes q), the FULL group (all permutations and flips), random g_i, the 2^J - 1 signed
restricted copies built gate by gate, L R multiplied out and compared with M; control 'plainsum' (no signs) must differ.
"""
import itertools
import math
import random
import sys

DLP, DRP = 0.007275870560, 0.492684058989   # rational pair of PROOF.md (only used to choose l_j)
FAIL = []


def req(cond, msg):
    if not cond:
        FAIL.append(msg)
        raise AssertionError(msg)


def is_prime(q):
    if q < 2:
        return False
    i = 2
    while i * i <= q:
        if q % i == 0:
            return False
        i += 1
    return True


def subset_sums(vals):
    out = [0]
    for v in vals:
        out = out + [s + v for s in out]
    return out          # index = mask over vals


def popc(x):
    return bin(x).count("1")


def H(s):
    return 0.0 if s <= 0 or s >= 1 else -s * math.log2(s) - (1 - s) * math.log2(1 - s)


def bits(z, tau):
    return (abs(tau) + sum(abs(v) for v in z) + 1).bit_length()


def coll(vals, p):
    c = {}
    for v in vals:
        c[v % p] = c.get(v % p, 0) + 1
    return sum(k * (k - 1) for k in c.values())


def cyc_conv(f, g, p):
    out = [0] * p
    fi = [(i, x) for i, x in enumerate(f) if x]
    gi = [(j, y) for j, y in enumerate(g) if y]
    for i, x in fi:
        for j, y in gi:
            out[(i + j) % p] += x * y
    return out


def hist(vals, p, neg=False):
    h = [0] * p
    for v in vals:
        h[(-v if neg else v) % p] += 1
    return h


# ---------------------------------------------------------------- covering (Lemma 2.1)
def greedy_cover(fam, p):
    """fam: list of residue sets K_T. Return R covering every (T, y), y in Z_p (r - y in K_T).
    Greedy: most newly covered pairs, ties to the least residue."""
    unc = [[True] * p for _ in fam]
    cnt = [sum(len(K) for K in fam)] * p
    left = len(fam) * p
    R = []
    while left:
        top = max(cnt)
        assert top > 0
        r = cnt.index(top)
        R.append(r)
        for K, U in zip(fam, unc):
            for k in K:
                y = (r - k) % p
                if U[y]:
                    U[y] = False
                    left -= 1
                    for k2 in K:
                        cnt[(y + k2) % p] -= 1
    return R


# ---------------------------------------------------------------- brute force
def brute_solutions(z, tau):
    s = subset_sums(z)
    return [c for c in range(1 << len(z)) if s[c] == tau]


# ---------------------------------------------------------------- few-sums branch (Step 2)
def few_sums(z, tau, m):
    n = len(z)
    pre = subset_sums(z[:m])
    rep = {}
    for a, v in enumerate(pre):
        rep.setdefault(v, a)
    N = len(rep)
    lp = max(0, (n - m - math.ceil(math.log2(N))) // 2)
    blk, rest = z[m:m + lp], z[m + lp:]
    sb, sr = subset_sums(blk), subset_sums(rest)
    L2 = {}
    for y, v in enumerate(sr):
        L2.setdefault(v, y)
    for v, a in rep.items():
        for x, w in enumerate(sb):
            y = L2.get(tau - v - w)
            if y is not None:
                return a | (x << m) | (y << (m + lp))
    return None


# ---------------------------------------------------------------- the trivial exact circuit (stand-in)
def completions(q):
    stars = [i for i, ch in enumerate(q) if ch == "*"]
    base = [0 if ch == "*" else int(ch) for ch in q]
    for bitsv in itertools.product((0, 1), repeat=len(stars)):
        x = list(base)
        for i, bv in zip(stars, bitsv):
            x[i] = bv
        yield tuple(x)


def pm_count(Arecs, Brecs):
    """Keyed partial-match count via labels (key, gate), as in Ye-Li Cor. 3.3, trivial circuit."""
    lab = {}
    for row, key in Arecs:
        lab.setdefault((key, row), [0, 0])[0] += 1
    tot = 0
    for q, key in Brecs:
        for g in completions(q):
            e = lab.get((key, g))
            if e:
                tot += e[0]
    return tot


# ---------------------------------------------------------------- many-sums branch (Steps 3-6)
def many_sums(z, tau, m, P0mode, Dmode, control=None, sols=(), stats=None):
    n = len(z)
    b = bits(z, tau)
    pre = subset_sums(z[:m])
    Sigma = sorted(set(pre))
    N = len(Sigma)
    # Step 3a: prime with coll_p <= 3N, scanning [P0, 2 P0]
    P0 = N * (b + 1) if P0mode == "true" else 2 * N
    p = next(q for q in itertools.count(P0) if is_prime(q) and coll(Sigma, q) <= 3 * N)
    cp = coll(Sigma, p)
    if P0mode == "true" and stats is not None:
        req(p <= 2 * P0, "no good prime in [P0, 2P0]")
        bad = sum(1 for q in range(P0, 2 * P0 + 1) if is_prime(q) and coll(Sigma, q) > 3 * N)
        req(bad < N * (b + 1) / (3 * math.log2(P0)), "bad-prime count above Lemma 2.3 bound")
        stats["bad"] = max(stats.get("bad", 0), bad)
    # Step 3b: layer sets
    layers = range(m // 2 + 1)
    Kint = {}
    for c in range(1 << m):
        for j in layers:
            Kint[c, j] = {pre[a] for a in range(1 << m) if popc(a ^ c) == j}
    Kmod = {key: {v % p for v in S} for key, S in Kint.items()}
    for c in range(1 << m):
        req(max(len(Kint[c, j]) for j in layers) * (m + 2) >= N, "Lemma 3.3")
        for j in layers:
            K = len(Kint[c, j])
            req(len(Kmod[c, j]) * (K + cp) >= K * K, "Lemma 3.4 (Cauchy-Schwarz)")
            req(len(Kmod[c, j]) * 4 * N >= K * K, "Lemma 3.4 (|K|^2/4N)")
    if Dmode == "proof":
        D = -(-N // (4 * (m + 2) ** 2))
    else:   # the largest D for which the families still cover every c_pre
        D = min(max(len(Kmod[c, j]) for j in layers) for c in range(1 << m))
    D = max(D, 1)
    T = {j: [c for c in range(1 << m) if len(Kmod[c, j]) >= D] for j in layers}
    req(set().union(*map(set, T.values())) == set(range(1 << m)), "families T_j cover all c_pre")
    # Step 3c: coverings
    if control == "sigma":
        R0 = greedy_cover([{v % p for v in Sigma}], p)
        Rj = {j: R0 for j in layers}
    else:
        Rj = {}
        for j in layers:
            fam = [Kmod[c, j] for c in T[j]]
            Rj[j] = greedy_cover(fam, p) if fam else []
            if fam and control is None:
                for c in T[j]:
                    for y in range(p):
                        req(any((r - y) % p in Kmod[c, j] for r in Rj[j]), "covering (i)")
                U = len(fam) * p
                req(len(Rj[j]) <= max(1, math.ceil(p / D * math.log(U))), "covering size (ii)")
    if stats is not None and control is None:
        stats["lay"] = stats.get("lay", 0) + sum(1 for j in layers if Rj[j])
        stats["filt"] = stats.get("filt", 0) + sum(1 for j in layers if Rj[j] and len(Rj[j]) < p)
    found = None
    total_kept = total_full = 0
    for j in layers:
        if not Rj[j]:
            continue
        s = j / m
        npr = 2 * m - 2 * j
        ell = int(math.floor(0.5 * (n - 2 * m + (H(s) + s) * m + 2 * (1 - s) * (DRP - DLP) * m)))
        ell = min(max(ell, 0), n - m)
        b1, b2 = z[m:m + ell], z[m + ell:]
        s1, s2 = subset_sums(b1), subset_sums(b2)
        rp = [(pos, neg) for pos in range(1 << m) for neg in range(1 << m)
              if not pos & neg and popc(pos | neg) == j]
        # Step 4: class sizes through the convolution route, checked against direct histograms
        h_pre = hist(pre, p)
        h1 = cyc_conv(hist(subset_sums(b1[:len(b1) // 2]), p), hist(subset_sums(b1[len(b1) // 2:]), p), p)
        hA = cyc_conv(h_pre, h1, p)
        h_rpre = hist([pre[pos] - pre[neg] for pos, neg in rp], p)
        h2 = cyc_conv(hist(subset_sums(b2[:len(b2) // 2]), p), hist(subset_sums(b2[len(b2) // 2:]), p), p)
        hBv = cyc_conv(h_rpre, h2, p)                     # histogram of b.z
        hB = [hBv[(tau - r) % p] for r in range(p)]       # right key tau - b.z = r
        dA = hist([pre[a] + v for a in range(1 << m) for v in s1], p)
        dB = hist([tau - (pre[pos] - pre[neg]) - v for pos, neg in rp for v in s2], p)
        req(hA == dA and hB == dB, "convolution histograms")
        wL, wR = 1, 2 ** (npr // 2)                      # stand-in pair (0, 1/2)
        w = [wL * hA[r] + wR * hB[r] for r in range(p)]
        R = Rj[j]
        if control == "single":
            R = [min(range(p), key=w.__getitem__)]
        sig = min(range(p), key=lambda t: sum(w[(r + t) % p] for r in R))
        C = {(r + sig) % p for r in R}
        kept = sum(w[r] for r in C)
        if control is None:
            req(p * kept <= len(R) * sum(w), "averaging (Lemma 2.2)")
        total_kept += kept
        total_full += sum(w)
        # Step 5: MITM generation of the kept records
        h0 = m // 2
        pre_lo, pre_hi = subset_sums(z[:h0]), subset_sums(z[h0:m])
        e1 = len(b1) // 2
        s1lo, s1hi = subset_sums(b1[:e1]), subset_sums(b1[e1:])
        list1 = {}
        for a1, v in enumerate(pre_lo):
            for x1, u in enumerate(s1lo):
                list1.setdefault((v + u) % p, []).append((a1, x1, v + u))
        genA = []
        for a2, v in enumerate(pre_hi):
            for x2, u in enumerate(s1hi):
                k2 = v + u
                for r in C:
                    for a1, x1, k1 in list1.get((r - k2) % p, []):
                        genA.append((a1 | (a2 << h0), x1 | (x2 << e1), k1 + k2))
        e2 = len(b2) // 2
        s2lo, s2hi = subset_sums(b2[:e2]), subset_sums(b2[e2:])

        def tern(lo, hi):
            out = []
            for pos in range(1 << (hi - lo)):
                for neg in range(1 << (hi - lo)):
                    if pos & neg == 0 and popc(pos | neg) <= j:
                        out.append((pos, neg, sum(z[lo + i] for i in range(hi - lo) if pos >> i & 1)
                                    - sum(z[lo + i] for i in range(hi - lo) if neg >> i & 1)))
            return out
        rlist1 = {}
        for pos, neg, v in tern(0, h0):
            for y1, u in enumerate(s2lo):
                rlist1.setdefault((popc(pos | neg), (v + u) % p), []).append((pos, neg, y1, v + u))
        genB = []
        for pos2, neg2, v in tern(h0, m):
            for y2, u in enumerate(s2hi):
                k2 = v + u
                g = j - popc(pos2 | neg2)
                if g < 0:
                    continue
                for r in C:
                    for pos1, neg1, y1, k1 in rlist1.get((g, (tau - r - k2) % p), []):
                        genB.append((pos1 | (pos2 << h0), neg1 | (neg2 << h0), y1 | (y2 << e2), tau - k1 - k2))
        bfA = [(a, x, pre[a] + s1[x]) for a in range(1 << m) for x in range(1 << len(b1))
               if (pre[a] + s1[x]) % p in C]
        bfB = [(pos, neg, y, tau - (pre[pos] - pre[neg]) - s2[y]) for pos, neg in rp
               for y in range(1 << len(b2)) if (tau - (pre[pos] - pre[neg]) - s2[y]) % p in C]
        req(sorted(genA) == sorted(bfA) and sorted(genB) == sorted(bfB), "MITM generation")
        # Lemma 5.2 directly: every solution c with c_pre in T_j has a kept correct pair in layer j
        if control is None:
            keptA = {(a, x) for a, x, _ in genA}
            for csol in sols:
                cpre = csol & ((1 << m) - 1)
                if cpre not in T[j]:
                    continue
                cx = (csol >> m) & ((1 << ell) - 1)
                req(any(popc(a ^ cpre) == j and (a, cx) in keptA for a in range(1 << m)), "Lemma 5.2")
        # Step 6: padded rows and queries; keyed count; cross-check by direct arithmetic
        dummy = m - 2 * j

        def row(a):
            return tuple([1] * dummy + [a >> i & 1 for i in range(m)])

        def query(pos, neg):
            q = "1" * dummy + "".join("0" if pos >> i & 1 else "1" if neg >> i & 1 else "*" for i in range(m))
            req(len(q) - q.count("*") == npr // 2, "half the query positions specified")
            return q
        Ar = [(row(a), k) for a, x, k in genA]
        Br = [(query(pos, neg), k) for pos, neg, y, k in genB]
        if control == "nocompat":
            byk = {}
            for _, k in Ar:
                byk[k] = byk.get(k, 0) + 1
            cnt = sum(byk.get(k, 0) for _, k in Br)
        else:
            cnt = pm_count(Ar, Br)
            direct = 0
            byk = {}
            for a, x, k in genA:
                byk.setdefault(k, []).append(a)
            for pos, neg, y, k in genB:
                for a in byk.get(k, []):
                    if a & pos == 0 and neg & ~a == 0:   # a + b in {0,1} on the prefix
                        direct += 1
            req(cnt == direct, "keyed count = direct count (padding, Lemma 3.2)")
        if cnt > 0 and found is None:
            if control == "nocompat":
                found = -1
                continue
            # recovery by bisection on the two record lists
            A_, B_ = list(zip(genA, Ar)), list(zip(genB, Br))
            while len(A_) > 1:
                half = A_[:len(A_) // 2]
                A_ = half if pm_count([r for _, r in half], [r for _, r in B_]) > 0 else A_[len(A_) // 2:]
            while len(B_) > 1:
                half = B_[:len(B_) // 2]
                B_ = half if pm_count([r for _, r in A_], [r for _, r in half]) > 0 else B_[len(B_) // 2:]
            (a, x, _), _ = A_[0]
            (pos, neg, y, _), _ = B_[0]
            cpre = (a | pos) & ~neg
            found = cpre | (x << m) | (y << (m + ell))
    if stats is not None:
        stats["kept"] = stats.get("kept", 0) + total_kept
        stats["full"] = stats.get("full", 0) + total_full
    return found


def is_solution(z, tau, c):
    return c is not None and c >= 0 and sum(z[i] for i in range(len(z)) if c >> i & 1) == tau


def gen(rng, n, m, kind):
    if kind == "random":
        z = [rng.randrange(1, 1 << 30) for _ in range(n)]
    elif kind == "small":
        z = [rng.randrange(1, 40) for _ in range(n)]
    elif kind == "mult":
        z = [667 * rng.randrange(1, 1 << 10) for _ in range(n)]
    elif kind == "pow2":
        z = [1 << i for i in range(m)] + [rng.randrange(1, 1 << 20) for _ in range(n - m)]
    elif kind == "neg":
        z = [rng.randrange(-(1 << 20), 1 << 20) for _ in range(n)]
    else:  # "gap": a prefix with few distinct sums
        z = [rng.choice([1, 2, 3, 5]) * 1000 for _ in range(m)] + [rng.randrange(1, 1 << 16) for _ in range(n - m)]
    if rng.random() < 0.65:
        tau = sum(v for v in z if rng.random() < 0.5)
    else:
        tau = rng.randrange(min(0, sum(z)), max(1, sum(abs(v) for v in z)))
    return z, tau


# ---------------------------------------------------------------- Lemma 9.1 (inclusion-exclusion, gate level)
def check_ie(n, eps_w, rng, jcap=11, pool=1):
    """Lemma 9.1 on P_{n,1/2} with a REAL depth-2 window circuit, the FULL symmetry group and random g_i.

    * X = {0,1}^n, Y = half-stars queries, M[x,q] = 1 iff x matches q on the specified positions.
    * G = all coordinate permutations combined with all flips (flip a bit of x, and the same bit of q if it is
      specified). It is transitive on X and on Y, and preserves M (checked on 20 randomly sampled (x, q) pairs per drawn g; the entry-by-entry product check
      would catch any error that sampling missed).
    * Scope: n = 4 lies outside the lemma's hypothesis 2 eta < 1 (the window is 6 of 16 rows), and at n = 6 the
      J used is below the J bound of part (a). So this tests parts (b)-(d), not the J bound in (a).
    * Window W = X0 x Y0 (binomial window). The circuit C of W is genuine gate level: its gates are the strings
      of {0,1}^n; the left matrix is L[x, gate x] = 1 for x in X0; the right matrix is R[gate, q] = 1 iff the
      gate is a completion of q (wildcards filled in), for q in Y0. So L R = M on W, and 0 off W, and the
      right side is NOT read off M.
    * g_1..g_J are drawn uniformly from G (no search among the group elements) until the g_i W cover X x Y;
      a draw sequence that needs more than jcap group elements is discarded and redrawn.
    * The 2^J - 1 copies g_{i_S} C are built by transporting gates and entries, restricted to X_S x Y_S, with the
      sign on the left; the sum is formed gate by gate (gates tagged by S) and L R is MULTIPLIED OUT and compared
      with M entry by entry. Degrees of every copy are compared with those of C.
    Control 'plainsum': the same circuits without the signs (must not equal M)."""
    rows = list(itertools.product((0, 1), repeat=n))
    queries = [q for q in itertools.product("01*", repeat=n) if q.count("*") == n // 2]
    ridx = {x: i for i, x in enumerate(rows)}
    qidx = {q: i for i, q in enumerate(queries)}

    def matches(x, q):
        return all(ch == "*" or int(ch) == xi for xi, ch in zip(x, q))
    M = {(x, q): int(matches(x, q)) for x in rows for q in queries}
    X0 = {x for x in rows if abs(sum(x) - n / 2) <= eps_w}
    Y0 = {q for q in queries if abs(q.count("0") - n / 4) <= eps_w and abs(q.count("1") - n / 4) <= eps_w}

    def completions_of(q):
        return list(completions("".join(q)))
    # the window circuit C: L[x] = {gate x: 1}; R[gate][q] = 1 iff gate completes q
    R0 = {}
    for q in Y0:
        for gate in completions_of(q):
            R0.setdefault(gate, {})[q] = 1
    L0 = {x: {x: 1} for x in X0}
    for x in X0:
        for q in Y0:       # L R = M on W
            assert sum(c * R0.get(gt, {}).get(q, 0) for gt, c in L0[x].items()) == M[x, q]
    ldeg0 = max(len(v) for v in L0.values())                       # gates per row
    rdeg0 = max(sum(1 for gt in R0 if q in R0[gt]) for q in Y0)    # gates per query

    def act_x(g, x):
        f, perm = g
        return tuple(x[perm[i]] ^ f[i] for i in range(n))

    def act_q(g, q):
        f, perm = g
        return tuple(q[perm[i]] if q[perm[i]] == "*" else str(int(q[perm[i]]) ^ f[i]) for i in range(n))

    def rand_g():
        perm = list(range(n))
        rng.shuffle(perm)
        return tuple(rng.randrange(2) for _ in range(n)), tuple(perm)

    while True:
        gs, unc = [], {(x, q) for x in rows for q in queries}
        imgs = []
        while unc and len(gs) <= jcap:
            g = rand_g()
            # invariance of M under g (checked on a sample of pairs)
            for _ in range(20):
                x, q = rng.choice(rows), rng.choice(queries)
                assert M[act_x(g, x), act_q(g, q)] == M[x, q], "M is not G-invariant"
            Xg = {act_x(g, x) for x in X0}
            Qg = {act_q(g, q) for q in Y0}
            imgs.append((g, Xg, Qg))
            unc = {(x, q) for (x, q) in unc if not (x in Xg and q in Qg)}
            gs.append(g)
        if not unc and len(gs) <= jcap:
            break
    J = len(imgs)

    def build(signed):
        tot = {}                      # (x, q) -> sum over gates and copies of L * R, multiplied out
        maxl = maxr = 0
        for k in range(1, J + 1):
            for sub in itertools.combinations(range(J), k):
                g = imgs[sub[0]][0]                       # g_{i_S}, i_S = least element of S
                XS = set.intersection(*[imgs[i][1] for i in sub])
                QS = set.intersection(*[imgs[i][2] for i in sub])
                sgn = (-1) ** (k + 1) if signed else 1
                # transported circuit g C: gates g(gate), L[g x] = {g(gate x): 1}, R[g(gate)][g q] = R0[gate][q]
                Lg = {}
                for x in X0:
                    gx = act_x(g, x)
                    if gx in XS:                           # restrict rows to X_S
                        Lg[gx] = {act_x(g, gt): sgn * c for gt, c in L0[x].items()}
                Rg = {}
                for gate, cols in R0.items():
                    for q, c in cols.items():
                        gq = act_q(g, q)
                        if gq in QS:                       # restrict columns to Y_S
                            Rg.setdefault(act_x(g, gate), {})[gq] = c
                maxl = max([maxl] + [len(v) for v in Lg.values()])
                cnt = {}
                for gate, cols in Rg.items():
                    for q in cols:
                        cnt[q] = cnt.get(q, 0) + 1
                maxr = max([maxr] + list(cnt.values()))
                for x, lrow in Lg.items():
                    for gate, c in lrow.items():
                        for q, d in Rg.get(gate, {}).items():
                            tot[x, q] = tot.get((x, q), 0) + c * d
        return tot, maxl, maxr
    tot, ml, mr = build(True)
    exact = all(tot.get(k, 0) == v for k, v in M.items()) and all(M.get(k, 0) == v for k, v in tot.items() if v)
    deg_ok = ml <= ldeg0 and mr <= rdeg0
    tot2, _, _ = build(False)
    plain = all(tot2.get(k, 0) == v for k, v in M.items())
    return J, exact, deg_ok, plain, len(X0), len(Y0)


def main():
    rng = random.Random(20261010)
    runs = [("run1", 10, 4, "true", "proof", 8), ("run2", 13, 6, "stand", "max", 8),
            ("run3", 18, 6, "true", "max", 4)]
    kinds = ["random", "small", "mult", "pow2", "neg", "gap"]
    ctl_bad = {"sigma": 0, "single": 0, "nocompat": 0}
    ok = True
    for name, n, m, P0mode, Dmode, per in runs:
        st = {}
        yes = misses = fps = 0
        for kind in kinds:
            for _ in range(per):
                z, tau = gen(rng, n, m, kind)
                sols = brute_solutions(z, tau)
                truth = bool(sols)
                yes += truth
                try:
                    f = few_sums(z, tau, m)
                    req((f is not None) == truth and (f is None or is_solution(z, tau, f)), "few-sums branch")
                    g = many_sums(z, tau, m, P0mode, Dmode, None, sols, st)
                    req((g is not None) == truth and (g is None or is_solution(z, tau, g)), "many-sums branch")
                except AssertionError as e:
                    ok = False
                    print("FAIL", name, kind, e)
                    continue
                for ctl in ctl_bad:
                    r = many_sums(z, tau, m, P0mode, Dmode, ctl, sols, None)
                    if ctl == "nocompat":
                        ctl_bad[ctl] += (r is not None and not truth)
                    else:
                        ctl_bad[ctl] += (r is None and truth)
        tot = len(kinds) * per
        inside = 3 * m <= n
        print(f"{name}: n={n} m={m} prime range={P0mode} D={Dmode}: {tot} instances, {yes} yes; "
              f"both branches exact; kept/full cost {st['kept'] / st['full']:.3f}; "
              f"layers filtered (R_j != Z_p): {st.get('filt', 0)}/{st.get('lay', 0)}; "
              f"inside Lemma 3.5 hypothesis m <= n/3: {'yes' if inside else 'NO (logic-only run)'}"
              + (f"; worst bad-prime count {st.get('bad', 0)}" if P0mode == "true" else ""))
        if name == "run3":
            ok &= inside and st.get("filt", 0) > 0     # run 3 must be inside the hypothesis and really filter
    # With the proof's own D = ceil(N / (4 (m+2)^2)) the filter is non-trivial (D >= 2) only once N > 4(m+2)^2
    # is possible, N <= 2^m: the least even m for which that happens.
    mstar = next(mm for mm in range(2, 40, 2) if 2 ** mm > 4 * (mm + 2) ** 2)
    print(f"proof's own D is 1 for every even m < {mstar}; D >= 2 first at m = {mstar} (n >= {3 * mstar}): "
          f"too large for the brute-force reference in pure Python (3^{mstar} right records, ~|T| p |K| greedy steps); "
          f"runs 1 and 3 use the proof's prime range, run 3 the largest D that still covers")
    ok &= mstar == 10
    print("controls (must be > 0):", ctl_bad)
    ok &= all(v > 0 for v in ctl_bad.values())
    for n, ew, seed in [(4, 0, 1), (6, 1, 2), (6, 1, 3)]:
        J, ie, deg, plain, nx, nq = check_ie(n, ew, random.Random(seed))
        print(f"Lemma 9.1, gate level, full group, random g_i, on P_{n},1/2 (window {nx} x {nq}): J = {J} group elements ({2 ** J - 1} copies); "
              f"L R multiplied out equals M: {ie}; copy degrees <= C's: {deg}; control plainsum equals M: {plain}")
        ok &= ie and deg and not plain
    if FAIL:
        ok = False
    print("CHECK PASS" if ok else "CHECK FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
