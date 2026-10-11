"""Brute-force checks of the deterministic-specific claims of Stage 4 (PROOF.md). Logic at toy sizes, not asymptotics.

Parts (each with must-fail controls):
  A  splitter (Lemma 4.1): for every K of every size, at every node of the fixed split tree a cyclic window with the
     prescribed count exists (discrete IVT), and the leaf counts are the deterministic floor/ceil values.
  B  product round family (Lemmas 4.3-4.4) at M = 16, q = 2, N_b = 8, core a_b = 3, s = 1/3 (s != 1/2), non-core
     b_b = 1: every round is a valid round with x' - x = sigma, every K of every layer is covered, and the family
     size obeys the bound. Control: splitter forced to offset 0.
  C  the whole deterministic pipeline DET4 (Sec. 5) at n = 14, block M = 8, s = 1/3, against brute force:
     few/many sums, prime scan, the sets C_k, a REAL fixed round family F_k (greedy, q = 1) repeated D times,
     one residue per round chosen by the fixed-point pessimistic estimator (Lemma 5.4), the global shift,
     kept-record generation by meet in the middle, exact keyed counting, recovery. Two prime regimes:
       'proof': p in [P0, 2 P0], P0 = floor(T / (2(M+1))), the proof's regime (p <= |W_c|);
       'big'  : p >= 4T, so p >> T and one round's keys cover a tiny fraction of Z_p; the multiplicity D and the
                estimator do all the work.
       'tight': T = 100 and colliding block sums, with layer 4's threshold raised from N/(M+1) to the median key
                count (still >= N/(M+1), and C_3 = C_5 = cube keep every c in some C_k). C_4 is then a proper subset
                of the cube, so the restricted covering universe C_k x Z_p of Lemma 5.4 is actually exercised.
     Controls: nocompat, wrongcore (u's core gets (1-s)a non-stars: s and 1-s swapped), dropcover, lowmult (D = 1
     in the big regime), noparity (rounds only with x' = x, so odd layers have none), nofew.
  D  density-s block grouping (Lemma 3.2): sort-deal-pad with c = den(s) ceil(k/(s den(s))) padding positions.
  E  hole fixing at density s (Lemma 3.3 via S2 Lemma 9.1), gate level on P_{6,1/3} with the full group.
  F  the one-pass covering circuit with RANDOM designs of the proof's size (Lemma 3.5, A2): covering, left-degree
     concentration for every row, exactness and right degrees for every query (all 0/1 splits) at N = 10.
Run: nice -n 15 /usr/bin/python3 -E check_stage4.py   (about 6 min, < 300 MB)
"""
import bisect
import itertools
import math
import random
import sys
from fractions import Fraction as Fr

import numpy as np

FAILS = []


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        print("   FAIL:", msg)
    return cond


def is_prime(q):
    return q > 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))


# ===================================================================== A. splitter
def split_tree(q):
    """the fixed tree: q -> (floor(q/2), ceil(q/2))"""
    if q == 1:
        return None
    return (q // 2, split_tree(q // 2), q - q // 2, split_tree(q - q // 2))


def leaf_counts(k, q):
    """deterministic leaf counts: a node with q' leaves and count k' gives floor(k' q1/q') to the left child"""
    if q == 1:
        return [k]
    q1 = q // 2
    k1 = (k * q1) // q
    return leaf_counts(k1, q1) + leaf_counts(k - k1, q - q1)


def balance(Z, Kset, k, q, Nb, offset0=False):
    """Z: cyclically ordered coordinates of a node (len q Nb); returns a list of leaf pieces with the deterministic
    counts, or None if some node has no window with the prescribed count."""
    if q == 1:
        return [Z]
    q1 = q // 2
    want = (k * q1) // q
    m, ell = len(Z), q1 * Nb
    inK = [1 if z in Kset else 0 for z in Z]
    pre = [0]
    for b in inK + inK:
        pre.append(pre[-1] + b)
    offs = [0] if offset0 else range(m)
    for o in offs:
        if pre[o + ell] - pre[o] == want:
            left = [Z[(o + j) % m] for j in range(ell)]
            right = [Z[(o + ell + j) % m] for j in range(m - ell)]
            a = balance(left, Kset, want, q1, Nb, offset0)
            b = balance(right, Kset, k - want, q - q1, Nb, offset0)
            if a is None or b is None:
                return None
            return a + b
    return None


def S_split(q):
    return 0.0 if q == 1 else math.log2(q) + S_split(q // 2) + S_split(q - q // 2)


def part_A():
    print("A. splitter (Lemma 4.1)")
    total = 0
    for q, Nb in ((2, 4), (3, 3), (3, 4), (4, 3), (5, 2), (6, 2), (7, 2)):
        M = q * Nb
        bad = 0
        for mask in range(1 << M):
            K = {i for i in range(M) if mask >> i & 1}
            k = len(K)
            pieces = balance(list(range(M)), K, k, q, Nb)
            if pieces is None:
                bad += 1
                continue
            cnt = [len(K & set(P)) for P in pieces]
            ok = cnt == leaf_counts(k, q) and all(c in (k // q, -(-k // q)) for c in cnt) and \
                sorted(sum(pieces, [])) == list(range(M)) and all(len(P) == Nb for P in pieces)
            bad += not ok
            total += 1
        check(bad == 0, f"splitter q={q} N_b={Nb}: {bad} subsets unbalanced")
        print(f"   q={q} N_b={Nb} M={M}: all {1 << M} subsets K balanced to the deterministic counts: {bad == 0}; "
              f"S(q) = {S_split(q):.3f} <= 3q-3-2log2 q = {3 * q - 3 - 2 * math.log2(q):.3f}")
        check(S_split(q) <= 3 * q - 3 - 2 * math.log2(q) + 1e-9, f"S({q}) bound")
    # control: offset fixed to 0 (no splitter search) must leave subsets unbalanced
    q, Nb = 3, 4
    M = q * Nb
    ub = sum(balance(list(range(M)), {i for i in range(M) if mask >> i & 1},
                     bin(mask).count("1"), q, Nb, offset0=True) is None for mask in range(1 << M))
    print(f"   control offset0 (q=3, N_b=4): {ub} subsets unbalanced -> detected: {ub > 0}")
    check(ub > 0, "control offset0 not detected")


# ===================================================================== local rounds and greedy families
def local_rounds(Nb, ab):
    out = []
    for Hm in itertools.combinations(range(Nb), Nb // 2):
        Hb = [i for i in range(Nb) if i not in Hm]
        for Hc in itertools.combinations(Hm, ab):
            for Hbc in itertools.combinations(Hb, ab):
                out.append((frozenset(Hm), frozenset(Hc), frozenset(Hbc)))
    return out


def compat_local(Kl, R, sa, x, xp, Nb):
    Hm, Hc, Hbc = R
    Hn = Hm - Hc
    Hbn = frozenset(range(Nb)) - Hm - Hbc
    ab = len(Hc)
    return len(Kl & Hc) == sa and len(Kl & Hbc) == ab - sa and len(Kl & Hn) == x and len(Kl & Hbn) == xp


def greedy_family(Nb, ab, sa, kk, eps, rounds=None):
    """greedy cover of all kk-subsets of [Nb] by local rounds with x = (kk - ab - eps)/2, x' = x + eps.
    Returns (family, p_loc). Lemma 4.3: size <= floor(ln C(Nb, kk)/p_loc) + 1."""
    x = (kk - ab - eps) // 2
    xp = x + eps
    assert 2 * x + eps == kk - ab
    rounds = rounds or local_rounds(Nb, ab)
    Ks = [frozenset(c) for c in itertools.combinations(range(Nb), kk)]
    comp = [[j for j, K in enumerate(Ks) if compat_local(K, R, sa, x, xp, Nb)] for R in rounds]
    bb = Nb // 2 - ab
    p_loc = Fr(math.comb(ab, sa) * math.comb(ab, ab - sa) * math.comb(bb, x) * math.comb(bb, xp), math.comb(Nb, kk))
    # every K is compatible with exactly a p_loc fraction of the rounds (transitivity), checked here
    deg = [0] * len(Ks)
    for c in comp:
        for j in c:
            deg[j] += 1
    assert all(Fr(d, len(rounds)) == p_loc for d in deg), "p_loc formula"
    unc = set(range(len(Ks)))
    fam = []
    while unc:
        i = max(range(len(rounds)), key=lambda i: (sum(1 for j in comp[i] if j in unc), -i))
        fam.append(rounds[i])
        unc -= set(comp[i])
    assert len(fam) <= math.floor(math.log(len(Ks)) / p_loc) + 1, "Lemma 4.3 size bound"
    return fam, p_loc, x, xp


def eps_pattern(kis, ab):
    """odd pieces (k_i - a_b odd) get +1, -1, +1, ... in index order; even pieces 0 (Lemma 4.4)."""
    out, sgn = [], 1
    for ki in kis:
        if (ki - ab) % 2:
            out.append(sgn)
            sgn = -sgn
        else:
            out.append(0)
    return out


# ===================================================================== B. product family
def part_B():
    print("B. product round family (Lemmas 4.3-4.4): M=16, q=2, N_b=8, a_b=3, s=1/3, b_b=1")
    q, Nb, ab, sa = 2, 8, 3, 1
    bb = Nb // 2 - ab
    M, a, b = q * Nb, q * ab, q * bb
    rounds = local_rounds(Nb, ab)
    fams = {}
    for k in range(q * ab, q * (ab + 2 * bb) + 1):
        sigma = (k - a) % 2
        kis = leaf_counts(k, q)
        eps = eps_pattern(kis, ab)
        check(sum(eps) == sigma, f"eps pattern sum k={k}")
        loc = []
        for ki, e in zip(kis, eps):
            if (ki, e) not in fams:
                fams[(ki, e)] = greedy_family(Nb, ab, sa, ki, e, rounds)
            loc.append(fams[(ki, e)])
        x = sum(l[2] for l in loc)
        xp = sum(l[3] for l in loc)
        check(xp - x == sigma, f"x' - x = sigma at k={k}")
        # the family: every offset o (window of length 8 from o, cyclic) x product of local families
        fam, byoff = [], {}
        for o in range(M):
            P1 = [(o + j) % M for j in range(Nb)]
            P2 = [(o + Nb + j) % M for j in range(Nb)]
            for R1 in loc[0][0]:
                for R2 in loc[1][0]:
                    Hm = Hc = Hbc = 0
                    for P, R in ((P1, R1), (P2, R2)):
                        for j in R[0]:
                            Hm |= 1 << P[j]
                        for j in R[1]:
                            Hc |= 1 << P[j]
                        for j in R[2]:
                            Hbc |= 1 << P[j]
                    fam.append((Hm, Hc, Hbc))
                    byoff.setdefault(o, []).append((Hm, Hc, Hbc))
        full = (1 << M) - 1
        pc = lambda v: bin(v).count("1")
        valid = all(pc(Hm) == M // 2 and pc(Hc) == a and pc(Hbc) == a and Hc & ~Hm == 0 and Hbc & Hm == 0
                    for Hm, Hc, Hbc in fam)
        check(valid, f"invalid round in the family at k={k}")
        okr = lambda Km, R: (pc(Km & R[1]) == sa * q and pc(Km & R[2]) == a - sa * q and pc(Km & R[0] & ~R[1]) == x
                             and pc(Km & full & ~R[0] & ~R[2]) == xp)
        unc, mults = 0, []
        win = [sum(1 << ((o + j) % M) for j in range(Nb)) for o in range(M)]
        for ti, Kt in enumerate(itertools.combinations(range(M), k)):
            Km = sum(1 << i for i in Kt)
            bal = [o for o in range(M) if pc(Km & win[o]) == kis[0]]
            order = bal + [o for o in range(M) if o not in bal]
            hit = any(okr(Km, R) for o in order for R in byoff[o])   # global compatibility, checked directly
            unc += not hit
            if ti < 60:
                mults.append(sum(okr(Km, R) for R in fam))
        mult_min = min(mults)
        # size bound of Lemma 4.4 (before the parity/entropy step): #splitters * prod (1 + N_b ln 2) / p_loc_i,
        # and prod 1/p_loc_i <= ((a_b+1)(b_b+1))^{2(q-1)} / P_glob
        Pglob = Fr(math.comb(a, sa * q) * math.comb(a, a - sa * q) * math.comb(b, x) * math.comb(b, xp), math.comb(M, k))
        prod_inv = Fr(1)
        for l in loc:
            prod_inv /= l[1]
        okb = prod_inv <= Fr(((ab + 1) * (bb + 1)) ** (2 * (q - 1))) / Pglob
        nspl = M   # one internal node with q' = 2: q' N_b offsets
        okF = len(fam) <= nspl * math.prod(math.floor(math.log(math.comb(Nb, ki)) / l[1]) + 1 for ki, l in zip(kis, loc))
        check(unc == 0 and okb and okF, f"product family k={k}: uncovered {unc}, bounds {okb} {okF}")
        print(f"   k={k} sigma={sigma} pieces {kis} eps {eps} (x, x') = ({x}, {xp}): |F0| = {len(fam)}, every round "
              f"valid {valid}, {math.comb(M, k)} K all covered {unc == 0} (min multiplicity over 60 K: {mult_min}); "
              f"prod 1/p_loc <= ((a_b+1)(b_b+1))^2/P_glob {okb}")
    # control: offset 0 only (no splitter) leaves K uncovered
    k = 8
    kis = leaf_counts(k, q)
    eps = eps_pattern(kis, ab)
    loc = [fams[(ki, e)] for ki, e in zip(kis, eps)]
    K = frozenset(range(8))   # all of K in the first window: counts (8, 0)
    P1, P2 = list(range(8)), list(range(8, 16))
    covered = any(compat_local(frozenset(j for j in range(Nb) if P1[j] in K), R1, sa, loc[0][2], loc[0][3], Nb) and
                  compat_local(frozenset(j for j in range(Nb) if P2[j] in K), R2, sa, loc[1][2], loc[1][3], Nb)
                  for R1 in loc[0][0] for R2 in loc[1][0])
    print(f"   control offset0: K = first 8 coordinates covered: {covered} -> detected: {not covered}")
    check(not covered, "control offset0 (product) not detected")


# ===================================================================== C. the pipeline DET4
n, M = 14, 8
BLK = list(range(M))
UOUT = [8, 9, 10]
VOUT = [11, 12, 13]
AB, SA, BB = 3, 1, 1          # core a = 3, s a = 1 (s = 1/3), non-core b = 1 per side
T_PROOF = 253                  # C(8,2) = 28 < T/(M+1): the layer range is k in {3, 4, 5}
T_TIGHT = 100                  # regime 'tight': lower T, so inputs with colliding sums (varying key counts) are many-sums
LAYERS = (3, 4, 5)


def subset_sums(z, idx):
    best = {}
    for mask in range(1 << len(idx)):
        s = sum(z[idx[i]] for i in range(len(idx)) if mask >> i & 1)
        if s not in best or mask < best[s]:
            best[s] = mask
    return sorted(best.items())


def family_for(k, noparity=False):
    sigma = (k - AB) % 2
    if noparity and sigma:
        return [], None, None
    fam, _, x, xp = greedy_family(M, AB, SA, k, sigma)
    return [(tuple(sorted(Hm)), tuple(i for i in BLK if i not in Hm), tuple(sorted(Hc)), tuple(sorted(Hbc)), x, xp)
            for Hm, Hc, Hbc in fam], x, xp


def compat(f, K):
    H, Hb, Hc, Hbc, x, xp = f
    return (sum(i in K for i in Hc) == SA and sum(i in K for i in Hbc) == AB - SA
            and sum(i in K for i in H if i not in Hc) == x and sum(i in K for i in Hb if i not in Hbc) == xp)


def gen_lists(z, tau, f, wrongcore=False):
    """block parts and outer parts of U_f and V_f, each as a list of (key part, vector dict)."""
    H, Hb, Hc, Hbc, x, xp = f
    Hn = [i for i in H if i not in Hc]
    Hbn = [i for i in Hb if i not in Hbc]
    ucore = (AB - SA) if wrongcore else SA

    def signed(core, ncore, nonc, nnon, left_on):
        out = []
        for sup in itertools.combinations(core, ncore):
            for supn in itertools.combinations(nonc, nnon):
                S = list(sup) + list(supn)
                for sg in itertools.product((-1, 1), repeat=len(S)):
                    for lb in itertools.product((0, 1), repeat=len(left_on)):
                        v = {i: 0 for i in core + nonc}
                        v.update(zip(S, sg))
                        v.update(zip(left_on, lb))
                        out.append(v)
        return out

    Ub = signed(list(Hc), ucore, Hn, x, list(Hb))
    Vb = signed(list(Hbc), SA, Hbn, BB - xp, list(H))
    Uo = [dict(zip(UOUT, ob)) for ob in itertools.product((0, 1), repeat=len(UOUT))]
    Vo = [dict(zip(VOUT, ob)) for ob in itertools.product((0, 1), repeat=len(VOUT))]
    dot = lambda v: sum(v[i] * z[i] for i in v)
    return ([(dot(v), v) for v in Ub], [(dot(v), v) for v in Uo],
            [(-dot(v), v) for v in Vb], [(tau - dot(v), v) for v in Vo])


def kept(A, B, p, r):
    Bs = sorted(((kb % p, kb, vb) for kb, vb in B), key=lambda t: t[0])
    res = [t[0] for t in Bs]
    out = []
    for ka, va in A:
        want = (r - ka) % p
        j = bisect.bisect_left(res, want)
        while j < len(res) and res[j] == want:
            _, kb, vb = Bs[j]
            v = dict(va)
            v.update(vb)
            out.append((ka + kb, v))
            j += 1
    return out


def count_pairs(U, V, f, nocompat=False):
    H, Hb = f[0], f[1]
    byk = {}
    for kv, vv in V:
        byk.setdefault(kv, []).append(vv)
    cnt = 0
    for ku, vu in U:
        for vv in byk.get(ku, ()):
            if nocompat or (all(vv[i] + vu[i] in (0, 1) for i in H) and all(vu[i] + vv[i] in (0, 1) for i in Hb)):
                cnt += 1
    return cnt


def recover(U, V, f, nocompat):
    while len(U) > 1:
        h1 = U[:len(U) // 2]
        U = h1 if count_pairs(h1, V, f, nocompat) > 0 else U[len(U) // 2:]
    while len(V) > 1:
        h1 = V[:len(V) // 2]
        V = h1 if count_pairs(U, h1, f, nocompat) > 0 else V[len(V) // 2:]
    c = [0] * n
    for vec in (U[0][1], V[0][1]):
        for i in vec:
            c[i] += vec[i]
    return c


def estimator(Sres, p, D, nU, lowbits=False):
    """Lemma 5.4 with fixed-point weights. Sres[c][f0] = residue array of S_{c,f0} over the base family F0;
    the run family is F0 repeated D times (copy-major). Returns the chosen residues r_f (one per run round) and the
    number of uncovered (c, y) at the end."""
    C = len(Sres)
    F0 = len(Sres[0]) if C else 0
    Ftot = F0 * D
    if C == 0 or Ftot == 0:
        return [], C * p
    B = math.ceil(math.log2(4 * Ftot * Ftot * nU)) if not lowbits else 4
    assert B <= 50, B
    sizes = np.array([[len(Sres[c][f]) for f in range(F0)] for c in range(C)], dtype=np.int64)   # (C, F0)
    # w[f] = weights after round f (rounds 1..Ftot), backward: w_Ftot = 2^B, w_{f-1} = floor(w_f (p - |S_f|)/p)
    W = np.zeros((Ftot + 1, C), dtype=np.int64)
    W[Ftot] = 1 << B
    for f in range(Ftot, 0, -1):
        W[f - 1] = (W[f] * (p - sizes[:, (f - 1) % F0])) // p
    width = max(1, int(sizes.max()))
    Smat = np.full((F0, C, width), -1, dtype=np.int64)
    for c in range(C):
        for f in range(F0):
            for j, sres in enumerate(Sres[c][f]):
                Smat[f, c, j] = sres
    Unc = np.ones((C, p), dtype=bool)
    rgrid = np.arange(p)
    cidx = np.arange(C)[:, None]
    picks = []
    for f in range(1, Ftot + 1):
        S = Smat[(f - 1) % F0]
        score = np.zeros(p, dtype=np.int64)
        covs = []
        for j in range(width):
            col = S[:, j:j + 1]
            valid = (col >= 0)
            idx = (rgrid[None, :] - np.where(valid, col, 0)) % p     # residue r covers (c, y) with y = r - s
            g = Unc[cidx, idx] & valid
            covs.append((idx, g))
            score += (W[f][:, None] * g).sum(axis=0)
        r = int(np.argmax(score))      # least r among the maxima
        picks.append(r)
        for idx, g in covs:
            rows = np.nonzero(g[:, r])[0]
            Unc[rows, idx[rows, r]] = False
    return picks, int(Unc.sum())


def det4(z, tau, regime="proof", ctl=None, stats=None):
    Sig = subset_sums(z, BLK)
    N = len(Sig)
    T = T_TIGHT if regime == "tight" else T_PROOF
    if N <= T:
        if ctl == "nofew":
            return None
        outer = UOUT + VOUT
        l = max(0, (len(outer) - (N.bit_length() - 1)) // 2)
        L1 = sorted((s + sum(z[outer[i]] for i in range(l) if m2 >> i & 1), mb, m2) for s, mb in Sig
                    for m2 in range(1 << l))
        keys = [t[0] for t in L1]
        rest = outer[l:]
        for m3 in range(1 << len(rest)):
            want = tau - sum(z[rest[i]] for i in range(len(rest)) if m3 >> i & 1)
            j = bisect.bisect_left(keys, want)
            if j < len(keys) and keys[j] == want:
                _, mb, m2 = L1[j]
                c = [0] * n
                for i in range(M):
                    c[BLK[i]] = mb >> i & 1
                for i in range(l):
                    c[outer[i]] = m2 >> i & 1
                for i in range(len(rest)):
                    c[rest[i]] = m3 >> i & 1
                return c
        return None
    sums = [s for s, _ in Sig]
    Bbits = max(1, (max(sums) - min(sums)).bit_length())
    small_p = regime in ("proof", "tight")
    if small_p:
        P0 = T // (2 * (M + 1))
        cands = [q for q in range(P0, 2 * P0 + 1) if is_prime(q)]
    else:
        q = 4 * T
        while not is_prime(q):
            q += 1
        cands = [q]

    def coll(q):
        cnt = {}
        for s in sums:
            cnt[s % q] = cnt.get(s % q, 0) + 1
        return sum(v * (v - 1) // 2 for v in cnt.values())

    p = min(cands, key=lambda q: (coll(q), q))
    if small_p:   # Lemma 5.1: min collision count <= 2 ln 2 B N^2 / p
        check(coll(p) <= 2 * math.log(2) * Bbits * N * N / p, "prime collision bound")
    allc = list(itertools.product((0, 1), repeat=M))
    picks_all = {}
    # distinct keys of every block assignment c in every served layer k
    layer_vals = {}
    for k in LAYERS:
        Ks = [frozenset(K) for K in itertools.combinations(BLK, k)]
        for c in allc:
            e = [2 * ci - 1 for ci in c]
            vals = {}
            for K in Ks:
                vals.setdefault(sum(e[i] * z[i] for i in K), K)
            layer_vals[(k, c)] = vals
    # C_k := {c : layer k of c has >= theta_k distinct keys}. The proof takes theta_k = N/(M+1) (pigeonhole), and
    # Lemmas 5.2-5.4 use only (i) every c lies in some served C_k and (ii) theta_k >= N/(M+1), so a larger theta_k
    # that keeps (i) is just as valid. At toy sizes N/(M+1) is far below every layer's key count, so C_k is always the
    # whole cube; regime 'tight' raises theta_4 to the median key count of layer 4 (C_3 = C_5 = cube keep (i)). Then
    # C_4 is a proper subset and Lemma 5.4 really runs on the restricted universe C_4 x Z_p.
    theta = {k: Fr(N, M + 1) for k in LAYERS}
    if regime == "tight":
        cnt4 = sorted(len(layer_vals[(4, c)]) for c in allc)
        theta[4] = max(theta[4], Fr(cnt4[len(cnt4) // 2]))
    check(all(any(len(layer_vals[(k, c)]) >= theta[k] for k in LAYERS) for c in allc),
          "every c lies in some served C_k")
    stats["theta"] = theta
    for k in LAYERS:
        Ks = [frozenset(K) for K in itertools.combinations(BLK, k)]
        Ck, Wc = [], {}
        for c in allc:
            if len(layer_vals[(k, c)]) >= theta[k]:
                Ck.append(c)
                Wc[c] = layer_vals[(k, c)]
        ngood = len(Ck)
        stats.setdefault("Ck", []).append(len(Ck))
        F0, x, xp = family_for(k, noparity=(ctl == "noparity"))
        if F0 and small_p:
            g = coll(p) * p / (N * N)
            G = 1 + 2 * g * (M + 1) ** 2
            for c in Ck:
                Wp = len({v % p for v in Wc[c]})
                # Lemma 5.2 needs p <= |W_c| (true here); the general form min(p, |W_c|)/G is checked too
                check(len(Wc[c]) >= p and Wp >= p / G, "W'_c has >= p/G distinct residues")
                check(Wp >= min(p, len(Wc[c])) / G, "W'_c has >= min(p, |W_c|)/G distinct residues")
        Sres = []
        for c in Ck:
            e = [2 * ci - 1 for ci in c]
            row = []
            for f in F0:
                const = sum(c[i] * z[i] for i in f[1]) - sum(e[i] * z[i] for i in f[1])
                row.append(sorted({(const + sum(e[i] * z[i] for i in K)) % p for K in Ks if compat(f, K)}))
            Sres.append(row)
        nU = max(1, len(Ck) * p)
        if F0 and Ck:
            tot = [sum(len(s) for s in row) for row in Sres]
            Dneed = max(1, max(math.ceil(p * math.log(4 * nU) / t) for t in tot))
            if small_p:
                Dproof = math.ceil((2 * M + 2) * math.log(2) * G)
                check(Dneed <= Dproof, "the proof's multiplicity D suffices")
            D = 1 if ctl == "lowmult" else Dneed
            # Phi_0 <= 1/4 iff every c has sum_f |S_{c,f}| >= p ln(4|U|)
            phi0 = sum(p * math.exp(-D * t / p) for t in tot)
            stats.setdefault("phi0", []).append(phi0)
            if ctl != "lowmult":
                check(phi0 <= 0.25 + 1e-12, "Phi_0 <= 1/4")
            picks, left = estimator(Sres, p, D, nU)
        else:
            D, picks, left, phi0 = 0, [], len(Ck) * p, float("inf")
        stats.setdefault("uncovered", []).append(left)
        if regime == "tight" and picks and ngood < len(allc):
            # the cover is of C_k x Z_p only: count the (c, y) left uncovered for the c outside C_k, which the
            # estimator never targeted (evidence that the restricted universe is what was covered)
            out = 0
            for c in allc:
                if c in Wc:
                    continue
                e = [2 * ci - 1 for ci in c]
                cov = np.zeros(p, dtype=bool)
                for i, r in enumerate(picks):
                    f = F0[i % len(F0)]
                    const = sum(c[j] * z[j] for j in f[1]) - sum(e[j] * z[j] for j in f[1])
                    for K in Ks:
                        if compat(f, K):
                            cov[(r - const - sum(e[j] * z[j] for j in K)) % p] = True
                out += int((~cov).sum())
            stats["outside_unc"] = stats.get("outside_unc", 0) + out
            stats["outside_c"] = stats.get("outside_c", 0) + len(allc) - ngood
        if ctl not in ("lowmult", "noparity", "dropcover"):
            check(left == 0, f"covering incomplete at k={k}: {left}")
        run = [(F0[i % len(F0)], picks[i]) for i in range(len(picks))]
        if ctl == "dropcover" and run:
            # keep only the first pick (one round covers at most |S_{c,f}| <= 9 < p residues per c), then recount
            # the uncovered (c, y) from scratch; dropping a few late picks is NOT detected, because D > 1 copies
            # cover redundantly in the proof regime (that redundancy is the multiplicity at work)
            run = run[:1]
            cov = np.zeros((len(Ck), p), dtype=bool)
            for f, r in run:
                fi = F0.index(f)
                for ci in range(len(Ck)):
                    for sres in Sres[ci][fi]:
                        cov[ci, (r - sres) % p] = True
            stats["dropped_lost"] = stats.get("dropped_lost", 0) + int((~cov).sum())
        # global shift by exact residue histograms (translation invariance keeps the covering)
        hist = {}
        for f, _ in run:
            if f not in hist:
                Ub, Uo, Vb, Vo = gen_lists(z, tau, f)
                hu = np.bincount((np.add.outer([kk for kk, _ in Ub], [kk for kk, _ in Uo]) % p).ravel(), minlength=p)
                hv = np.bincount((np.add.outer([kk for kk, _ in Vb], [kk for kk, _ in Vo]) % p).ravel(), minlength=p)
                hist[f] = hu + hv
        if run:
            tot_t = np.zeros(p, dtype=np.int64)
            for f, r in run:
                tot_t += np.roll(hist[f], -r)        # tot_t[t] = sum_f hist_f[(r_f + t) % p]
            t = int(np.argmin(tot_t))
            check(tot_t[t] <= tot_t.mean() + 1e-9, "best shift <= average")
            stats.setdefault("rec", []).append((int(tot_t[t]), float(tot_t.mean())))
            run = [(f, (r + t) % p) for f, r in run]
        stats.setdefault("rounds", []).append((len(F0), D))
        picks_all[k] = run
    stats["layer_viol"] = stats.get("layer_viol", 0) + layer_check(z, tau, p, picks_all, ctl, theta)
    seen = set()
    for k in LAYERS:
        for f, r in picks_all[k]:
            if (f, r) in seen:
                continue
            seen.add((f, r))
            Ub, Uo, Vb, Vo = gen_lists(z, tau, f, wrongcore=(ctl == "wrongcore"))
            U = kept(Ub, Uo, p, r)
            V = kept(Vb, Vo, p, r)
            if len(seen) <= 3:   # meet in the middle on sorted residues returns exactly the direct filter
                direct = sorted(ka + kb for ka, _ in Ub for kb, _ in Uo if (ka + kb - r) % p == 0)
                check(sorted(kk for kk, _ in U) == direct, "kept() equals the direct filter")
            if count_pairs(U, V, f, nocompat=(ctl == "nocompat")) > 0:
                return recover(U, V, f, ctl == "nocompat")
    return None


def layer_check(z, tau, p, picks_all, ctl, theta):
    """every solution c* has, in some layer k with its block part in C_k... we test the stronger statement used by
    the proof: in EVERY layer k whose C_k contains the block part, some pick keeps a compatible representation."""
    viol = 0
    for mask in range(1 << n):
        c = [mask >> i & 1 for i in range(n)]
        if sum(a * b for a, b in zip(c, z)) != tau:
            continue
        e = [2 * ci - 1 for ci in c[:M]]
        y = sum(c[i] * z[i] for i in UOUT)
        for k in LAYERS:
            Ks = [frozenset(K) for K in itertools.combinations(BLK, k)]
            if len({sum(e[i] * z[i] for i in K) for K in Ks}) < theta[k]:
                continue
            found = False
            for f, r in picks_all.get(k, ()):
                H, Hb, Hc = f[0], f[1], f[2]
                const = sum(c[i] * z[i] for i in Hb) - sum(e[i] * z[i] for i in Hb)
                for K in Ks:
                    if not compat(f, K):
                        continue
                    # the representation's u: right numbers e_i on H cap K; it lies in U_f iff its non-star counts
                    # on Hc and on H \ Hc are the list's (s a and x); v likewise on Hbc and Hbar \ Hbc
                    ucore = (AB - SA) if ctl == "wrongcore" else SA
                    in_u = len(K & set(Hc)) == ucore and len(K & (set(H) - set(Hc))) == f[4]
                    in_v = len(set(f[3]) - K) == SA and len((set(Hb) - set(f[3])) - K) == BB - f[5]
                    if in_u and in_v and (const + sum(e[i] * z[i] for i in K) + y - r) % p == 0:
                        found = True
                        break
                if found:
                    break
            viol += not found
    return viol


def brute(z, tau):
    return any(sum(z[i] for i in range(n) if mask >> i & 1) == tau for mask in range(1 << n))


def instances(seed, per):
    rng = random.Random(seed)
    fams = {
        "large": lambda: [rng.randint(1, 1 << 20) for _ in range(n)],
        "signed": lambda: [rng.randint(-(1 << 18), 1 << 18) for _ in range(n)],
        "small": lambda: [rng.randint(1, 6) for _ in range(n)],
        "mixed": lambda: [rng.randint(1, 1 << 12) for _ in range(M)] + [rng.randint(1, 3) for _ in range(n - M)],
    }
    out = []
    for name, gen in fams.items():
        for _ in range(per):
            z = gen()
            c = [rng.randint(0, 1) for _ in range(n)]
            out.append((name, z, sum(a * b for a, b in zip(c, z))))
            out.append((name, z, rng.randint(min(0, sum(z)), max(0, sum(z)))))
    return out


def run_pipeline(inst, regime, ctl=None):
    stats = {}
    wrong = yes = 0
    for name, z, tau in inst:
        truth = brute(z, tau)
        yes += truth
        c = det4(z, tau, regime, ctl, stats)
        ok = (c is None and not truth) or (c is not None and all(x in (0, 1) for x in c)
                                           and sum(a * b for a, b in zip(c, z)) == tau)
        wrong += not ok
    return wrong, yes, stats


def part_C():
    print("C. the deterministic pipeline DET4 (n = 14, M = 8, s = 1/3, T = 253; regime 'tight': T = 100)")
    global FAILS
    inst = instances(7, 5)
    wrong, yes, st = run_pipeline(inst, "proof")
    print(f"   regime 'proof' (p in [P0, 2P0]): {len(inst)} instances ({yes} yes): wrong answers {wrong}, "
          f"layer-level violations {st.get('layer_viol', 0)}, uncovered (c, y) {sum(st.get('uncovered', []))}; "
          f"|C_k| {sorted(set(st.get('Ck', [])))}; (|F0_k|, D) {sorted(set(st.get('rounds', [])))}")
    if st.get("rec"):
        print(f"      kept records at the best shift / average: {sum(a for a, _ in st['rec'])} / "
              f"{sum(b for _, b in st['rec']):.0f}")
    check(wrong == 0 and st.get("layer_viol", 0) == 0, "pipeline (proof regime)")
    big = [t for t in instances(11, 1) if t[0] == "large"][:2]
    wrong, yes, st = run_pipeline(big, "big")
    print(f"   regime 'big' (p >= 4T = 1012): {len(big)} instances ({yes} yes): wrong answers {wrong}, "
          f"layer-level violations {st.get('layer_viol', 0)}, uncovered (c, y) {sum(st.get('uncovered', []))}; "
          f"(|F0_k|, D) {sorted(set(st.get('rounds', [])))}")
    check(wrong == 0 and st.get("layer_viol", 0) == 0, "pipeline (big regime)")
    # regime 'tight': colliding block sums, T = 100, theta_4 raised to the median, so C_4 is a proper subset
    rng = random.Random(13)
    tight = []
    while len(tight) < 12:
        z = [rng.randint(1, 60) for _ in range(M)] + [rng.randint(1, 1 << 10) for _ in range(n - M)]
        if len(subset_sums(z, BLK)) <= T_TIGHT:
            continue
        c = [rng.randint(0, 1) for _ in range(n)]
        tight += [("tight", z, sum(a * b for a, b in zip(c, z))), ("tight", z, rng.randint(0, sum(z)))]
    wrong, yes, st = run_pipeline(tight, "tight")
    sizes = sorted(set(st.get("Ck", [])))
    print(f"   regime 'tight' (T = {T_TIGHT}, theta_4 = median key count): {len(tight)} instances ({yes} yes): wrong answers "
          f"{wrong}, layer-level violations {st.get('layer_viol', 0)}, uncovered (c, y) in C_k x Z_p "
          f"{sum(st.get('uncovered', []))}; |C_k| {sizes}")
    print(f"      outside C_4 ({st.get('outside_c', 0)} c over all instances, never targeted by the estimator): "
          f"{st.get('outside_unc', 0)} (c, y) left uncovered")
    check(wrong == 0 and st.get("layer_viol", 0) == 0 and any(0 < x < 1 << M for x in sizes),
          "pipeline (tight regime, proper C_k)")
    nf = len(FAILS)
    wrong, _, st = run_pipeline(tight[:4], "tight", "dropcover")
    FAILS = FAILS[:nf]
    unc = sum(st.get("uncovered", [])) + st.get("dropped_lost", 0)
    print(f"      control dropcover in regime 'tight': (c, y) left uncovered {unc}, layer-level violations "
          f"{st.get('layer_viol', 0)} -> detected: {unc > 0 or st.get('layer_viol', 0) > 0}")
    check(unc > 0 or st.get("layer_viol", 0) > 0, "control dropcover (tight) not detected")
    print("   controls (each must be detected):")
    sub = inst[::3]   # every family, few sums included
    for ctl in ("nocompat", "wrongcore", "dropcover", "noparity", "nofew"):
        if ctl == "dropcover":
            sub_c = [t for t in sub if t[0] in ("large", "signed")][:4]
        else:
            sub_c = sub
        nf = len(FAILS)
        wrong, _, st = run_pipeline(sub_c, "proof", ctl)
        FAILS = FAILS[:nf]   # assertion failures inside a control run are expected
        unc = sum(st.get("uncovered", [])) + st.get("dropped_lost", 0)
        det = wrong > 0 or st.get("layer_viol", 0) > 0 or unc > 0
        print(f"      {ctl}: wrong answers {wrong}, layer-level violations {st.get('layer_viol', 0)}, "
              f"(c, y) left uncovered {unc} -> detected: {det}")
        check(det, f"control {ctl} not detected")
    nf = len(FAILS)
    wrong, _, st = run_pipeline(big[:1], "big", "lowmult")
    FAILS = FAILS[:nf]
    unc = sum(st.get("uncovered", []))
    print(f"      lowmult (D = 1, p >= 4T): (c, y) left uncovered {unc}, layer-level violations "
          f"{st.get('layer_viol', 0)} -> detected: {unc > 0}")
    check(unc > 0, "control lowmult not detected")


# ===================================================================== D. density-s block grouping
def part_D():
    print("D. density-s block grouping (Lemma 3.2): sort-deal-pad")
    rng = random.Random(3)
    for s, k, d in ((Fr(1, 3), 3, 2), (Fr(1, 3), 3, 3), (Fr(1, 4), 4, 2), (Fr(1, 3), 6, 2), (Fr(1, 8), 8, 2),
                    (Fr(2, 5), 5, 2)):
        den = s.denominator
        c = den * math.ceil(Fr(k) / (s * den))
        tot = s * k * k * d
        assert tot.denominator == 1
        bad = cnt = 0
        nblocks = k * d
        exhaustive = (k + 1) ** nblocks <= 400000

        def sample():
            w = [0] * nblocks
            for _ in range(int(tot)):
                i = rng.choice([j for j in range(nblocks) if w[j] < k])
                w[i] += 1
            return tuple(w)

        extremes = []
        for lo in range(k + 1):   # as flat as possible from a floor lo, then filled greedily: the extreme spreads
            w = [lo] * nblocks
            rem = int(tot) - lo * nblocks
            for i in range(nblocks):
                add = max(0, min(k - w[i], rem))
                w[i] += add
                rem -= add
            if rem == 0:
                extremes.append(tuple(w))
        it = itertools.product(range(k + 1), repeat=nblocks) if exhaustive else \
            itertools.chain((sample() for _ in range(20000)), extremes)
        for w in it:
            if sum(w) != tot:
                continue
            cnt += 1
            ws = sorted(w)
            W = [sum(ws[j * d + i] for j in range(k)) for i in range(d)]
            zs = [s * (k * k + c) - Wi for Wi in W]
            bad += not (max(W) - min(W) <= k and all(zz.denominator == 1 and 0 <= zz <= c for zz in zs))
        print(f"   s={s} k={k} d={d} c={c}: {cnt} descriptions {'(all)' if exhaustive else '(sampled + extremes)'}, "
              f"padding feasible for all: {bad == 0}")
        check(bad == 0 and cnt > 0, f"grouping s={s} k={k} d={d}")
    # control: padding c = k (s = 1/2's 2k halved) fails at s = 1/3
    s, k, d = Fr(1, 3), 3, 3
    c = k
    fails = 0
    for w in itertools.product(range(k + 1), repeat=k * d):
        if sum(w) != s * k * k * d:
            continue
        ws = sorted(w)
        W = [sum(ws[j * d + i] for j in range(k)) for i in range(d)]
        fails += not all(0 <= s * (k * k + c) - Wi <= c for Wi in W)
    print(f"   control c = k (< k/s) at s = 1/3, k = 3, d = 3: infeasible descriptions {fails} -> detected: {fails > 0}")
    check(fails > 0, "grouping control")


# ===================================================================== E. hole fixing at density s
def part_E():
    print("E. hole fixing at density s (Lemma 3.3 via S2 Lemma 9.1): P_{6,1/3}, full group, random g_i")
    Nn, sp = 6, 2
    X = list(range(1 << Nn))
    Y = []
    for S in itertools.combinations(range(Nn), sp):
        for vals in itertools.product((0, 1), repeat=sp):
            Y.append(tuple(zip(S, vals)))
    match = lambda x, y: all((x >> i & 1) == v for i, v in y)
    Mmat = np.array([[1 if match(x, y) else 0 for y in Y] for x in X], dtype=np.int64)
    X0 = [x for x in X if abs(bin(x).count("1") - 3) <= 1]
    Y0 = [y for y in Y if sum(v for _, v in y) == 1]
    # window circuit: gates = rows of X0; L[x, x] = 1, R[g, y] = [g matches y] (a real depth-2 circuit on W)
    rng = random.Random(5)

    def act(g, x=None, y=None):
        perm, flip = g
        if x is not None:
            out = 0
            for i in range(Nn):
                if (x >> i & 1) ^ (flip >> i & 1):
                    out |= 1 << perm[i]
            return out
        return tuple(sorted((perm[i], v ^ (flip >> i & 1)) for i, v in y))

    J = 0
    gs = []
    covered = np.zeros((len(X), len(Y)), dtype=bool)
    yidx = {y: j for j, y in enumerate(Y)}
    while not covered.all():
        perm = list(range(Nn))
        rng.shuffle(perm)
        g = (perm, rng.randrange(1 << Nn))
        gs.append(g)
        gx = [act(g, x=x) for x in X0]
        gy = [yidx[act(g, y=y)] for y in Y0]
        covered[np.ix_(gx, gy)] = True
        J += 1
        assert J <= 14
    total = np.zeros_like(Mmat)
    total_nosign = np.zeros_like(Mmat)
    for size in range(1, J + 1):
        for Ssub in itertools.combinations(range(J), size):
            XS = set(range(len(X)))
            YS = set(range(len(Y)))
            for i in Ssub:
                XS &= {act(gs[i], x=x) for x in X0}
                YS &= {yidx[act(gs[i], y=y)] for y in Y0}
            if not XS or not YS:
                continue
            g = gs[Ssub[0]]
            # copy g C: gates g x0; L[g x0, g x0] = 1 (rows restricted to X_S); R[g x0, g y0] = [x0 matches y0]
            Lm = np.zeros((len(X), len(X0)), dtype=np.int64)
            Rm = np.zeros((len(X0), len(Y)), dtype=np.int64)
            for gi, x0 in enumerate(X0):
                gx = act(g, x=x0)
                if gx in XS:
                    Lm[gx, gi] = 1
                for y0 in Y0:
                    gy = yidx[act(g, y=y0)]
                    if gy in YS and match(x0, y0):
                        Rm[gi, gy] = 1
            prod = Lm @ Rm
            total += (-1) ** (size + 1) * prod
            total_nosign += prod
    ok = (total == Mmat).all()
    print(f"   J = {J} group elements cover X x Y; {2 ** J - 1} signed copies; L R == P_(6,1/3) exactly: {ok}; "
          f"control (no signs) equal: {(total_nosign == Mmat).all()}")
    check(ok and not (total_nosign == Mmat).all(), "hole fixing at density s")


# ===================================================================== F. random designs of the proof's size
def part_F():
    print("F. one-pass covering circuit with random designs of the proof's size (Lemma 3.5), N = 10, 4 specified")
    Nn, SPEC = 10, 4
    rho = Fr(5, 2)
    rng = random.Random(9)
    designs = {}
    worst = 0.0
    cov_ok = deg_ok = True
    rows = list(range(1 << Nn))
    for k1 in range(SPEC + 1):
        for m in range(k1, SPEC + 1):
            b = max(m, min(Nn, math.floor(k1 + rho * (m - k1))))
            size = math.ceil(Nn * Nn * math.comb(Nn, m) / math.comb(b, m))
            D = [frozenset(rng.sample(range(Nn), b)) for _ in range(size)]
            Dm = [sum(1 << i for i in B) for B in D]
            # (P1) covering of every m-subset
            arr0 = np.array(Dm, dtype=np.int64)
            for U in itertools.combinations(range(Nn), m):
                um = sum(1 << i for i in U)
                if not ((arr0 & um) == um).any():
                    cov_ok = False
            # (P2) for every row x and every d: #{B : |x cap B| = d} <= 6 mu + 3N, mu = |D| C(w,d)C(N-w,b-d)/C(N,b)
            arr = np.array(Dm, dtype=np.int64)
            POP = np.array([bin(i).count("1") for i in range(1 << Nn)], dtype=np.int64)
            for x in rows:
                w = bin(x).count("1")
                cnts = np.bincount(POP[x & arr], minlength=b + 1)
                for d in range(b + 1):
                    mu = size * math.comb(w, d) * math.comb(Nn - w, b - d) / math.comb(Nn, b)
                    if cnts[d] > 6 * mu + 3 * Nn:
                        deg_ok = False
                    if mu > 0:
                        worst = max(worst, cnts[d] / (6 * mu + 3 * Nn))
            designs[(k1, m)] = (b, D)
    print(f"   designs |D| = ceil(N^2 C(N,m)/C(b,m)): every m-set covered: {cov_ok}; left degree <= 6 mu + 3N for "
          f"every row and colour: {deg_ok} (largest ratio {worst:.3f})")
    check(cov_ok and deg_ok, "random designs (P1), (P2)")
    # exactness and right degrees for every query (all splits) against every row
    assign = {}
    for (k1, m), (b, D) in designs.items():
        arr = np.array([sum(1 << i for i in B) for B in D], dtype=np.int64)
        for U in itertools.combinations(range(Nn), m):
            um = sum(1 << i for i in U)
            assign[(k1, frozenset(U))] = int(np.argmax((arr & um) == um))
    Xa = np.arange(1 << Nn, dtype=np.int64)
    mism = degfail = nq = 0
    for S in itertools.combinations(range(Nn), SPEC):
        for vals in itertools.product((0, 1), repeat=SPEC):
            if rng.random() > 0.25:      # a quarter of the 3360 queries, every split represented
                continue
            nq += 1
            Y1 = [i for i, v in zip(S, vals) if v == 1]
            Y0 = [i for i, v in zip(S, vals) if v == 0]
            k1, k0 = len(Y1), len(Y0)
            Rcol = {}
            for t in range(k0 + 1):
                for add in itertools.combinations(Y0, t):
                    U = frozenset(Y1) | frozenset(add)
                    m = len(U)
                    bi = assign[(k1, U)]
                    b, D = designs[(k1, m)]
                    B = sorted(D[bi])
                    free = [i for i in B if i not in U]
                    for ones in itertools.product((0, 1), repeat=len(free)):
                        sig = tuple(1 if (i in U or ones[free.index(i)]) else 0 for i in B)
                        g = (m, bi, sig)
                        Rcol[g] = Rcol.get(g, 0) + (-1) ** (m - k1)
            Rcol = {g: c for g, c in Rcol.items() if c}
            col = {}
            for (m, bi, sig) in Rcol:
                col[(m, sum(sig))] = col.get((m, sum(sig)), 0) + 1
            for (m, d), cnt in col.items():
                b = designs[(k1, m)][0]
                degfail += cnt > math.comb(k0, m - k1) * math.comb(b - m, d - m)
            val = np.zeros(1 << Nn, dtype=np.int64)
            for (m, bi, sig), c in Rcol.items():
                B = sorted(designs[(k1, m)][1][bi])
                mask = sum(1 << i for i in B)
                pat = sum(1 << i for i, v in zip(B, sig) if v)
                val[(Xa & mask) == pat] += c
            m1 = sum(1 << i for i in Y1)
            m0 = sum(1 << i for i in Y0)
            fy = (((Xa & m1) == m1) & ((Xa & m0) == 0)).astype(np.int64)
            mism += int((val != fy).sum())
    print(f"   {nq} queries (all splits k1 = 0..4) x 1024 rows: mismatches {mism}, right-degree violations {degfail}")
    check(mism == 0 and degfail == 0, "covering circuit with random designs")


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C", "D", "E", "F"]
    for part in which:
        globals()["part_" + part]()
    print("STAGE 4 CHECK", "PASS" if not FAILS else f"FAIL ({len(FAILS)}): {FAILS[:5]}")
    sys.exit(1 if FAILS else 0)
