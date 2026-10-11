"""Stage 5 brute-force logic check: Record 3's deterministic route (Stage 4's DET4) with A22's OUTER-SUM DEDUPE (A39),
no few/many dichotomy, at n = 25, against brute force. Logic at toy size, not asymptotics.

Setting: three blocks of M = 8 (B0, B1, B2) and one rest coordinate. P := the LEAST deficient block (max |Sigma|, least
index on ties) is the representation block; the other two, Qa and Qc, are whole dedupe blocks on the u-outer and the
v-outer side. The rest coordinate goes to u or v depending on the layer's design (an unequal outer split, as A38's w).
For every layer the u-list is (block part of u) x Sigma(Qa) x Sigma(Ru) and the v-list (block part of v) x Sigma(Qc) x
Sigma(Rv): one record per DISTINCT outer sum pair, each with its least-mask representative (sorted merges).
Pipeline (proofs/stage5.md Sec. 2): N := |Sigma(P)|; prime p in [P0, 2 P0], P0 := max(floor(N/(2(M+1))), 2), least collision
count; every layer k = 0..8 is served; C_k := {c : layer k of c has >= N/(M+1) distinct keys}; each c is owned by the
FIRST layer in the regime's order whose C_k holds it; a greedy round family per layer, repeated D times; one residue per
round by Stage 4's fixed-point pessimistic estimator (vendored below, verbatim); the global shift; kept records by meet in
the middle on sorted residues; the exact compatible equal-key count; recovery by bisection plus representatives.
Designs: 'sym' = Stage 4's core design (core a = 3, s a = 1, s = 1/3, non-core b = 1, x' = x + sigma) on k = 3, 4, 5;
'asym' = A38-style cores (u side s1 a = 1, v side s2 a = 2) on k = 2, 3, 4, with the rest coordinate moved to v;
'free' = the core-free design (alpha = 0) on every other layer.
Regimes: 'center' (layers 4, 3, 5, 2, 6, ...), 'far' (0, 8, 1, 7, ...: far layers own most c), 'asym' (layers 2, 3, 4 use the
asymmetric design and layers 2, 3 are served first, so they own c; ownership counts are printed per regime).
Asserted: agreement with brute force; every counted pair is a 0/1 solution (soundness); the recovered vector is a
solution; layer-level completeness for sampled solutions; the list bound |Sigma(Qa)|, |Sigma(Qc)| <= N (so
|U'| <= |U| N 2^{-M}); deduped and raw outer lists give the same positivity on sampled picks; Lemma 5.2' (distinct
residues >= min(|W_c|, p)/G) and D_need <= the proof's D'; Phi_0 <= 1/4; full coverage; best shift <= average;
the sorted-residue MITM equals the direct filter, and the merge-join count equals the table count, on sampled picks.
Must-fail controls: nocompat, mostdef, blockdedupe, straddle, lowmult.
Run: nice -n 15 /usr/bin/python3 -B -E check_stage5.py        (several minutes under load, < 200 MB)
"""
import bisect
import itertools
import math
import os
import random
import sys
from fractions import Fraction as Fr

sys.dont_write_bytecode = True
import numpy as np  # noqa: E402  (REQUIRED: this brute force needs numpy; cert_stage5.py is standard library only)



def estimator(Sres, p, D, nU, lowbits=False):
    """Stage 4's fixed-point pessimistic estimator (Lemma 5.4), copied verbatim from certificates/stage4/check_stage4.py so that
    stage5 is self-contained. Sres[c][f0] = residue array of S_{c,f0} over the base family F0; the run family is F0
    repeated D times (copy-major). Returns the chosen residues r_f and the number of uncovered (c, y) at the end."""
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


n, M = 25, 8
BLOCKS = [list(range(0, 8)), list(range(8, 16)), list(range(16, 24))]
REST = [24]
A_CORE, B_NON = 3, 1
FAILS = []
STATS = {}


def check(cond, msg):
    if not cond:
        FAILS.append(msg)
        if len(FAILS) < 20:
            print("   FAIL:", msg)
    return cond


def bump(key, v=1):
    STATS[key] = STATS.get(key, 0) + v


def is_prime(q):
    return q > 1 and all(q % d for d in range(2, int(q ** 0.5) + 1))


def sigma_sorted(z, idx):
    """distinct subset sums of z on idx, built by sorted merges; each with its least-mask representative."""
    S = [(0, 0)]
    for b, i in enumerate(idx):
        T = [(s + z[i], m | (1 << b)) for s, m in S]
        out, a, c = [], 0, 0
        while a < len(S) or c < len(T):
            if c >= len(T) or (a < len(S) and S[a][0] <= T[c][0]):
                x = S[a]
                a += 1
            else:
                x = T[c]
                c += 1
            if out and out[-1][0] == x[0]:
                if x[1] < out[-1][1]:
                    out[-1] = x
            else:
                out.append(x)
        S = out
    return S


# ------------------------------------------------------------------ rounds
def all_rounds(blk, design):
    a = A_CORE if design in ("sym", "asym") else 0
    out = []
    for H in itertools.combinations(blk, M // 2):
        Hb = [i for i in blk if i not in H]
        for Hc in itertools.combinations(H, a):
            for Hbc in itertools.combinations(Hb, a):
                out.append((H, tuple(Hb), Hc, Hbc))
    return out


def design_counts(k, design):
    """(cu, cv, x, x') = |K n Hc|, |K n Hbc|, |K n (H - Hc)|, |K n (Hbar - Hbc)|, or None if the layer has no round."""
    if design == "sym":
        cu, cv = 1, 2
    elif design == "asym":
        cu, cv = 1, 1
    else:
        cu, cv = 0, 0
    b = B_NON if design in ("sym", "asym") else M // 2
    rest = k - cu - cv
    if rest < 0:
        return None
    sig = rest % 2
    x = (rest - sig) // 2
    xp = x + sig
    if xp > b:
        return None
    return cu, cv, x, xp


def compat_K(R, Kset, cnt):
    H, Hb, Hc, Hbc = R
    cu, cv, x, xp = cnt
    return (len(Kset & set(Hc)) == cu and len(Kset & set(Hbc)) == cv
            and len(Kset & (set(H) - set(Hc))) == x and len(Kset & (set(Hb) - set(Hbc))) == xp)


FAM_CACHE = {}


def greedy_family(blk, k, design):
    key = (tuple(blk), k, design)
    if key in FAM_CACHE:
        return FAM_CACHE[key]
    cnt = design_counts(k, design)
    rounds = all_rounds(blk, design)
    Ks = [frozenset(K) for K in itertools.combinations(blk, k)]
    comp = [[j for j, K in enumerate(Ks) if compat_K(R, K, cnt)] for R in rounds]
    unc, fam = set(range(len(Ks))), []
    while unc:
        i = max(range(len(rounds)), key=lambda i: (sum(1 for j in comp[i] if j in unc), -i))
        fam.append(rounds[i])
        unc -= set(comp[i])
    FAM_CACHE[key] = (fam, cnt)
    return fam, cnt


# ------------------------------------------------------------------ lists
def block_parts(z, R, cnt, side):
    """u: r on H (cu non-zeros on Hc, x on H - Hc, any signs), l on Hbar binary. v: l on H binary, r on Hbar
    (|Hbc| - cv non-zeros on Hbc, |Hbar - Hbc| - x' on Hbar - Hbc). Returns list of (block key, vector dict)."""
    H, Hb, Hc, Hbc = R
    cu, cv, x, xp = cnt
    if side == "u":
        core, nc, non, nn, left = list(Hc), cu, [i for i in H if i not in Hc], x, list(Hb)
    else:
        core, nc, non, nn, left = list(Hbc), len(Hbc) - cv, [i for i in Hb if i not in Hbc], len(Hb) - len(Hbc) - xp, \
            list(H)
    out = []
    for sup in itertools.combinations(core, nc):
        for supn in itertools.combinations(non, nn):
            S = list(sup) + list(supn)
            for sg in itertools.product((-1, 1), repeat=len(S)):
                for lb in itertools.product((0, 1), repeat=len(left)):
                    v = {i: 0 for i in core + non}
                    v.update(zip(S, sg))
                    v.update(zip(left, lb))
                    out.append((sum(v[i] * z[i] for i in v), v))
    return out


def outer_records(z, parts):
    """deduped outer records: the product of Sigma(part) over the parts, each record (sum, ((idx, mask), ...))."""
    recs = [(0, ())]
    for idx in parts:
        S = sigma_sorted(z, idx) if idx else [(0, 0)]
        recs = [(s + t, reps + ((tuple(idx), m),)) for s, reps in recs for t, m in S]
    return recs


def raw_outer(z, idx):
    return [(sum(z[idx[i]] for i in range(len(idx)) if m >> i & 1), ((tuple(idx), m),)) for m in range(1 << len(idx))]


def kept(A, B, p, r, sign=1):
    """meet in the middle on sorted residues: all (a, b) with (ka + sign kb) = r mod p, output-sensitive."""
    Bs = sorted((((sign * kb) % p), kb, vb) for kb, vb in B)
    res = [t[0] for t in Bs]
    out = []
    for ka, va in A:
        want = (r - ka) % p
        j = bisect.bisect_left(res, want)
        while j < len(res) and res[j] == want:
            out.append((ka + sign * Bs[j][1], va, Bs[j][2]))
            j += 1
    return out


def compat_pair(vu, vv, R):
    H, Hb = R[0], R[1]
    return all(vv[i] + vu[i] in (0, 1) for i in H) and all(vu[i] + vv[i] in (0, 1) for i in Hb)


def count_merge(U, V, R, nocompat=False):
    """compatible equal-key pairs by a sorted merge-join on keys."""
    U = sorted(U, key=lambda t: t[0])
    V = sorted(V, key=lambda t: t[0])
    i = j = cnt = 0
    while i < len(U) and j < len(V):
        if U[i][0] < V[j][0]:
            i += 1
        elif U[i][0] > V[j][0]:
            j += 1
        else:
            k = U[i][0]
            i2, j2 = i, j
            while i2 < len(U) and U[i2][0] == k:
                i2 += 1
            while j2 < len(V) and V[j2][0] == k:
                j2 += 1
            for a in range(i, i2):
                for b in range(j, j2):
                    if nocompat or compat_pair(U[a][1], V[b][1], R):
                        cnt += 1
            i, j = i2, j2
    return cnt


def assemble(u, v):
    c = [0] * n
    for rec in (u, v):
        for i, val in rec[1].items():
            c[i] += val
        for idx, m in rec[2]:
            for b, i in enumerate(idx):
                c[i] += m >> b & 1
    return c


# ------------------------------------------------------------------ the pipeline
ORDERS = {"center": [4, 3, 5, 2, 6, 1, 7, 0, 8], "far": [0, 8, 1, 7, 2, 6, 3, 5, 4], "asym": [2, 3, 4, 5, 6, 1, 7, 0, 8]}   # asym: the non-central asymmetric layers 2, 3 are served FIRST so they own c


def layer_design(k, regime):
    if regime == "asym" and k in (2, 3, 4):
        return "asym"
    if regime != "asym" and k in (3, 4, 5):
        return "sym"
    return "free"


def choose_blocks(z, ctl):
    sizes = [len(sigma_sorted(z, b)) for b in BLOCKS]
    order = sorted(range(3), key=lambda i: (sizes[i], -i) if ctl == "mostdef" else (-sizes[i], i))
    P = BLOCKS[order[0]]
    Qa, Qc = [BLOCKS[i] for i in sorted(order[1:])]
    return P, Qa, Qc


def det5(z, tau, regime, ctl=None, sols=None):
    P, Qa, Qc = choose_blocks(z, ctl)
    SigP = sigma_sorted(z, P)
    N = len(SigP)
    nSa, nSc = len(sigma_sorted(z, Qa)), len(sigma_sorted(z, Qc))
    lb_ok = nSa <= N and nSc <= N
    if not lb_ok:
        bump("list_bound_viol")
    if ctl != "mostdef":
        check(lb_ok, "list bound |Sigma(Qa)|, |Sigma(Qc)| <= N")
    bump("N_" + ("1-16" if N <= 16 else "17-128" if N <= 128 else "129-256"))
    sums = [s for s, _ in SigP]
    P0 = max(N // (2 * (M + 1)), 2)
    cands = [q for q in range(P0, 2 * P0 + 1) if is_prime(q)]

    def coll(q):
        cnt = {}
        for s in sums:
            cnt[s % q] = cnt.get(s % q, 0) + 1
        return sum(v * (v - 1) // 2 for v in cnt.values())

    p = min(cands, key=lambda q: (coll(q), q))
    g = coll(p) * p / (N * N)
    G = 1 + 2 * g * (M + 1) ** 2
    # keys of every block assignment c in every layer: keys[c][Kmask] = sum_{i in K} e_i z_i
    zP = np.array([z[i] for i in P], dtype=np.int64)
    masks = np.arange(1 << M)
    Kmat = ((masks[:, None] >> np.arange(M)[None, :]) & 1).astype(np.int64)        # (K, i)
    pop = Kmat.sum(axis=1)
    Cmat = Kmat.copy()                                                              # c as bit vectors, same order
    E = (2 * Cmat - 1) * zP[None, :]                                                # (c, i)
    keys = E @ Kmat.T                                                               # (c, K)
    theta = Fr(N, M + 1)
    owner = {}
    Wsize = {}
    for k in ORDERS[regime]:
        if design_counts(k, layer_design(k, regime)) is None:
            continue
        cols = np.nonzero(pop == k)[0]
        for c in range(1 << M):
            if c in owner:
                continue
            nd = len(np.unique(keys[c, cols]))
            if nd >= theta:
                owner[c] = k
                Wsize[c] = nd
    check(len(owner) == 1 << M, "every c lies in some served C_k (layer pigeonhole)")
    for c, k in owner.items():
        bump(f"own_{min(k, M - k)}")
    if any(Wsize[c] < p for c in Wsize):
        bump("p_above_W")       # Stage 4's Lemma 5.2 (p <= |W_c|) fails here; Lemma 5.2' with min(|W_c|, p) is used
    picks = []
    for k in ORDERS[regime]:
        design = layer_design(k, regime)
        Ck = [c for c in range(1 << M) if owner.get(c) == k]
        if not Ck:
            continue
        fam, cnt = greedy_family(P, k, design)
        cols = np.nonzero(pop == k)[0]
        Kfr = {int(col): frozenset(P[i] for i in range(M) if col >> i & 1) for col in cols}
        Sres = []
        for c in Ck:
            cvec = [c >> i & 1 for i in range(M)]
            e = {P[i]: 2 * cvec[i] - 1 for i in range(M)}
            cv = {P[i]: cvec[i] for i in range(M)}
            row = []
            for R in fam:
                const = sum((cv[i] - e[i]) * z[i] for i in R[1])
                ks = [int(col) for col in cols if compat_K(R, Kfr[int(col)], cnt)]
                row.append(sorted({int(const + keys[c, col]) % p for col in ks}))
            Sres.append(row)
            Wd = len({int(v) % p for v in np.unique(keys[c, cols])})
            check(Wd >= min(Wsize[c], p) / G - 1e-9, "Lemma 5.2': distinct residues >= min(|W_c|, p)/G")
        nU = len(Ck) * p
        tot = [sum(len(s) for s in row) for row in Sres]
        Dneed = max(1, max(math.ceil(p * math.log(4 * nU) / t) for t in tot))
        minW = min(Wsize[c] for c in Ck)
        Dproof = math.ceil((2 * M + 2) * math.log(2) * G * math.ceil(p / min(p, minW)))
        check(Dneed <= Dproof, "D_need <= the proof's D' (Lemma 5.2' with the p/min(|W_c|, p) factor)")
        D = 1 if ctl == "lowmult" else Dneed
        phi0 = sum(p * math.exp(-D * t / p) for t in tot)
        if ctl != "lowmult":
            check(phi0 <= 0.25 + 1e-12, "Phi_0 <= 1/4")
        rs, left = estimator(Sres, p, D, nU)
        bump("uncovered", left)
        if ctl != "lowmult":
            check(left == 0, f"covering incomplete at k = {k}")
        run = [(fam[i % len(fam)], rs[i]) for i in range(len(rs))]
        # outer split of this layer's design: the rest coordinate goes to v for 'asym', to u otherwise
        Ru, Rv = ([], REST) if design == "asym" else (REST, [])
        Uparts = [Qa, Ru]
        if ctl == "straddle":
            Uparts = [Qa + [Qc[0]], Ru]           # control: a block straddling the u and v sides is deduped on u
        Uo = outer_records(z, Uparts)
        Vo = [(tau - s, reps) for s, reps in outer_records(z, [Qc, Rv])]
        hist = {}
        for R, _ in run:
            if R not in hist:
                Ub, Vb = block_parts(z, R, cnt, "u"), block_parts(z, R, cnt, "v")
                hu = np.bincount((np.add.outer([a for a, _ in Ub], [b for b, _ in Uo]) % p).ravel(), minlength=p)
                hv = np.bincount((np.add.outer([-a for a, _ in Vb], [b for b, _ in Vo]) % p).ravel(), minlength=p)
                hist[R] = (hu + hv, Ub, Vb)
        tot_t = np.zeros(p, dtype=np.int64)
        for R, r in run:
            tot_t += np.roll(hist[R][0], -r)
        t = int(np.argmin(tot_t))
        check(tot_t[t] <= tot_t.mean() + 1e-9, "best shift <= average (Lemma 5.5 on deduped weights)")
        bump("kept_best", int(tot_t[t]))
        bump("kept_mean", float(tot_t.mean()))
        for R, r in run:
            picks.append((k, R, cnt, (r + t) % p, Uo, Vo, hist[R][1], hist[R][2], Ru, Rv))
    if sols is not None:
        layer_check(z, P, Qa, Qc, picks, owner, p, sols)
    seen, sampled, rawn = set(), 0, 0
    for (k, R, cnt, r, Uo, Vo, Ub, Vb, Ru, Rv) in picks:
        tag = (R, cnt, r, len(Ru))
        if tag in seen:
            continue
        seen.add(tag)
        L = Lists(R, Ub, Uo, Vb, Vo, p)
        U, V = L.kept_u(r), L.kept_v(r)
        if ctl == "blockdedupe":           # control: also keep ONE u (and one v) per KEY, i.e. dedupe on P's side
            U = U[:, np.unique(U[0], return_index=True)[1]]
            V = V[:, np.unique(V[0], return_index=True)[1]]
        cnt_f = L.count(U, V, ctl == "nocompat")
        if sampled < 2:
            sampled += 1
            # the explicit sorted-residue MITM and merge-join agree with the array version
            Ul = kept(Ub, Uo, p, r)
            Vl = _kept_v(Vb, Vo, p, r)
            check(sorted(kk for kk, _, _ in Ul) == sorted(L.kept_u(r)[0].tolist()), "sorted-residue MITM (u) = arrays")
            check(sorted(kk for kk, _, _ in Vl) == sorted(L.kept_v(r)[0].tolist()), "sorted-residue MITM (v) = arrays")
            direct = sorted(a + b for a, _ in Ub for b, _ in Uo if (a + b - r) % p == 0)
            check(sorted(kk for kk, _, _ in Ul) == direct, "sorted-residue MITM = direct filter")
            if ctl != "blockdedupe" and len(Ul) * len(Vl) < 4 * 10 ** 6:
                check(count_merge(Ul, Vl, R, ctl == "nocompat") == cnt_f, "merge-join count = array count")
        if rawn < 4 or ctl == "blockdedupe":
            # raw outer vectors (no dedupe): same positivity (proofs/stage5.md Lemma 2.3)
            Lr = Lists(R, Ub, _raw_product(z, Uparts_of(Qa, Ru, Qc, ctl)),
                       Vb, [(tau - s, reps) for s, reps in _raw_product(z, [Qc, Rv])], p)
            raw_pos = Lr.count(Lr.kept_u(r), Lr.kept_v(r), ctl == "nocompat") > 0
            bump("pos_checked")
            if raw_pos != (cnt_f > 0):
                bump("pos_disagree")
                if ctl != "blockdedupe":
                    check(False, "deduped and raw outer lists agree on positivity")
            rawn += 1
        if cnt_f > 0:
            return L.recover(U, V, ctl == "nocompat")
    return None


class Lists:
    """kept records as int64 arrays (key, block-part index, outer-record index), built by meet in the middle on
    residues: the outer records are grouped by residue (a sorted residue table), each block part looks up its group."""

    def __init__(self, R, Ub, Uo, Vb, Vo, p):
        self.R, self.Ub, self.Uo, self.Vb, self.Vo, self.p = R, Ub, Uo, Vb, Vo, p
        self.kbU = np.array([a for a, _ in Ub], dtype=np.int64)
        self.koU = np.array([b for b, _ in Uo], dtype=np.int64)
        self.kbV = np.array([-a for a, _ in Vb], dtype=np.int64)       # key'(v) = (tau - outer) - block.z
        self.koV = np.array([b for b, _ in Vo], dtype=np.int64)
        self.gU = self._groups(self.koU)
        self.gV = self._groups(self.koV)
        coords = list(R[0]) + list(R[1])
        Uv = np.array([[d[i] for i in coords] for _, d in Ub], dtype=np.int64)
        Vv = np.array([[d[i] for i in coords] for _, d in Vb], dtype=np.int64)
        S = Uv[:, None, :] + Vv[None, :, :]
        self.CM = ((S == 0) | (S == 1)).all(axis=2).astype(np.int64)    # compatibility depends on block parts only

    def _groups(self, ko):
        order = np.argsort(ko % self.p, kind="stable")
        res = (ko % self.p)[order]
        return order, res

    def _kept(self, kb, ko, g, r):
        order, res = g
        parts_b, parts_o = [], []
        for i, kbi in enumerate(kb.tolist()):
            want = (r - kbi) % self.p
            lo, hi = np.searchsorted(res, want, "left"), np.searchsorted(res, want, "right")
            if hi > lo:
                parts_o.append(order[lo:hi])
                parts_b.append(np.full(hi - lo, i, dtype=np.int64))
        if not parts_b:
            return np.zeros((3, 0), dtype=np.int64)
        bi, oi = np.concatenate(parts_b), np.concatenate(parts_o)
        return np.vstack([kb[bi] + ko[oi], bi, oi])

    def kept_u(self, r):
        return self._kept(self.kbU, self.koU, self.gU, r)

    def kept_v(self, r):
        return self._kept(self.kbV, self.koV, self.gV, r)

    def count(self, U, V, nocompat=False):
        CM = np.ones_like(self.CM) if nocompat else self.CM
        if U.shape[1] == 0 or V.shape[1] == 0:
            return 0
        order = np.argsort(V[0], kind="stable")
        vk, vb = V[0][order], V[1][order]
        lo, hi = np.searchsorted(vk, U[0], "left"), np.searchsorted(vk, U[0], "right")
        tot = int((hi - lo).sum())
        if tot == 0:
            return 0
        if tot <= 3 * 10 ** 6:
            rep = np.repeat(np.arange(U.shape[1]), hi - lo)
            idx = np.concatenate([np.arange(a, b) for a, b in zip(lo.tolist(), hi.tolist()) if b > a])
            return int(CM[U[1][rep], vb[idx]].sum())
        cnt = 0                                  # few distinct keys, huge groups: hu^T CM hv per common key
        for key in np.intersect1d(U[0], vk).tolist():
            hu = np.bincount(U[1][U[0] == key], minlength=CM.shape[0])
            hv = np.bincount(vb[vk == key], minlength=CM.shape[1])
            cnt += int(hu @ CM @ hv)
        return cnt

    def recover(self, U, V, nocompat):
        while U.shape[1] > 1:
            h1 = U[:, :U.shape[1] // 2]
            U = h1 if self.count(h1, V, nocompat) > 0 else U[:, U.shape[1] // 2:]
        while V.shape[1] > 1:
            h1 = V[:, :V.shape[1] // 2]
            V = h1 if self.count(U, h1, nocompat) > 0 else V[:, V.shape[1] // 2:]
        u = (0, self.Ub[int(U[1][0])][1], self.Uo[int(U[2][0])][1])
        v = (0, self.Vb[int(V[1][0])][1], self.Vo[int(V[2][0])][1])
        return assemble(u, v)


def Uparts_of(Qa, Ru, Qc, ctl):
    return [Qa + [Qc[0]], Ru] if ctl == "straddle" else [Qa, Ru]


def _raw_product(z, parts):
    recs = [(0, ())]
    for idx in parts:
        Rr = raw_outer(z, idx) if idx else [(0, ())]
        recs = [(s + t, a + b) for s, a in recs for t, b in Rr]
    return recs


def _kept_v(Vb, Vo, p, r):
    """explicit sorted-residue MITM for v: key'(v) = (tau - outer sum) - block.z = r mod p."""
    Bs = sorted(((kb % p), kb, vb) for kb, vb in Vo)
    res = [t[0] for t in Bs]
    out = []
    for ka, va in Vb:
        want = (r + ka) % p
        j = bisect.bisect_left(res, want)
        while j < len(res) and res[j] == want:
            out.append((-ka + Bs[j][1], va, Bs[j][2]))
            j += 1
    return out


def layer_check(z, P, Qa, Qc, picks, owner, p, sols):
    """every sampled solution: in the layer owning its block part, some pick keeps a compatible representation."""
    for sol in sols:
        cidx = sum(sol[P[i]] << i for i in range(M))
        k = owner[cidx]
        e = {i: 2 * sol[i] - 1 for i in P}
        found = False
        for (kk, R, cnt, r, Uo, Vo, Ub, Vb, Ru, Rv) in picks:
            if kk != k:
                continue
            y = sum(sol[i] * z[i] for i in Qa + Ru)
            const = sum((sol[i] - e[i]) * z[i] for i in R[1])
            for K in itertools.combinations(P, k):
                Ks = frozenset(K)
                if compat_K(R, Ks, cnt) and (const + sum(e[i] * z[i] for i in K) + y - r) % p == 0:
                    found = True
                    break
            if found:
                break
        bump("layer_checked")
        if not found:
            bump("layer_viol")


def mitm_solutions(z, tau, cap=40):
    L, Rr = list(range(12)), list(range(12, n))
    right = {}
    for m in range(1 << len(Rr)):
        right.setdefault(sum(z[Rr[i]] for i in range(len(Rr)) if m >> i & 1), []).append(m)
    sols = []
    for m in range(1 << len(L)):
        s = sum(z[L[i]] for i in range(len(L)) if m >> i & 1)
        for m2 in right.get(tau - s, ()):
            c = [m >> i & 1 for i in range(len(L))] + [m2 >> i & 1 for i in range(len(Rr))]
            sols.append(c)
            if len(sols) >= cap:
                return sols
    return sols


def instances(seed, per):
    rng = random.Random(seed)
    fams = {
        "large": lambda: [rng.randint(1, 1 << 30) for _ in range(n)],
        "signed": lambda: [rng.randint(-(1 << 20), 1 << 20) for _ in range(n)],
        "small": lambda: [rng.randint(1, 5) for _ in range(n)],
        "planted": lambda: [7] * 8 + [rng.randint(1, 1 << 24) for _ in range(n - 8)],
        "uneven": lambda: ([rng.randint(1, 1 << 24) for _ in range(8)] + [rng.randint(1, 3) for _ in range(8)]
                           + [rng.randint(1, 40) for _ in range(8)] + [rng.randint(1, 1 << 24)]),
        "ones": lambda: [1] * n,
    }
    out = []
    for name, gen in fams.items():
        for _ in range(per):
            z = gen()
            c = [rng.randint(0, 1) for _ in range(n)]
            out.append((name, z, sum(a * b for a, b in zip(c, z))))
            out.append((name, z, rng.randint(min(0, sum(z)), max(0, sum(z))) | 1 if name != "ones" else n + 3))
    return out


def straddle_instances(seed, cnt):
    """large random z (all blocks have N = 256, so P, Qa, Qc = B0, B1, B2 and Qc[0] = 16) and a target that is a
    subset sum PLUS z[16] once more, with 16 in the subset: only a vector with c_16 = 2 hits it, i.e. a pseudo-solution
    if coordinate 16 is offered on both sides."""
    rng = random.Random(seed)
    out = []
    for _ in range(cnt):
        z = [rng.randint(1, 1 << 30) for _ in range(n)]
        c = [rng.randint(0, 1) for _ in range(n)]
        c[16] = 1
        out.append(("straddle-target", z, sum(a * b for a, b in zip(c, z)) + z[16]))
    return out


def run(inst, regime, ctl=None, layer=True):
    wrong = yes = pseudo = 0
    for name, z, tau in inst:
        sols = mitm_solutions(z, tau)
        truth = len(sols) > 0
        yes += truth
        c = det5(z, tau, regime, ctl, sols[:12] if (layer and truth) else None)
        good = c is not None and all(x in (0, 1) for x in c) and sum(a * b for a, b in zip(c, z)) == tau
        if c is not None and not good:
            pseudo += 1
        wrong += (c is None) == truth or (c is not None and not good)
    return wrong, yes, pseudo


def main():
    global FAILS, STATS
    inst = instances(5, 3)
    sinst = straddle_instances(9, 4)
    print(f"check_stage5: n = {n}, three blocks of M = {M} + rest {len(REST)}; {len(inst)} instances per regime, plus "
          f"{len(sinst)} straddle instances in 'center' only (40 there)")
    for regime, sub in (("center", inst + sinst), ("far", inst), ("asym", inst)):
        STATS = {}
        wrong, yes, pseudo = run(sub, regime)
        print(f"[{regime}] {len(sub)} instances ({yes} yes): wrong {wrong}, pseudo-solutions {pseudo}; layer-level "
              f"violations {STATS.get('layer_viol', 0)} of {STATS.get('layer_checked', 0)} sampled solutions; "
              f"uncovered (c, y) {STATS.get('uncovered', 0)}; list-bound violations {STATS.get('list_bound_viol', 0)};"
              f" positivity raw vs dedupe disagreements {STATS.get('pos_disagree', 0)} of {STATS.get('pos_checked', 0)}",
              flush=True)
        own = {k: v for k, v in sorted(STATS.items()) if k.startswith("own_") or k.startswith("N_")}
        print(f"      ownership by distance to the cube's middle layer (0 = layer 0 or 8) and N ranges: {own}; "
              f"instances with p > some |W_c| (Lemma 5.2' needed): {STATS.get('p_above_W', 0)}; kept records at "
              f"best shift / mean {STATS.get('kept_best', 0)} / {STATS.get('kept_mean', 0):.0f}")
        check(wrong == 0 and pseudo == 0 and STATS.get("layer_viol", 0) == 0, f"regime {regime}")
    print("Must-fail controls (each must be DETECTED):")
    for ctl, sub, what in (("nocompat", inst[::3], "wrong/pseudo"), ("mostdef", inst, "list-bound violations"),
                           ("blockdedupe", inst[::2], "positivity disagreements or wrong"),
                           ("straddle", straddle_instances(9, 4), "wrong/pseudo"), ("lowmult", inst[:6], "uncovered")):
        nf = len(FAILS)
        STATS = {}
        wrong, yes, pseudo = run(sub, "center", ctl, layer=(ctl == "lowmult"))
        FAILS = FAILS[:nf]
        det = {"nocompat": wrong + pseudo, "straddle": wrong + pseudo, "mostdef": STATS.get("list_bound_viol", 0),
               "blockdedupe": STATS.get("pos_disagree", 0) + wrong,
               "lowmult": STATS.get("uncovered", 0) + STATS.get("layer_viol", 0)}[ctl]
        print(f"   {ctl}: {len(sub)} instances: wrong {wrong}, pseudo {pseudo}, {what} = {det} -> detected: {det > 0}",
              flush=True)
        check(det > 0, f"control {ctl} not detected")
    print("STAGE 5 CHECK", "PASS" if not FAILS else f"FAIL ({len(FAILS)}): {sorted(set(FAILS))[:8]}")
    return len(FAILS)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
