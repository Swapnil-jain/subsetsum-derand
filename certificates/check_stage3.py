"""Brute-force logic check of DET3 (PROOF.md Sec. 3), Stage 3's algorithm. Logic only, small n; not asymptotics.

DET3 is DET2-DD (the outside-sum dedupe) run with the re-tuned pair (dL', dR') of cert_stage3.py; the pair enters
the algorithm only through the split l*_j and the weights 2^{e_L}, 2^{e_R}. Self-contained (no imports outside the
standard library).

Everything is deterministic and uses sorted lists, bisection and sorted merges; no hash set or dict decides
membership, dedupe, matching or counting. Instances come from a seeded generator.

Per instance and target:
  * the DET2-DD answer equals brute force;
  * on a yes, the bisection recovery of S2 Cor. 2 isolates one record pair, the stored representatives assemble
    a vector c, and c is checked to be binary with c . z = tau;
  * Lemma 3.2 (completeness): for every solution c (up to a cap) and every layer j with c_P in T_j, the record pair
    built from c's own block sums is kept;
  * Lemma 3.4 (sizes): |A'_j| * 2^{d(P)} <= |A_j| and |B'_j| * 2^{d(P)} <= |B_j|, in integers via N;
  * Lemma 2.2 on the deduped weights, and the final kept-cost line (|R_j|/p) * W'_j, in integers;
  * Step 5: the meet-in-the-middle generation equals the direct filter of A'_j and B'_j (sorted multisets);
  * the fit m <= l_j <= n - 2m on every layer.
Must-fail controls (each must produce at least one failure):
  nocompat  count equal keys only (no compatibility test): wrong yes answers;
  overlap   dedupe a block that lies on both sides (Qc's sums also offered on the left): wrong yes answers;
  dedupP    also merge a_P by prefix sum (one row per prefix sum): S2 Lemma 5.2 fails in individual layers. This is
            detected at LAYER level only; the final answers stay right, because another layer catches the solution;
  wrongP    P := the MOST deficient block: the size line |A'| 2^{d(P)} <= |A| is violated on some instance.
Run: nice -n 15 python3 -I check_stage3.py     (about 2-3 min, < 100 MB)
"""
import bisect
import math
import random
import sys
import time
from itertools import product

DLP, DRP, EPS = 0.009610513770, 0.490316857078, 1e-9     # Stage 3's rational pair (cert_stage3.py [S3])


def h(s):
    return 0.0 if s in (0, 1) else -s * math.log2(s) - (1 - s) * math.log2(1 - s)


def is_prime(q):
    if q < 2:
        return False
    i = 2
    while i * i <= q:
        if q % i == 0:
            return False
        i += 1
    return True


def sums_with_reps(z, idx):
    """Sorted distinct subset sums of z over coordinates idx, each with its least-mask representative."""
    k = len(idx)
    pairs = []
    for mask in range(1 << k):
        s = 0
        for t in range(k):
            if mask >> t & 1:
                s += z[idx[t]]
        pairs.append((s, mask))
    pairs.sort()
    out = []
    for s, mask in pairs:
        if not out or out[-1][0] != s:
            out.append((s, mask))
    return out                       # list of (sum, mask), sorted by sum


def rep_vector(n, idx, mask):
    v = [0] * n
    for t, i in enumerate(idx):
        if mask >> t & 1:
            v[i] = 1
    return v


def sorted_count(lst, x):
    return bisect.bisect_right(lst, x) - bisect.bisect_left(lst, x)


class Fail(Exception):
    pass


def run(z, tau, m, mode, stats, all_sums, cap_sol=40):
    n = len(z)
    blocks = [list(range(i * m, (i + 1) * m)) for i in range(4)]
    rest = list(range(4 * m, n))
    sig = [sums_with_reps(z, b) for b in blocks]
    d = [m - math.log2(len(s)) for s in sig]
    # P: least deficient (ties: least index). wrongP: most deficient.
    if mode == "wrongP":
        ip = max(range(4), key=lambda i: (d[i], -i))
    else:
        ip = min(range(4), key=lambda i: (d[i], i))
    others = [i for i in range(4) if i != ip]
    P, Qa, Qb, Qc = blocks[ip], blocks[others[0]], blocks[others[1]], blocks[others[2]]
    order = P + Qa + rest + Qb + Qc                 # the relabelling P, Qa, Rr, Qb, Qc
    sigP = sig[ip]
    N = len(sigP)
    sumsP = [s for s, _ in sigP]
    zP = [z[i] for i in P]
    # bit bound b and the collision-bounded prime of S2 Lemma 2.3, scanned upward from P0 = N (b + 1).
    b = max(1, max(abs(x) for x in z) * n + abs(tau)).bit_length() + 1
    p = N * (b + 1)
    while True:
        if is_prime(p):
            res = sorted(s % p for s in sumsP)
            runs, i = 0, 0
            while i < len(res):
                j = i
                while j < len(res) and res[j] == res[i]:
                    j += 1
                runs += (j - i) * (j - i - 1)
                i = j
            if runs <= 3 * N:
                break
        p += 1
    D = -(-N // (4 * (m + 2) ** 2))
    if stats.get("tightD"):
        D = None                                     # filled per instance below: the largest D that still covers
    aP_sum = [sum(zP[t] for t in range(m) if a >> t & 1) for a in range(1 << m)]
    # K(c, j) mod p, sorted distinct, for all c and j <= m/2.
    K = {}
    for c in range(1 << m):
        buckets = [[] for _ in range(m // 2 + 1)]
        for a in range(1 << m):
            dist = bin(a ^ c).count("1")
            if dist <= m // 2:
                buckets[dist].append(aP_sum[a] % p)
        for j in range(m // 2 + 1):
            lst = sorted(buckets[j])
            K[c, j] = [x for t, x in enumerate(lst) if t == 0 or lst[t - 1] != x]
    if D is None:
        D = 1
        while all(any(len(K[c, j]) >= D + 1 for j in range(m // 2 + 1)) for c in range(1 << m)):
            D += 1
    T = {j: [c for c in range(1 << m) if len(K[c, j]) >= D] for j in range(m // 2 + 1)}
    covered_cs = sorted(c for j in T for c in T[j])
    for c in range(1 << m):
        if sorted_count(covered_cs, c) == 0:
            raise Fail("Lemma 5.1: prefix in no family")

    answer = False
    found = None
    for j in range(m // 2 + 1):
        if not T[j]:
            continue
        s = j / m
        lstar = 0.5 * (n - 2 * m + (h(s) + s) * m + 2 * (1 - s) * (DRP - DLP) * m)
        l = int(round(lstar))
        if not (m <= l <= n - 2 * m):
            raise Fail(f"fit: l_j = {l} outside [m, n - 2m]")
        stats["fit_checks"] += 1
        outside = order[m:]
        B1, B2 = outside[:l], outside[l:]
        B1r = [i for i in B1 if i not in Qa]          # B1 \ Qa  (Qa is B1's first m coordinates)
        B2r = [i for i in B2 if i not in Qc]          # B2 \ Qc
        assert B1[:m] == Qa and B2[-m:] == Qc
        if mode == "overlap":
            left_blocks = (Qa, B1r + Qc)              # INVALID: Qc lies in B2 but its sums are offered on the left
        else:
            left_blocks = (Qa, B1r)
        right_blocks = (B2r, Qc)
        SA1, SA2 = sums_with_reps(z, left_blocks[0]), sums_with_reps(z, left_blocks[1])
        SB1, SB2 = sums_with_reps(z, right_blocks[0]), sums_with_reps(z, right_blocks[1])
        # Greedy covering (S2 Lemma 2.1) on T_j x Z_p with K_c = K(c, j); incremental counts, least residue on ties.
        Tj = T[j]
        unc = [[1] * p for _ in Tj]
        cnt = [sum(len(K[c, j]) for c in Tj)] * p
        left_unc = len(Tj) * p
        R = []
        while left_unc:
            best = max(range(p), key=lambda r: (cnt[r], -r))
            R.append(best)
            for ti, c in enumerate(Tj):
                for k in K[c, j]:
                    y = (best - k) % p
                    if unc[ti][y]:
                        unc[ti][y] = 0
                        left_unc -= 1
                        for k2 in K[c, j]:
                            cnt[(y + k2) % p] -= 1
        if len(R) > (p / D) * (1 + math.log(len(Tj) * p)) + 1:
            raise Fail("Lemma 2.1(ii)")
        # Deduped record lists. Left record: (aP, s1, s2) with key aP.z + s1 + s2.
        bP_list = []
        for v in product((-1, 0, 1), repeat=m):
            if sum(1 for x in v if x) == j:
                bP_list.append(v)
        bP_sum = [sum(zP[t] * v[t] for t in range(m)) for v in bP_list]
        A = []
        for a in range(1 << m):
            for s1, _ in SA1:
                for s2, _ in SA2:
                    A.append((aP_sum[a] + s1 + s2, a, s1, s2))
        B = []
        for bi, v in enumerate(bP_list):
            for t1, _ in SB1:
                for t2, _ in SB2:
                    B.append((tau - (bP_sum[bi] + t1 + t2), bi, t1, t2))
        sizeA_raw = 1 << (m + l)
        sizeB_raw = len(bP_list) * (1 << (n - m - l))
        # Lemma 3.4 sizes, d(P) = m - log2 N: |A'| <= |A| N / 2^m.
        if mode != "overlap":
            if len(A) * (1 << m) > sizeA_raw * N or len(B) * (1 << m) > sizeB_raw * N:
                raise Fail("Lemma 3.4 size line")
            stats["size_checks"] += 1
        # Weights and best shift (S2 Lemma 2.2) on the DEDUPED histograms.
        nprime = 2 * m - 2 * j
        eL, eR = math.ceil((DLP + EPS) * nprime), math.ceil((DRP + EPS) * nprime)
        hA, hB = [0] * p, [0] * p
        for rec in A:
            hA[rec[0] % p] += 1
        for rec in B:
            hB[rec[0] % p] += 1
        # Convolution route (Step 4) must equal the direct histogram.
        hP = [0] * p
        for a in range(1 << m):
            hP[aP_sum[a] % p] += 1
        h1 = [0] * p
        for s1, _ in SA1:
            for s2, _ in SA2:
                h1[(s1 + s2) % p] += 1
        conv = [0] * p
        for r1 in range(p):
            if hP[r1]:
                for r2 in range(p):
                    if h1[r2]:
                        conv[(r1 + r2) % p] += hP[r1] * h1[r2]
        if conv != hA:
            raise Fail("Step 4 convolution")
        w = [(1 << eL) * hA[r] + (1 << eR) * hB[r] for r in range(p)]
        Wtot = sum(w)
        shifted = [sum(w[(r + sg) % p] for r in R) for sg in range(p)]
        sg = min(range(p), key=lambda x: (shifted[x], x))
        if shifted[sg] * p > len(R) * Wtot:
            raise Fail("Lemma 2.2")
        C = sorted((r + sg) % p for r in R)
        stats["kept_w"] += shifted[sg]
        stats["full_w"] += Wtot
        # Step 5 generation by meet in the middle; compare with the direct filter.
        h_ = m // 2
        L1 = sorted(((aP_sum[a1] + s1) % p, a1, s1) for a1 in range(1 << h_) for s1, _ in SA1)
        L1keys = [x[0] for x in L1]
        genA = []
        for a2 in range(1 << (m - h_)):
            for s2, _ in SA2:
                k2 = aP_sum[a2 << h_] + s2
                for r in C:
                    want = (r - k2) % p
                    lo, hi = bisect.bisect_left(L1keys, want), bisect.bisect_right(L1keys, want)
                    for _, a1, s1 in L1[lo:hi]:
                        a = a1 | (a2 << h_)
                        genA.append((aP_sum[a] + s1 + s2, a, s1, s2))
        genA.sort()
        keptA = sorted(rec for rec in A if sorted_count(C, rec[0] % p))
        if genA != keptA:
            raise Fail("Step 5 left generation")
        # Right side: ternary halves grouped by nonzero count.
        def tern_half(lo_t, hi_t):
            out = []
            for v in product((-1, 0, 1), repeat=hi_t - lo_t):
                nz = sum(1 for x in v if x)
                if nz <= j:
                    out.append((nz, sum(zP[lo_t + t] * v[t] for t in range(hi_t - lo_t)), v))
            return out
        H1, H2 = tern_half(0, h_), tern_half(h_, m)
        R1 = sorted(((tau - (ps + t1)) % p, nz, ps, v, t1) for nz, ps, v in H1 for t1, _ in SB1)
        genB = []
        for nz2, ps2, v2 in H2:
            for t2, _ in SB2:
                for r in C:
                    for (res, nz1, ps1, v1, t1) in R1:          # small lists: a linear sweep stands in for the
                        if nz1 + nz2 != j:                       # grouped binary search of S2 Step 5
                            continue
                        if (res - ps2 - t2) % p == r:
                            bi = bisect.bisect_left(bP_list, v1 + v2)
                            genB.append((tau - (ps1 + ps2 + t1 + t2), bi, t1, t2))
        genB.sort()
        keptB = sorted(rec for rec in B if sorted_count(C, rec[0] % p))
        if genB != keptB:
            raise Fail("Step 5 right generation")
        stats["gen_checks"] += 1

        # Exact keyed counter (trivial circuit): a query lists the completions of its wildcards and looks up
        # (key, aP) in the sorted row list.
        if mode == "dedupP":
            # INVALID: one row per prefix SUM. Each a_P is replaced by the least mask with the same prefix sum
            # (sorted list + bisection), then the rows are deduplicated by a sorted pass.
            reps = sorted((aP_sum[a], a) for a in range(1 << m))
            def rep_of(a):
                return reps[bisect.bisect_left(reps, (aP_sum[a], -1))][1]
            tmp = sorted((k, rep_of(a), s1, s2) for (k, a, s1, s2) in keptA)
            keptA = [x for t, x in enumerate(tmp) if t == 0 or tmp[t - 1] != x]

        def count(Al, Bl):
            rows = sorted((rec[0], rec[1]) for rec in Al)
            tot = 0
            for rec in Bl:
                v = bP_list[rec[1]]
                if mode == "nocompat":
                    tot += sum(1 for x in rows if x[0] == rec[0])
                    continue
                fixed = 0
                free = []
                for t in range(m):
                    if v[t] == 1:
                        pass              # a_t must be 0
                    elif v[t] == -1:
                        fixed |= 1 << t   # a_t must be 1
                    else:
                        free.append(t)
                for bits in range(1 << len(free)):
                    a = fixed
                    for u, t in enumerate(free):
                        if bits >> u & 1:
                            a |= 1 << t
                    tot += sorted_count(rows, (rec[0], a))
            return tot

        cA, cB = keptA, keptB
        total = count(cA, cB)
        if total > 0 and not answer:
            answer = True
            # Recovery by bisection (S2 Cor. 2), then representatives.
            while len(cA) > 1:
                half = cA[:len(cA) // 2]
                cA = half if count(half, cB) > 0 else cA[len(cA) // 2:]
            while len(cB) > 1:
                half = cB[:len(cB) // 2]
                cB = half if count(cA, half) > 0 else cB[len(cB) // 2:]
            (ka, a, s1, s2), (kb, bi, t1, t2) = cA[0], cB[0]

            def rep(S, idx, sval):
                pos = bisect.bisect_left(S, (sval, -1))
                assert S[pos][0] == sval
                return rep_vector(n, idx, S[pos][1])
            vec = [0] * n
            for t, i in enumerate(P):
                vec[i] = (a >> t & 1) + bP_list[bi][t]
            for part in (rep(SA1, left_blocks[0], s1), rep(SA2, left_blocks[1], s2),
                         rep(SB1, right_blocks[0], t1), rep(SB2, right_blocks[1], t2)):
                for i in range(n):
                    vec[i] += part[i]
            found = vec
        # dedupP control, layer level: does some kept row (any a' with a row) pair compatibly with b = c - a for
        # an a at distance j, with c's own outside sums? S2 Lemma 5.2 needs this in EVERY layer holding c_P.
        if mode == "dedupP" and stats["sol_list"]:
            rowsk = sorted((r[1], r[2], r[3]) for r in keptA)
            keptB_k = sorted((r[1], r[2], r[3]) for r in keptB)
            for cvec in stats["sol_list"][:cap_sol]:
                cP = sum(cvec[P[t]] << t for t in range(m))
                if sorted_count(T[j], cP) == 0:
                    continue
                s1c = sum(z[i] for i in Qa if cvec[i]); s2c = sum(z[i] for i in B1r if cvec[i])
                t1c = sum(z[i] for i in B2r if cvec[i]); t2c = sum(z[i] for i in Qc if cvec[i])
                hit = False
                for a in range(1 << m):
                    if bin(a ^ cP).count("1") != j:
                        continue
                    v = tuple(((cP >> t) & 1) - ((a >> t) & 1) for t in range(m))
                    bi = bisect.bisect_left(bP_list, v)
                    if not sorted_count(keptB_k, (bi, t1c, t2c)):
                        continue
                    for a2 in range(1 << m):
                        if aP_sum[a2] != aP_sum[a] or not sorted_count(rowsk, (a2, s1c, s2c)):
                            continue
                        if all((v[t] == 0) or (v[t] == 1 and not a2 >> t & 1) or (v[t] == -1 and a2 >> t & 1)
                               for t in range(m)):
                            hit = True
                            break
                    if hit:
                        break
                if not hit:
                    stats["dedupP_layer_miss"] += 1

        # Lemma 3.2: every solution's own record pair is kept in every layer whose family holds c_P.
        if mode == "normal" and stats["sol_list"]:
            keptA_k = sorted((r[1], r[2], r[3]) for r in keptA)
            keptB_k = sorted((r[1], r[2], r[3]) for r in keptB)
            for cvec in stats["sol_list"][:cap_sol]:
                cP = sum(cvec[P[t]] << t for t in range(m))
                if sorted_count(T[j], cP) == 0:
                    continue
                def bsum(idx):
                    return sum(z[i] for i in idx if cvec[i])
                s1c, s2c, t1c, t2c = bsum(Qa), bsum(B1r), bsum(B2r), bsum(Qc)
                ok = False
                for a in range(1 << m):
                    if bin(a ^ cP).count("1") != j:
                        continue
                    v = tuple(((cP >> t) & 1) - ((a >> t) & 1) for t in range(m))
                    bi = bisect.bisect_left(bP_list, v)
                    if sorted_count(keptA_k, (a, s1c, s2c)) and sorted_count(keptB_k, (bi, t1c, t2c)):
                        ok = True
                        break
                if not ok:
                    raise Fail("Lemma 3.2: a solution's pair was dropped")
                stats["d2_checks"] += 1
    return answer, found


def instances(rng, n, kind):
    if kind == "random":
        return [rng.randrange(1, 1 << 20) for _ in range(n)]
    if kind == "small":
        return [rng.randrange(1, 6) for _ in range(n)]
    if kind == "digits":
        # Each block is internally deficient (values from a small set), blocks on separate scales.
        out = []
        for i in range(n):
            blk = min(i // 4, 4)
            out.append(rng.choice((1, 2, 3)) * (64 ** blk))
        return out
    if kind == "mixed":
        return [rng.choice((rng.randrange(1, 4), rng.randrange(1, 1 << 16), -rng.randrange(1, 1 << 10)))
                for _ in range(n)]
    if kind == "uneven":
        # Blocks of very different deficiency: block 0 all equal, block 1 powers of 2, rest random.
        return [7] * 4 + [1 << t for t in range(4)] + [rng.randrange(1, 1 << 14) for _ in range(n - 8)]
    if kind == "adv":
        # Prefix values all equal: many a_P share a sum; one valid completion per target region.
        return [5] * 4 + [rng.randrange(1, 1 << 12) for _ in range(n - 4)]
    raise ValueError(kind)


def main():
    t0 = time.time()
    rng = random.Random(20261010)
    m = 4
    fails = []
    stats = {"fit_checks": 0, "size_checks": 0, "gen_checks": 0, "d2_checks": 0, "kept_w": 0, "full_w": 0,
             "sol_list": None, "dedupP_layer_miss": 0}
    plan = [(18, k) for k in ("random", "small", "digits", "mixed", "uneven", "adv")] * 2 + \
           [(19, "random"), (19, "small"), (19, "mixed"), (19, "uneven")]
    pairs = yes = 0
    ctl = {"nocompat": 0, "overlap": 0, "dedupP": 0, "wrongP": 0}
    ctl_by_D = {"dedupP": [0, 0]}
    for idx, (n, kind) in enumerate(plan):
        z = instances(rng, n, kind)
        allp = sorted((sum(z[i] for i in range(n) if mask >> i & 1), mask) for mask in range(1 << n))
        allsums = [x for x, _ in allp]
        targets = []
        for _ in range(3):
            targets.append(allsums[rng.randrange(len(allsums))])
        for _ in range(2):
            targets.append(rng.randrange(min(allsums) - 3, max(allsums) + 4))
        for tight in (False, True):
            stats["tightD"] = tight
            for tau in targets:
                lo, hi = bisect.bisect_left(allsums, tau), bisect.bisect_right(allsums, tau)
                truth = hi > lo
                sols = [[allp[k][1] >> i & 1 for i in range(n)] for k in range(lo, min(hi, lo + 40))]
                stats["sol_list"] = sols
                try:
                    ans, vec = run(z, tau, m, "normal", stats, allsums)
                except Fail as e:
                    fails.append((n, kind, tau, str(e)))
                    continue
                pairs += 1
                yes += truth
                if ans != truth:
                    fails.append((n, kind, tau, f"answer {ans} vs {truth}"))
                if ans:
                    if not (all(x in (0, 1) for x in vec) and sum(z[i] * vec[i] for i in range(n)) == tau):
                        fails.append((n, kind, tau, "recovered vector invalid"))
                # Controls on the first tightness setting only (time).
                if True:   # controls run in both D settings; dedupP is only exposed when layer 0 is not a family (tight D)
                    for mode in ctl:
                        stats["sol_list"] = sols if mode == "dedupP" else None
                        try:
                            a2, v2 = run(z, tau, m, mode, stats, allsums)
                            if a2 != truth:
                                ctl[mode] += 1
                                if mode in ctl_by_D:
                                    ctl_by_D[mode][int(tight)] += 1
                            elif a2 and not (all(x in (0, 1) for x in v2) and
                                             sum(z[i] * v2[i] for i in range(n)) == tau):
                                ctl[mode] += 1
                        except Fail:
                            ctl[mode] += 1
                        except AssertionError:
                            ctl[mode] += 1
        if time.time() - t0 > 540:
            print("time cap reached at plan item", idx)
            break
    print(f"pairs {pairs} (yes {yes}); failures {len(fails)}")
    for f in fails[:10]:
        print("  FAIL", f)
    print(f"checks: fit {stats['fit_checks']}, sizes {stats['size_checks']}, Step-5 generation {stats['gen_checks']}, "
          f"Lemma 3.2 {stats['d2_checks']}")
    print(f"kept/full deduped weight {stats['kept_w'] / max(1, stats['full_w']):.3f}")
    ok = not fails
    ctl["dedupP"] += stats["dedupP_layer_miss"]
    print(f"dedupP layer-level misses (S2 Lemma 5.2 broken in a layer): {stats['dedupP_layer_miss']}")
    for mode, k in ctl.items():
        print(f"control {mode}: {k} failures -> {'rejected (good)' if k else 'NOT DETECTED'}")
        ok &= k > 0
    print(f"dedupP failures: proof's D {ctl_by_D['dedupP'][0]}, tight D {ctl_by_D['dedupP'][1]}")
    print(f"time {time.time() - t0:.1f} s; EXIT {0 if ok else 1}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
