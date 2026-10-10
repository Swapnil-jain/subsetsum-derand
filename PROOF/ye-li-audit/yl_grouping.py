"""Exhaustive check of Ye-Li Lemma 3.1 (block grouping) bookkeeping, arXiv 2610.10446v1.

For even k and d >= 1, a query on k^2 d coordinates with k^2 d / 2 specified positions is described by
w in {0..k}^{kd} (specified count per block of length k). Sort the blocks by w (ties by position), deal them
cyclically into d groups of k blocks; group i gets total W_i. Claims checked for every description:
  W_d - W_1 <= w_max - w_min <= k, so every W_i in [k^2/2 - k, k^2/2 + k];
  the padding of each group (2k extra positions: k + k^2/2 - W_i zeros, rest stars) is valid (0..2k zeros);
  each enlarged group has exactly (k^2 + 2k)/2 specified positions.
Also an end-to-end matching check at k = 2, d = 2: for every row x of length 8 and every query y with 4
specified positions, y matches x iff every padded group matches its padded row group. Exit 0 = pass.
"""
import sys
from itertools import product

def groups(w, k, d):
    order = sorted(range(k * d), key=lambda j: (w[j], j))
    return [[order[j * d + i] for j in range(k)] for i in range(d)]

def check_desc(k, d):
    n_bad = n = 0
    for w in product(range(k + 1), repeat=k * d):
        if sum(w) != k * k * d // 2: continue
        n += 1
        G = groups(w, k, d)
        W = sorted(sum(w[b] for b in g) for g in G)
        zeros = [k + k * k // 2 - Wi for Wi in W]
        good = (W[-1] - W[0] <= max(w) - min(w) <= k and all(0 <= z <= 2 * k for z in zeros)
                and all(Wi + z == (k * k + 2 * k) // 2 for Wi, z in zip(W, zeros)))
        n_bad += not good
    return n, n_bad

def end_to_end(k=2, d=2):
    L = k * k * d
    bad = 0
    for x in product((0, 1), repeat=L):
        for y in product((0, 1, 2), repeat=L):            # 2 = star
            if sum(c != 2 for c in y) != L // 2: continue
            match = all(c == 2 or c == xi for c, xi in zip(y, x))
            w = [sum(y[b * k + t] != 2 for t in range(k)) for b in range(k * d)]
            ok_all = True
            for g in groups(w, k, d):
                pos = [b * k + t for b in g for t in range(k)]
                W = sum(w[b] for b in g)
                xr = [x[p] for p in pos] + [0] * (2 * k)
                yq = [y[p] for p in pos] + [0] * (k + k * k // 2 - W) + [2] * (k - k * k // 2 + W)
                assert sum(c != 2 for c in yq) == (k * k + 2 * k) // 2
                ok_all &= all(c == 2 or c == xi for c, xi in zip(yq, xr))
            bad += match != ok_all
    return bad

if __name__ == "__main__":
    ok = True
    for k, d in ((2, 1), (2, 2), (2, 3), (2, 4), (4, 1), (4, 2), (6, 1)):
        n, b = check_desc(k, d)
        print("k=%d d=%d descriptions %d, violations %d" % (k, d, n, b))
        ok &= b == 0
    b = end_to_end()
    print("end-to-end k=2 d=2: matching mismatches %d" % b)
    ok &= b == 0
    print("ALL PASS" if ok else "SOME CHECK FAILED")
    sys.exit(0 if ok else 1)
