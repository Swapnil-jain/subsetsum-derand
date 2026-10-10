"""Brute-force check of the deterministic algorithm DET of PROOF.md (Sec. 3) on small n.

Logic check only, not asymptotics: at these sizes D/p is not small, so the saving is not visible.
Written from PROOF.md; it imports nothing from the other check scripts and runs no third-party code.

What is asserted on every instance (exit 1 on any failure):
  * DET answers exactly as brute force (no misses, no false positives);
  * Lemma 4.2 directly: for each target t' in {t, sum X - t} and each solution S' of (X, t') with
    S' cap C in the family T, the class set R + sigma* contains r with r - sum(S' cap A) in K_T (mod p),
    and Lines 5-6 on (X, t') answer yes; this is tested whether or not Step 2 (Lemma 5) fires;
  * Lemma 2.3: R covers all of T x Z_p, exhaustively, and |R| <= (p/D)(1 + ln|T x Z_p|);
  * Lemma 2.4: p * sum_{r in R+sigma*} w(r) <= |R| * sum_r w(r), exactly in integers;
  * the cost function w(r) equals the number of couples Lines 5 creates for class r;
  * run 1 only: the prime of Lemma 2.1 is injective on W(C), and the number of bad primes in [P0, 2 P0]
    is at most the counting bound of Lemma 2.1.
Negative controls (each must miss on some instance with a solution balanced on C):
  * 'single': one residue only (the cheapest class), no covering;
  * 'oneshift': a covering of T x {0} only (every T, but one shift), then the best shift.
Run 2 uses a deliberately non-injective small prime: correctness must not depend on p (Remark 4.4).
"""
import math
import random
import sys
from fractions import Fraction as Fr


def is_prime(q):
    if q < 2:
        return False
    i = 2
    while i * i <= q:
        if q % i == 0:
            return False
        i += 1
    return True


def sums_by_mask(vals):
    out = [0]
    for v in vals:
        out += [s + v for s in out]
    return out


def popc(x):
    return bin(x).count("1")


class Setup:
    """Everything that depends only on (X, C, eps1, eps2) and the prime p (Steps 3 and 4)."""

    def __init__(self, X, c, e1, e2, prime_mode, P0):
        self.X, self.n, self.c, self.e1, self.e2 = X, len(X), c, e1, e2
        n = self.n
        self.Cidx = list(range(c))
        rest = list(range(c, n))
        self.Aidx = rest[: (n - c + 1) // 2]
        self.Bidx = rest[(n - c + 1) // 2:]
        self.SC = sums_by_mask([X[i] for i in self.Cidx])  # sum of Q, Q a mask over C
        self.WC = sorted(set(self.SC))
        # family T (Def. 3.1): masks with (1 - e1) c/2 <= |T| <= c/2
        self.fam = [T for T in range(1 << c) if (1 - e1) * Fr(c, 2) <= popc(T) <= Fr(c, 2)]
        # Q^{+e2}(C): |Q| <= (1 + e2) c/4
        self.Qplus = [Q for Q in range(1 << c) if popc(Q) <= (1 + e2) * Fr(c, 4)]
        self.p, self.injective, self.bad, self.badbound = self.choose_prime(prime_mode, P0)
        p = self.p
        # K_T = W'(T) mod p, W'(T) = {sum Q : Q subset T, (1-e2)|T|/2 <= |Q| <= (1+e2)|T|/2}
        self.K = {}
        for T in self.fam:
            k = popc(T)
            self.K[T] = sorted({self.SC[Q] % p for Q in range(1 << c) if Q & ~T == 0
                                and (1 - e2) * Fr(k, 2) <= popc(Q) <= (1 + e2) * Fr(k, 2)})
        self.D = min(len(v) for v in self.K.values())
        LA = sorted(set(sums_by_mask([X[i] for i in self.Aidx])))
        LB = sorted(set(sums_by_mask([X[i] for i in self.Bidx])))
        self.LA, self.LB = LA, LB
        # Line 3: sorted sublists by residue (a scan in sorted order keeps each sublist sorted)
        self.LAi = [[] for _ in range(p)]
        self.LBi = [[] for _ in range(p)]
        for a in LA:
            self.LAi[a % p].append(a)
        for b in LB:
            self.LBi[b % p].append(b)
        self.sQ = [self.SC[Q] % p for Q in self.Qplus]

    def choose_prime(self, mode, P0):
        WC = self.WC
        if mode == "injective":
            # Lemma 2.1: first prime in [P0, 2 P0] on which W(C) is injective
            primes = [q for q in range(P0, 2 * P0 + 1) if is_prime(q)]
            bad = [q for q in primes if len({w % q for w in WC}) < len(WC)]
            maxbits = max(1, max(WC) - min(WC)).bit_length()
            # each nonzero difference |d| < 2^maxbits has < maxbits / log2(P0) prime factors >= P0
            per_diff = math.floor(maxbits / math.log2(P0))
            badbound = (len(WC) * (len(WC) - 1) // 2) * per_diff
            good = [q for q in primes if q not in set(bad)]
            return (good[0] if good else None), True, len(bad), badbound
        # mode 'small': first prime >= P0, no injectivity requirement (Remark 4.4)
        q = P0
        while not is_prime(q):
            q += 1
        return q, len({w % q for w in WC}) == len(WC), None, None

    def greedy_cover(self, shifts):
        """Lemma 2.3: greedy cover of U = {(T, y) : T in fam, y in shifts}; r covers (T, y) iff r - y in K_T.
        cnt[r] = number of uncovered elements r covers; a bucket queue finds a maximiser (counts only fall)."""
        p = self.p
        shifts = list(shifts)
        unc = {T: bytearray(p) for T in self.fam}
        for T in self.fam:
            for y in shifts:
                unc[T][y] = 1
        left = len(self.fam) * len(shifts)
        if len(shifts) == p:
            cnt = [sum(len(v) for v in self.K.values())] * p
        else:
            cnt = [0] * p
            for T in self.fam:
                for y in shifts:
                    for k in self.K[T]:
                        cnt[(y + k) % p] += 1
        top = max(cnt)
        buckets = [set() for _ in range(top + 1)]
        for r, v in enumerate(cnt):
            buckets[v].add(r)
        R = []
        while left:
            while not buckets[top]:
                top -= 1
            assert top > 0
            r = min(buckets[top])  # ties: smallest residue
            R.append(r)
            for T in self.fam:
                U = unc[T]
                KT = self.K[T]
                for k in KT:
                    y = (r - k) % p
                    if U[y]:
                        U[y] = 0
                        left -= 1
                        for k2 in KT:
                            z = (y + k2) % p
                            v = cnt[z]
                            buckets[v].discard(z)
                            buckets[v - 1].add(z)
                            cnt[z] = v - 1
            assert cnt[r] == 0
        assert len(set(R)) == len(R)
        return R

    def covers_all(self, classes):
        """Exhaustive check of Lemma 2.3 (i): every (T, y) has some r in classes with r - y in K_T."""
        p = self.p
        for T in self.fam:
            hit = bytearray(p)
            for r in classes:
                for k in self.K[T]:
                    hit[(r - k) % p] = 1
            if sum(hit) != p:
                return False
        return True

    def weights(self, tp):
        """w(r) = |R_{A,r}| + |R_{B,r}| in couples, R_{B,r} being the class of t' - r (Def. 3.2)."""
        p = self.p
        hA = [len(s) for s in self.LAi]
        hB = [len(s) for s in self.LBi]
        return [sum(hA[(r - s) % p] for s in self.sQ) + sum(hB[(tp - r - s) % p] for s in self.sQ)
                for r in range(p)]

    def best_shift(self, R, w):
        """sigma* = argmin_sigma sum_{r in R} w(r + sigma) (ties: smallest sigma). All p scores at once, exactly,
        as one big-integer product (Kronecker substitution): coefficient p - 1 + sigma of
        (sum_{i < 2p} w_{i mod p} x^i) * (sum_{r in R} x^{p - 1 - r}) is sum_{r in R} w_{r + sigma}."""
        p = self.p
        width = (sum(w) * 2 + 2).bit_length() // 8 + 1
        A = int.from_bytes(b"".join(w[i % p].to_bytes(width, "little") for i in range(2 * p)), "little")
        ind = bytearray(width * p)
        for r in R:
            ind[width * (p - 1 - r)] = 1
        B = int.from_bytes(bytes(ind), "little")
        prod = (A * B).to_bytes(width * 3 * p + width, "little")
        score = [int.from_bytes(prod[width * (p - 1 + sg): width * (p + sg)], "little") for sg in range(p)]
        sg = min(range(p), key=score.__getitem__)
        assert score[sg] == sum(w[(r + sg) % p] for r in R)
        assert sum(score) == len(R) * sum(w)  # the averaging identity of Lemma 2.4, exactly
        return sg

    def lines56(self, tp, r):
        """Lines 5-6 for one class r: build R_{A,r}, R_{B,r} (Residue-Couple-List) and search them.
        Returns (found, number of couples created)."""
        p = self.p
        RA, RB = {}, {}
        made = 0
        for Q, sq in zip(self.Qplus, self.sQ):
            SQ = self.SC[Q]
            for a in self.LAi[(r - sq) % p]:
                RA.setdefault(a + SQ, []).append(Q)
                made += 1
            for b in self.LBi[(tp - r - sq) % p]:
                RB.setdefault(b + SQ, []).append(Q)
                made += 1
        for a2, qa in RA.items():
            qb = RB.get(tp - a2)
            if qb and any(Q1 & Q2 == 0 for Q1 in qa for Q2 in qb):
                return True, made
        return False, made


def unbal(X, c, e1, tp):
    """Step 1 (CJRS Lemma 6, as in its proof): is there S' with sum t' and |S' cap C| < (1 - e1) c/2?
    A' = C plus the A half; L'_A = sums of subsets T of A' with |T cap C| < (1 - e1) c/2."""
    n = len(X)
    Ap = list(range(c)) + list(range(c, c + (n - c + 1) // 2))
    rest = [i for i in range(n) if i not in set(Ap)]
    sA = sums_by_mask([X[i] for i in Ap])
    LpA = {sA[T] for T in range(1 << len(Ap)) if popc(T & ((1 << c) - 1)) < (1 - e1) * Fr(c, 2)}
    Lr = set(sums_by_mask([X[i] for i in rest]))
    return any(tp - a in Lr for a in LpA)


def mitm(X, t):
    h = len(X) // 2
    L = set(sums_by_mask(X[:h]))
    return any(t - b in L for b in set(sums_by_mask(X[h:])))


def det(X, t, c, e1, e2, kappa, prime_mode, P0, stats, control=None):
    """DET of PROOF.md Sec. 3 (returns its answer). Also runs the Lemma 4.2 check on both targets."""
    total = sum(X)
    targets = [t, total - t]
    # Step 1
    step1 = any(unbal(X, c, e1, tp) for tp in targets)
    S = Setup(X, c, e1, e2, prime_mode, P0)
    stats["inj"] += S.injective
    if S.bad is not None:
        assert S.bad <= S.badbound, ("Lemma 2.1 bad-prime bound", S.bad, S.badbound)
        if S.bad >= stats["maxbad"]:
            stats["maxbad"], stats["maxbound"] = S.bad, S.badbound
    # Step 2 (Lemma 5): exact MITM if |W(C)| <= 2^c kappa
    step2 = len(S.WC) <= (1 << c) * kappa
    stats["step2"] += step2
    if S.p is None:
        stats["noprime"] += 1
        return mitm(X, t)
    p = S.p
    # Step 4: covering
    if control == "single":
        R = None
    elif control == "oneshift":
        R = S.greedy_cover([0])
    else:
        R = S.greedy_cover(range(p))
        U = len(S.fam) * p
        assert len(R) * S.D <= p * (1 + math.log(U)) * (1 + 1e-12), "Lemma 2.3 (ii)"
    found_core = False
    for tp in targets:
        w = S.weights(tp)
        if control == "single":
            classes = [min(range(p), key=w.__getitem__)]
        else:
            sg = S.best_shift(R, w)
            classes = [(r + sg) % p for r in R]
            if control is None:
                assert S.covers_all(classes), "Lemma 2.3 (i) after the shift"
                kept = sum(w[r] for r in classes)
                assert p * kept <= len(R) * sum(w), "Lemma 2.4"
                stats["kept"] += kept
                stats["tot"] += sum(w)
        got = False
        for r in classes:
            f, made = S.lines56(tp, r)
            assert made == w[r], "w(r) must equal the couples created"
            if f:
                got = True
                break
        found_core |= got
        # Lemma 4.2 against brute force on target tp: every solution S' with S' cap C in the family
        # must have a correct key in some class, and then Lines 5-6 must answer yes on tp.
        sumsX = sums_by_mask(X)
        Cmask = (1 << c) - 1
        has_bal = False
        for mask, s in enumerate(sumsX):
            if s != tp:
                continue
            T = mask & Cmask
            if T not in S.K:
                continue
            has_bal = True
            stats["bal_sols"] += 1
            yA = sum(X[i] for i in S.Aidx if mask >> i & 1)
            KT = set(S.K[T])
            hit = any((r - yA) % p in KT for r in classes)
            stats["unhit_sols"] += not hit
            if control is None:
                assert hit, "Lemma 4.2: no class holds a correct key"
        if has_bal:
            stats["bal_targets"] += 1
            stats["bal_target_miss"] += not got
            if control is None:
                assert got, "Lemma 4.2: Lines 5-6 missed a target with a balanced solution"
    answer = step1 or (mitm(X, t) if step2 else found_core)
    return answer


def brute(X, t):
    return t in set(sums_by_mask(X))


def make_instance(rng, n, fam):
    if fam == "random":
        X = [rng.randrange(1, 1 << 30) for _ in range(n)]
    elif fam == "small":
        X = [rng.randrange(1, 41) for _ in range(n)]
    elif fam == "mult":
        X = [667 * rng.randrange(1, 1 << 12) for _ in range(n)]
    else:
        X = [1 << rng.randrange(0, 20) for _ in range(n)]
    if rng.random() < 0.7:
        t = sum(x for x in X if rng.random() < 0.5)
    else:
        t = rng.randrange(1, sum(X) + 1)
    return X, t


def run(name, n, c, e1, e2, kappa, prime_mode, P0fun, trials, seed):
    rng = random.Random(seed)
    res = {}
    fails = 0
    for ctl in (None, "single", "oneshift"):
        res[ctl] = dict(inst=0, yes=0, miss=0, fp=0, bal_targets=0, bal_target_miss=0, bal_sols=0,
                        unhit_sols=0, step2=0, inj=0, noprime=0, kept=0, tot=0, maxbad=0, maxbound=0)
    for fam in ("random", "small", "mult", "pow2"):
        for _ in range(trials):
            X, t = make_instance(rng, n, fam)
            truth = brute(X, t)
            WC = set(sums_by_mask(X[:c]))
            P0 = P0fun(len(WC))
            for ctl in (None, "single", "oneshift"):
                st = res[ctl]
                ans = det(X, t, c, e1, e2, kappa, prime_mode, P0, st, ctl)
                st["inst"] += 1
                st["yes"] += truth
                st["miss"] += truth and not ans
                st["fp"] += ans and not truth
    print(f"== {name}: n={n} |C|={c} eps1={e1} eps2={e2} prime={prime_mode}")
    for ctl, st in res.items():
        extra = ""
        if ctl is None:
            extra = f" kept/total={st['kept'] / max(1, st['tot']):.3f} injective_p={st['inj']}/{st['inst']}" \
                    f" no_prime={st['noprime']}"
        if ctl is None and prime_mode == "injective":
            extra += f" worst_bad_primes={st['maxbad']}<=bound {st['maxbound']}"
        print(f"  {str(ctl):9s} instances={st['inst']} yes={st['yes']} misses={st['miss']} false_pos={st['fp']}"
              f" | targets with a balanced solution={st['bal_targets']} Lines5-6 misses={st['bal_target_miss']}"
              f" | balanced solutions={st['bal_sols']} without a key in the classes={st['unhit_sols']}"
              f" | step2_fired={st['step2']}{extra}")
    d = res[None]
    if d["miss"] or d["fp"] or d["bal_target_miss"] or d["unhit_sols"]:
        print("  FAIL: deterministic algorithm missed or false-positived")
        fails += 1
    for ctl in ("single", "oneshift"):
        if res[ctl]["bal_target_miss"] == 0:
            print(f"  FAIL: control {ctl} never missed")
            fails += 1
        if res[ctl]["fp"]:
            print(f"  FAIL: control {ctl} gave a false positive")
            fails += 1
    return fails


def main():
    fails = 0
    # Run 1: the prime of Lemma 2.1, range [P0, 2 P0] with P0 = 2 |W(C)|^2 (toy stand-in for l^5).
    fails += run("run 1 (injective prime)", 14, 6, Fr(3, 10), Fr(1, 2), Fr(1, 2), "injective",
                 lambda N: 2 * N * N, 25, 2026)
    # Run 2: larger C, deliberately small non-injective prime (correctness must not depend on p).
    fails += run("run 2 (small prime, non-injective allowed)", 16, 8, Fr(3, 10), Fr(1, 2), Fr(1, 4), "small",
                 lambda N: 2 * N, 20, 138)
    print("CHECK", "PASS" if fails == 0 else "FAIL")
    sys.exit(0 if fails == 0 else 1)


if __name__ == "__main__":
    main()
