# Deterministic Subset Sum in time O(2^{n/2} n^{-gamma}) for every gamma < 0.010104

Draft, private. Base result: Chen, Jin, Randolph and Servedio, "Subset Sum in Time 2^{n/2}/poly(n)",
arXiv 2301.07134 ("CJRS"); all numbering below (Lemmas 1-8, Observations 1-4, Theorem 2, Equations (1)-(4),
Figures 4-5, footnote 8) is that of the arXiv version. Certificate: `cert_gamma.py` (exact rationals, outward
rounding). Mechanical check on small instances: `check_stage1.py` (Sec. 8).

**Review status.** The argument was audited (`../AUDIT.md`, sec. 2(a)) and then judged from refute-by-default
against the primary text (`../JUDGE_S1.md`): CONFIRMED WITH FIXES, all of them bookkeeping or presentation. This
write-up applies every fix; where each one lands is listed at the end of Sec. 0. This complete write-up has not
had its own adversarial review yet.

## 0. Statement

*Model (CJRS Sec. 1.1).* Input: a multiset X = {x_1, ..., x_n} of positive integers and a target t, every number
of at most l bits, on a RAM with l-bit words, where **l = poly(n)** and l >= log2 t. Circuit RAM: an operation
mapping O(1) words to one word with a poly(l)-size unbounded fan-in circuit costs its depth; in particular AC0
operations cost O(1) and multiplication or reduction mod p cost O(log l). Word RAM: the usual unit-cost
arithmetic, no free AC0. Logarithms are base 2; ln is natural; H(y) = -y log y - (1-y) log(1-y). O~ hides factors
polylog(l) = polylog(n). Every algorithm below is deterministic and its time bound holds for every input.

*Constants (CJRS, proof of Theorem 2).* For eps1, eps2 in (0, 1) put

    beta    = 1 / H((1 + eps2)/4),
    lambda0 = (1 - eps1)/2 * beta * (1 - H((1 - eps2)/2)),
    delta   = (1 - H((1 - eps1)/2)) * beta,
    theta0  = (1 - eps1/2) * beta - 1 - lambda0,
    g(eps1, eps2) = min( lambda0/2, delta/2, theta0 ).

CJRS fix (eps1, eps2) = (eps1*, eps2*), the solution of their Equations (3) and (4):

    (3)  (1 - H((1 - eps1)/2)) / ((1 - eps1)/2) = 1 - H((1 - eps2)/2),
    (4)  1 + eps1 - 3 H((1 - eps1)/2) = -2 H((1 + eps2)/4).

(3) says delta = lambda0 and (4) says lambda0/2 = theta0, so at the root the three terms are equal. CJRS then use
lambda = (1 - 10^{-5}) lambda0. Define **gamma* := g(eps1*, eps2*)**.

**Theorem 1.** For every constant gamma < gamma*, Subset Sum is decided deterministically in time
O(2^{n/2} l^{-gamma}) <= O(2^{n/2} n^{-gamma}) in the circuit RAM, for all l = poly(n).

**Corollary 2 (word RAM).** The same bound, O(2^{n/2} n^{-gamma}) for every gamma < gamma*, holds in the word RAM.

**Corollary 3 (search).** A solution can be found deterministically in the same time.

**Certificate 6.3 (values).** gamma* lies in [0.0101041782, 0.0101041783] (all three terms enclosed there, on a
certified root box of (3), (4)), so gamma* = 0.010104 to six digits and gamma* > 0.0101. Independently of the
roots, the rational point P = (0.15792, 0.24267) has g(P) >= 0.0101038, so Theorem 1 with gamma = 0.0101 needs
no irrational constant. CJRS's printed rounding (0.1579, 0.2427) gives g < 0.0101 (certified), so the exact
roots, or a better rational point, are needed for the value 0.0101.

*Context.* CJRS's Sec. 6 asks: "Can our results be extended to achieve deterministic algorithms with worst-case
running time 2^{n/2}/poly(n)?" Theorem 1 answers yes. A literature search on 2026-10-10 found no earlier
deterministic 2^{n/2}/poly(n) algorithm; that is evidence, not proof, of novelty. The saving is CJRS's Sec. 4
saving (n^{-0.0101}); their stronger Sec. 3 (n^{-1/2}) and Sec. 5 (n^{-0.5023}) results stay randomized, because
the pseudolinear hash h_m of their Lemma 1 has no deterministic replacement here.

*Credit.* Taken from CJRS, cited fact by fact in Sec. 1: the model, the reductions of Observation 1 and
footnote 8, Lemmas 2, 3, 5, 6 and 8 with Residue-Couple-List and the OV word operation, Observations 2 and 4,
the constants, the good-residue characterisation and the size bound on W' in the proof of Theorem 2, and the cost
accounting of Lines 1-3. **New here:** the deterministic prime (Lemma 2.1, replacing the random prime and
Lemma 7), the bound on W'(T) for all T at once (Lemma 2.2, CJRS's argument without Lemma 7), the universal
residue covering with the best shift (Lemmas 2.3 and 2.4, replacing the s(l) random residues and the cutoff
k(n, l)), the accounting of Sec. 5 with the per-class overhead, the choice of lambda below lambda0 that gives every
gamma < gamma* (Lemma 6.2), and the certificate. Lemma 2.3 is greedy set cover (Johnson 1974, Lovasz 1975,
Chvatal 1979) and Lemma 2.4 is an averaging step; what is new is to use them on the family T x Z_p.

*Judge fixes applied.* (F1) "every gamma < gamma* = 0.010104" with the exact roots: Theorem 1, Def. 6.1,
Certificate 6.3. (F2) the per-class |Q| term and the p-sublist memory: Lemmas 5.1 and 5.2. (F3) the notation
slip (the audit wrote R_{B,t-r}; in CJRS's notation R_{B,r} already is the class t - r; the audit also wrote t
for the shift): Def. 3.2, shift renamed sigma. (F4) the input model: Sec. 0 and Remark 7.2. (F5) Step 1 is CJRS's
Lemma 6 procedure, not an arbitrary exact search: Fact F5 and Step 1; `check_stage1.py` implements that
procedure. The prime-search cost, asked for separately, is Lemma 2.1(ii).

## 1. What is used from CJRS

Write Lambda := l/(beta log l), c := |C| and Q+ := Q^{+eps2}(C) = {Q subset C : |Q| <= (1 + eps2) c/4}.
For a set Y of integers, W(Y) is the set of distinct subset sums and L_Y the sorted list of W(Y). Subsets of C
are subsets of index positions, so multisets cause no trouble.

- **(F1) Equation (1) (Stirling).** For integers 0 <= j <= k/2, sum_{i <= j} binom(k, i) <= 2^{H(j/k) k}.
- **(F2) Observation 1.** Elements larger than t can be dropped. If t <= 2^{0.499n}, dynamic programming decides
  the instance in O(n t) time, deterministically. Hence assume t >= 2^{0.499n}, so l >= 0.499n.
- **(F3) Footnote 8 and the proof of Lemma 6.** S is a solution of (X, t) iff X \ S is a solution of
  (X, Σ(X) - t), and |(X \ S) ∩ C| = c - |S ∩ C|.
- **(F4) Lemma 5.** Given Y subset X with |Y| <= n/2 and |W(Y)| <= 2^{|Y|} l^{-lambda}, (X, t) is decided
  deterministically in O~(2^{n/2} l^{-lambda/2}).
- **(F5) Lemma 6, as its proof gives it.** For |Y| = c and a constant eps > 0, the procedure UNBAL(X, t', Y, eps)
  of that proof (fix A' ⊇ Y with |A'| = (n + (delta/beta) c)/2; build the sorted list of Σ(T) over T subset A'
  with |T ∩ Y| < (1 - eps) c/2, and L_{X \ A'}; run the two-pointer scan) answers whether some solution S' of
  (X, t') has |S' ∩ Y| < (1 - eps) c/2. It is exact (every reported pair is a solution, every such solution is
  reported) and takes O~(2^{n/2} l^{-delta/2}) time with delta = (1 - H((1 - eps)/2)) beta. The time bound comes
  from the list sizes alone and does not use the lemma's hypothesis that such a solution exists.
- **(F6) Lemmas 2 and 3.** Sorted-Sum-Enumeration lists W(Y) in sorted order in O(2^{|Y|}) time.
- **(F7) Lemma 8 and Figure 5 (Residue-Couple-List).** Given sorted sublists {L_{A,i}}_{i in Z_p} and a residue
  r, Line 5 builds R_{A,r} = {(a + Σ(Q), Q) : a in L_A, Q in Q+, a + Σ(Q) ≡ r (mod p)} sorted by sum, with all
  couples of equal sum merged into one record; likewise R_{B,r} for b + Σ(Q) ≡ t' - r. Line 6 then finds a pair
  (a', Q1) in R_{A,r}, (b', Q2) in R_{B,r} with a' + b' = t' and Q1 ∩ Q2 = ∅, if one exists, in time linear in
  the two lists, using one OV word operation per candidate record pair (each record's sub-collection of Q+ fits
  in one word because c |Q+| <= l). The only randomness in Sec. 4 is the prime p and the residues r (with the
  cutoff k(n, l)); Lemmas 2, 3, 5, 6, 8 are deterministic as written.
- **(F8) Proof of Theorem 2, part (i).** If |S ∩ C| = k and Q ranges over subsets of S ∩ C, at most
  2 * 2^{H((1 - eps2)/2) k} of them have |Q| outside [(1 - eps2) k/2, (1 + eps2) k/2] (by F1 and Q -> (S ∩ C) \ Q).
  Also |W(C)| <= |W(T)| 2^{|C \ T|} for T subset C, so Condition (2), |W(C)| > 2^c l^{-lambda}, gives
  |W(T)| > 2^{|T|} l^{-lambda} for every T subset C.
- **(F9) Observation 2.** n runs of a deterministic decision algorithm on shrinking subinstances find a solution.
- **(F10) Observation 4.** The word RAM variant: run with word length l' = 0.1n (block C' sized for l'), store
  sub-collections in ceil(l'/l) = O(1) words, and replace OV by a memo table built in 2^{0.21n} time.

Also used, from CJRS's proof of Theorem 2: |Q+| <= 2^{H((1 + eps2)/4) c} = 2^{c/beta} <= Lambda (F1 with
(1 + eps2)/4 <= 1/2), and the time of Line 3, O((2^{|A|} + 2^{|B|} + 2^c) log l).

## 2. The new ingredients

Fix (eps1, eps2) with g(eps1, eps2) > 0 and a constant lambda with 0 < lambda < lambda0. Let c be an integer in
[beta log Lambda - 1, beta log Lambda] (rational approximations of beta and log Lambda to within 1/4 find one in
poly(l) time). The family is

    T := { T subset C : (1 - eps1) c/2 <= |T| <= c/2 },

and for T in T, W'(T) := { Σ(Q) : Q subset T, (1 - eps2)|T|/2 <= |Q| <= (1 + eps2)|T|/2 }.

**Lemma 2.1 (deterministic prime).** (i) For l >= l_0, the interval [l^5, 2 l^5] contains a prime p for which
the map W(C) -> Z_p, w -> w mod p, is injective. (ii) The least such p is found deterministically in
O(l^5 log log l + l^{3 beta + 1} log^2 l) = O(l^5 log log l) circuit-RAM time and O(l^5) bits of memory (using
beta < 4/3, Certificate 6.3[A]).

*Proof.* (i) Every element of W(C) is a sum of at most c numbers below 2^l, so a difference d of two distinct
elements satisfies 0 < |d| < c 2^l < 2^{2l}. A product of k distinct primes >= l^5 is at least l^{5k}, so at most
2l/(5 log l) primes in [l^5, 2 l^5] divide d. A prime is bad (not injective) iff it divides some such d, so the
bad primes number at most binom(|W(C)|, 2) * 2l/(5 log l) <= 2^{2c} l <= Lambda^{2 beta} l <= l^{2 beta + 1}. By the
prime number theorem, pi(2x) - pi(x) >= x/(2 ln x) for x large, so [l^5, 2 l^5] holds at least l^5/(10 ln l)
primes. Since 2 beta + 1 < 5, the primes outnumber the bad primes for l >= l_0.
A sum of at most n of the input numbers can need up to l + log n bits, slightly more than one word; as in CJRS this
costs O(1) words per sum, and the bound c 2^l above is unaffected.
(ii) Sieve [2, 2 l^5] (O(l^5 log log l) operations on O(log l)-bit numbers). Compute W(C) once (O(2^c)). Test the
primes of [l^5, 2 l^5] in increasing order: reduce the |W(C)| <= Lambda^beta elements mod p (O(log l) each), sort
and compare neighbours. At most l^{2 beta + 1} + 1 primes are tested before the first good one, so the tests cost
O(l^{2 beta + 1} Lambda^beta log^2 l) = O(l^{3 beta + 1} log^2 l), and 3 beta + 1 < 5. ∎

**Lemma 2.2 (W'(T) is large for every T at once).** Suppose |W(C)| > 2^c l^{-lambda}. For l >= l_1 and every
T in T, |W'(T)| >= (1/2) 2^{|T|} l^{-lambda}. With the prime of Lemma 2.1, every K_T := (W'(T) mod p) has
|K_T| = |W'(T)| >= D := (1/4) Lambda^{(1 - eps1) beta/2} l^{-lambda}.

*Proof.* W(T) is contained in W'(T) together with the sums of the unbalanced Q subset T, so by F8,
|W'(T)| >= 2^{|T|} l^{-lambda} - 2 * 2^{H((1 - eps2)/2)|T|}. The subtracted term is at most half the first iff
2^{(1 - H((1 - eps2)/2))|T|} >= 4 l^lambda. Now |T| >= (1 - eps1) c/2 >= (1 - eps1)(beta log Lambda - 1)/2, so
(1 - H((1 - eps2)/2))|T| >= lambda0 log Lambda - 1 = lambda0 log l - lambda0 log(beta log l) - 1, which exceeds
lambda log l + 2 for large l because lambda < lambda0. For the second claim, W'(T) subset W(C) and Lemma 2.1 make
reduction mod p injective on W'(T), and 2^{|T|} >= 2^{(1 - eps1)(beta log Lambda - 1)/2} >= (1/2)
Lambda^{(1 - eps1) beta/2}. ∎

This replaces CJRS's use of Lemma 7, which gives |W' mod p| = Theta(|W'|) with probability 3/4 over a random
prime, for the one unknown T = S ∩ C. Here the bound holds for all T together and involves no probability.

**Lemma 2.3 (universal residue covering).** Let T be a finite family and, for T in T, K_T a nonempty subset of
Z_p with |K_T| >= D. Put U := T x Z_p, and say r in Z_p covers (T, y) iff (r - y) mod p is in K_T. The greedy
algorithm (repeatedly take a residue covering the most uncovered elements of U) returns a set R of distinct
residues such that
(i) every (T, y) in U is covered by some r in R;
(ii) |R| <= ceil((p/D) ln|U|) <= (p/D)(1 + ln|U|);
(iii) for every sigma in Z_p, R + sigma also satisfies (i).
It runs in O(|T| p k_max + |R| (p + |T| k_max)) operations on residues, k_max := max_T |K_T|.

*Proof.* Each (T, y) is covered by exactly the |K_T| >= D residues y + K_T. If u elements are uncovered, the
residues together cover sum |K_T| >= D u of them (with multiplicity), so the greedy choice covers at least
D u/p, and u_{j+1} <= (1 - D/p) u_j < e^{-D/p} u_j. After j_0 = ceil((p/D) ln|U|) >= 1 steps, u_{j_0} < |U| e^{-ln|U|}
= 1, so u_{j_0} = 0 (if |U| = 1 one step suffices). A chosen residue covers nothing new afterwards, while any
uncovered element makes the maximum positive, so no residue is chosen twice. (iii) r covers (T, y) iff r + sigma
covers (T, y + sigma), and y -> y + sigma is a bijection of Z_p. Time: keep cnt[r] = the number of uncovered
elements r covers, initially sum_T |K_T| for every r. When (T, y) becomes covered, decrement cnt at the |K_T|
residues y + K_T. Each step is an argmax over Z_p plus a scan of r - K_T for every T. ∎

**Lemma 2.4 (best shift).** For any w: Z_p -> R_{>=0} and any set R subset Z_p,
sum_{sigma in Z_p} sum_{r in R} w(r + sigma) = |R| sum_{r in Z_p} w(r). Hence sigma* := argmin_sigma
sum_{r in R} w(r + sigma) satisfies sum_{r in R + sigma*} w(r) <= (|R|/p) sum_{r in Z_p} w(r). Given w, sigma*
is found in O(p |R|) operations.

*Proof.* Exchange the two sums; for each fixed r, r + sigma runs over Z_p once. A minimum is at most the mean. ∎

## 3. The algorithm DET

**Definition 3.1.** T, W'(T), K_T as in Sec. 2; Q+ as in Sec. 1.

**Definition 3.2 (class costs; CJRS's notation).** For a target t' and r in Z_p, R_{A,r} is as in F7 and R_{B,r}
is the class of b + Σ(Q) ≡ t' - r (mod p); R_{B,r} already denotes the class t' - r, and no further shift is
applied. Their sizes in couples (before merging equal sums) are

    w_{t'}(r) := |R_{A,r}| + |R_{B,r}| = sum_{Q in Q+} |L_{A, (r - Σ(Q)) mod p}| + sum_{Q in Q+} |L_{B, (t' - r - Σ(Q)) mod p}|,

and sum_{r in Z_p} w_{t'}(r) = (|L_A| + |L_B|) |Q+| =: W_tot.

**DET(X, t).** Constants: eps1, eps2, lambda as in Sec. 2.
- *Step 0.* Apply F2 (drop x_i > t; if t <= 2^{0.499n}, run the DP and stop). Fix a partition X = A ⊔ B ⊔ C with
  |C| = c and |A|, |B| = ceil, floor of (n - c)/2.
- *Step 1.* For t' in {t, Σ(X) - t}: if UNBAL(X, t', C, eps1) (F5) says yes, return yes.
- *Step 2.* Compute W(C). If |W(C)| <= 2^c l^{-lambda}, return the answer of F4 with Y = C.
- *Step 3.* Find p by Lemma 2.1. Build L_A, L_B (F6) and the sorted sublists L_{A,i}, L_{B,i}, i in Z_p, by one
  scan of each list in sorted order into p buckets. Build Q+, the family T, and K_T for T in T. If no prime was
  found in [l^5, 2 l^5] or some K_T is empty (both only for l < max(l_0, l_1), by Lemmas 2.1 and 2.2), run
  meet-in-the-middle on (X, t) and return its answer.
- *Step 4.* Compute R by Lemma 2.3 on U = T x Z_p.
- *Step 5.* For t' in {t, Σ(X) - t}: compute w_{t'}(r) for all r (Def. 3.2); compute sigma_{t'} by Lemma 2.4 with
  w = w_{t'}; for each r in R + sigma_{t'}, run Lines 5-6 of CJRS (F7) with target t' and residue r; if Line 6
  finds a pair, return yes.
- *Step 6.* Return no.

Relative to CJRS's Representation-OV (Figure 4), the random prime is replaced by Step 3's prime, and Line 4
(s(l) random residues, cutoff k(n, l)) by Steps 4-5. Lines 1 and 2 are CJRS's, with footnote 8 made explicit in
Steps 1 and 5. No step uses randomness: every choice (p, R, sigma_{t'}) is computed.

## 4. Correctness

**Lemma 4.1 (no false positives).** If DET returns yes, (X, t) has a solution.

*Proof.* Steps 0-3 return the answers of exact procedures (F2, F4, F5, meet-in-the-middle). In Step 5, a pair
found by Line 6 gives a in L_A, b in L_B, Q1, Q2 in Q+ with Q1 ∩ Q2 = ∅ and a + Σ(Q1) + b + Σ(Q2) = t'. Since
a = Σ(S_A) and b = Σ(S_B) for some S_A subset A, S_B subset B, and A, B, C are disjoint, S_A ∪ S_B ∪ Q1 ∪ Q2 is
a subset of X with sum t'. If t' = Σ(X) - t, its complement has sum t (F3). ∎

**Lemma 4.2 (balanced solutions are found).** Let t' in {t, Σ(X) - t} and let S' be a solution of (X, t') with
T := S' ∩ C in T. If DET reaches Step 5, then Step 5 returns yes while processing t'.

*Proof.* Let y := Σ(S' ∩ A) mod p. By Lemma 2.3 (i) and (iii), some r in R + sigma_{t'} covers (T, y): there is
Q1 subset T with (1 - eps2)|T|/2 <= |Q1| <= (1 + eps2)|T|/2 and Σ(S' ∩ A) + Σ(Q1) ≡ r (mod p). Put
Q2 := T \ Q1. Then |Q1|, |Q2| <= (1 + eps2)|T|/2 <= (1 + eps2) c/4, as |T| <= c/2; so Q1, Q2 are in Q+ and
disjoint. With a := Σ(S' ∩ A) in L_A and a' := a + Σ(Q1), the couple (a', Q1) lies in R_{A,r}. With
b := Σ(S' ∩ B) in L_B and b' := b + Σ(Q2), a' + b' = Σ(S') = t', so b' ≡ t' - r and (b', Q2) lies in R_{B,r}.
Line 6 finds this pair or another one (F7), so Step 5 returns yes, at the latest at this class. ∎

This is CJRS's good-residue argument (proof of Theorem 2: residue i is good iff i - Σ(S ∩ A) is in
W'(S ∩ C) mod p), with "some sample is good, with probability 2/3" replaced by "some class is good, always":
the covering ranges over every possible restriction T and every possible shift y, so it does not need to know S.

**Lemma 4.3.** DET(X, t) returns yes iff (X, t) has a solution.

*Proof.* "Only if" is Lemma 4.1. Let S be a solution. If |S ∩ C| <= c/2, put (S', t') := (S, t); otherwise
(S', t') := (X \ S, Σ(X) - t), which is a solution with |S' ∩ C| < c/2 (F3). If |S' ∩ C| < (1 - eps1) c/2, Step 1
returns yes on t' (F5). Otherwise S' ∩ C is in T. If DET stops at Step 2 or Step 3, it returns an exact answer,
which is yes. Otherwise Lemma 4.2 applies. ∎

**Remark 4.4.** Correctness never uses the size of p or injectivity: Lemma 4.2 needs only that every K_T is
nonempty, so that the covering exists. The prime matters only for the running time (through D in Lemma 5.2).
`check_stage1.py` tests this with a deliberately non-injective prime (Sec. 8, run 2).

## 5. Running time

Assume l >= max(l_0, l_1) (otherwise n = O(1) by F2) and that DET reaches Step 5 (Steps 1-3 bound the
other exits).

**Lemma 5.1 (cost of each step).**
- Step 0: O(n t) = 2^{0.499n + o(1)} if the DP runs; otherwise O(n).
- Step 1: O~(2^{n/2} l^{-delta/2}) (F5, two targets).
- Step 2: O(2^c) to compute |W(C)|; if F4 runs, O~(2^{n/2} l^{-lambda/2}).
- Step 3: the prime, O(l^5 log log l) (Lemma 2.1(ii)). L_A, L_B: O((2^{|A|} + 2^{|B|}) log l) =
  O(2^{n/2} Lambda^{-beta/2} log l) (F6, with the O(log l) cost of mod p). The sublists need an array of p
  bucket heads, O(p) = O(l^5) words, beyond CJRS's p = Theta(l^{1 + beta/2}); every list element is stored once. This O(l^5) memory is polynomial but far above CJRS's; it is not needed
  for the time bound (Lemma 2.1 could use an interval of size about l^{2 beta + 1 + o(1)}).
  Q+, T and the K_T: O(2^{2c} log l) = O(l^{2 beta} log l). Meet-in-the-middle, when it runs: O(2^{n/2}), for
  l < max(l_0, l_1) only.
- Step 4: by Lemma 2.3 with |T| <= 2^c <= Lambda^beta, k_max <= 2^c, |R| <= p <= 2 l^5:
  O(l^{5 + 2 beta} + l^{10}) operations of O(log l) each.
- Step 5, per target: w_{t'} for all r: O(p |Q+|) = O(l^6). sigma_{t'}: O(p |R|) = O(l^{10}). Per class r: the
  p-independent work of Lines 5-6 is O~(w_{t'}(r)) (F7), plus an **additive O(|Q+| log l) per class**: Line 5(a)
  computes j(Q) = (r - Σ(Q)) mod p and visits one sublist for every Q in Q+, even when the sublist is empty, and
  Line 5(b) merges |Q+| sorted lists. Summed over the classes:
  O~( sum_{r in R + sigma_{t'}} w_{t'}(r) ) + O(|R| |Q+| log l), and |R| |Q+| log l = O(l^6 log l).

So the time is O~(2^{n/2} l^{-delta/2}) + O~(2^{n/2} l^{-lambda/2}) + O(2^{n/2} Lambda^{-beta/2} log l)
+ O~( sum_{t'} sum_{r in R + sigma_{t'}} w_{t'}(r) ) + O(l^{10} log l). ∎

**Lemma 5.2 (the filtered work).** For each t',
sum_{r in R + sigma_{t'}} w_{t'}(r) = O( 2^{n/2} l^{-theta} (log l)^{1 + x} ), where
x := (1 - eps1/2) beta - 1 and theta := x - lambda = (1 - eps1/2) beta - 1 - lambda.

*Proof.* By Lemma 2.4 and Lemma 2.3 (ii), the sum is at most (|R|/p) W_tot <= ((1 + ln|U|)/D) W_tot. Here
|U| = |T| p <= 2^c * 2 l^5, so 1 + ln|U| = O(log l). Next, W_tot = (|L_A| + |L_B|)|Q+| <=
2 * 2^{(n - c + 1)/2} * 2^{c/beta} <= 4 * 2^{n/2} Lambda^{1 - beta/2}, using c >= beta log Lambda - 1 for the first
factor and c/beta <= log Lambda for the second. With D from Lemma 2.2,
W_tot/D <= 16 * 2^{n/2} Lambda^{1 - beta/2 - (1 - eps1) beta/2} l^{lambda} = 16 * 2^{n/2} Lambda^{-x} l^{lambda}.
As g > 0 forces theta0 > 0, x > lambda0 > 0, and
Lambda^{-x} = l^{-x} (beta log l)^{x}, with x < beta. So the sum is O(2^{n/2} l^{-(x - lambda)} (log l)^{1 + x}). ∎

CJRS's own bound for Lines 4-6 is O~(k(n, l)) = O~(2^{n/2} l^{-theta}). The deterministic version loses only the
factor 1 + ln|U| = O(log l), which O~ absorbs. Their s(l) random residues out of p also amount to
about p/|W' mod p| samples, so the covering is about as large as their sample set, up to that log factor.

**Lemma 5.3 (total).** DET runs in time O~(2^{n/2} l^{-min(delta/2, lambda/2, theta)}) + poly(l).

*Proof.* Lemmas 5.1 and 5.2. Lambda^{-beta/2} log l = O~(l^{-beta/2}) and beta/2 > 1/2 > theta. Step 0's
2^{0.499n + o(1)} and the additive poly(l) = poly(n) are both o(2^{n/2} l^{-1}). ∎

## 6. The exponent

**Definition 6.1.** (eps1, eps2) in (0, 1)^2 is admissible if g(eps1, eps2) > 0 (Sec. 0); then
lambda0 > 0, theta0 > 0 and beta > 1.

**Lemma 6.2 (every gamma below g).** If (eps1, eps2) is admissible and 0 < gamma < g(eps1, eps2), then
lambda := any rational number in (2 gamma, lambda0) satisfies 0 < lambda < lambda0 and min(delta/2, lambda/2, theta) > gamma.
Hence DET with these constants runs in time O(2^{n/2} l^{-gamma}).

*Proof.* (lambda0 involves logarithms, so the midpoint (2 gamma + lambda0)/2 is irrational even at a rational
point; the algorithm compares |W(C)| with 2^c l^{-lambda}, so it uses a rational lambda.) 2 gamma < lambda0 gives 2 gamma < lambda < lambda0, so lambda/2 > gamma. delta/2 >= g > gamma.
theta = theta0 + (lambda0 - lambda) > theta0 >= g > gamma. Let gamma' be the minimum; Lemma 5.3 gives
O~(2^{n/2} l^{-gamma'}) + poly(l), and the polylog(l) factors are absorbed by l^{gamma' - gamma}. ∎

The strict inequality is where the polylog factors go: the deterministic O(log l) loss and CJRS's own
(beta log l)^{x} factor in D are absorbed only for gamma < g strictly. At gamma = gamma* itself we claim nothing.

**Certificate 6.3 (`cert_gamma.py`).** Interval arithmetic over exact rationals, outward rounding to 2^{-256},
ln by the atanh series with a rigorous tail bound, H enclosed by monotonicity on (0, 1/2]. Results:
- [A] At P = (15792/10^5, 24267/10^5): beta in [1.118640217, 1.118640218], and
  lambda0/2 >= 0.0101042693, delta/2 >= 0.0101041272, theta0 >= 0.0101038476. So P is admissible and
  g(P) > 0.0101.
- [B] Eliminating eps2 through (4) (H is increasing on [1/4, 1/2], so eps2 is a continuous function of eps1,
  enclosed by bisection) leaves one continuous equation G(eps1) = 0 from (3). G is certified negative at
  eps1 = 0.157920369638 and positive at 0.157920369640, so a root lies between; there
  eps2 in [0.242668928273, 0.242668928287]. On that box all three terms lie in [0.0101041782, 0.0101041783].
- [C1] Must fail: at (0.1579, 0.2427), g < 0.01009977 < 0.0101 (certified), so the claim "g > 0.0101" is
  rejected there.
- [C2] Must fail: on the root box, g < 0.010105 (certified), so an overclaim of one more unit in the sixth digit is
  rejected.

Hence gamma* in [0.0101041782, 0.0101041783], and Theorem 1 holds for every gamma < gamma*. [A] alone already
gives every gamma <= 0.0101 with rational constants. Whether some other admissible point beats the CJRS roots
is not claimed. A float grid search (`../judge_checks/nums.py`) found none [float].

*Proof of Theorem 1.* Given gamma < gamma*, take (eps1, eps2) = (eps1*, eps2*) (or any admissible rational point
with g > gamma, which exists by continuity of g and Certificate 6.3[B]) and lambda from Lemma 6.2. DET is
correct by Lemma 4.3 and runs in O(2^{n/2} l^{-gamma}) by Lemma 6.2, and l >= 0.499n (F2) gives
O(2^{n/2} n^{-gamma}). ∎

*Proof of Corollary 3.* F9 with DET as the decision algorithm: sum_{i=1}^{n} O(2^{(n-i+1)/2} n^{-gamma}) =
O(2^{n/2} n^{-gamma}). DET is run only on subinstances with m > c + O(1) numbers, where m is the number of
numbers and c = Theta(log l) is the block size, because the partition of Step 0 needs that many. For m <= c + O(1)
we brute-force all 2^m subsets. The word length l stays fixed throughout, so each of the n subinstances costs
poly(l) = poly(n) extra, and the total is n poly(n) = poly(n), negligible next to 2^{n/2} n^{-gamma}. ∎

## 7. Word RAM and the input model

*Proof of Corollary 2.* Run DET with CJRS's Observation 4 (F10): the block C' and every l-dependent constant use
l' = 0.1n, sub-collections are stored in O(1) words, and OV becomes a lookup in the 2^{0.21n}-time memo table.
Two of our steps change with it:
- The prime still comes from [l^5, 2 l^5] with the true word length l >= 0.499n > l'. Lemma 2.1's count becomes
  binom(|W(C')|, 2) * 2l/(5 log l) <= l'^{2 beta} l <= l^{2 beta + 1}, the same bound. p < 2^l fits in a word, and
  reduction mod p is a unit-cost operation.
- Lemma 2.2 and Lemma 5.2 hold with l' in place of l in Lambda, c and D. p enters only through |R|/p and the
  additive poly(l) terms.
Sorting, merging and the two-pointer scans are unit-cost word operations. The time is
O(2^{n/2} l'^{-gamma} ceil(l'/l)) + O(2^{0.21n}) + poly(n) = O(2^{n/2} n^{-gamma}). CJRS state Observation 4
with "it is easy to check" and give no further proof; Corollary 2 inherits that level of detail, and its two
changes above are ours. ∎

**Remark 7.1 (what the model assumes).** l = poly(n) is used three times: poly(l) is negligible next to 2^{n/2},
log l = O(log n) inside O~, and every input fits in a word. Observation 1 supplies l >= 0.499n.

**Remark 7.2 (b-bit inputs, not claimed).** For b-bit inputs with b > l, the prime range in Lemma 2.1 can be
raised to about |W(C)|^2 b poly(l), since bad primes number at most |W(C)|^2 b / log p. Every p-dependent cost is
then additive poly(p) = 2^{o(n)} when b = 2^{o(n)}. That model is not CJRS's, because meet-in-the-middle itself
then pays b/l per operation, so we state Theorem 1 only in CJRS's model.

## 8. Mechanical check (small instances; logic, not asymptotics)

`check_stage1.py` implements DET from this document (Steps 1-6; Step 1 is Lemma 6's procedure with
A' = C plus the A half, which is correct for any A' ⊇ C, the size of A' setting only the time; the greedy of
Lemma 2.3 with a bucket queue, the shift of Lemma 2.4 computed exactly for all sigma at once) and compares it
with brute force. Every run asserts:
- Lemma 2.3 (i) exhaustively over T x Z_p after the shift, and (ii);
- Lemma 2.4 exactly in integers (the full averaging identity, and the bound at sigma*);
- w(r) equal to the number of couples Line 5 creates;
- Lemma 4.2 directly: every brute-force solution S' with S' ∩ C in T has a correct key in some class, and
  Lines 5-6 answer yes on its target. This is checked whether or not Step 2 fires.

Families: random 30-bit, small values in [1, 40], multiples of 667, powers of 2. 70% of the targets come from a
random subset. Results (about one minute on one core):
- *Run 1*, n = 14, c = 6, the prime of Lemma 2.1 on [P0, 2 P0] with P0 = 2|W(C)|^2 (a small stand-in for
  l^5): 100 instances (72 yes), 0 misses, 0 false positives. 92 targets with a balanced solution, 0 missed by
  Lines 5-6. 1464 balanced solutions, all with a correct key. The prime was injective in 100/100. Worst bad-prime
  count 37 against the Lemma 2.1 bound 4032. Kept/total cost 0.39.
- *Run 2*, n = 16, c = 8, a deliberately small prime (the first prime >= 2|W(C)|, injective in only 23/80
  instances, Remark 4.4): 80 instances (68 yes), 0 misses, 0 false positives. 117 targets with a balanced
  solution, 0 missed. 8013 balanced solutions, all with a key. Kept/total 0.49.
- *Controls, which must miss:* 'single' (only the cheapest class, no covering) misses 92/92 and 116/117 balanced
  targets (6 and 23 wrong final answers). 'oneshift' (a greedy cover of T x {0} only, then the best shift) misses
  92/92 and 109/117 (6 and 21 wrong answers). Neither gives a false positive, as Lemma 4.1 predicts.

At these sizes D/p is not small, so the saving itself is not visible; the check tests logic only. It also does not
exercise the Step 3 fallback (an empty K_T would make D = 0 and fail the greedy's `assert top > 0` instead of
falling back), and its Step 2 uses meet-in-the-middle rather than F4.

## 9. What is not proved here

- No claim at gamma = gamma* itself, and no claim that the CJRS roots maximise g (float evidence only).
- CJRS's Sec. 3 (n^{-1/2}) and Sec. 5 (n^{-0.5023}) are not derandomised (ledger rows C1 and C4: UNKNOWN).
- Corollary 2 rests on CJRS's Observation 4, which they only sketch.
- The facts F1-F10 are cited from CJRS, not re-proved. The judge re-read Sec. 4 against them, but this write-up
  has not had its own adversarial review.
- Stage 2 (a deterministic 2^{(1/2 - eps)n}) is not part of this document; see README.md.

## Review fixes (second referee)

1. Corollary 3 (Sec. 6): DET runs only for m > c + O(1) numbers; smaller subinstances are brute-forced in 2^m
   time, extra cost poly(n) in total.
2. Lemma 6.2: lambda is any rational in (2 gamma, lambda0), not the irrational midpoint.
3. Lemma 2.1 proof: sums may need l + log n bits, O(1) words, stated.
4. Sec. 8: the check does not exercise the Step 3 fallback and uses meet-in-the-middle in Step 2; stated.
5. Corollary 2 stays labelled as inheriting CJRS's Observation 4 sketch (already in Sec. 7, Sec. 9, README).
6. Step 3 cost list: the O(l^5) memory is noted as polynomial and unnecessary for the time bound.
