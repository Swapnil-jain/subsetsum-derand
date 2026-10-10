# A deterministic, non-explicit Subset Sum algorithm in time poly(n, L) * 2^{0.49999834 n}

Draft, private. Base results:
- **YL**: Ye and Li, "Subset Sum via Partial Match", arXiv 2610.10446, v1 (the only version). All
  numbering is that of v1: Def. 2.1, Thm 2.2, Lemma 3.1, Cor. 3.2, Cor. 3.3, Lemma 3.4, Sec. 3.5,
  Thm 4.1, Prop. 4.2.
- **AL25**: Alman and Li, arXiv 2509.14489 (FOCS 2025): Appendix B (Thm B.2) and Thm 6.1.
- Stage 1 of this project (`../stage1/PROOF.md`): a derandomisation of CJRS (arXiv 2301.07134, Sec. 4). Only
  its covering lemma and best-shift lemma are reused, and both are stated and proved in Sec. 2 below. Sec. 12
  says what Stage 1 is and how it relates to CJRS; nothing else of Stage 1 is used.

Certificate: `cert_eps.py` (exact rationals, outward bounds). Mechanical check on small instances:
`check_stage2.py` (Sec. 10).

**Labels.** Every claim carries one label:
- [proof]: proved in this document, completely;
- [arg]: argued here, but less than a complete proof (each one is listed in Sec. 11);
- [cite]: taken from the named source, at the named place.

**Review status.** The reduction was audited (`../AUDIT.md`, sec. 2(b)) and judged from refute-by-default
(`../JUDGE_S1.md`, Stage 2): CONFIRMED WITH FIXES as a reduction conditional on YL Prop. 4.2. Prop. 4.2
itself was then audited from the TeX source (`AUDIT_YELI.md`): HOLDS, with no claim-level defect. This
write-up applies every fix (indexed at the end of Sec. 0). It then had two independent adversarial referees
(2026-10-10): both CONFIRMED WITH FIXES, neither found a claim-level defect; their fixes are applied and listed
in Sec. 0 ("Referee fixes"). The audit and judge files named above are the authors' own and are not part of
this directory; Sec. 12 summarises what is needed from them, so that this document can be checked alone.

## 0. Statement

*Model (YL Sec. 2).* Input: integers z = (z_1, ..., z_n) in Z^n and a target tau in Z; decide whether some
c in {0,1}^n has c . z = tau. Integers may be negative. Running time counts bit operations. Write L for the
total binary length of the input. YL assume L = 2^{o(n)}. Logarithms are base 2; ln is natural;
h(s) = -s log s - (1-s) log(1-s), with h(0) = 0.

**Theorem 1.** There exists a deterministic algorithm that decides Subset Sum in poly(n, L) * 2^{E n} bit
operations on every input, where E <= 0.4999983316 (Certificate 7.2[A]). On inputs with L = 2^{o(n)} this is
O(2^{0.49999834 n}). So the saving over meet-in-the-middle is a factor 2^{eps n} with eps >= 1.66e-6. The
algorithm is **non-explicit**: it is a fixed finite program that is proven to exist, but the proof does not
say which program it is (Sec. 8). [proof, given the cited results of Sec. 1]

**Corollary 2 (search).** A solution can be found deterministically in the same time. [proof]

*Status of the algorithm (Sec. 8).* The algorithm is **deterministic but non-explicit**. It is a fixed,
finite program. It uses no random bits. Its answer and its time bound hold for every input. However, one
component of the program, a constant-size integer circuit hardcoded inside YL's partial-match subroutine, is
only **proven to exist**: the proof does not say which circuit it is. No feasible computation can find it,
because the circuit has at least 2^{N'} rows with N' >= 2.2e22 (Sec. 8.3). We can prove the program exists; we cannot write
it down or run it.

*Dependence (JUDGE fix S4, in the wording of AUDIT_YELI sec. 5).* The theorem "uses YL Prop. 4.2 (audited
2026-10-10: holds), which imports AL25 Thm B.2 and Thm 6.1 (refereed). The algorithm is deterministic but
non-explicit (hardcoded circuit of length >= 10^15, shown to exist)." At the slack chosen here the length
bound is in fact larger: N' >= 2.2e22, from both conditions of Cor. 3.2 (Sec. 8.3). The dependence on AL25 Thm 6.1 can be dropped. Sec. 9
replaces it with a self-contained inclusion-exclusion argument (Lemma 9.1), for which the full Thm 6.1 proof
is not needed.

*Context.* Horowitz-Sahni (1974) meet-in-the-middle decides Subset Sum deterministically in 2^{n/2} poly
time. YL Thm 4.1 gives a randomized 2^{(1/2 - 1/450000) n} algorithm [cite]. A literature search on
2026-10-10 found no deterministic algorithm with exponent below 1/2 (`../AUDIT.md`, header) [arg: evidence
of novelty, not proof]. If that search is right, Theorem 1 is the first deterministic improvement on the
1974 exponent.

*Credit.* Each item below is cited where it is used:
- From YL: the representation on a prefix, the layers, the compatibility and padding argument, the
  complement argument, the list shapes and the split l, the meet-in-the-middle record generation, the
  keyed count with recovery, the few-sums branch (via AKKN16 Lemma 3.2), and, above all, Prop. 4.2.
- **New here:**
  - the deterministic filter, built from three parts:
    - a collision-bounded prime found by scanning (Lemma 2.3);
    - layer families defined by a residue threshold (Step 3);
    - one universal covering per layer over (prefix, shift), with the best rotation (Lemmas 2.1 and 2.2,
      from Stage 1);
  - the re-derivation of YL's exponent at a general prefix m = pi n;
  - the choice pi = 0.2499, which balances the 2^{2m} covering cost against the gain;
  - the certificate;
  - the inclusion-exclusion replacement for hole fixing (Lemma 9.1).

*Fixes applied.* JUDGE_S1.md lists four Stage 2 fixes, S1 to S4; it has no S5. The audit's corrections D6
and D7 to our own notes are also applied.
- (S1) The layer families are defined by "at least D residues", not by "best layer": Step 3 and Lemma 5.1.
- (S2) The right partial list is 1/4 + 3 pi/4, not 1/4 + pi/2: Lemma 6.1(g) and Certificate 7.2.
- (S3) The prime-scan cost N^2 (b+1) poly is written out (Lemma 2.3(ii)), and so are the costs of the
  histograms and convolutions (Lemma 6.1(f)).
- (S4) The AUDIT_YELI wording is used above and in Sec. 8.
- (D6) The circuit is hardcoded in YL **Cor. 3.2**. Cor. 3.3 is the step from circuit to partial match, and
  there is no Cor. 3.5.
- (D7) The finite search (Sec. 8.4) dovetails over the block length, and existence also uses hole fixing and
  AL25 rebalancing.

*Referee fixes (2026-10-10, two independent referees J1, J2).*
- (R1) The block length kappa uses both conditions of Cor. 3.2. The second, log2(kappa+1)/kappa <= eps/4,
  binds: kappa >= 1.4844e11, N' >= 2.2036e22 (was 1.55e19). Sec. 7, Sec. 8; `cert_eps.py`.
- (R2) Remark 5.4: coverage needs coll_p <= 3N (Lemma 3.4, Lemma 5.1), not only nonempty K_c.
- (R3) Certificate 7.2[B] now uses only the stated xi > 0.00002 for xi. The table enters [B] only as upper
  bounds on dL and dR, and the pair (dL', dR') is a rational just above them (Cor. 3.2's conditions are restated
  for it). Two new must-fail controls. Sec. 1 (Y3), Sec. 7, Sec. 8.1, Sec. 8.4.
- (R4) Theorem 1 is stated as poly(n, L) * 2^{E n} and carries "non-explicit" in its statement.
- (R5) Lemma 9.1 is now tested at gate level, with the full group and random g_i (Sec. 9, Sec. 10).
- (R6) Run 2 (and run 1) are marked logic-only, since m > n/3. A new run 3 is inside the hypothesis, with the
  proof's prime range and a really filtered layer. The proof's own D is 1 below m = 10, so no run with
  the proof's own D >= 2 is feasible (Sec. 10).
- (R7) Provenance of Stage 1 and CJRS: new Sec. 12. Lemma 2.1 and 2.2 are proved here.
- (R8) Lemma 4.1's size bound was checked again: it is +1, not +3/2 (see the note there). No change.
## 1. What is cited

**From YL.**
- **(Y1) Def. 2.1 [cite].** A pair (dL, dR) of nonnegative reals is admissible if, for every eps > 0, there
  is a deterministic algorithm PM_eps with the following input and output.
  - Input: a list A of pairs (x, k), where x is in {0,1}^{n'}; and a list B of pairs (y, k'), where y is in
    {0,1,*}^{n'} with ||S(y)| - n'/2| <= 1 and S(y) is the set of non-* positions. The keys are integers of
    bit length at most L'.
  - Output: the exact number of pairs ((x,k), (y,k')) with k = k' such that x matches y on S(y).
  - Time: (n' + L' + log(|A| + |B|))^{O(1)} (2^{(dL+eps) n'} |A| + 2^{(dR+eps) n'} |B|), for every
    length n'.
  - Admissibility is closed upward in each coordinate (YL, after Def. 2.1).
- **(Y2) Prop. 4.2 [cite; audited in AUDIT_YELI.md: holds].** The pair (dL, dR) of YL Sec. 4 is
  admissible, and dL + dR = 1/2 - 2 xi with xi > 0.00002.
- **(Y3) Sec. 4 table [cite].** It gives 20-place truncations, certified by YL's interval computation:
  - dL = 0.00727587055962990941...;
  - dR = 0.49268405898808998771...;
  - xi = 0.00002003522614005143....

  Our own 60-digit recomputation (`yl_numbers.py`) reproduces them. Certificate 7.2[B] uses only
  xi > 0.00002 from (Y2) for xi. It still needs numbers for dL and dR themselves, which the statement of
  Prop. 4.2 does not give; for those it uses the table as upper bounds only (dL <= table + 10^-20,
  dR <= table + 10^-20), and the algorithm's rational pair (dL', dR') lies just above them.
- **(Y4) What Prop. 4.2 rests on [cite].** These are used only through (Y2):
  - Sec. 3.5: the EXACT_Z circuit on a window;
  - Lemma 3.4: colored transfer. Its hole fixing uses AL25 Thm 6.1, and its numerical rebalancing uses
    AL25 Thm B.2;
  - Lemma 3.1: block grouping;
  - Cor. 3.2: enumeration. It **hardcodes** one exact integer circuit for P_{kappa^2+2kappa, 1/2}, with
    kappa a sufficiently large even integer, and its degree exponents are dL + eps/4 and dR + eps/4;
  - Cor. 3.3: circuit to partial match, by label sums over (key, gate).
  AUDIT_YELI sec. 1 re-derives each of these steps or tests it.
- **(Y5) Thm 2.2, proof [cite as a source; every part used is re-proved in Sec. 3 for a general prefix
  m].** The parts used are the representation, the dummy padding, "Many correct keys", the split l,
  "Generating the surviving records" (after MNPW19 Lemma 3.8), and "Counting and recovery".
- **(Y6) Thm 2.2, few sums [cite: AKKN16 Lemma 3.2, as used by YL; re-proved for general m in Lemma 4.1].**

**From AL25** (refereed, FOCS 2025; used only inside (Y4)).
- **(A1) Thm B.2 [cite].** Numerical rebalancing, used in YL's list form. AUDIT_YELI read its statement and
  proof and tested it numerically (`yl_rebalance.py`). AUDIT_YELI D1 notes an exponent swap in AL25's
  printed Thm B.1, which YL's tau-form avoids.
- **(A2) Thm 6.1 [cite].** Hole fixing. AUDIT_YELI read its statement and overview but not its full proof.
  It is not needed: Lemma 9.1 replaces it.

**Classical.**
- **(K1) Prime number theorem [cite].** For x >= x_0, the interval [x, 2x] contains at least x/(2 ln x)
  primes.
- **(K2) Fast integer multiplication [cite: Schoenhage-Strassen 1971].** Two N-bit integers can be
  multiplied in O(N log N log log N) bit operations. Hence two length-p integer vectors with entries below
  2^e can be cyclically convolved exactly, by Kronecker substitution with 2e + log p + 1 bits per slot and
  then folding mod x^p - 1, in p * poly(e, log p) bit operations [proof of the reduction: standard].
- **(K3) Horowitz-Sahni 1974 [cite].** Two sorted lists of integers can be searched for a pair with a given
  sum in time linear in the lists, times the arithmetic cost.

## 2. Shared tools

**Lemma 2.1 (universal residue covering; Stage 1 Lemma 2.3, with a convolution implementation).** Let T be a
finite family and, for each T in T, let K_T be a subset of Z_p with |K_T| >= D >= 1. Put U := T x Z_p, and
say that r covers (T, y) iff (r - y) mod p lies in K_T. The greedy algorithm repeatedly takes the least
residue that covers the most uncovered elements. It returns a set R of distinct residues with the following
properties:
- (i) every element of U is covered;
- (ii) |R| <= ceil((p/D) ln|U|) <= (p/D)(1 + ln|U|);
- (iii) R + sigma also satisfies (i), for every sigma in Z_p;
- (iv) R is computed in |R| * |T| * p * poly(log p, log|T|) bit operations.

*Proof.* (i)-(iii) are Stage 1 Lemma 2.3; the proof is repeated here in full, so that nothing outside this
file is needed. It uses only |K_T| >= D. Each (T, y) is covered by exactly |K_T| >= D residues, namely
r = y + k for k in K_T. So when u elements are uncovered, the total number of (residue, uncovered element)
incidences is at least D u, and some residue covers at least D u/p of them. A residue already taken covers
no uncovered element, so the greedy never repeats one, and the greedy's choice leaves at most u (1 - D/p)
uncovered. After t steps at most |U| (1 - D/p)^t < |U| e^{-tD/p} remain, which is below 1 once
t >= (p/D) ln|U|; this gives (i) and (ii). For (iii): r covers (T, y) iff r + sigma covers (T, y + sigma),
and translation permutes U.
(iv): let u_T be the 0/1 indicator of the uncovered y for T. The number of uncovered pairs that r covers is
cnt(r) = sum_T (u_T * 1_{K_T})(r), where * is cyclic convolution on Z_p, because r covers (T, y) iff
r - y is in K_T. Each greedy step computes all |T| convolutions exactly by (K2), with entries of O(1) bits
and sums below p |T|. It then takes the argmax and marks as covered the |K_T| <= p pairs (T, r - k), k in
K_T. ∎ [proof]

**Lemma 2.2 (best shift; Stage 1 Lemma 2.4).** For any w: Z_p -> R_{>=0} and any R subset of Z_p,
sum over sigma of sum_{r in R} w(r + sigma) = |R| sum_r w(r). Hence the minimiser sigma* satisfies
sum_{r in R + sigma*} w(r) <= (|R|/p) sum_r w(r). Given w, sigma* is found in O(p |R|) operations.
∎ [proof: Stage 1 Lemma 2.4. For each r, sum over sigma of w(r + sigma) = sum over all residues of w, so exchanging the two sums gives the identity; the minimiser is at most the mean]

**Lemma 2.3 (collision-bounded prime).** Let Sigma be a set of N >= 1 integers whose pairwise differences
have absolute value below 2^{b+1}. For a prime q, put

    coll_q := #{(u, v) in Sigma^2 : u != v, u ≡ v (mod q)}.

Put P0 := N(b + 1), and assume P0 >= x_0 of (K1).
- (i) Fewer than N(b+1)/(3 log P0) primes q in [P0, 2 P0] have coll_q > 3N, and this is fewer than the
  number of primes there. So a prime with coll_q <= 3N exists in [P0, 2 P0].
- (ii) The least such prime is found deterministically in N^2 (b+1) * poly(b, log N) bit operations. This
  is the cost written out for JUDGE fix S3.

*Proof.* (i) A difference d != 0 with |d| < 2^{b+1} has fewer than (b+1)/log P0 prime factors that are at
least P0, since a product of k such primes is at least P0^k. Summing over the N(N-1) ordered pairs gives
sum_q coll_q <= N^2 (b+1)/log P0 over the primes q in [P0, 2 P0]. So fewer than N(b+1)/(3 log P0) primes
have coll_q > 3N. By (K1) there are at least P0/(2 ln P0) = N(b+1)/(2 ln 2 * log P0) primes in
[P0, 2 P0], and 2 ln 2 < 3. (ii) Sieve [2, 2 P0], which takes O(P0 log log P0) = N(b+1) polylog operations
on O(log P0)-bit numbers. Test the primes of [P0, 2 P0] in increasing order. A test reduces the N elements
mod q, at poly(b) each, then sorts and counts equal runs, at O(N log N) comparisons. By (i), at most
N(b+1)/(3 log P0) + 1 primes are tested, so the tests cost N^2 (b+1) poly(b, log N) in total. ∎ [proof]

Why not an injective prime, as in Stage 1? Injectivity on Sigma needs p of order N^2 b. Then the covering
of Sec. 4 would have |R| of order p/D, about N b = 2^{m + o(n)} classes. Record generation pays |R| per
partial entry (Lemma 6.1(g)), so a factor 2^m would be added to the partial lists. A collision bound is
enough for the residue count (Lemma 3.4) and keeps |R| = 2^{o(n)}. [arg: explains the design choice; nothing
depends on it]

## 3. The representation on a prefix of length m

Fix an even m with 2 <= m <= n/3. The *prefix* P is coordinates 1..m. Write z_P for the restriction of z
to P, and similarly for other blocks and vectors.
- Sigma := {a . z_P : a in {0,1}^m} is the set of distinct prefix sums, and N := |Sigma|.
- For c, a in {0,1}^m, dist(a, c) is their Hamming distance.
- A *layer* is j in {0, 1, ..., m/2}, with density s := j/m <= 1/2.
- T_{m,j} := {b in {-1,0,1}^m : exactly j nonzero entries}.
- For each layer the outside coordinates P^c are split into B1_j (the next l_j coordinates) and B2_j (the
  remaining n - m - l_j), with l_j chosen in Lemma 3.5.
- *Lists of layer j:*

      A_j := {a in {0,1}^n : a = 0 on B2_j},
      B_j := {b in {-1,0,1}^n : b_P in T_{m,j}, b = 0 on B1_j, b in {0,1} on B2_j}.

  So |A_j| = 2^{m + l_j} and |B_j| = binom(m, j) 2^j 2^{n - m - l_j}.
- The *left key* of a is a . z, and the *right key* of b is tau - b . z (YL Sec. 2).
- Let b be large enough that every key, and every element of Sigma, has absolute value below 2^b. Then
  b <= L + 1, and differences of keys or of prefix sums are below 2^{b+1}.
- *Layer sets:* K(c, j) := {a . z_P : a in {0,1}^m, dist(a, c) = j}, a subset of Sigma, for c in {0,1}^m.

**Lemma 3.1 (representations of a solution) [proof; source YL Thm 2.2, "Many-sums"].**
- (a) Let c in {0,1}^n be a solution and a_P in {0,1}^m. Put a := (a_P on P, c on B1_j, 0 on B2_j) and
  b := c - a. Then a is in A_j and b is in B_j, where j := dist(a_P, c_P) <= m/2 is assumed. Both keys are
  equal to a_P . z_P + c_{B1_j} . z_{B1_j}, and a + b = c is in {0,1}^n.
- (b) Conversely, if a in A_j and b in B_j have equal keys and a + b is in {0,1}^n, then a + b is a
  solution.

*Proof.* (a) On P, b_P = c_P - a_P lies in {-1,0,1}^m and is nonzero exactly where a_P != c_P, so it has j
nonzeros. On B1_j, b = c - c = 0. On B2_j, b = c, which is binary. The left key is a . z. The right key is
tau - (c - a) . z = a . z, because c . z = tau. (b) Equal keys mean a . z = tau - b . z, that is,
(a + b) . z = tau. ∎

**Lemma 3.2 (compatibility is half-stars partial match) [proof; source YL Thm 2.2, the paragraph "In a
prefix coordinate"].**
- *Rows and queries.* For a in A_j and b in B_j, set x(a) := (1^{m-2j}, a_P), in {0,1}^{n'} with
  n' := 2m - 2j. Set y(b) := (1^{m-2j}, phi(b_P)), where phi maps 1 to '0', -1 to '1' and 0 to '*'
  coordinatewise.
- *Claim.* y(b) has exactly n'/2 specified positions. Moreover, a + b is in {0,1}^n iff x(a) matches y(b)
  on S(y(b)).

*Proof.*
- *Count.* The specified positions are the m - 2j dummies and the j nonzeros of b_P, and m - j = n'/2.
- *Dummies.* A dummy position has row bit 1 against the specified '1', so it always matches.
- *Prefix coordinate.* a_i + b_i is in {0,1} iff (b_i = 1 and a_i = 0) or (b_i = -1 and a_i = 1) or
  b_i = 0. That is exactly a_i = phi(b_i) or phi(b_i) = '*'.
- *Outside the prefix.* a is binary and 0 on B2_j; b is 0 on B1_j and binary on B2_j. So a + b is always
  binary there. ∎

**Lemma 3.3 (a dense layer for every prefix) [proof; YL "Many correct keys", for m = n/3].** For every c in
{0,1}^m there is a layer j <= m/2 with |K(c, j)| >= N/(m + 2).

*Proof.* Let Z := sum of z_P, and let G be the set of sigma in Sigma that equal a . z_P for some a with
dist(a, c) <= m/2. If sigma is in Sigma but not in G, pick any a with a . z_P = sigma. Its complement
1 - a has sum Z - sigma and dist(1 - a, c) = m - dist(a, c) < m/2. So Z - sigma is in G. The map
sigma -> Z - sigma is injective, so |Sigma \ G| <= |G| and |G| >= N/2. G is the union of the m/2 + 1 sets
K(c, j) with j <= m/2, so one of them has at least (N/2)/(m/2 + 1) = N/(m + 2) elements. ∎

**Lemma 3.4 (residues of a layer set) [proof].** Let p be a prime with coll_p <= 3N on Sigma (Lemma 2.3).
For every K subset of Sigma, |K mod p| >= |K|^2/(|K| + 3N) >= |K|^2/(4N). In particular,
|K(c, j) mod p| >= D := ceil(N/(4(m+2)^2)) whenever |K(c, j)| >= N/(m+2).

*Proof.* Let n_r be the number of elements of K in class r. Then sum_r n_r = |K|, and
sum_r n_r^2 = |K| + (collisions within K) <= |K| + 3N. By Cauchy-Schwarz, the number of nonempty classes is
at least |K|^2 / sum_r n_r^2. Use |K| <= N for the second inequality, and note that the count is an
integer. ∎

**Lemma 3.5 (the split and the list exponents) [proof; source YL Thm 2.2, "Choose l", re-derived for
general m].** Let (dL', dR') be rationals with dL' >= dL, dR' >= dR and dL' + dR' <= 1/2 - 2 xi', where
0 <= xi' <= xi (Certificate 7.2 fixes them). Put

    l*_j := (1/2) (n - 2m + (h(s) + s) m + 2(1 - s)(dR' - dL') m),

and let l_j be an integer in [0, n - m] with |l_j - l*_j| <= 1 (such an integer exists by (a)). YL compute l*_j to error 1/4 and round; the computation
takes poly(n) time. Then, for m <= n/3:
- (a) 0 <= l*_j <= n - m.
- (b) Let e_L := ceil((dL' + eps) n') and e_R := ceil((dR' + eps) n'). Then 2^{e_L} |A_j| and
  2^{e_R} |B_j| are both at most 2^{X_j + 3}, where X_j := n/2 + m((1 + h(s))/2 - 2 xi'(1 - s)) + 2 eps m.
  Moreover X_j <= n/2 + (1 - xi') m + 2 eps m.
- (c) m/2 + l_j/2 <= n/4 + m/2 + 1, and m/2 + j + (n - m - l_j)/2 <= n/4 + 3m/4 + 2.

*Proof.*
- (a) We have 0 <= dR' <= dL' + dR' <= 1/2, so |dR' - dL'| <= 1/2. Lower bound:
  2 l*_j >= n - 2m - m >= 0 when m <= n/3. Upper bound: h(s) + s <= 3/2, so
  2 l*_j <= n - 2m + (5/2) m <= 2(n - m) when m <= 2n/5.
- (b) Use binom(m, j) <= 2^{h(s) m}. Substituting l*_j, both log-sizes equal
  n/2 + (1 - s)(dL' + dR') m + (h(s) + s) m/2 + 2(1 - s) eps m (expand both). The roundings add at most 3.
  Then:
  - (1 - s)(dL' + dR') <= (1 - s)(1/2 - 2 xi') gives the form of X_j.
  - h(s) <= 1 and 1 - s >= 1/2 give the bound by n/2 + (1 - xi') m + 2 eps m.
- (c) Left: m/2 + l*_j/2 = n/4 + m((h(s) + s)/4 + (1 - s)(dR' - dL')/2). With dR' - dL' <= 1/2 - 2 xi',
  this is at most n/4 + m((1 + h(s))/4 - xi'(1 - s)) <= n/4 + m/2.
  Right: m/2 + sm + (n - m - l*_j)/2 = n/4 + m(1/2 + s - (h(s) + s)/4 - (1 - s)(dR' - dL')/2). With
  dR' - dL' >= -dL' >= -(1/2 - 2 xi'), this is at most n/4 + m(3/4 + s/2 - h(s)/4 - xi'(1 - s)). That is at
  most n/4 + 3m/4, because h(s) >= 2s on [0, 1/2] (h is concave, h(0) = 0 and h(1/2) = 1). The roundings add
  at most 1 and 2. ∎

The right bound is JUDGE fix S2. AUDIT.md had 1/4 + pi/2 there. Neither bound is binding (Certificate 7.2).

## 4. The algorithm DET2

Constants, fixed once and for all:
- pi := 2499/10000;
- xi' := 2.0035e-5. Certificate 7.2[B] shows that xi' := 2e-5 also works;
- gamma := 2 xi'/3;
- eps := 10^{-9}, the partial-match slack;
- dL' := 0.007275870560 and dR' := 0.492684058989.

Certificate 7.2 checks that (dL', dR') dominates YL's pair and that dL' + dR' <= 1/2 - 2 xi'. So
(dL', dR') is admissible by (Y2) and upward closure. PM := PM_eps, the algorithm of (Y1) for YL's
pair (dL, dR). Its time bound also holds with (dL', dR') in place of (dL, dR). Sec. 8 says what is
hardcoded in PM.

**Lemma 4.1 (few sums) [proof; source AKKN16 Lemma 3.2 via YL, re-derived for general m].** Given Sigma with
one representative a_sigma for each sigma, put l' := floor((n - m - ceil(log N))/2). Then meet-in-the-middle
between L1 := {sigma + x . z_{B'} : sigma in Sigma, x in {0,1}^{l'}}, where B' is the l' coordinates after
P, and L2 := {y . z_{rest}} decides the instance exactly. It takes poly(n, L) 2^{(n - m + log N)/2 + 1} time.

*Proof.*
- *Range of l'.* Since log N <= m <= n/3, we have 0 <= l' <= n - m.
- *Correctness.* A solution c gives sigma = c_P . z_P in Sigma, x = c_{B'} and y = c_rest with
  sigma + x . z_{B'} + y . z_rest = tau. Conversely, every match gives the solution
  (a_sigma, x, y). Apply (K3).
- *List sizes.* |L1| = N 2^{l'} <= 2^{(n - m + log N)/2} and |L2| = 2^{n - m - l'} <= 2^{(n - m + log N)/2 + 1}.
  - *Check of the exponent (referee J2 asked for 3/2).* Put x := n - m - ceil(log N), so l' = floor(x/2) >=
    (x - 1)/2. Then n - m - l' <= (n - m + ceil(log N))/2 + 1/2 < (n - m + log N)/2 + 1/2 + 1/2, because
    ceil(log N) < log N + 1. So +1 is right, and the floor and the ceiling each cost 1/2 but together stay
    below 1. Also |L1| = N 2^{l'} <= 2^{log N + x/2} <= 2^{(n - m + log N)/2}. A sweep of all n < 400,
    2 <= m <= n/3 and N <= 3000 found no violation. The exponent margin is unchanged. ∎

**DET2(z, tau).**
- **Step 0.** If n < n_0, solve by brute force. Otherwise put m := 2 floor(pi n/2).
- **Step 1.** Enumerate the 2^m prefix sums, sort them, and keep Sigma with one representative each. N := |Sigma|.
- **Step 2 (few sums).** If N <= 2^{(1 - gamma) m}, run Lemma 4.1, return its answer, and stop.
- **Step 3 (deterministic filter).**
  - (a) Find the prime p of Lemma 2.3 for Sigma, with P0 = N(b+1).
  - (b) For every c in {0,1}^m and every layer j, compute K(c, j) mod p, by bucketing a . z_P mod p over all
    pairs (a, c) by dist(a, c).
  - (c) Put D := ceil(N/(4(m+2)^2)) and T_j := {c in {0,1}^m : |K(c, j) mod p| >= D} (JUDGE fix S1).
  - (d) For each layer j with T_j nonempty, compute R_j by Lemma 2.1 on U_j := T_j x Z_p, with
    K_c := K(c, j) mod p.
- **Step 4 (class costs and best rotation).** For each layer j:
  - Compute the histograms hA_j(r) := #{a in A_j : a . z ≡ r} and hB_j(r) := #{b in B_j : tau - b . z ≡ r},
    for r in Z_p, as follows:
    - hA_j is the cyclic convolution of the prefix histogram (over all 2^m vectors) with the histogram of
      B1_j-sums. The B1_j histogram is itself the convolution of the histograms of the two halves of B1_j.
    - hB_j is obtained in the same way, from the histogram of {b_P . z_P : b_P in T_{m,j}} (by enumerating
      the at most 3^m vectors) and the two halves of B2_j, followed by r -> tau - r.
    - All convolutions are exact, by (K2).
  - Put w_j(r) := 2^{e_L} hA_j(r) + 2^{e_R} hB_j(r).
  - Compute sigma_j by Lemma 2.2, and put C_j := R_j + sigma_j.
- **Step 5 (generate the kept records; YL "Generating the surviving records", with the interval replaced
  by C_j).** For each layer j:
  - Split P into halves, and each of B1_j and B2_j into halves.
  - *Left.* List 1 holds the left partial assignments (first half of P, first half of B1_j), sorted by key
    mod p. For each entry of list 2 (the second halves) with key part k2, and for each r in C_j, report the
    list-1 entries with residue (r - k2) mod p.
  - *Right.* Use half-prefixes in {-1,0,1}^{m/2} with at most j nonzeros, grouped by their number of
    nonzeros, and look up residue (tau - r - k2) mod p in the group that completes j.
  - This lists exactly the records of A_j and of B_j whose key residue lies in C_j, with multiplicity.
- **Step 6 (count).** For each layer j, run PM on the kept records: rows x(a) keyed by a . z, and queries
  y(b) keyed by tau - b . z (Lemma 3.2). If some count is positive, return yes; otherwise return no.

Relative to YL Thm 2.2, the following are replaced:
- the random multiply-add-shift filter (alpha, beta), by Steps 3-4;
- the 10n repetitions and the Markov cutoff, by one pass per layer with the exact cost bounds of Sec. 6.
Every other step is YL's, re-derived for general m (Sec. 3). No step uses randomness: p, T_j, R_j and
sigma_j are all computed. [proof: by inspection of Steps 0-6]

## 5. Correctness

**Lemma 5.1 (every prefix is in some family) [proof].** In Step 3, the union of the T_j over j <= m/2 is
{0,1}^m, and every K_c used in Lemma 2.1 has at least D >= 1 elements.

*Proof.* By Lemma 3.3, every c has a layer j with |K(c, j)| >= N/(m+2). By Lemma 3.4, that layer has
|K(c, j) mod p| >= D, so c is in T_j. Membership in T_j means |K_c| >= D by definition. ∎

**Lemma 5.2 (a correct pair of every solution is kept) [proof].** Let c be a solution and let j be any
layer with c_P in T_j. Then Step 5 keeps some a in A_j and b in B_j with a + b = c and equal keys.

*Proof.* Put y := c_{B1_j} . z_{B1_j} mod p. By Lemma 2.1 (i) and (iii), some r in C_j covers (c_P, y):
r - y ≡ sigma (mod p) for some sigma in K(c_P, j). So sigma = a_P . z_P for some a_P with
dist(a_P, c_P) = j. Lemma 3.1(a) gives a in A_j and b = c - a in B_j, whose common key is
sigma + c_{B1_j} . z_{B1_j} ≡ r (mod p). Both have residue r, which is in C_j, so Step 5 keeps both. ∎

The covering ranges over c_P because the layer set K(c_P, j) is not a translate of one fixed set: its
elements depend on c_P (JUDGE_S1, Stage 2, "Key set"). A covering of the translates of Sigma reused in every
layer is wrong. The control 'sigma' of `check_stage2.py` shows it missing solutions.

**Lemma 5.3. DET2(z, tau) returns yes iff the instance has a solution [proof].**

*Proof.*
- *Few sums.* Step 0 is exact, and so is Step 2 (Lemma 4.1).
- *If yes, then a solution exists.* A positive count in Step 6 gives kept a in A_j and b in B_j with equal
  keys such that x(a) matches y(b). By Lemma 3.2, a + b is binary, and by Lemma 3.1(b) it is a solution.
  This uses only that PM's count is exact (Y1).
- *If a solution c exists, then yes.* By Lemma 5.1, c_P lies in some T_j. By Lemma 5.2, the pair (a, b) is
  kept in layer j. It has equal keys and is compatible by Lemma 3.2, so PM's exact count is at least 1. ∎

**Remark 5.4.**
- *Exactness, not speed.* Correctness uses only that PM counts exactly. Any exact keyed counter gives a
  correct algorithm. For example, the trivial circuit, in which each query lists its 2^{n'/2} completions,
  is a correct counter. `check_stage2.py` runs DET2 with that counter. The hardcoded circuit of Sec. 8
  matters only for the running time.
- *The prime.* The prime p enters correctness only through coverage, namely the claim that the families T_j
  cover {0,1}^m (Lemma 5.1). That claim uses coll_p <= 3N: Lemma 3.4 turns it into |K(c, j) mod p| >= D for a
  dense layer, and Lemma 3.3 supplies the dense layer. Nothing else about p is used, so with any prime that
  breaks coll_p <= 3N, DET2 can miss a solution because c_P lies in no T_j. Everything after that (Lemma 5.2,
  Step 6) needs only that K_c is nonempty. Time is affected by p through |R_j| <= p/D (...); D itself does not depend on p.

*Proof of Corollary 2.* If layer j has a positive count, bisect its two kept record lists. Halve A, keep a
half whose count against B is still positive, and repeat; then do the same for B. This takes
O(log(|A| + |B|)) = O(n + log L) further PM calls, each on sublists, so each costs at most the layer's
original call. One pair (a, b) remains, and c = a + b is a solution (Lemma 5.3) (YL "Counting and
recovery"). In the few-sums branch, the meet-in-the-middle match gives (a_sigma, x, y) directly. ∎ [proof]

## 6. Running time

Write poly for poly(n, L). Note that b <= L + 1, and keys and gate data have O(L + n) bits.

**Lemma 6.1 (cost of each step) [proof].** Assume n >= n_0 and m = 2 floor(pi n/2), so
pi n - 2 < m <= pi n. Then the steps cost as follows.
- (a) Step 1: 2^m poly.
- (b) Step 2: poly * 2^{n/2 - gamma m/2} when it runs. This is Lemma 4.1 with N <= 2^{(1 - gamma) m}.
- (c) Step 3(a): N^2 (b+1) poly <= 2^{2m} poly (Lemma 2.3(ii)).
- (d) Step 3(b): 2^{2m} poly. It visits each pair (a, c) once per layer, then sorts and deduplicates per
  bucket.
- (e) Step 3(d): by Lemma 2.1(iv), with |T_j| <= 2^m and p <= 2 P0 = 2N(b+1):

      |R_j| <= (p/D)(1 + ln(2^m p)) <= 8(b+1)(m+2)^2 (1 + ln(2^m p)) = poly,

  so the coverings cost (m/2 + 1) * poly * 2^m * p * poly = 2^{2m} poly.
- (f) Step 4 (histograms and convolutions; JUDGE fix S3):
  - the prefix histogram: 2^m poly;
  - the half-block histograms: 2^{ceil(l_j/2)} + 2^{ceil((n - m - l_j)/2)}, times poly;
  - the right prefix histogram: 3^m poly <= 2^{1.585 m} poly (since 3^200 < 2^317);
  - four exact cyclic convolutions of length p, with entries below 2^{n+1}: p poly by (K2);
  - the weights w_j: O(p) operations;
  - the shift: O(p |R_j|) = p poly.
- (g) Step 5. Left partial lists have at most 2^{m/2 + ceil(l_j/2)} <= 2^{n/4 + m/2 + 2} entries, and right
  ones at most sum_{i <= j} binom(m/2, i) 2^i * 2^{ceil((n - m - l_j)/2)} <= 2^{m/2 + j + (n - m - l_j)/2 + 1}
  <= 2^{n/4 + 3m/4 + 3} entries (Lemma 3.5(c); this is JUDGE fix S2). Each list-2 entry does |C_j| = |R_j|
  = poly lookups, by binary search. The reported records number |A_j ∩ kept| + |B_j ∩ kept|, which is at
  most the cost of (h).
- (h) Step 6, many sums. By (Y1) for (dL', dR'), PM costs poly * (2^{e_L} |A_j ∩ kept| + 2^{e_R} |B_j ∩ kept|)
  = poly * sum_{r in C_j} w_j(r). By Lemmas 2.2, 2.1(ii) and 3.5(b), together with D >= N/(4(m+2)^2):

      sum_{r in C_j} w_j(r) <= (|R_j|/p) sum_r w_j(r) <= (4(m+2)^2 (1 + ln|U_j|)/N) * 2 * 2^{X_j + 3}
                             <= poly * 2^{n/2 + (1 - xi') m + 2 eps m} / N.

  Step 6 runs only when N > 2^{(1 - gamma) m}, so this is at most poly * 2^{n/2 - (xi' - gamma) m + 2 eps m}.
- (i) Recovery (Corollary 2): O(n + log L) times (h).

So with m <= pi n, m > pi n - 2 and gamma = 2 xi'/3, the total over the m/2 + 1 layers is

    poly * 2^{E n},   E := max{ 2 pi, log2(3) pi, 1/4 + pi/2, 1/4 + 3 pi/4,
                               1/2 - gamma pi/2, 1/2 - (xi' - gamma) pi + 2 eps pi }.

The 2 pi term collects (a), (c), (d) and (e). The term pi from (a) and from p is dominated by it. The
half-block histograms of (f) are dominated by (g). ∎

## 7. The exponent

**Lemma 7.1 [proof].** With gamma = 2 xi'/3, the two branch terms are 1/2 - xi' pi/3 (few sums) and
1/2 - xi' pi/3 + 2 eps pi (many sums). At pi = 3/(12 + 2 xi), 2 pi equals 1/2 - xi pi/3. This is the
balance point of AUDIT.md (pi* = 0.2499991652), where the exponent would be 0.4999983304. We use the
rational pi = 0.2499 instead, which has a margin.

**Certificate 7.2 (`cert_eps.py`; exact rationals) [proof by exact computation].**
- [A] pi = 0.2499, xi' = 2.0035e-5 (at most the table's xi), eps = 1e-9:
  - side conditions: pi <= 1/3, pi <= 2/5, dL' >= dL, dR' >= dR, and dL' + dR' = 0.499959929549 <=
    1/2 - 2 xi' = 0.49995993;
  - terms: 2 pi = 0.4998; 1/4 + 3 pi/4 = 0.437425; 1/4 + pi/2 = 0.37495; log2(3) pi <= 0.3960915;
    few sums <= 0.499998331085; many sums <= 0.499998331585;
  - so E <= 0.499998331585 < 0.49999834 (margin 8.4e-9), and the gain is 1/2 - E >= 1.668e-6.
- [B] The same with xi' = 2e-5. [B] is NOT weaker in assumptions than [A]: dL and dR still come from the table
  (upper bounds, truncation + 10^-20), and that pair alone already gives xi' = (1/2 - dL' - dR')/2 = 2.00352e-5.
  [B] only checks the xi_cap bookkeeping (xi' = 2e-5 is the stated bound). The rational pair (dL', dR') = (0.007275870560,
  0.492684058989) lies above them with dL' + dR' = 0.499959929549 <= 1/2 - 2 * 2e-5 = 0.49996.
  E <= 0.4999983345 < 0.49999834 (margin 5.5e-9), and the gain is >= 1.6655e-6. [proof by exact computation,
  given the table as upper bounds on dL, dR]
- [K] Block length (Cor. 3.2 restated for the rational pair). Cor. 3.2 assumes (dL, dR) in K(1/2) (circuits exist). The PROOF of
  Prop. 4.2 (not only its statement) gives Ye-Li's pair in K(1/2), and K is closed upward, so (dL', dR') is in K(1/2). Its two conditions for the pair, at eps = 1e-9, are
  (2/kappa)(max(dL', dR') + eps/4) <= eps/4 and log2(kappa + 1)/kappa <= eps/4. The first gives
  kappa >= 8 (dR' + eps/4)/eps = 3.9415e9. The second is monotone for kappa >= 1 and gives kappa >= 1.4844e11,
  so it is the binding one. The least even kappa is 148444531984, and N' = kappa^2 + 2 kappa >= 2.2036e22.
  (The second condition was missed in the first write-up, which stated N' >= 1.55e19; that was a true but loose
  lower bound.) [proof by computation; the second condition is evaluated by bisection in 60-digit decimals]
- Must-fail controls (each rejected by the same checker):
  - [C1] at [A], the claim E <= 0.49999833;
  - [C2] pi = 1/4 (the covering then costs 2^{n/2});
  - [C3] YL's own prefix pi = 1/3 (the covering then costs 2^{2n/3});
  - [C4] eps = 1e-6;
  - [C5] xi' = 0 (Prop. 4.2 false);
  - [C6] a pair rounded down below YL's table (the admissibility check fails);
  - [C7] in [B], the false claim xi' = 2.1e-5 (the pair is too large for it);
  - [C8] in [B], a pair rounded down below the upper bounds on dL, dR.

*Proof of Theorem 1.* Lemma 5.3 gives correctness. Lemma 6.1 and Certificate 7.2[A] give time
poly(n, L) 2^{E n} with E <= 0.499998331585. Since 0.49999834 - E > 8e-9, the factor poly(n, L) = 2^{o(n)}
(when L = 2^{o(n)}) is at most 2^{8e-9 n} for large n. So the time is O(2^{0.49999834 n}). ∎ [proof]

*What the deterministic version loses.* YL's randomized exponent is 1/2 - xi/9 = 0.4999977739 at pi = 1/3.
Deterministically, the covering costs 2^{2m}. That forces m < n/4, and the gain shrinks from xi/9 to about
xi/12. A cheaper universal covering would recover part of the gap (`../AUDIT.md`, sec. 5, item 3) [arg].

## 8. Non-explicitness, stated precisely

**8.1 What exists [cite: (Y2), (Y4)].** Fix eps = 1e-9. By Prop. 4.2, through Cor. 3.2, there exist:
- an even integer kappa that satisfies Cor. 3.2's conditions, (2/kappa)(max(dL', dR') + eps/4) <= eps/4 and
  log(kappa + 1)/kappa <= eps/4, for the algorithm's rational pair (dL', dR') of Sec. 4 (this is Cor. 3.2
  applied to (dL', dR') in K(1/2) by upward closure from the proof of Prop. 4.2, Sec. 7 item [K]);
- an exact integer depth-2 circuit C* = (L*, R*) for the matrix P_{N', 1/2}, where N' := kappa^2 + 2 kappa.
  Here L* R* = P_{N', 1/2} holds entrywise over Z. Every row has at most 2^{(dL' + eps/4) N'} incident gates,
  and every query has at most 2^{(dR' + eps/4) N'}.

The existence proof is non-constructive:
- the window circuit of Sec. 3.5 comes from random orderings and a union bound;
- hole fixing comes from random symmetries (AL25 Thm 6.1, or Lemma 9.1);
- rebalancing comes from AL25 Thm B.2, a recursion over a min that is not given explicitly;
- "kappa sufficiently large" is ineffective: it hides the hole-fixing constant, Stirling terms and the
  2^{o(d)} of Thm B.2 (AUDIT_YELI sec. 3).

**8.2 What DET2 hardcodes [proof: by inspection of Sec. 4 and YL Cor. 3.2, Cor. 3.3].** The hardcoded data
is the pair (kappa, C*): a finite table of integers. PM_eps is YL Cor. 3.3 applied to Cor. 3.2's enumerators,
and those enumerators are built from (kappa, C*) by the explicit Lemma 3.1 grouping and tensor powering.
Everything else in DET2 is explicit and written out in Sec. 4: the constants pi, xi', gamma, eps, dL', dR',
the prime scan, the coverings, the shift, the generation, and the bisection.

**8.3 Why this is a legitimate deterministic algorithm [arg: standard definitions].**
- *Program.* A deterministic algorithm is a single finite program, for a RAM or a Turing machine, that halts
  on every input with the correct answer. Its time bound is a function of the input size that holds for
  every input. For the right (kappa, C*), DET2[kappa, C*] is such a program.
- *No randomness.* It reads no random bits.
- *Uniform.* The same finite constant serves every n. It is not advice that depends on n, so this is not a
  non-uniform circuit family.
- *Correct everywhere.* Correctness (Lemma 5.3) and the time bound (Lemma 6.1) hold for every input.
- *Logical form.* Theorem 1 says that **there exists** such a program. The proof establishes this
  existentially: the program DET2[kappa, C*] for the (kappa, C*) of 8.1 works. It does not identify which
  (kappa, C*) that is. So the result is non-constructive.

  The logical form is the same as that of Robertson-Seymour's theorem. Each minor-closed graph class has a
  finite obstruction set, and so membership is decidable in cubic time, but the obstruction set is in
  general not known (Robertson-Seymour, Graph Minors XIII and XX; Fellows-Langston 1988 on such
  non-constructive algorithms) [cite].
- *What we do not claim.* We do not claim an algorithm that anyone can run. The hardcoded circuit has at
  least 2^{N'} rows. Certificate 7.2[K] computes kappa >= 1.4844e11 from Cor. 3.2's two conditions at
  eps = 1e-9 (the second binds), so N' >= 2.2e22. Merely checking one candidate means touching 2^{N'} rows and
  binom(N', N'/2) 2^{N'/2} queries.

**8.4 A self-searching variant [arg].** Let DET2-search first search for a witness, then run DET2 with it:
- For even kappa = kappa_0, kappa_0 + 2, ..., with kappa_0 the least even integer meeting Cor. 3.2's two
  conditions for the rational pair (dL', dR') (Sec. 7 item [K]: kappa_0 = 148444531984), dovetail over all
  integer pairs (L, R) in order of size.
- Check exactly that L R = P_{kappa^2+2kappa, 1/2} and that the degree caps hold. The caps are
  2^{(dL' + eps/4) N'} and 2^{(dR' + eps/4) N'} with the RATIONAL exponents dL', dR': a rational exponent
  a = u/v gives the integer test degree^v <= 2^{u N'}, which is a finite exact check. Using YL's irrational
  dL and dR here would not be a finite test.
- Run DET2 with the first witness found.

Why this works:
- The search halts, because 8.1 guarantees a witness for every sufficiently large kappa.
- Any witness serves Cor. 3.2, because that proof uses only exactness, the degree caps, and the two
  conditions on kappa. This is AUDIT_YELI sec. 3, with the dovetailing of fix D7.
- The search does not depend on the input, so it costs an additive constant c_eps.

So DET2-search is a fully specified program, with time c_eps + O(2^{0.49999834 n}). Its constant c_eps is
finite but astronomically large: verifying the witness alone takes at least 2^{N'} >= 2^{2.2 * 10^22} bit
operations. Our
proofs give no upper bound on c_eps, because "sufficiently large kappa" is ineffective. This variant
strengthens the formal statement: an explicit program exists. It changes nothing in practice. We label it
[arg], because we have not written the search's exact degree check against Cor. 3.2's proof line by line.

## 9. Replacing AL25 Thm 6.1: hole fixing by inclusion-exclusion

YL Lemma 3.4 extends a circuit on a window to the full half-stars matrix by "hole fixing [AL25 Thm 6.1 and
its proof]". It asserts that the proof partitions the matrix into disjoint rectangles, so that integer
coefficients survive. That part of AL25's proof was not read (AUDIT_YELI D2). The following lemma gives the
same conclusion directly, with no appeal to Thm 6.1.

**Lemma 9.1 (inclusion-exclusion assembly) [proof].** Setting:
- M is a matrix with row set X and column set Y.
- G is a finite group acting on X and on Y with M_{g x, g y} = M_{x, y}, transitively on each of X and Y.
- W = X0 x Y0 is a window with |X \ X0| <= eta |X| and |Y \ Y0| <= eta |Y|, where 2 eta < 1.
- C is a coloured exact integer depth-2 circuit for M restricted to W.

Let J > ln(|X||Y|)/ln(1/(2 eta)) be an integer. Then:
- (a) There are g_1, ..., g_J in G such that the rectangles g_i W = g_i X0 x g_i Y0 cover X x Y.
- (b) For nonempty S subset [J], put X_S := ∩_{i in S} g_i X0 and Y_S := ∩_{i in S} g_i Y0. Then

      M = sum over nonempty S subset [J] of (-1)^{|S|+1} M|_{X_S x Y_S},

  where M|_{X_S x Y_S} agrees with M on X_S x Y_S and is 0 elsewhere.
- (c) Let i_S be the least element of S. The copy g_{i_S} C, with its rows restricted to X_S, its columns
  restricted to Y_S, and its left coefficients multiplied by (-1)^{|S|+1}, computes the S-th term exactly
  over Z.
- (d) The sum of these 2^J - 1 copies, with colours tagged by S, is an exact integer circuit for M. In every
  copy, each colour has left and right degrees at most those of the same colour of C. So the volume obeys
  Upsilon(tau) <= (2^J - 1) Upsilon_C(tau) for every tau.

*Proof.*
- (a) Take g uniform in G. Transitivity makes g^{-1} x uniform on X, since all stabilisers have equal size.
  So Pr[x not in g X0] <= eta, and likewise for y. Hence Pr[(x, y) not in g W] <= 2 eta. For J independent
  draws, a fixed (x, y) is missed with probability at most (2 eta)^J < 1/(|X||Y|). By the union bound, some
  choice misses no pair.
- (b) For each (x, y), put e_i := [x in g_i X0][y in g_i Y0]. Then sum_S (-1)^{|S|+1} prod_{i in S} e_i =
  1 - prod_i (1 - e_i). This equals 1, because by (a) some e_i = 1. Moreover prod_{i in S} e_i = [(x, y) in
  X_S x Y_S].
- (c) g_{i_S} C computes M exactly on g_{i_S} W, by the invariance of M, and X_S x Y_S lies inside that
  rectangle. Restricting L to rows in X_S and R to columns in Y_S (zeroing the rest) computes M there and 0
  elsewhere. Restriction removes edges only, and a global sign changes no degree.
- (d) Concatenating the middle gates sums the circuits. Then (b) and (c) give the result. ∎

*Use in YL Lemma 3.4 [proof, given YL's stated facts (cite)].* The facts YL state are:
- X = {0,1}^n and Y = the half-stars queries;
- G is generated by coordinate permutations and simultaneous flips of row bits and specified query bits.
  These preserve matching and act transitively on each side (YL Lemma 3.4 proof);
- the window omits a fraction eta = 2^{-Omega(eps'^2 n)} of each side, by binomial concentration (same
  place).

Then ln(|X||Y|) <= 3n, so J = O(1/eps'^2) suffices, independent of n. The number of copies,
2^J - 1 = 2^{O(1/eps'^2)}, is a constant. As in YL, it costs at most 2^{eps_1 n/2} in volume for large n.
Colours are tagged by copy, exactly as YL do ("Add the copy index to each color"). So Lemma 3.4's conclusion
holds with Lemma 9.1 in place of AL25 Thm 6.1. The g_i are chosen by the probabilistic method, which is one
more non-constructive step, and harmless here because the circuit is non-explicit anyway (Sec. 8).
`check_stage2.py` tests parts (b)-(d) (not the J bound of (a): n = 4 is outside 2 eta < 1, and n = 6 uses J below it) at gate level on P_{4,1/2} and P_{6,1/2} [proof by exhaustive computation at
those sizes]. The window circuit is a real depth-2 circuit (gates are the strings of {0,1}^n, left matrix
L[x, x] = 1 for x in X0, right matrix R[gate, q] = 1 iff the gate completes q), so its right side is not
copied from M. The group is the FULL group (all coordinate permutations combined with all flips), the g_i are
drawn at random, and the 2^J - 1 signed, restricted, transported copies are assembled gate by gate and multiplied
out. The product equals M entry by entry (J = 11 for n = 4; J = 9 and 8 for n = 6, two draws; J group elements give 2^J - 1 copies), and every copy
has left and right degrees at most those of C. The control (no signs) does not equal M. Sizes beyond
n = 6 need J > 11, hence more than 2^11 copies, and were not run.

## 10. Mechanical check (small instances; logic, not asymptotics)

`check_stage2.py` implements DET2 from this document and compares it with brute force.

**Stand-in for the hardcoded circuit.** The real C* cannot be run (Sec. 8). The check uses YL Cor. 3.3's
label-sum interface, with labels (key, gate), on the trivial exact circuit, whose exponent pair is (0, 1/2):
- a row x has the single gate x;
- a query has one gate per completion of its wildcards.

This counter is exact, which is all that correctness uses (Remark 5.4). Every count is also cross-checked
by direct arithmetic (a + b in {0,1}^m), which tests Lemma 3.2's padding.

Asserted on every instance:
- *Answers.* Both branches (Lemma 4.1, and Steps 3-6) are run on every instance, and each equals brute
  force. A recovered solution is verified.
- *Lemmas 3.3 and 3.4,* for every (c, j).
- *Lemma 5.1.* The families T_j cover {0,1}^m.
- *Lemma 2.1 (i)-(ii),* exhaustively.
- *Lemma 2.2's bound,* in integers.
- *Step 4.* The convolution histograms equal the direct histograms.
- *Step 5.* The meet-in-the-middle generation equals the brute-force filtered record multisets.
- *Lemma 5.2,* for every solution and every layer containing its prefix.
- *Run 1 only (true prime range).* coll_p <= 3N, and the bad-prime count is below Lemma 2.3's bound.

Families: random 30-bit, small values in [1, 40], multiples of 667, powers of 2 on the prefix, mixed signs
in (-2^20, 2^20), and a prefix with few distinct sums. 65% of the targets are subset sums. Results, in
about 90 s on one core and about 42 MB:
- *Run 1 (logic only):* n = 10, m = 4, P0 = N(b+1) as in Lemma 2.3, D as in Step 3. 48 instances (37 yes),
  0 errors in either branch. The worst bad-prime count was 0. Kept/full weighted cost was 0.50. Here
  m > n/3, so Lemma 3.5's hypothesis fails. The proof's D = ceil(N/(4(m+2)^2)) is 1 on every instance, so
  layer 0 holds every prefix with R_0 = Z_p; 96 of the 144 layers were filtered, 48 were not.
- *Run 2 (logic only):* n = 13, m = 6, so again m > n/3: this run is outside Lemma 3.5's hypothesis, and it
  tests the filter's logic only. P0 = 2N (a small stand-in, scanned upward until coll_p <= 3N), with D the
  largest threshold for which the families still cover {0,1}^m, which makes the coverings tight. 48
  instances (37 yes), 0 errors. Kept/full cost was 0.20. All 64 layers filtered.
- *Run 3 (m = n/3, formally inside the hypothesis m <= n/3):* n = 18, m = 6. The run does not check Lemma 3.5's size bounds, so being inside the hypothesis changes nothing in what is tested. Its D is the largest value that still covers, not the proof's D, and only 32 of the 96 layer slots are nonempty. P0 = N(b+1) as in Lemma 2.3,
  and D the largest threshold for which the families still cover {0,1}^m. 24 instances (18 yes), 0 errors in
  either branch. Every one of the 32 layers is filtered (R_j != Z_p), and the kept/full cost is 0.22. The
  script requires run 3 to be inside the hypothesis and to filter at least one layer.
- *The proof's own D with D >= 2 is out of reach.* D = ceil(N/(4(m+2)^2)) exceeds 1 only when
  N > 4(m+2)^2, and N <= 2^m, so the least even m is 10 (m = 8 gives 400 > 256), which needs n >= 30. At
  m = 10 the greedy covering has about |T_j| p |K| ~ 10^9 steps in the layers where it filters, and the
  reference records number 3^10 per layer. That is beyond a pure-Python reference. So no run combines the
  proof's own D >= 2 with a filtered layer. What the runs do show: the proof's prime range with a filtered
  layer inside the hypothesis (run 3), and the proof's own D (= 1) with the proof's prime range (run 1).
  The step from D = 1 to the proof's D >= 2 changes only the threshold in the definition of T_j, which
  Lemmas 3.4 and 5.1 prove for every D.
- *Controls, which must fail:*
  - 'sigma' (one covering of the translates of Sigma, reused in every layer) missed 44 times;
  - 'single' (one residue per layer) missed 90 times;
  - 'nocompat' (equal keys counted without compatibility) gave 1 false positive.
- *Lemma 9.1 (gate level, full group, random g_i):* L R multiplied out equals M on P_{4,1/2} (J = 11, 2047 copies) and
  P_{6,1/2} (J = 9 and 8, two draws), every copy's degrees are at most those of C, and the unsigned sum is
  not M. See Sec. 9.

At these sizes D/p is not small, so the saving is not visible. The check tests logic only. It does not
exercise PM's speed, which only the real C* provides, nor the prime-number-theorem regime of Lemma 2.3(i).

## 11. What is not proved here

- **Cited, not re-proved:** YL Prop. 4.2 and its chain (Y2)-(Y4). These were audited in AUDIT_YELI.md:
  HOLDS, with no claim-level defect. Also cited: AL25 Thm B.2 (refereed; read and tested), and the classical
  facts (K1)-(K3). AL25 Thm 6.1 is no longer needed (Lemma 9.1). Nothing else is assumed.
- **[arg] items:**
  - the novelty statement (a literature search, Sec. 0);
  - the explanation of why the prime is not injective (Sec. 2), on which nothing depends;
  - the standard-definitions discussion of Sec. 8.3;
  - the self-searching variant of Sec. 8.4 (its rational degree check is now stated, but not written against
    Cor. 3.2's proof line by line);
  - the remark on a cheaper covering (Sec. 7).
- **Non-explicitness.** The algorithm exists, but nobody can run it or print it (Sec. 8).
- **Table inputs.** Certificate [B] avoids the table's xi but still takes dL, dR from the table, as upper
  bounds (Sec. 1, Y3).
- **Tests.** No end-to-end run has the proof's own D >= 2 (Sec. 10); Lemma 9.1 is tested only up to n = 6.
- **The constant.** It is not effective: the O(.) of Theorem 1 hides a constant that comes from YL's
  "sufficiently large" choices.
- **No claim at the exact balance point pi*,** and none that pi = 0.2499 is optimal.
- **Review.** Two independent referees confirmed the reduction with the fixes now applied. The fixed text has
  not been reviewed again.

## 12. Provenance, and what Stage 1 is

This section exists so that the document can be read without the other files of the project.

**What Stage 1 is [arg: a description of our own earlier work].** `../stage1/PROOF.md` proves that Subset Sum
is decided *deterministically* in time O(2^{n/2} n^{-gamma}) for every gamma < 0.010104, in the word-RAM and
circuit-RAM models of CJRS. It does this by taking the algorithm of Chen, Jin, Randolph and Servedio,
"Subset Sum in Time 2^{n/2}/poly(n)" (arXiv 2301.07134, CJRS), Sec. 4 (Representation-OV), which is
randomized, and replacing its two random objects: the random prime by a prime found by a deterministic scan on
which a certain sum set is injective, and the s(l) random residues by a greedy covering of all (restriction,
shift) pairs together with a best rotation. CJRS list derandomisation as open (their Sec. 6). So "Stage 1"
is a derandomisation of CJRS Sec. 4; the saving it obtains is CJRS's own Sec. 4 saving.

**How Stage 2 relates to CJRS [arg].** Stage 2 (this document) does not use CJRS's algorithm or any CJRS
statement; PROOF.md therefore cites CJRS nowhere in its proofs. It derandomises a different algorithm, Ye and Li's
(YL, arXiv 2610.10446), which beats the 1974 exponent 1/2 only randomizedly. The only thing it takes from
Stage 1 is the *technique* of the deterministic filter, i.e. two tools: a universal covering of residues
over all (prefix, shift) pairs, and the best rotation of it. CJRS's 2^{n/2}/poly(n) bound is in the word RAM and
concerns a polynomial factor; it has no bearing on the exponent here, and YL's model (bit operations) is not
the word RAM.

**Which Stage 1 statements are used, and where they are proved here.**
- Stage 1 Lemma 2.3 (covering, with all shifts): this is Lemma 2.1 above. Its statement is copied and its
  proof repeated in full.
- Stage 1 Lemma 2.4 (best shift): this is Lemma 2.2 above, with its two-line proof.
- Stage 1's injective-prime lemma (its Lemma 2.1) is *not* used. It is replaced by Lemma 2.3 above, which is
  proved here from the prime number theorem.
- Nothing else of Stage 1 is used. In particular none of Stage 1's CJRS facts F1-F10, constants or certificate.

**The other files named in this document.**
- `AUDIT_YELI.md` and `yl_*.py` (in this directory, stage2/; they were committed earlier and are not part of the self-contained checking package): our audit of YL Prop. 4.2. Logically, this proof uses only
  its verdict, (Y2): the statement of Prop. 4.2 as cited. The audit is not needed for any step here, but it is
  what makes (Y2) credible to us. It is our own audit, not an independent one.
- `../AUDIT.md`, `../JUDGE_S1.md`, `../RANDOMNESS_LEDGER.md`: our own design notes and a refute-by-default
  judge's report on the reduction. They record review history, the first derivation of the balance point
  pi*, and the earlier error 1/4 + pi/2 (Lemma 3.5 note). Everything they contribute is re-derived in this
  document (Lemma 7.1 re-derives pi*). No step depends on them.
- `cert_eps.py` and `check_stage2.py` (this directory) are self-contained scripts, written from this document
  and importing nothing from the other scripts.

**Review history [arg].** The reduction was audited and then judged (JUDGE_S1, four fixes). YL Prop. 4.2 was
audited from the TeX (AUDIT_YELI). Two independent referees then read the package on 2026-10-10 and confirmed
it with fixes; both re-checked the citations against the arXiv sources, re-derived the lemmas by hand, and ran
the scripts. Their fixes are listed in Sec. 0.
