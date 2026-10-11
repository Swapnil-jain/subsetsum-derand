# Stage 5: outer-sum dedupe on Record 3's deterministic route

Stage 5 is Stage 4 (`stage4.md`, the deterministic Record 3 route, E <= 0.4998322132) with Stage 3's outside-sum dedupe
(`stage3.md` Sec. 3) ported to it, and a per-layer menu of core densities. Bases: Stage 4, Stage 4+ (its Sec. 8, the
two-circuit family) and Stage 3. Credit: as Stage 4 (`stage4.md`, CREDIT); the reduction and the circuit family are
Record 3's, and the two changes made here are ours.

**Review.** Two independent clean internal referee passes confirmed R3; their fixes are applied here and in the code.
Internal referee passes are not peer review.

**Names.** Labels from our internal notes, used below: **A22** is Stage 3's outside-sum dedupe; **A39** is its port
to Record 3's route (this file); **A38** is the kappa-adaptive core menu (per layer, different core densities s1, s2 on
the two sides, with an unequal outer split w); **A41** is the observation that P6 is the wall of the D1 estimator.
D1 is Stage 4's residue estimator; nothing here uses any other estimator.

Scripts: `certificates/stage5/` (certificate `cert_stage5.py`, output `cert_stage5.out`; brute force `check_stage5.py`,
output `check_stage5.out`). Lean: `lean/SubsetsumLean/Stage5*.lean`.

Labels: [proof] proved here, given the cited items; [arg] argued, less than a proof; [cite] taken from the named place;
[iv] outward-rounded interval certificate (`cert_stage5.py`, Stage 4's arithmetic and prover imported read only);
[exp] brute force at toy size; [float] floating point, not a proof.

## Summary of the result

- **Mechanism [proof].** A22's dedupe ports to Record 3's route exactly. Take P := the least deficient of 2j + 1
  blocks, and list the outer parts by distinct sums. Both lists shrink by 2^{-dM}, and the filter at p ~ N pays 2^{dM}.
  The few/many branch, P2 and delta disappear. Every deficiency-sensitive step (prime, collisions, distinct
  residues, C_k, the estimator's universe) is a function of N = |Sigma(block)| alone. Cores, H/Hbar and layers live
  inside the block. So the least-deficient argument transfers without change (Lemma 3.1 below).
- **Best certified deterministic E [iv]: 0.4989524521** (saving 1.0475e-3, 6.2x Stage 4).

  | row | design | E_det <= | saving | binding |
  |---|---|---|---|---|
  | R1: A39 alone | Stage 4's symmetric s = 11/100 circuit, alpha per layer | 0.4995054714 | 4.9453e-4 | P3 at kappa 0.471, alpha 1/2 |
  | R1b: A39 alone, 2 blocks per side | same, j = 2 | 0.4993293934 | 6.7061e-4 | P3 at kappa 0.485, alpha 3/4 |
  | R2: A39 + A38 | 7-point menu, pairs (s1, s2), w per layer | 0.4991541425 | 8.4586e-4 | P3 at kappa 0.498; P6 0.499007 |
  | R3: A39 + A38 + Stage 4+ | R2 + the family point at 11/100 | **0.4989524521** | 1.0475e-3 | P3 at kappa 0.489 |

- **Reproduce.** `certificates/stage5/` is self-contained. `cert_stage5.py` is standard library only and uses `stage4_cert_vendored.py` (a verbatim copy of `certificates/stage4/cert_stage4.py`, re-copied after Stage 4's Lean check corrected its [F1] brackets; Stage 5 never calls [F1], since its contact lines already use the trivial values t1 h(s) and (1 - t2)(1 - s), so every number here is unchanged). `check_stage5.py` REQUIRES numpy (it vendors Stage 4's `estimator`); it was run with numpy 2.0.2.
- **Fixes (each is at its breaking site below and in the code).**
  1. **The layer range.** Without delta, the layers run over ALL kappa (Lemma 2.5), because an instance of
     deficiency d could own layers down to h(kappa) = 1 - d (a case the proof cannot exclude; in the brute force random
     instances are served by the central layer, far ownership appears only when the layer order is forced). The rows
     are therefore conservative upper bounds. With symmetric cores the off-centre curvature caps the saving
     at mu xi/2, not mu alpha xi (Sec. 5.3). So A39's "ceiling mu alpha xi" needs A38's asymmetric cores.
     Controls K6 and K6b reject the ceiling for R1.
  2. **A39's design set {0, alpha} leaves a gap** at kappa ~ 0.4485, just past the last feasible menu pair. A39's
     own script gives 0.4992334 there, above its printed 0.49919788 [float]; it sampled (0.402, 0.45) at no point.
     Repair: intermediate alphas per layer. A39's number then holds and improves: 8.02e-4 [float] becomes 8.4586e-4 [iv].
  3. **Stage 4 Lemma 5.2 assumes p <= |W_c|.** That fails at p ~ N once N < 2(M + 1) x_0. Repaired by the
     min(p, |W_c|) form (Lemma 2.4), at no cost.
- **A38 [proof here for the deterministic rows].** Lemma 3.3 gives per-piece families with two-valued x_i, x'_i
  (S4's parity rule only covers |x' - x| <= 1). Lemma 3.4 gives per-side circuits at two densities. The unequal outer
  split w needs no A3. Its menu circuits are re-proved with Stage 4's prover, with must-fail controls.
- **Weakest step.** Inheritance from Stage 4, which carries its cited (AL-B2), S2 Lemma 9.1 and the non-explicitness
  convention. Inside Stage 5, the weakest new step is Lemma 3.3 for the asymmetric (A38) designs. It is proved, but
  the brute force reaches only q = 1 piece (but two asymmetric layers, 2 and 3, as owners). R3 also leans on Stage 4+.
- **Brute force [exp].** n = 25; regimes center, far and asym; 112 runs. Results:
  - 0 wrong answers and 0 pseudo-solutions;
  - 0 layer-level violations on 693 sampled solutions;
  - 0 uncovered (c, y);
  - the list bound held on every instance;
  - raw and deduped lists agreed on positivity on 253 sampled picks;
  - the regime p > |W_c| was hit on 18 runs (6 in each of the three regimes);
  - ownership: center `own_4` only; far `own_0/1/3`; asym `own_2` (3072 c) and `own_3` (6144 c), so the two-valued
    asymmetric rule is served at non-central layers (layer 4, the third asymmetric one, stays unused as an owner);
  - instances: 36 per regime plus 4 straddle instances in center (40).

  Every must-fail control was detected: nocompat, mostdef (18 list-bound violations), blockdedupe (15), straddle
  (4/4 pseudo) and lowmult (80 uncovered).

## 0. Statements

**Theorem 5 (R1, A39 alone) [proof, given Stage 4's cited items; numbers [iv]].** Stage 4's DET4 with the few/many
dichotomy removed and the outer lists built from distinct outer sums (DET5, Sec. 2), on Stage 4's own round design
(one circuit at s = 11/100, symmetric cores) with the core fraction chosen per layer from {0, 1/20, ..., 19/20}, runs
deterministically in poly(n, L) 2^{(E + eps) n} with **E <= 0.4995054714** (saving 4.9453e-4, 2.95x Stage 4's 1.678e-4).

**Theorem 5A (R2, A39 + A38) [proof, same footing; numbers [iv]].** With A38's seven-density circuit menu, per-layer
pairs (s1, s2), per-layer alpha from {0, 1/10, ..., 9/10, 97/100} and a per-layer outer split w:
**E <= 0.4991541425** (saving 8.4586e-4; A39 printed 8.02e-4 [float]).

**Theorem 5F (R3, A39 + A38 + Stage 4+) [proof, same footing; numbers [iv]].** The same with the Stage 4+ family point
(s = 11/100, rho = 49/20 and 11/4) added to the menu: **E <= 0.4989524521** (saving 1.0475e-3). This is the best
certified deterministic exponent here.

**Theorem 5b (R1b, ours) [proof; [iv]].** Theorem 5 with two dedupe blocks per outer side: E <= 0.4993293934
(saving 6.7061e-4). It rescues the symmetric design off-centre (Sec. 5.3); it does not improve R2 or R3 (Sec. 5.5).

Every row here is D1 (Stage 4's residue estimator, term P6 included).

## 1. What is used

- **(S4)** [cite `stage4.md`] Secs. 1.2 (block representations, soundness, key identity), 1.4 (keys of a layer are
  a translate of a subset of Sigma; pigeonhole; C_k), 1.5 (compatible fraction, J), 2 (lists, tensor circuit, exact
  count, recovery, the s-cancellation), 3 (density-s circuits: Lemma 3.4 for a finite family, Lemmas 3.5, 3.5', the
  [XI] prover), 4 (splitter, per-piece greedy families, product family, lambda, multiplicity), 5.1-5.5 (prime,
  distinct residues, estimator, shift), 7 (non-explicitness). Every statement there is for an arbitrary instance and an
  arbitrary rational s in (0, 1/2); none uses the few/many branch except through T, which we replace.
- **(S4+)** [cite Stage 4 Sec. 8] Lemma 3.4 with P = 2 at s = 11/100; re-proved here by `cert_stage5.py` [iv].
- **(A22)** [cite `stage3.md` Sec. 3, Lemmas 3.1-3.3 and "Counting with multiplicity"] the template: P := the
  least deficient block, whole blocks deduped on one side each, representatives kept, positivity preserved, the d(P)
  cancellation. We re-prove each step on Record 3's route below rather than citing it, because the route differs.
- **(SUP)** [proof, standard] |Sigma(X u Y)| <= |Sigma(X)| |Sigma(Y)| for disjoint X, Y.

Notation as Stage 4: block of M = N_b floor(mu n/N_b) coordinates, N := |Sigma(block)|, d := 1 - (log2 N)/M in [0, 1]
(the instance's own deficiency per block coordinate), kappa := k/M, layers k = 0..M.

## 2. The algorithm DET5

Changes to DET4 (Stage 4 Sec. 5.2), each with its reason; every other step is DET4's.
- **Step 1 (blocks).** Partition 2j + 1 disjoint M-sets B_0, ..., B_{2j} (j = 1, or 2 for R1b) and a rest Rr. Build
  each Sigma(B_i) by sorted merges, keeping the least-mask representative of each sum (cost (2j + 1) 2^M poly: term
  **P1 = mu**). The block is P := the B_i with the largest |Sigma| (least index on ties); the others are Qa_1..Qa_j and
  Qc_1..Qc_j. There is no threshold T, no delta and no few-sums branch.
- **Step 2 (prime).** P0 := max(floor(N/(2(M + 1))), x_0), x_0 the threshold of (K1); p := the prime of [P0, 2 P0] with
  the least collision count (least p on ties). Cost N p polylog <= 2^{2 mu n}: **Pscan <= 2 mu**.
- **Step 3 (layers).** C_k := {c : layer k of c has >= N/(M + 1) distinct keys}, for every k = 0..M (term
  **P5 = 2 mu**). A c may be kept only in the first served layer that holds it (any fixed order); this changes nothing
  below, as every lemma uses only "every c is in some served C_k with threshold >= N/(M + 1)".
- **Step 4 (designs).** A finite table, fixed with the algorithm, assigns to each kappa-piece a design
  (alpha, s1, s2, w): alpha from the row's menu (alpha = 0 is the core-free design), s1, s2 circuit densities from the
  row's menu (s1 = s2 = 11/100 in R1, R1b), w a rational outer split (w = 0 in R1, R1b). Layer k uses the design of
  the piece holding k/M. Its u-outer part is Qa_1 u ... u Qa_j u Rr_u(k), its v-outer part Qc_1 u ... u Qc_j u Rr_v(k),
  where Rr = Rr_u(k) u Rr_v(k) with |u-outer| = (1/2 + w)(n - M) up to rounding.
- **Step 5 (rounds).** F_k: Stage 4's product family for the design's counts (Lemma 3.3), repeated D times,
  D := ceil((2M + 2) ln 2 * G * ceil(p/min(p, w_min))) (Lemma 2.4), with w_min the least |W_c|.
- **Steps 6-8.** Stage 4's S_{c,f}, estimator and shift, the shift weights computed from the DEDUPED histograms
  (block-part histogram convolved with the histograms of the Sigma(.) mod p).
- **Step 9 (records).** u-records are (block part of u, s_1, ..., s_j, s_r) with s_i in Sigma(Qa_i), s_r in
  Sigma(Rr_u(k)); key = block part . z + sum of the s's. v-records likewise with key' = tau - (block part . z) - sum.
  Generation, the keyed count and bisection are Stage 4's on these lists; a recovered pair is turned into a vector by
  the stored representatives.
- *Gotcha (placed at Step 9 of the code):* only the OUTER parts may be deduped. Merging block parts with equal keys
  loses compatibility options (control blockdedupe, Sec. 6), and a deduped set straddling the two sides creates
  pseudo-solutions (control straddle).

## 3. Correctness

**Lemma 2.1 (soundness) [proof].** A counted pair is (u_b, s_1..s_r) and (v_b, t_1..t_r) with compatible block parts
and equal keys. Replace each sum by its representative: the u-outer vector is supported in u-outer, the v-outer vector
in v-outer, these are disjoint, and on the block u_b + v_b is binary by compatibility (S4 1.2(a)). The keys are the two
dot products, so the assembled vector is a solution. ∎ (`check_stage5.py`: 0 pseudo-solutions; control straddle: 4/4.)

**Lemma 2.2 (completeness) [proof].** Let c* be a solution, c its block part, owned by layer k. y* := (u-outer part of
c*) . z mod p depends only on c*'s u-outer SUM, which is s_1 + ... + s_r for the record of c*'s outer sums. By S4
Lemma 5.3, after Step 8 some round f with residue r_f has a K compatible with f and blockpart(u) ≡ r_f - y*. The
u-record (u_b, c*'s u-outer sums) and the v-record (v_b, c*'s v-outer sums) exist (each sum of c*'s restriction lies in
its Sigma), have equal keys because c* . z = tau, are compatible (S4 1.2(b)), lie in U_f, V_f (counts of S4 1.5, or of
Lemma 3.3 for the asymmetric design) and both have residue r_f. So the count is >= 1. ∎ The y-coverage of Lemma 5.4
is universal in y, so it never sees the outer lists.

**Lemma 2.3 (decision and search) [proof].** The count on deduped lists is positive iff some solution exists (2.1,
2.2); bisection uses only positivity (S4 2, YL's counting and recovery), and the filter uses the histograms only to
choose a shift (S4 Lemma 5.5 holds for any weights). No step uses raw multiplicities. ∎ (Brute force: deduped and raw
outer lists agree on positivity on every sampled pick.)

**Lemma 2.4 (distinct residues for every N) [proof].** For c in C_k with W_c as in S4 Lemma 5.2, W_c has at least
min(|W_c|, p)/G distinct residues mod p, G := 1 + 2 g'(M + 1)^2, g' := max(2 B ln 2, 2 x_0) (B the bit length of S4
Lemma 5.1). *Proof.* If P0 >= x_0, S4 Lemma 5.1 gives coll_p <= 2B ln 2 N^2/p; otherwise P0 = x_0 > N/(2(M+1)), p <=
2 x_0 and coll_p <= N^2 <= 2 x_0 N^2/p. With w = |W_c| >= N/(M + 1), Cauchy-Schwarz gives >= 1/(1/w + 2 g'(M+1)^2/p)
>= min(w, p)/G. ∎ Hence D of Step 5 makes sum_f |S_{c,f}| >= p ln(4|U_k|) and S4 Lemma 5.4 applies verbatim.
*Gotcha:* S4 Lemma 5.2 as written needs p <= |W_c|, which FAILS when N < 2(M + 1) x_0 (every block nearly constant):
then p = x_0 can exceed |W_c|. The factor p/min(p, w) <= 2 x_0 repairs it at no cost. The brute force hits this regime
on the 'ones' and 'small' instances (p > |W_c| on 6 instances in each of the three regimes: 18 runs, 6 of the 40 in 'center'), and D_need <= D' is asserted there.

**Lemma 2.5 (layer range) [proof].** If C_k is non-empty then C(M, k) >= N/(M + 1), so
h(kappa) >= 1 - d - log2(M + 1)/M - O(log M/M). Conversely nothing bounds d: for every kappa in (0, 1) the proof must
cover layer k = kappa M (the sup in Sec. 4 runs over all of [0, 1]). ∎

## 4. Cost

**Lemma 3.1 (list sizes; the least-deficient choice) [proof].** For each layer, |U'_f| <= |U_f| 2^{-j d M} and
|V'_f| <= |V_f| 2^{-j d M}. *Proof.* d(Qa_i) := M - log2|Sigma(Qa_i)| >= d(P) = dM by the choice of P, and by (SUP)
|Sigma(u-outer)| <= prod_i |Sigma(Qa_i)| |Sigma(Rr_u)| <= 2^{|u-outer| - j dM}; the block part is untouched. ∎
*This is the exact analogue of A22's argument and it transfers without change.* On Record 3's route every quantity
that sees the deficiency is a function of N = |Sigma(block)| alone: the prime and its collision bound (S4 5.1), the
distinct residues (Lemma 2.4), the thresholds of C_k and the estimator's universe C_k x Z_p (S4 1.4, 5.4). The kappa
layers, the cores, the H/Hbar split and the second moment of the filter all live inside the block; the outer bits
enter only through key(u) = u . z. So the A22 cancellation 2^{-dM} (both lists) x 2^{+dM} (filter, p ~ N) holds in
every layer. The place where the port costs something is not here but in the layer range (Sec. 5).

**Lemma 3.2 (the count, P3) [proof].** For a design (alpha = a, s1, s2, w) at layer kappa, with t := (1 + D)/2,
D := (2 kappa - a(s1 + 1 - s2))/(1 - a) - 1 (a = 0: t = kappa), and certified (l_i, r_i) in K(s_i). The non-core densities are
t1 := x/b (the fraction of H - Hc, with b := |H - Hc|, used by the u-side) and t2 := 1 - x'/b (the fraction of the
v-side's non-zero part on Hbar - Hbc), so the count constraint reads t1 - t2 = D; the optimum is t1 = t, t2 = 1 - t:

    u-line = 1/2 + mu[h(kappa) - (1-a) h(t)/2 + (1-a)/2 - 1 + lambda + (a/2)(s1 - h(s2) + r1 + l2)] + (1 - mu) w
    v-line = 1/2 + mu[h(kappa) - (1-a) h(t)/2 + (1-a)/2 - 1 + lambda + (a/2)(s2 - h(s1) + l1 + r2)] - (1 - mu) w
    P3 = max(u-line, v-line) - (j - 1) mu d,    d >= 1 - h(kappa) (Lemma 2.5, the O(log M/M) into eps).

*Proof.* By S4 Lemma 5.5 the kept weight is <= |F_k|(2^{dU}|U'| + 2^{dV}|V'|)/p with |F_k| <= 2^{M(J + lambda)} poly,
p >= N/(4(M+1)) - 1 = 2^{(1 - d)M}/poly, and Lemma 3.1. Per n the u-term is
mu J + log|U| + deg(u) - (1 - d) mu - j d mu with (A38's per-side generalisation of S4 Sec. 2)
J = h(kappa) - (a/2)(h(s1) + h(s2)) - (1 - a)(h(t1) + h(t2))/2, log|U| = (1/2 + w)(1 - mu) + mu/2
+ (mu/2)[a(h(s1) + s1) + (1 - a)(h(t1) + t1)], deg(u) = (a mu/2)(r1 + l2) + ((1 - a) mu/2)(1 - t1), and the v-term with
(s2, t2, l1 + r2, -w). Take t1 = t, t2 = 1 - t (this choice maximises h(t1) + h(t2) under the count constraint
t1 - t2 = D, so it is optimal, but any choice is valid). Then the t1-terms cancel (+ (1-a) mu t/2 - (1-a) mu t/2), and
-(1-a) mu h(t) + (1-a) mu h(t)/2 = -(1-a) mu h(t)/2; the filter and dedupe give -(1 - d) mu - j d mu = -mu - (j-1) d mu.
For s1 = s2 = s, l + r = h(s) - s - 2 xi, the core term is -a xi and w = 0: S4's P3 without "+ mu delta". ∎
The u-line and v-line are evaluated in the certificate in this cancelled form (no interval dependency on t).

**Lemma 3.3 (round families for the general design) [proof].** Stage 4 Lemmas 4.1-4.4 and Cor. 4.5 hold for a design
with |K n Hc| = s1 a, |K n Hbc| = (1 - s2) a, |K n (H - Hc)| = x, |K n (Hbar - Hbc)| = x', with the same lambda bound,
for any rational alpha in [0, 1) with a_b = alpha N_b/2 and s_i a_b integral.
*Proof.* The splitter (4.1, 4.2) does not look at the design. Per piece put m_i := k_i - s1 a_b - (1 - s2) a_b (two
consecutive values, since k_i is floor or ceil of k/q). Choose x_i in {X0, X0 + 1} with sum x, giving X0 + 1 first to
pieces with the larger m_i; then x'_i := m_i - x_i takes two consecutive values as well (if R_x <= R_m pieces get
X0 + 1, x'_i in {m0 - X0, m0 - X0 + 1}; otherwise in {m0 - X0 - 1, m0 - X0}), and sum x'_i = x'. The pattern is a
function of k only. So both compositions are balanced, and Lemma 4.4(c)'s chain (Vandermonde; the balanced composition
is the largest term, by log-concavity) gives the same loss. Lemma 4.3's greedy and Cor. 4.5 are design-blind.
(a_b + 1)(b_b + 1) <= (N_b/4 + 1)^2 for every a_b, so lambda <= 2.3982e-8 at N_b = 8 * 10^9 for every design [iv].
The bound log2(1/P_glob) <= M J + O(log M) needs no t-range now: b|h(x/b) - h(t)| <= b h(1/(2b)) <= log2(2eb), since
|h(u) - h(v)| <= h(|u - v|) (h concave with h(0) = 0). The core-free design (a = 0) has J = 0 up to O(log M). ∎
*Gotcha:* S4's per-piece parity rule x'_i = x_i + eps_i only covers |x' - x| <= 1, so the general asymmetric design
needs the two-valued rule above. At the optimum t1 = t, t2 = 1 - t of Lemma 3.2 one has x/b = x'/b = t, hence
|x' - x| <= 1 and S4's parity rule already suffices there; the two-valued rule is kept for the general (any t1, t2) case.

**Lemma 3.4 (the asymmetric design is exact) [proof].** On H the queries are u's r on Hc (s1 a specified) and the rows
v's l; on Hbar the rows are u's l and the queries v's r on Hbc (s2 a specified). With exact integer circuits C(s1) on
Hc and C(s2) on Hbc (S4 Lemma 3.4 at each rational s_i, Prop. 3.7's argument) and (I, P_1) on the non-cores, the
tensor product is exact and the degrees are those of Lemma 3.2. ∎ This closes A38's blocks 2 and 4 for the
deterministic algorithm (A3's balanced half-splits are randomized-only), and block 5 is replaced by Lemma 3.3.

**Lemma 3.5 (the other terms) [proof].**
- **P6** = mu(2 - d + J + lambda) <= mu(1 + h(kappa) + J + lambda): S4 Lemma 5.4's cost |C_k| p |F_k| with p <= 2^{(1-d)M}
  and Lemma 2.5.
- **Kenum** = mu(1 + h(kappa) + lambda) <= mu(2 + lambda): S4 Sec. 5.2 step 6, unchanged.
- **P4** = mu(J + lambda) + mu(log2 3 + 1)/4 + max(mu, (1 - mu)(1/2 + |w|) - mu): the u-list's MITM halves are
  (half the block part) x Sigma(Qa_1) and (other half) x Sigma(rest of u-outer), each <= 3^{M/4} 2^{M/4} times
  2^{mu n} or 2^{(1/2 + |w|)(1 - mu) n - mu n}; Sigma(rest) is built by enumeration in the same time; output is the
  kept list, paid by P3. (A39 used the randomized balanced-half form mu J + max(lU, lV)/2; P4 never binds.)
- **Fit.** Each outer side holds j whole blocks: (1 - mu)(1/2 - |w|) >= j mu, checked exactly per design.
- **Tails** kappa in [0, 2/5] u [3/5, 1]: core-free design, J = 0, P3 = 1/2 - mu(1 - h(kappa))(1/2 + j - 1), increasing in
  h, so bounded at kappa = 2/5. ∎

**Theorem 5 / 5A / 5F / 5b, proof.** Correctness: Lemmas 2.1-2.4. Time: Lemmas 3.2-3.5 over the M + 1 layers, the
design table of Step 4 being the certificate's per-piece choice (6000 pieces of [2/5, 3/5] plus the tails), with eps,
O(N_b) and poly(n, L) absorbed. `cert_stage5.py` evaluates every term in intervals per piece (rigour does not depend
on the float choice of the design) and passes each claim. ∎

## 5. Where the port could fail, and where it does

### 5.1 The least-deficient argument: holds [proof]
Lemma 3.1 and the remark after it. Superadditivity and d(Qa_i) >= d(P) are all A22 needed, and Record 3's filter
loss is a function of N alone. Brute force: |Sigma(Qa)|, |Sigma(Qc)| <= N on every instance; control mostdef (P = the
most deficient block) violates it on 18/36 instances.

### 5.2 The filter's second moment at p ~ N: holds, with one repair [proof]
Lemma 2.4. Stage 4's Lemma 5.2 silently assumes p <= |W_c|, true for p ~ T but false for p ~ N once N is below
2(M + 1) x_0. Repaired by the min(p, |W_c|) form.

### 5.3 The layer range: this is where A39's ceiling fails [proof for the numbers; [arg] for the closed form]
Stage 4's delta did two jobs: it paid the few-sums branch AND cut the layer range to h(kappa) >= 1 - delta, i.e.
|kappa - 1/2| <~ 0.03. Without the dichotomy (Lemma 2.5) the range is all of (0, 1): an instance of deficiency d could
own layers down to h(kappa) = 1 - d (a case the proof cannot exclude, so the rows are conservative upper bounds), and with j = 1 the d-saving is spent exactly on the filter, so a far layer gets
nothing back. With symmetric cores, P3(kappa) - 1/2 = mu[h(kappa) - 1 - a xi + (1 - a)(1 - h(t))/2]. Near the centre,
with e := kappa - 1/2 and c := 2/ln 2, this is mu[c e^2 (2a - 1)/(2(1 - a)) - a xi] to second order, so

    sup_e min_a [c e^2 (2a - 1)/(2(1 - a)) - a xi] = -xi/2,   attained at e = sqrt(xi/(2c)) ~ 0.028, a = 1/2

[arg: second-order algebra; minimise over b = 1 - a, then maximise over e]. So on Stage 4's design the saving is
mu xi/2, whatever alpha is allowed: R1's certified 4.9453e-4 against mu xi/2 = 4.967e-4, binding at kappa = 0.4709 with
alpha = 1/2 [iv]. A39's "ceiling mu alpha xi" holds only with A38's asymmetric cores (R2), which make the off-centre
layers as cheap as the centre. Controls: K6 (R1 at the ceiling 1/2 - mu alpha xi is rejected) and K6b (one fixed
alpha = 19/20 plus core-free elsewhere: E >= 1/2).

### 5.4 A39's own design set leaves a gap [float + iv]
A39 offers each layer either the global alpha with a menu pair or the core-free design. Just below the kappa where the
most asymmetric pair (2/25, 29/200) stops being feasible, only the core-free design is left, worth
1/2 - mu(1 - h(kappa))/2. A39's script sampled the far range at 10 points (0.02..0.45) and missed (0.402, 0.45):
its own float model (not part of this package; control K5b below reproduces the gap rigorously) gives 0.4992334 at kappa = 0.4485, (alpha, mu) = (0.90, 0.200),
above its printed 0.49919788 [float]. Control K5b certifies the gap's side: that design set's rigorous bound is
0.4992433. The repair is free: allow intermediate alphas per layer (Step 4). R2 then certifies 8.4586e-4 at
(0.97, 0.201), above A39's 8.02e-4, binding near the centre (kappa ~ 0.498, menu granularity) with P6 0.499007 close.

### 5.5 Two blocks per side [proof; ours]
With j = 2 the d-saving exceeds the filter loss by d mu, and d >= 1 - h(kappa) off-centre. The curvature condition
becomes a <= 3/4, and the same second-order computation gives 3 mu xi/4. R1b certifies 6.7061e-4 at mu = 0.1999 (the
fit (1 - mu)/2 >= 2 mu caps mu at 1/5). It does not help R2/R3: their binding layers are central (d ~ 0), and the fit
with |w| ~ 0.015 forces mu < 0.196 < 0.201.

### 5.6 What else was checked
- **Pseudo-solutions:** none by Lemma 2.1; controls nocompat and straddle produce them.
- **Representatives:** least masks from the sorted merges; recovery assembles and verifies.
- **The unequal outer split per layer (A38's w):** Lemma 2.2's y-coverage is universal in y, so the u-outer set may
  change with the layer. Exercised in the brute force (regime asym moves the rest coordinate to v).
- **P6 is the D1 wall** (A41, consistent): R2's P6 = 0.499007 at mu = 0.201; mu + 1% is rejected (K2).

## 6. Checks

- `cert_stage5.py` [iv], about 3.5 min, < 100 MB: re-proves the seven menu circuits with Stage 4's prover from A38's
  contact data (each with must-fail controls: the contacts moved 1e-4 outward are refuted by explicit colours), the
  Stage 4 single circuit and the Stage 4+ family (control C3); lambda; the rows R1, R1b, R2, R3; controls K1-K8
  (K1 claim - 1e-9 for every row; K2 mu + 1%; K3 no cores, E >= 1/2; K4 one-sided dedupe, E = 0.70 > 1/2; K5 A39's
  design set at R2's point; K5b A39's printed point; K6, K6b the ceiling for symmetric cores; K7 R3 without the family;
  K8 the R1b fit). Output: STAGE 5 CERTIFICATE PASS.
- `check_stage5.py` [exp], about 1.5 min, < 200 MB: n = 25, three blocks of 8 and one rest coordinate; the full DET5
  with sorted-merge Sigma tables, the prime at p ~ N (down to p = 2), every layer 0..8 served, greedy families (core
  design s = 1/3, asymmetric cores s1 a = 1, s2 a = 2, core-free), Stage 4's fixed-point estimator (imported), the shift,
  sorted-residue MITM, exact count, bisection and representatives. Regimes center, far (layers 0, 8, 1, 7, ... first,
  so core-free far layers own c's) and asym; families large, signed, small, planted, uneven, ones, plus targeted
  straddle instances. Asserted throughout: brute-force agreement, soundness, layer-level completeness on sampled
  solutions, the list bound, positivity raw = dedupe, Lemma 2.4 and D_need <= D', Phi_0 <= 1/4, full coverage, best
  shift <= mean, MITM = direct filter, merge-join count = array count. Controls nocompat, mostdef, blockdedupe,
  straddle, lowmult are each detected. Output: STAGE 5 CHECK PASS.
- **Lean 4 (kernel-checked).** `lean/SubsetsumLean/Stage5*.lean` check every inequality of `cert_stage5.py`: the
  rows R1, R1b, R2, R3 for every kappa in [0, 1], the menu circuits' contacts, lines and xi, and lambda; the controls
  K1-K8 and C1, C2 are proved false (C3 is Stage 4's). Standard axioms only (`lean/axioms_stage5.out`, 83 theorems);
  `lean/check_stage5.sh` rebuilds and re-audits it in one command. Scope: `lean/LEAN_SCOPE.md`, Stage 5.
- **Limits.** The toy's PM is the exact trivial counter (Stage 4 part F tests the circuit separately); M = 8 means
  q = 1 piece; asymptotic rates are not tested, only the logic.

## 7. Not proved here
- [cite] everything Stage 4 cites ((AL-B2), S2 Lemma 9.1, (K1)-(K3), YL's counting and recovery), and Stage 4 itself.
- [arg] the second-order closed forms mu xi/2 and 3 mu xi/4 (Secs. 5.3, 5.5); the certified rows do not use them.
- [arg] Sec. 7 of Stage 4 (a non-explicit program counts as an algorithm), inherited.
- Not claimed: optimality of the menus or parameters; the closed form mu alpha xi for symmetric cores; any row with
  another estimator; the randomized rows.
