# Stage 4: a deterministic, non-explicit Subset Sum algorithm in time poly(n, L) * 2^{0.4998322132 n}, on Ye-Li's Record 3 reduction

Stage 4 replaces Stage 3's route (`stage3.md`, E3 <= 0.499990922) by the reduction of Ye-Li's unpublished
"Record 3", ported to a deterministic algorithm. Its earlier, randomized write-up (our working notes, not part of this
package) was reviewed by two clean internal referees (R1: randomized CONFIRMED WITH FIXES, deterministic UNDECIDED
pending A4; R2: both CONFIRMED WITH FIXES, conditional on A4). This file closes A1-A4 as [proof], applies every
referee fix, and puts the round-family loss lambda into the exponent. This file itself had two internal referee
passes (G1, G2); their fixes are applied (Sec. 0.1). Scripts: `certificates/stage4/`. Lean: `lean/SubsetsumLean/Stage4*.lean`.

## CREDIT

Four separate things, kept apart because only the first two can be checked by a reader of the paper.

- **Public: the number.** The only Record 3 result in print is the numerical candidate 0.499664500303..., quoted in
  the AI disclosure of Ye and Li (Lixi Ye, Baitian Li), arXiv 2610.10446 v1, "Subset Sum via Partial Match"
  (section "AI disclosure and timestamps"). No reduction, circuit or proof of it is published.
- **What we read in that disclosure.** Inside Ye-Li's project, on 28 September 2026, the AI model "GPT-6 astra
  ultra" found "a reduction showing that ordinary subset sum could also break meet-in-the-middle using the same P_1
  circuit improvement"; "Record 3 contains a detailed reduction at 06:22, and the numerical candidate
  0.499664500303... at 06:42, where the complete formal proof is explicitly still pending". The same passage says the
  project had moved from s = 1/2 to s = 1/8 and that "the broader criterion allows any fixed s in (0, 1/2]". So the
  reduction is credited, by its authors, to an AI model working in Ye-Li's project, and it is unproved there.
- **Reconstructed by us, from the linked Record 3 transcript.** The specifics were read in the Record 3 transcript that the paper's "AI disclosure and timestamps" section links (https://chatgpt.com/share/6ac5a437-5d0c-83e8-afea-fcc450b322b0), so readers can check the attribution. We re-derived every one of them and certified the numbers independently; the ideas
  remain Record 3's (Ye-Li's project), not ours:
  - the block representation (c_i = l_i + r_i with l in {0,1}, r in {-1,0,1}) on a mu n block, few/many sums on the
    block, the kappa-layer pigeonhole and enumeration;
  - balanced splits H / Hbar with cores at a chosen density s, the round count J, filtering without isolation or
    fingerprints, and the tensor circuit C_core (x) (I, P_1) inside the symmetric (R^T (x) L, L^T (x) R) circuit;
  - the s-cancellation identity (re-derived in Sec. 2), the cost functions and the saving coefficients
    mu alpha/3, mu alpha(1-alpha)/(2-alpha), (3 - 2 sqrt 2)/2;
  - the details of the one-pass covering circuit family (cover size k + rho(m - k), degree formulas, the trivial
    pairs (h(s), 0), (0, 1 - s)); Lemma 3.5 proves them here;
  - xi(1/8) and xi(0.11): certified here by branch and bound (Sec. 3.6, xi >= 0.0043428267 and 0.0044849038), with
    Record 3's floats 0.004342871357 and 0.004484944104 inside our [F1] brackets.
- **Ours (this repository).**
  - The proofs of every step the earlier write-up left as [arg]: the density-s Lemmas 3.1 and 3.4 with unbalanced
    queries (A1), the left-degree concentration (A2), the balanced half-splits (A3), and the fixed round family with
    its multiplicity and loss (A4). The published Ye-Li paper (YL) supplies the half-stars framework these adapt to
    density s: Def. 2.1, Lemma 3.1 (block grouping), Cor. 3.2, Cor. 3.3, Lemma 3.4.
  - The repairs: the filter cap (randomized), Phi's universe restricted to the good c, the prime p ~ T with the
    collision count, the parity bit sigma, the fixed-point estimator, the enumeration of compatible K, the
    poly(n, L) factors.
  - The whole deterministic port and its exponents, the certificates `cert_stage4.py` and `cert_stage4plus.py`, the
    brute force `check_stage4.py`.
  - The family certificate of Stage 4+ (Sec. 8), and the idea of a family of circuits on this route.
- **So this package presents the reduction and the circuit family as Record 3's (Ye-Li's project, AI-found per
  their disclosure, proof pending there), says that only the number is public, and claims as ours only the proofs of
  the [arg] steps, the repairs, the certificates and the deterministic port.**

## 0. Statements

**Labels.** [proof]: proved here, completely, given the cited items. [arg]: argued, less than a proof (all listed
in Sec. 10). [cite]: taken from the named source and place. [iv]: checked by outward-rounded interval arithmetic
in `cert_stage4.py` (IEEE-754 with one-ulp outward rounding; libm log2 and log padded by four ulps). Model as YL
Sec. 2: integers z_1..z_n (negatives allowed), a target tau, total input length L, bit operations, L = 2^{o(n)}.
h is binary entropy in bits; H(n, k) := n h(k/n) (0 when n = 0).

**Theorem 4 (headline).** For every eps > 0 there is a deterministic, non-explicit algorithm DET4 that decides
Subset Sum, and finds a solution, in poly(n, L) * 2^{(E4 + eps) n} bit operations on every input, with

    E4 <= 0.4998322132     (gain 1/2 - E4 >= 1.677868e-4, 18.5 times Stage 3's 9.0779e-6),

at s = 11/100. The round-family loss is included: N_b = 8 * 10^9, lambda <= 2.3977e-8, mu lambda <= 5.26e-9.
At s = 1/8 the same algorithm gives E <= 0.4998357367. [proof, given the cited items of Sec. 0.2; numbers [iv]]

**Theorem 4R (randomized, for reference).** Record 3's randomized algorithm runs in 2^{(0.4996416844 + eps) n}
at s = 11/100 (0.4996427665 at s = 1/8). [proof, given Sec. 0.2 and the balanced half-splits of Sec. 6 (A3)]

**Theorem 4+ (separate, Sec. 8).** With a family of two Record 3 circuits (rho = 49/20, 11/4), xi(11/100) >=
0.0070361406, and DET4 runs in 2^{(0.4997369618 + eps) n} (gain 2.6304e-4). [proof, same footing as Theorem 4]

### 0.1 Where each referee fix is

| fix (referee) | where |
|---|---|
| A4: the fixed round family, its cost, existence and loss lambda with explicit N_b (R1, R2) | Sec. 4 |
| multiplicity: each round repeated D = poly times, each copy with its own residue, so Phi_0 <= 1/4 (R2 defect 1) | Cor. 4.5, Lemma 5.4 |
| restrict Phi's universe to the good c for each layer (R1 D1, R2 defect 3) | Sec. 1.4 (C_k), Lemma 5.4 |
| prime scan costs N p, not N poly (R2 defect 4) | Lemma 5.1, term Pscan |
| the S_{c,f} are built by enumerating the compatible K directly (R2 defect 5) | Sec. 5.2 step 6, term Kenum |
| "poly" in the collision bound is bit-length, i.e. poly(n, L) = 2^{o(n)} (R1) | Lemmas 5.1, 5.2 |
| A1: density-s Lemmas 3.1 and 3.4, unbalanced queries k +- eps' N with degree bounds (R1 defect 1, R2 defect 7) | Lemmas 3.2-3.5' |
| A2: left-degree concentration of the random design | Lemma 3.5(c) |
| A3: balanced half-splits (randomized only) | Sec. 6 |
| brute force of the deterministic claims: s != 1/2, x and x' fixed by the layer, a real fixed family with multiplicity, p >> T (R2 defect 6) | Sec. 9, `check_stage4.py` part C |
| the restricted universe C_k x Z_p exercised with C_k a proper subset of the cube (Stage 4 referee G2, defect 2) | Sec. 9, part C regime 'tight' |
| Lemma 5.2's step p <= |W_c|: stated, and the min(p, |W_c|) form for general p (Stage 5 verifier) | Lemma 5.2 |
| one-sided rounding in the estimator; the Kenum chain; the cost of the backward pass; the hidden 2^{2^33} constant; [K]'s per-s lmax (Stage 4 referees G1, G2) | Lemma 5.4, Sec. 5.2 step 6, Secs. 4.3, 7, Cor. 3.8 |
| the credit section separates the public number, the disclosure, our reconstruction and our own work (G2 defect 3) | CREDIT |
| the headline randomized E needs A3 (R1, R2 defect 8) | Theorem 4R, Sec. 6 |

### 0.2 What is cited

- **YL** = Ye and Li, arXiv 2610.10446 v1 (TeX e-print main.tex): the "Counting and recovery" bisection
  (Sec. 2.2), and the numerical rebalancing statement before Lemma 3.4, quoted below as **(AL-B2)** [cite]. YL
  extract it from AL25 App. B, Lemmas B.2-B.4 and Thm B.2 (Alman-Li, arXiv 2509.14489, FOCS 2025):
  > For a fixed finite family of nonempty lists (a_{i,j}, b_{i,j})_j with entries at least one, put
  > Upsilon_i(tau) := sum_j a_{i,j}^tau b_{i,j}^{1-tau}, Upsilon(tau) := min_i Upsilon_i(tau), F_0(lambda) := 1 +
  > lambda, F_d(lambda) := min_i sum_j a_{i,j} F_{d-1}(lambda b_{i,j}/a_{i,j}). Suppose a list attaining the minimum at
  > tau = 0 has a_{i,j} >= b_{i,j} termwise, and one attaining it at tau = 1 has the reverse inequalities. Then
  > F_d(lambda) <= 2^{o(d)} max_{0<=tau<=1} Upsilon(tau)^d lambda^{1-tau}, uniformly over lambda > 0, with the error
  > depending only on the fixed family.
- **S2** = our Stage 2 (`stage2.md`, refereed): Lemma 9.1 (hole fixing by inclusion-exclusion, for
  any finite group acting transitively on both sides) [proof there], and Sec. 8.3 (what a non-explicit
  deterministic algorithm is) [arg there].
- **AKKN16** Lemma 3.2 (few distinct sums), as used in YL Thm 2.2 [cite]; **HS74** meet in the middle [cite].
- **(K1)** for x >= x_0, [x, 2x] contains at least x/(2 ln x) primes (prime number theorem) [cite]; **(K2)** fast
  integer multiplication, hence exact cyclic convolution of length p with O(log p + n)-bit entries in
  p polylog(p) poly(n) bit operations [cite]; **(K3)** Chernoff: a sum X of independent 0/1 variables with mean mu
  has Pr[X >= R] <= 2^{-R} for every R >= 6 mu (Mitzenmacher-Upfal, Thm 4.4(3)) [cite].
- Nothing from Record 3 is cited as a fact: every step of the reduction is re-derived (Secs. 1, 2).

## 1. The reduction (Ye-Li, Record 3), re-derived

### 1.1 Setting [proof]
- **Coordinates.** Fix rationals s in (0, 1/2), alpha, mu in (0, 1/2], delta in (0, 1), and the piece length N_b of
  Sec. 4.3, chosen so that a_b := alpha N_b/2 and s a_b are integers (Theorem 4: N_b = 8 * 10^9; then
  a_b = 2228738800, s a_b = 245161268).
  - The **block** is M := N_b floor(mu n/N_b) coordinates; q := M/N_b pieces. M differs from mu n by less than
    N_b, a constant, so every cost exponent below, which is affine in M for fixed per-coordinate rates, moves by
    O(N_b) bits: a constant factor (Sec. 5.3).
  - The **outer part** is the other n - M coordinates, split once and for all into a u-outer and a v-outer half
    (sizes floor and ceil).
  - Core length a := q a_b = alpha M/2, non-core length b := M/2 - a = (1 - alpha) M/2.
- **Thresholds.** T := ceil(2^{(1 - delta) M}).

### 1.2 Block representations [proof]
- On the block, c_i = l_i + r_i with l_i in {0,1}, r_i in {-1,0,1}, using 0 = 0 + 0 = 1 + (-1) and
  1 = 1 + 0 = 0 + 1.
- A **round** is f = (H, Hc, Hbc) with H ⊆ block, |H| = M/2, Hc ⊆ H and Hbc ⊆ Hbar := block \ H, |Hc| = |Hbc| = a.
- **u** holds r on H, l on Hbar and the u-outer bits; **v** holds l on H, r on Hbar and the v-outer bits.
  key(u) := u.z, key'(v) := tau - v.z. A pair is **compatible** if l_i + r_i is in {0,1} at every block coordinate.
- **(a) Soundness.** If (u, v) is compatible and key(u) = key'(v), then u + v is in {0,1}^n (the outer halves are
  disjoint and binary) and (u + v).z = tau. So every counted pair is a solution.
- **(b) Representations of a solution c.** Put e_i := 2c_i - 1. For K ⊆ block, put R := (H ∩ K) ∪ (Hbar \ K),
  r_i := e_i on R and 0 elsewhere, l := c - r (on the block). Then l is binary: on R, c_i - e_i = 1 - c_i; off R,
  l = c. So (u, v) built from (c, K) is compatible, and key(u) = key'(v) because u + v = c.
- **(c) Key identity.** blockpart(u) := sum_H r_i z_i + sum_Hbar l_i z_i = const(c, f) + sum_{i in K} e_i z_i with
  const(c, f) := sum_{Hbar} (c_i - e_i) z_i. *Check:* sum_{H∩K} e z + sum_{Hbar} c z - sum_{Hbar\K} e z, and
  sum_{Hbar\K} e z = sum_{Hbar} e z - sum_{Hbar∩K} e z.

### 1.3 Few/many sums [proof; cite AKKN16 Lemma 3.2, HS74]
- **Sigma**, the sorted distinct subset sums of the block, is built incrementally (Sigma_{j+1} = Sigma_j ∪
  (Sigma_j + z_j) by sorted merge). |Sigma_j| never decreases, so the build stops once T is exceeded: cost
  T poly, term **P1 = mu(1 - delta)**.
- **Few sums (N := |Sigma| <= T).** AKKN: the N representatives times ell := floor((n - M - log2 N)/2) outer
  coordinates against the other outer coordinates, by sorted merge. Lists N 2^ell and 2^{n - M - ell}, so the cost
  is 2^{n/2 - delta M/2} poly: term **P2 = 1/2 - mu delta/2**. (ell >= 0 since N <= 2^M <= 2^{n - M}, mu <= 1/2.)
- **Many sums (N > T):** the rest of this file.

### 1.4 Layers and the good sets C_k [proof]
- **Keys of one layer.** For a block assignment c in {0,1}^M, sum_{K} e_i z_i = S(K Δ Cbar) - S(Cbar), where S is
  the subset-sum map and Cbar = block \ supp(c): indeed sum_{K∩C} z - sum_{K∩Cbar} z, and S(K Δ Cbar) =
  S(K ∩ C) + S(Cbar) - S(K ∩ Cbar). As K -> K Δ Cbar is a bijection, the keys of all representations take exactly
  N distinct values.
- **Pigeonhole.** For each c, some layer |K| = k carries at least N/(M + 1) distinct keys.
- **C_k** := {c in {0,1}^M : layer k of c has at least N/(M + 1) distinct values sum_K e_i z_i}. Every c lies in
  some C_k. Computing all C_k: 2^M choices of c times 2^M choices of K, sorted: term **P5 = 2 mu**.
  *Gotcha (referees R1 D1, R2 defect 3):* the covering universe of layer k is C_k x Z_p, NOT {0,1}^M x Z_p. For c
  outside C_k nothing guarantees many residues, and Phi_0 < 1 fails (Lemma 5.4 uses c in C_k).
- **Range.** If C_k is nonempty, C(M, k) >= N/(M + 1) > T/(M + 1), so h(k/M) >= 1 - delta - log2(M + 1)/M. The
  certificate fixes kappa_lo with h(kappa_lo) < 1 - delta (checked [iv]); for M >= M_0 every such k has
  k/M in (kappa_lo, 1 - kappa_lo). The exponent takes the sup over this range.

### 1.5 Rounds compatible with a layer, and J [proof]
- **The parity bit.** For a layer k, put sigma(k) := (k - a) mod 2, x := (k - a - sigma)/2, x' := x + sigma.
- K (|K| = k) is **compatible** with f if |K ∩ Hc| = s a, |K ∩ Hbc| = (1 - s) a, |K ∩ (H \ Hc)| = x and
  |K ∩ (Hbar \ Hbc)| = x'. Then u's right numbers have exactly s a non-zeros on Hc (namely Hc ∩ K) and x on H \ Hc;
  v's have exactly s a on Hbc (namely Hbc \ K) and b - x' on Hbar \ Hbc.
  *Gotcha:* with x' = x forced, a layer with k - a odd has NO compatible round and its c would never be found;
  the earlier write-up suppressed this floor. Control `noparity` in `check_stage4.py` detects it.
- **The compatible fraction.** For fixed K, the fraction of rounds compatible with K is
  P_glob(k) = C(a, s a) C(a, (1-s) a) C(b, x) C(b, x') / C(M, k), the same for every K (the symmetric group acts
  transitively on k-sets and on rounds, preserving compatibility; double counting).
- **J.** Put kappa := k/M, t := (kappa - alpha/2)/(1 - alpha) = (k - a)/(2b) and
  J(kappa) := h(kappa) - alpha h(s) - (1 - alpha) h(t).
  If t +- 1/(2b) lies in [1/3, 2/3], then

      log2(1/P_glob(k)) <= M J(kappa) + 2 log2((a + 1)(b + 1)) + 1.

  *Proof.* C(M, k) <= 2^{M h(kappa)}; C(a, sa) >= 2^{a h(s)}/(a + 1), likewise (1 - s); C(b, x) >= 2^{b h(x/b)}/(b+1).
  x/b and x'/b are within 1/(2b) of t, and |h'| <= 1 on [1/3, 2/3], so b h(x/b), b h(x'/b) >= b h(t) - 1/2. ∎
  The certificate checks the t-range [iv] (it lies in [0.448, 0.552] at Theorem 4's parameters).

## 2. Lists, the tensor circuit and the keyed count [proof]

- **Lists of a round f for layer k.** U_f: all u with r on Hc having exactly s a non-zeros (any signs), r on H \ Hc
  exactly x non-zeros, l on Hbar arbitrary, u-outer bits arbitrary. V_f: l on H arbitrary, r on Hbc exactly s a
  non-zeros, r on Hbar \ Hbc exactly b - x' non-zeros, v-outer bits arbitrary. Per n, up to O(log n / n):

      log|U| = 1/2 + (mu/2)[alpha(h(s) + s) + (1 - alpha)(h(t) + t)],   log|V|: the last t replaced by 1 - t.

- **Compatibility as partial match.** Relabel r: 1 -> '0', -1 -> '1', 0 -> '*'. Then l_i + r_i in {0,1} iff the row
  bit l_i matches the query symbol (YL Sec. 1.2's table). On H, v's l is the row and u's r the query; on Hbar, u's l
  is the row and v's r the query.
- **The circuit.** Let C_core = (L_c, R_c) be an exact integer circuit for P_{a,s} (Sec. 3) with degrees
  2^{(l + eps) a}, 2^{(r + eps) a}, and (I, P_1^{(x) b}) the trivial circuit on the non-core (gates = rows; right
  degree 2^{#stars}). With C_H := C_core (x) (I, P_1^{(x) b}) on H and C_Hbar likewise on Hbar,
  compat(u, v) = compat_H(v_H, u_H) compat_Hbar(u_Hbar, v_Hbar) = sum_{e, e'} (R_H[e, u_H] L_Hbar[u_Hbar, e'])
  (L_H[v_H, e] R_Hbar[e', v_Hbar]). So u's vector is R_H^T (x) L_Hbar and v's is L_H^T (x) R_Hbar, and

      deg(u) <= 2^{(l + r + 2 eps) a + (b - x)},   deg(v) <= 2^{(l + r + 2 eps) a + x'}.

  Per n: (alpha mu/2)(l + r) + ((1 - alpha) mu/2)(1 - t) for u, and t for v, up to O(eps + 1/n).
- **Count and recovery.** sum over (key, gate) of (sum_u coefficient)(sum_v coefficient) is exactly the number of
  compatible equal-key pairs among the kept records (sort by (key, gate); YL Cor. 3.3's argument). A positive count
  is bisected down to one pair [cite YL "Counting and recovery"]; Sec. 1.2(a) makes it a solution.
- **The s-cancellation (Record 3's identity, re-derived).** With l + r = h(s) - s - 2 xi, the circuit term
  mu J + log|U| + deg(u) - (1 - delta) mu simplifies to

      P3 = 1/2 + mu [h(kappa) - alpha xi + (1 - alpha)(1 - h(t))/2 - 1 + delta],

  the s-terms cancelling: -alpha h(s) + (alpha/2)(h(s) + s) + (alpha/2)(h(s) - s - 2 xi) = -alpha xi. The u and v
  terms are equal (t + (1 - t) = 1).

## 3. Partial match at density s (A1, A2)

### 3.1 Definitions and the trivial pairs
- P_{N,s}: rows {0,1}^N, queries y in {0,1,*}^N with exactly sN specified positions (sN an integer), entry 1 iff x
  matches y on the specified positions. K(s): the pairs (l, r) in R_{>=0}^2 such that for every eps > 0 and all
  sufficiently large N with sN integral, an exact integer circuit for P_{N,s} has degrees at most 2^{(l + eps) N}
  and 2^{(r + eps) N}. K(s) is closed upward.
- Colours, colour classes, colour subcircuits C_zeta and the colored volume
  Upsilon_C(tau) = sum_zeta deg_L(C_zeta)^tau deg_R(C_zeta)^{1 - tau} are as in YL Sec. 3.1 (empty colours and
  gates with no edges removed, so every active degree is at least 1).

**Lemma 3.1 (trivial pairs) [proof].** For M_0 := P_{N0,s}, the single-colour circuits (M_0, I) (gates = queries)
and (I, M_0) (gates = rows) have degree pairs (C(N0, sN0), 1) and (1, 2^{(1-s) N0}). Their volumes are
<= 2^{N0 tau h(s)} and 2^{N0 (1 - tau)(1 - s)}; (M_0, I) attains Upsilon(0) = 1 with a >= b, and (I, M_0) attains
Upsilon(1) = 1 with b >= a.
*Proof.* A row matches C(N0, sN0) queries (choose the specified set; the values are forced); a query matches
2^{(1 - s) N0} rows. C(N0, sN0) <= 2^{N0 h(s)}. ∎

### 3.2 Block grouping at density s

**Lemma 3.2 (YL Lemma 3.1 at density s) [proof].** Let s = p_s/q_s, let k be a multiple of q_s, and put
c := q_s ceil(k/(s q_s)) (so c >= k/s and s c is an integer). For d >= 1, a circuit C for (P_{k^2 + c, s})^{(x) d}
gives an exact integer circuit C' for P_{k^2 d, s} with deg_L(C') <= (k + 1)^{kd} deg_L(C) and
deg_R(C') <= deg_R(C).
*Proof.*
- Split the k^2 d coordinates into kd blocks of length k. A query's **description** is its vector of
  specified-position counts w_j in [0, k]; there are at most (k + 1)^{kd} descriptions.
- For a fixed description, sort the blocks by w (ties by position) and deal them cyclically into d groups of k
  blocks: group i gets the sorted positions i, d + i, ..., (k - 1)d + i. With w_(1) <= ... <= w_(kd), the group
  totals W_i := sum_j w_(jd+i) satisfy W_1 <= ... <= W_d and W_d - W_1 <= sum_j (w_(jd+d) - w_(jd+1)) <=
  w_(kd) - w_(1) <= k (telescoping). Their mean is s k^2, so every W_i is in [s k^2 - k, s k^2 + k].
- Append c positions to each group: the row gets c zeros; the query gets z_i := s(k^2 + c) - W_i specified zeros and
  c - z_i stars. 0 <= z_i <= c holds because z_i >= s c - k >= 0 (c >= k/s) and z_i <= s c + k <= c
  (c >= k/(1 - s), implied by s <= 1/2). The new positions always match. Each padded group is a query of
  P_{k^2 + c, s} that matches the padded row iff the original group matches.
  *Gotcha:* YL's padding 2k is k/s at s = 1/2. With c = k at s = 1/3 the padding is infeasible
  (`check_stage4.py` part D, control: 756 descriptions).
- Restrict C to these embeddings and give each description its own copy of the gates: a row is incident to every
  description's copy, a query only to its own. Exactness is preserved, and the degree bounds follow. ∎
`check_stage4.py` part D checks the padding arithmetic exhaustively (s = 1/3, 1/4 at small k, d) and by sampling
plus extremes (s = 1/3, 1/8, 2/5).

### 3.3 Hole fixing at density s

**Lemma 3.3 [proof, given S2 Lemma 9.1].** Fix eps' > 0. Let W = X0 x Y0 be the window of P_{N,s}:
X0 = {x : |#1(x) - N/2| <= eps' N}, Y0 = {y : |#1(y) - sN/2| <= eps' N} (so also |#0(y) - sN/2| <= eps' N). If the
submatrix on W has a colored exact integer circuit C, then P_{N,s} has one with Upsilon(tau) <= 2^{J0} Upsilon_C(tau)
for every tau, where J0 = O(1/eps'^2) does not depend on N.
*Proof.* The group G generated by coordinate permutations and simultaneous flips of a row bit and the same specified
query bit preserves matching. It is transitive on X = {0,1}^N (flips) and on the queries with exactly sN specified
positions (a permutation moves the specified set anywhere; flips set the values). By Hoeffding, |X \ X0| <=
2 e^{-2 eps'^2 N} |X|, and since #1(y) of a uniform query is Binomial(sN, 1/2), |Y \ Y0| <= 2 e^{-2 eps'^2 N/s}|Y|.
So eta := 2 e^{-2 eps'^2 N} meets 2 eta < 1 for large N, and S2 Lemma 9.1 applies with
J0 > ln(|X||Y|)/ln(1/(2 eta)); ln(|X||Y|) <= N ln 6, so J0 = O(1/eps'^2). Its copies are exact, each colour's
degrees in a copy are at most those of C, and the 2^{J0} - 1 copies are tagged by colour. ∎
`check_stage4.py` part E builds this at gate level on P_{6,1/3} with the full group and random g_i (J0 = 11, 2047
signed copies): L R equals P_{6,1/3} exactly; without the signs it does not.

### 3.4 Colored transfer at density s

**Lemma 3.4 (YL Lemma 3.4 at density s, for a finite family) [proof, given (AL-B2) and Lemmas 3.1-3.3].** Let
V_1, ..., V_P : [0,1] -> R be continuous. Suppose that for every eps_1 > 0 there is eps' > 0 such that for every
member j and all sufficiently large N in a fixed residue class, the window W of P_{N,s} has a colored exact integer
circuit with Upsilon(tau) <= 2^{N (V_j(tau) + eps_1)} for all tau. If l, r >= 0 and

    min{ V_1(tau), ..., V_P(tau), tau h(s), (1 - tau)(1 - s) } <= tau l + (1 - tau) r     (0 <= tau <= 1),

then (l, r) is in K(s).
*Proof.*
- Fix eps_1 > 0, take a large k (a multiple of q_s and of the residue modulus) and N0 := k^2 + c (Lemma 3.2's c),
  M_0 := P_{N0, s}. By Lemma 3.3, each member j gives a colored exact circuit for M_0 with
  Upsilon_j(tau) <= 2^{J0} 2^{N0 (V_j(tau) + eps_1)}. Adjoin (M_0, I) and (I, M_0) (Lemma 3.1).
- These P + 2 circuits give a fixed finite family of lists (their colour-degree pairs, entries >= 1), with the
  endpoint conditions of (AL-B2) met by the trivial circuits (Lemma 3.1). For N0 large (2^{J0} <= 2^{eps_1 N0}):

      Upsilon(tau) = min_i Upsilon_i(tau) <= 2^{N0 (tau l + (1 - tau) r + 2 eps_1)}.

- **Recursion.** For every d and lambda > 0 there is an exact circuit for M_0^{(x) d} with deg_L + lambda deg_R <=
  F_d(lambda): for d = 0 the one-gate circuit for (1); at the root choose circuit i, write M_0 = sum_zeta M_zeta
  over its colours, and tensor each colour subcircuit with the circuit E_zeta given by induction at weight
  lambda b_{i,zeta}/a_{i,zeta}; the results sum to M_0^{(x) d}, with weighted degree at most
  sum_zeta a_{i,zeta} F_{d-1}(lambda b_{i,zeta}/a_{i,zeta}). (A colour may hold many gates; it is not treated as
  rank one.) This is YL's argument verbatim; nothing in it uses s.
- **Read-off.** Take lambda := 2^{N0 d (l - r)}. By (AL-B2), Upsilon(tau)^d lambda^{1 - tau} <=
  2^{N0 d (l + 2 eps_1)}, so deg_L <= 2^{N0 d (l + 2 eps_1) + o(d)} and deg_R <= 2^{N0 d (r + 2 eps_1) + o(d)}.
- **Length.** Lemma 3.2 turns M_0^{(x) d} into P_{k^2 d, s} with left exponent overhead log2(k+1)/k and length
  overhead c/k^2 <= 2/(s k); both tend to 0 as k grows. Lengths that are not multiples of k^2 are padded (rows by
  zeros; queries by floor(s N') - floor(s N) specified zeros and stars), N' - N = O(k^2).
- First eps_1 small, then k large, then d -> infinity: (l, r) is in K(s). ∎
With P = 1 this is the single-circuit statement used by Theorem 4; P = 2 is Stage 4+ (Sec. 8).

### 3.5 The one-pass covering circuit (Record 3 Sec. E), with the proof's random designs

Fix rho > 1 rational. For a query y with Y1 := {i : y_i = 1}, Y0 := {i : y_i = 0}, k1 := |Y1|, k0 := |Y0|,
k0 + k1 = sN:

    f_y(x) = prod_{Y1} x_i prod_{Y0} (1 - x_i) = sum_{Y1 ⊆ U ⊆ Y0 ∪ Y1} (-1)^{|U| - k1} x^U.

For each type k1 and each m in [k1, sN] put b(k1, m) := floor(k1 + rho(m - k1)) (>= m) and take a design
D_{k1,m} of b-subsets covering all m-subsets; assign each m-set U the first block B(U) ⊇ U. Gates are
(k1, m, B, sigma) with B in D_{k1,m}, sigma in {0,1}^B:
L[x, g] = [x|_B = sigma], R[g, y] = [k1(y) = k1] (-1)^{m - k1} #{U of y : |U| = m, B(U) = B, sigma|_U = 1}.
The colour of g is (k1, m, d) with d := |sigma|.

**Lemma 3.5 [proof].**
- (a) **Exactness.** L R = f_y for every row x and every query y of every type. *Proof.* x^U =
  sum_{sigma in {0,1}^{B(U)}, sigma|_U = 1} [x|_{B(U)} = sigma]; sum over U with the signs. ∎
- (b) **Right degree.** In colour (k1, m, d), a query of type k1 has at most C(k0, m - k1) C(b - m, d - m) gates:
  choose U ⊇ Y1 of size m, then the d - m extra ones of sigma on B(U) \ U. ∎
- (c) **Designs exist with both properties below (A2).** Let D_{k1,m} consist of |D| := ceil(N^2 C(N,m)/C(b,m))
  independent uniform b-subsets. Then with positive probability, simultaneously for every (k1, m):
  - (P1) every m-subset is covered;
  - (P2) for every row x (w := #1(x)) and every d: #{B in D_{k1,m} : |x ∩ B| = d} <= 6 mu_{x,d} + 3N, where
    mu_{x,d} := |D| C(w, d) C(N - w, b - d)/C(N, b).
  *Proof.* A uniform b-set contains a fixed m-set with probability C(N-m, b-m)/C(N, b) = C(b, m)/C(N, m), so (P1)
  fails with probability <= C(N, m) e^{-N^2}. Each count in (P2) is a sum of |D| independent indicators with mean
  mu_{x,d}; by (K3) with R = 6 mu + 3N it exceeds R with probability <= 2^{-3N}. A union bound over <= (N+1)^2
  designs, 2^N rows and N + 1 values of d gives total failure < (N+1)^3 (2^{-2N} + 2^N e^{-N^2}) < 1 for N >= 8. ∎
- (d) **Left degree.** With such designs, a row x has at most 10 N^3 2^{N max(L, 0)} gates of colour (k1, m, d), where
  per coordinate (w, m, b, d all divided by N)

      L(w; m, b, d) = H(w, d) + H(1 - w, b - d) - H(1 - m, b - m).

  *Proof.* By (P2) the count is <= 6 mu + 3N. With X := C(wN, dN) C((1-w)N, (b-d)N)/C((1-m)N, (b-m)N), the identity
  C(N, b) C(b, m) = C(N, m) C(N - m, b - m) gives mu <= N^2 X + 1 (the + 1 from the ceiling, as
  C(w,d) C(N-w, b-d) <= C(N, b)), and X <= (N + 1) 2^{N L} (C(n,k) <= 2^{n h(k/n)} above, C(n,k) >=
  2^{n h(k/n)}/(n+1) below). So the count is <= 6 N^2 (N + 1) 2^{NL} + 3N + 6 <= 10 N^3 2^{N max(L,0)} for N >= 8. ∎
  *Gotcha (Stage 3's X-c trap):* a non-empty colour has degree >= 1, so the true
  left exponent is max(L, 0), not L; the certificate bounds max(tau L + (1-tau) R, (1-tau) R) >= tau max(L,0) +
  (1-tau) R. (At Theorem 4's parameters L >= 0.05 > 0 on the whole polygon anyway.)
- (e) **Right degree exponent.** R(k0, k1; m, b, d) = H(k0, m - k1) + H(b - m, d - m) per coordinate, by (b).

`check_stage4.py` part F draws random designs of exactly this size at N = 10, sN = 4, rho = 5/2 and verifies (P1),
(P2) for every row and colour (largest ratio 0.264), exactness for a quarter of the 3360 queries (every split
k1 = 0..4) against all 1024 rows (0 mismatches) and (b) (0 violations).

**Lemma 3.5' (window and rounding, with unbalanced queries) [proof].** Let V(tau) be the max over the central
polygon Poly := {s/2 <= m <= s, s/2 + rho(m - s/2) =: beta, m <= d <= beta} of
G := tau max(L, 0) + (1 - tau) R at w = 1/2, k0 = k1 = s/2, b = beta. For every eps_1 > 0 there is eps' > 0 such
that for all large N the window circuit (all types k1 with |k1 - sN/2| <= eps' N, rows with
|#1(x) - N/2| <= eps' N) has Upsilon(tau) <= 2^{N (V(tau) + eps_1)} for every tau.
*Proof.*
- **Reparametrize** every colour by fixed coordinates: m = k1 + theta1 k0, beta* := k1 + rho(m - k1), the true block
  size b = beta* - phi min(eta, (rho - 1) theta1 k0) (so m <= b <= beta*; the floor moves b by < 1/N, so eta = 1/N
  suffices), and d = m + theta2 (b - m), with theta1, theta2, phi in [0, 1]. All side conditions hold: d <= w and
  d >= b - (1 - w) because b <= k1 + rho k0 <= s rho + 2 eps' < 1/2 - eps' (s rho = 0.302 at Theorem 4).
- **Continuity.** H(n, j) = n h(j/n) is continuous on {0 <= j <= n} (0 log 0 = 0). So G is a continuous function of
  (tau, w, k0, k1, eta, theta1, theta2, phi) on a compact box, and so is its max over (theta1, theta2, phi). At
  (w, k0, k1, eta) = (1/2, s/2, s/2, 0) that max is V(tau). By uniform continuity, for every eps_1 there are eps',
  eta_0 with the max within eps_1/2 of V(tau), for all tau and all parameters in the window.
- **Degrees to volume.** By Lemma 3.5(b), (d), each colour's degrees are at most 10 N^3 2^{N max(L,0)} and
  2^{N R} at its own parameters; there are at most (N + 1)^3 colours; so Upsilon(tau) <= 10 N^3 (N+1)^3
  2^{N (V(tau) + eps_1/2)} <= 2^{N (V(tau) + eps_1)} for N >= max(1/eta_0, N_1). ∎
This answers R1's defect 1: the circuit is built per query type k1, and its degrees at unbalanced types are covered
by the same continuous profile. `circuit_toy` style exactness at every split is part F above.

### 3.6 The certificate for xi [iv]

`cert_stage4.py` [XI] proves, by branch and bound over Poly (natural interval bounds everywhere, plus a centered
mean-value bound on interior boxes), V(t1) <= t1 h(s) and V(t2) <= (1 - t2)(1 - s) at rational t1, t2, and checks
that the slope of the line through (t1, t1 h(s)) and (t2, (1 - t2)(1 - s)) lies in (-(1 - s), h(s)). V is a max of
affine functions of tau, hence convex, so V <= line on [t1, t2]; the slope puts tau h(s) under the line on [0, t1]
and (1 - tau)(1 - s) under it on [t2, 1]. So min{V, tau h(s), (1 - tau)(1 - s)} <= line on [0, 1].

| s | rho | t1, t2 | boxes | l = line(1), r = line(0) | xi >= | [F1] every valid line <= |
|---|---|---|---|---|---|---|
| 1/8 | 27/10 | 798773/2500000, 7218613/10^7 | 1437, 2029 | 0.291551994, 0.118326796 | **0.0043428267** | 0.0043428941 |
| 11/100 | 549/200 | 49989/156250, 1850541/2500000 | 1321, 2003 | 0.275259811, 0.105686340 | **0.0044849038** | 0.0044849681 |

Here xi := (h(s) - s)/2 - line(1/2), so l + r = h(s) - s - 2 xi. Must-fail controls C1, C2: one 1e-7 grid step past
each contact, the prover finds an explicit colour whose rigorous lower bound beats the trivial line. So at c1 the
minimum in Lemma 3.4's condition is the trivial line, and every valid line has line(c1) >= c1 h(s) and
line(c2) >= (1 - c2)(1 - s); the chord through those two points gives the [F1] bracket (a bound against this upper
bound V, not against the circuit's true degrees). *Gotcha (found by the Lean check):* the line need not pass above
the witness colours' own values G(c1), G(c2) (only above the trivial lines there); the earlier certificate used
G(c1), G(c2) and printed brackets about 3e-8 too small (0.0043428848, 0.0044849401). Record 3's values
0.004342871357 and 0.004484944104 lie inside the corrected brackets.

### 3.7 The pair and the hardcoded enumerators

**Proposition 3.7 [proof, given Lemmas 3.4, 3.5, 3.5' and [XI]].** At s = 11/100 the pair (l, r) =
(0.275259811..., 0.105686340...) is in K(11/100), with l + r = h(s) - s - 2 xi, xi >= xi' := 22424519/(5 * 10^9).
Likewise at s = 1/8 with xi' = 21714133/(5 * 10^9). ∎ (Lemma 3.4 with P = 1, V from Lemma 3.5', and the line of
Sec. 3.6.) By upward closure, the 10-place round-ups (l', r') are in K(s); only l' + r' <= h(s) - s - 2 xi' + 2e-10
enters the costs, and the certificate charges the exponent with xi' (a lower bound), so the rounding is absorbed by
the eps of Theorem 4.

**Corollary 3.8 (enumerators at density s; YL Cor. 3.2) [proof].** For every eps > 0 there are deterministic
algorithms A_L, A_R that, given x in {0,1}^a or y with exactly s a specified positions, list the incident gates
and coefficients of a common exact circuit for P_{a,s}, in time 2^{(l' + eps) a} and 2^{(r' + eps) a}; gate names
and coefficients have O(a) bits.
*Proof.* Hardcode, for a large k (a multiple of q_s), an exact circuit C* for P_{N0, s}, N0 := k^2 + c, with degree
exponents l' + eps/4 and r' + eps/4 (Prop. 3.7). Choose k with (a) (max(l', r') + eps/4) c/k^2 <= eps/4 and
(b) log2(k + 1)/k <= eps/4. Pad a to a' := k^2 ceil((a + k^2)/k^2) (rows: zeros; queries: s a' - s a specified
zeros), apply Lemma 3.2 to the (a'/k^2)-fold tensor power of C*: neighbours are Cartesian products of C*'s finite
adjacency lists plus descriptions, each processed in poly(a) time. The exponents are <= l' + 3 eps/4 and
r' + eps/2 by (a), (b), and a' = a + O(1), so the slack pays the processing. ∎
At eps = 1e-9 the two conditions give k >= k_0 = 148444532000 at s = 11/100 (c = 1349495745500,
N0 = 22035779082048519745500 >= 2.2035e22) [iv, `cert_stage4.py` [K], with lmax = 0.2753 >= l for s = 11/100 and
0.2916 for s = 1/8, each s's own certified l rounded up; condition (b) binds, so k_0 does not depend on lmax]; they
are necessary, not sufficient (Lemma 3.4 needs "k large").

## 4. The fixed round family (A4)

Notation: layer k, pieces of length N_b (even), per-piece core a_b, per-piece non-core b_b := N_b/2 - a_b,
q := M/N_b pieces.

### 4.1 The splitter

**The split tree.** T_q: a node with q' leaves splits into children with q1 := floor(q'/2) and q2 := q' - q1 leaves.
A node with q' leaves owns q' N_b coordinates in a cyclic order; the root owns the block in natural order.
**A splitter** assigns to each internal node an offset o in Z_{q' N_b}: the left child is the cyclic window of
length q1 N_b starting at o (ordered from o), the right child the rest (ordered from o + q1 N_b). Leaves are the
q pieces. **Leaf counts.** kappa_T(k): the root gets k; a node with count k' passes floor(k' q1/q') to its left child
and the rest to its right child.

**Lemma 4.1 (balancing) [proof].** For every K ⊆ block with |K| = k there is a splitter whose leaf i contains exactly
k_i := kappa_T(k)_i elements of K, for every i; each k_i is floor(k/q) or ceil(k/q).
*Proof.*
- **Discrete IVT at a node.** Let Z be the node's cyclically ordered set (|Z| = m' = q' N_b), K' := K ∩ Z, |K'| = k',
  and f(o) := |K' ∩ window(o)| for the window of length ell := q1 N_b. Each element lies in exactly ell windows, so
  the mean of f over o is k' q1/q'. f(o + 1) - f(o) is in {-1, 0, 1}, so around the cycle f takes every integer
  value between its min and max; min <= mean <= max and the min is an integer, so floor(k' q1/q') is taken.
  Choose that o and recurse into both children (they are independent).
- **Floor/ceil.** Write k = q c0 + r0 with 0 <= r0 < q. Claim: a node with q' leaves gets k' = q' c0 + r' with
  0 <= r' <= q'. Its left child gets floor(k' q1/q') = q1 c0 + floor(r' q1/q'), with floor(r' q1/q') in [0, q1];
  its right child gets q2 c0 + ceil(r' q2/q'), in [q2 c0, q2 c0 + q2]. At a leaf (q' = 1), k_i = c0 + r_i with
  r_i in {0, 1}. ∎
*Gotcha:* the windows must be CYCLIC; the counts are then a deterministic function of k, so the per-piece families
need not be enumerated over count vectors. Control `offset0` (no splitter search) leaves 3230 of 4096 sets
unbalanced at q = 3, N_b = 4.

**Lemma 4.2 (number of splitters) [proof].** There are prod over internal nodes of q' N_b splitters, and
log2 of that is (q - 1) log2 N_b + S(q) with S(q) := sum over internal nodes of log2 q' <= 3q - 3 - 2 log2 q.
*Proof.* T_q has q - 1 internal nodes. S(1) = 0, S(2) = 1 = 3*2 - 3 - 2, S(3) = log2 3 + 1 <= 6 - 2 log2 3. For
q >= 3, S(q) = log2 q + S(q1) + S(q2) <= log2 q + 3q - 6 - 2 log2(q1 q2) by induction, and this is
<= 3q - 3 - 2 log2 q iff q^3 <= 8 (q1 q2)^2, which holds since q1 q2 >= (q^2 - 1)/4 and 2 q^3 <= (q^2 - 1)^2 for
q >= 3. (q2 = 1 at q = 3 uses S(1) = 0 <= 0.) ∎ [also checked [iv] for q <= 2^14]

### 4.2 Per-piece families

**Parity pattern.** Given the leaf counts k_i, set eps_i := 0 if k_i - a_b is even; number the pieces with k_i - a_b
odd in index order and give them +1, -1, +1, ... . Then sum_i eps_i = sigma(k): the number of odd pieces has the
parity of sum_i (k_i - a_b) = k - a. Put x_i := (k_i - a_b - eps_i)/2 and x'_i := x_i + eps_i, so
sum_i x_i = x and sum_i x'_i = x' (Sec. 1.5).

**Lemma 4.3 (per-piece family) [proof].** For each (k_i, eps_i) there is a family F(k_i, eps_i) of local rounds on
[N_b] (H_i of size N_b/2, cores of size a_b) such that every k_i-subset K_i is locally compatible with one of them
(|K_i ∩ Hc_i| = s a_b, |K_i ∩ Hbc_i| = (1 - s) a_b, |K_i ∩ (H_i \ Hc_i)| = x_i, |K_i ∩ (Hbar_i \ Hbc_i)| = x'_i), of
size at most floor(ln C(N_b, k_i)/p_loc) + 1 <= (1 + N_b ln 2)/p_loc, where
p_loc := C(a_b, s a_b) C(a_b, (1-s) a_b) C(b_b, x_i) C(b_b, x'_i)/C(N_b, k_i). It is found deterministically by
greedy in time depending on N_b only.
*Proof.* Every K_i is compatible with exactly a p_loc fraction of all local rounds (transitivity and double
counting, as in Sec. 1.5). Greedy picks the round compatible with the most uncovered sets (least index on ties);
the average round covers a p_loc fraction of the uncovered sets, so after m steps at most
C(N_b, k_i)(1 - p_loc)^m < 1 remain once m > ln C(N_b, k_i)/p_loc. ∎
(The local counts are in range: x_i, x'_i in [0, b_b] whenever 2 <= (kappa_lo - alpha/2) N_b, which holds by a wide
margin.)

### 4.3 The product family and its loss lambda

**Lemma 4.4 [proof].** F0_k := { the union over pieces of the local rounds R_i in F(k_i, eps_i), placed on the
pieces of a splitter } over all splitters and all choices (R_i). Then:
- (a) every member is a round (|H| = M/2, |Hc| = |Hbc| = a, Hc ⊆ H, Hbc ⊆ Hbar);
- (b) every K in layer k is compatible with at least one member;
- (c) log2 |F0_k| <= M (J(k/M) + lambda) + 2 log2((a+1)(b+1)) + 1, where

      lambda := [ log2 N_b + 3 + log2(1 + N_b ln 2) + 2 log2((a_b + 1)(b_b + 1)) ] / N_b.

*Proof.* (a) Sizes add over pieces. (b) Take the splitter of Lemma 4.1 for K; on piece i, K_i has k_i elements, so
some R_i in F(k_i, eps_i) is locally compatible; local compatibility on every piece gives the global counts s a,
(1 - s) a, x = sum x_i, x' = sum x'_i. (c) |F0_k| = #splitters * prod_i |F(k_i, eps_i)| <=
2^{(q - 1) log2 N_b + 3q} (1 + N_b ln 2)^q prod_i 1/p_loc,i (Lemmas 4.2, 4.3). Then:
- prod_i C(N_b, k_i) <= C(M, k) (Vandermonde);
- prod_i C(a_b, s a_b) >= C(a, s a)/(a_b + 1)^{q-1}: C(a, sa) is a sum over at most (a_b + 1)^{q-1} compositions of
  products prod_i C(a_b, j_i), and the balanced composition (j_i = s a_b) is the largest by log-concavity; same for
  (1 - s);
- the x_i take at most two consecutive values (check both parities of floor(k/q) - a_b), so they are a balanced
  composition of x and prod_i C(b_b, x_i) >= C(b, x)/(b_b + 1)^{q-1}; same for x'_i.
So prod_i 1/p_loc,i <= ((a_b + 1)(b_b + 1))^{2(q - 1)}/P_glob(k), and Sec. 1.5's bound on 1/P_glob finishes. ∎
**Construction cost** [proof]: the per-piece families cost O_{N_b}(1), a constant independent of n, but an
astronomical one: greedy enumerates every local round and every k_i-subset of [N_b], so it takes 2^{Theta(N_b)} bit
operations, of order 2^{2^{33}} at N_b = 8e9 (about 2^{32.9}). Listing F0_k costs |F0_k| poly(n). The constant is
also stated with n0 in Sec. 7.

**Explicit N_b.** N_b = 8 * 10^9 (a multiple of the denominators: a_b = 2228738800 and s a_b = 245161268 at
Theorem 4's alpha). Then lambda <= 2.3977e-8 and mu lambda <= 5.26e-9 [iv]. Control K7: N_b = 2e7 gives
lambda = 7.0e-6 and the claim fails. Control K8: the lambda-free bound 0.4998322078 is below the claim, so the
claim really contains lambda. Every term of Sec. 5.3 that pays for rounds carries mu lambda.

`check_stage4.py` part B builds F0_k at M = 16, q = 2, N_b = 8, a_b = 3, s = 1/3, b_b = 1 for every layer
k = 6..10 (both parities, eps patterns (0,0), (0,1), (1,-1), (1,0), (0,0)): every round valid, every K covered
(directly, by global compatibility), the p_loc formula exact, and prod 1/p_loc <= ((a_b+1)(b_b+1))^2/P_glob.

### 4.4 Multiplicity

**Corollary 4.5 [proof].** F_k := D copies of F0_k (fixed order, copy-major), D a positive integer. Every K in layer
k is compatible with at least D rounds of F_k, and |F_k| = D |F0_k|. Each copy will get its own residue. Sec. 5
uses D := ceil((2M + 2) ln 2 * G) with G = poly(n, L) of Lemma 5.2. ∎
*Gotcha (R2 defect 1):* with D = 1, sum_f |S_{c,f}| is only >= p/G, so Phi_0 < 1 fails. Control `lowmult` (D = 1
with p >= 4T) leaves 712161 pairs (c, y) uncovered.

## 5. The algorithm DET4 and Theorem 4

### 5.1 The prime

**Lemma 5.1 (prime p ~ T) [proof, given (K1)].** Put P0 := floor(T/(2(M + 1))) and B := the bit length of
1 + sum_i |z_i| (so B <= L + log2 n). Let coll_p := #{unordered pairs of distinct elements of Sigma congruent mod p}.
If P0 >= x_0, some prime p in [P0, 2 P0] has coll_p <= g N^2/p with g := 2 B ln 2. DET4 takes the prime with the
least coll_p (least p on ties). The scan costs P0 polylog (sieve) plus N polylog per prime: term
**Pscan = mu(2 - delta)** (R2 defect 4).
*Proof.* A nonzero difference of absolute value < 2^B has fewer than B/log2 P0 prime factors >= P0. Summing,
sum_p coll_p <= C(N, 2) B/log2 P0 over primes in [P0, 2P0], and there are >= P0/(2 ln P0) of them, so the least is
<= C(N, 2) B (2 ln P0)/(P0 log2 P0) <= N^2 B ln 2/P0 <= 2 B ln 2 N^2/p. ∎

**Lemma 5.2 (distinct residues of a good layer) [proof].** For c in C_k, let W_c be a set of layer-k
representations with pairwise distinct keys sum_K e_i z_i, |W_c| >= N/(M + 1). Then W_c contains a subset W'_c with
pairwise distinct residues mod p and |W'_c| >= p/G, G := 1 + 2 g (M + 1)^2 = poly(n, L).
*Proof.* The keys of W_c are a translate of a subset of Sigma (Sec. 1.4), and collisions mod p are invariant under
translation and monotone under subsets, so coll(W_c) <= coll_p <= g N^2/p. With w := |W_c| and n_r residue
multiplicities, sum n_r = w and sum n_r^2 = w + 2 coll, so by Cauchy-Schwarz the number of distinct residues is
>= w^2/(w + 2 coll) >= 1/(1/w + 2 g (M+1)^2/p). Since p <= 2 P0 <= T/(M+1) < N/(M+1) <= w, this is >= p/G. ∎
*Gotcha (R1):* the factor is bit-length, poly(n, L), not poly(n). It is 2^{o(n)} because L = 2^{o(n)}.
*Gotcha (the step p <= w; found by the Stage 5 verifier):* the last inequality needs p <= |W_c|. Here it holds
because p <= 2 P0 <= T/(M + 1) < N/(M + 1) <= |W_c| in the many-sums branch, with P0 >= x_0 (n >= n0, Sec. 7). The
general statement, valid for any prime p (e.g. p ~ N, Stage 5), is: W_c has at least min(p, |W_c|)/G' distinct
residues, G' := 1 + 2 g'(M + 1)^2 with g' := max(2 B ln 2, 2 x_0), by the same Cauchy-Schwarz step, since
w^2/(w + 2 coll) >= 1/(1/w + 2 g'(M+1)^2/p) >= min(p, w)/G'. Multiplicity then uses D := ceil((2M + 2) ln 2 G
ceil(p/min(p, w_min))); the extra factor is 1 when p <= w_min and at most 2 x_0 (a constant) otherwise, so it costs
nothing in the exponent. For Stage 4's parameters the factor is 1 and nothing below changes; `check_stage4.py`
part C asserts |W_c| >= p in the proof regime.

### 5.2 DET4

Constants: the rationals s, alpha, mu, delta and N_b of Sec. 5.3; the hardcoded (k, C*) of Cor. 3.8; eps > 0.
- 0. If n < n0, brute force. (n0 >= N_b/mu, so that q >= 1, plus the thresholds of Secs. 1.4, 3, 5.1.)
- 1. Build Sigma up to T (Sec. 1.3). If N <= T, run AKKN and stop.
- 2. Find p (Lemma 5.1).
- 3. Compute every C_k (Sec. 1.4).
- 4. For each k with C_k nonempty (all have k/M in the certified range):
  - 5. List F_k = D copies of F0_k (Sec. 4).
  - 6. For every c in C_k and f in F_k, build S_{c,f} := {const(c, f) + sum_K e_i z_i mod p : K compatible with f},
    by enumerating the compatible K directly: a choice of s a elements of Hc, (1 - s) a of Hbc, x of H \ Hc and x'
    of Hbar \ Hbc (R2 defect 5; testing all K per (c, f) would cost 2^{(1 + h + J) M}). Term
    **Kenum = mu(2 + lambda)**: per (c, f) there are P_glob C(M, k) compatible K, and Lemma 4.4's proof gives
    |F0_k| P_glob <= 2^{M lambda} poly, so |F_k| P_glob C(M, k) <= D 2^{M lambda} C(M, k) poly <= 2^{M(1 + lambda)}
    poly; multiplying by |C_k| <= 2^M gives 2^{M(2 + lambda)} poly.
  - 7. Choose one residue r_f per round of F_k by the fixed-point estimator (Lemma 5.4), so that every
    (c, y) in C_k x Z_p is covered: r_f - y in S_{c,f} for some f.
  - 8. Choose one global shift t (Lemma 5.5) and replace r_f by r_f + t.
  - 9. For each f: generate the kept records {u in U_f : key(u) ≡ r_f (mod p)} and {v in V_f : key'(v) ≡ r_f} by
    meet in the middle (split u's coordinates into two halves, all count classes, sorted residues; cost half-lists
    plus output), run the keyed count of Sec. 2 with the enumerators of Cor. 3.8, and if it is positive, recover a
    pair by bisection and output u + v.
- 10. Output "no".

**Lemma 5.3 (correctness) [proof].** Soundness: Sec. 1.2(a) and the exactness of the count. Completeness: let c* be
a solution, c its block part, y* := (u-outer part of c*).z mod p. Some C_k contains c (Sec. 1.4). After step 8 some
f has r_f - y* in S_{c,f} (coverage is shift invariant, Lemma 5.5), i.e. some K compatible with f has
blockpart(u) ≡ r_f - y*. The (u, v) of (c*, K) (Sec. 1.2(b)) then have key(u) = key'(v) ≡ r_f, u in U_f and v in
V_f (the non-star counts are those of Sec. 1.5), so both are kept and the count is >= 1. ∎

**Lemma 5.4 (one residue per round: the fixed-point pessimistic estimator) [proof].** Let F_k = (f_1, ..., f_F),
U_k := C_k x Z_p, P_f(c) := |S_{c,f}|/p, omega_c(f) := prod_{f' > f} (1 - P_{f'}(c)), and let U_c(f) be the set of y
uncovered for c after rounds 1..f. Put Phi_f := sum_{c in C_k} omega_c(f) |U_c(f)|. Suppose every c in C_k has
sum_f |S_{c,f}| >= p ln(4|U_k|). Choose r_f to maximize A~(r) := sum_c w~_c(f) cov_c(r), where cov_c(r) :=
#{y in U_c(f-1) : r - y in S_{c,f}} and the w~_c(f) are fixed-point numbers with B' := ceil(log2(4 F^2 |U_k|))
fractional bits computed backwards: w~_c(F) = 1, w~_c(f-1) = w~_c(f) (1 - P_f(c)) rounded down. Then every (c, y) is
covered at the end.
*Proof.*
- Phi_0 = p sum_c prod_f (1 - P_f(c)) <= p sum_c exp(-sum_f P_f(c)) <= |C_k| p/(4 |U_k|) = 1/4.
- For a uniform r, each y in U_c(f-1) is covered with probability exactly P_f(c), so the average of
  Phi_f(r) := sum_c omega_c(f) (|U_c(f-1)| - cov_c(r)) over r is Phi_{f-1}. Write A(r) := sum_c omega_c(f) cov_c(r);
  then Phi_f(r) = const - A(r).
- **Rounding.** By induction, 0 <= omega_c(f) - w~_c(f) <= (F - f) 2^{-B'} =: e_f (each step multiplies the old
  error by a factor <= 1 and adds at most 2^{-B'}). The weights are rounded DOWN, so the error is one-sided: since
  0 <= cov_c(r) and sum_c cov_c(r) <= |U_k|, every r has 0 <= A(r) - A~(r) <= e_f |U_k|. With r* maximizing A:
  A(r_f) >= A~(r_f) >= A~(r*) >= A(r*) - e_f |U_k| >= mean A - F 2^{-B'} |U_k|, i.e.
  Phi_f <= Phi_{f-1} + F 2^{-B'} |U_k|.
- So Phi_F <= 1/4 + F^2 2^{-B'} |U_k| <= 1/2. As omega_c(F) = 1, Phi_F is the number of uncovered pairs: 0. ∎
  *Gotcha (referees G1, G2):* the one-sided bound needs the round-down. With a two-sided error |A - A~| <= e_f |U_k|
  (e.g. round to nearest) the chain only gives A(r_f) >= max A - 2 e_f |U_k|, hence Phi_F <= 1/4 + 2/4 = 3/4; that
  is still < 1, so the conclusion survives either way.
- **The hypothesis holds** with D of Cor. 4.5: by Lemma 5.2 and Cor. 4.5, sum_f |S_{c,f}| >= D |W'_c| >= D p/G >=
  p (2M + 2) ln 2 >= p ln(4 * 2^M * p) >= p ln(4|U_k|) (p <= 2^M).
- **Cost.** Each round: one cyclic correlation of the uncovered indicator with 1_{S_{c,f}} per c, exactly by (K2), plus
  the weighted sum with O(n)-bit numbers: |C_k| p polylog poly(n) per round. Term **P6 = mu(2 - delta + J + lambda)**
  (|F_k| <= 2^{M(J + lambda)} poly, |C_k| <= 2^M, p <= 2^{(1 - delta) M}).
- **The backward pass.** The w~_c(f) are computed from f = F down to 1, so every |S_{c,f}| is needed before the
  first forward step. DET4 therefore runs step 6 twice: a first enumeration that records only the sizes |S_{c,f}|
  (|F_k| |C_k| numbers of O(M) bits; the w~ table itself has |F_k| |C_k| entries of B' = O(n) bits, or is
  recomputed per c on the fly), and a second one, interleaved with the forward pass, that rebuilds each S_{c,f} when
  round f is processed. Storing all the sets instead would take |F_k| |C_k| p words. Either way the cost is at most
  twice Kenum plus the |F_k| |C_k| poly(n, L) arithmetic on weights, below P6.
*Gotcha:* do NOT keep a full residue covering per round. A typical round meets only
2^{(1 - delta - J) M} compatible keys of the solution, so a per-round covering would multiply the records by 2^{JM}.

**Lemma 5.5 (shift) [proof].** For every t, {r_f + t} still covers U_k: if (c, y - t) is covered by r_f then (c, y)
is covered by r_f + t, and U_k is closed under y-shifts. Let w_f(r) := 2^{dU} #{u in U_f : key(u) ≡ r} +
2^{dV} #{v in V_f : key'(v) ≡ r} with the degree caps dU, dV of Sec. 2. The t minimizing sum_f w_f(r_f + t) (least
on ties) costs at most the mean over t, sum_f (2^{dU} |U_f| + 2^{dV} |V_f|)/p. The histograms w_f come from
half-list histograms per count class by cyclic convolution (K2); the sums over t cost |F_k| p. ∎

### 5.3 The exponent

**Lemma 5.6 (costs) [proof].** Per n, with sup over kappa in the certified layer range and up to poly(n, L) and
O(N_b) factors, the steps cost:

| term | step | exponent |
|---|---|---|
| P1 | 1, Sigma up to T | mu(1 - delta) |
| P2 | 1, AKKN | 1/2 - mu delta/2 |
| Pscan | 2 | mu(2 - delta) |
| P5 | 3 | 2 mu |
| Kenum | 6 | mu(2 + lambda) |
| P6 | 7 and the sums of 8 | mu(2 - delta + J + lambda) |
| P4 | 8 histograms, 9 generation | mu(J + lambda) + 1/4 + mu log2(3)/4 |
| P3 | 9 count (kept records times degrees) | P3 of Sec. 2 + mu lambda |

*Proof.* P3: by Lemma 5.5 the kept weight is at most |F_k| (2^{dU}|U| + 2^{dV}|V|)/p, with |F_k| <=
2^{M(J + lambda)} poly(n, L) (Lemma 4.4, Cor. 4.5) and p >= P0 >= T/(2(M+1)) - 1; with Sec. 2 this is P3 + mu lambda.
The kept count itself is at most the kept weight. P4: the half-lists of u have at most 3^{M/4} 2^{M/4} 2^{(n - M)/4}
entries (half of H with values in {-1, 0, 1}, half of Hbar and of the u-outer bits binary), over poly many count
classes; times |F_k| rounds. (The deterministic E does not need balanced half-splits; P4 is slack, 0.398.) The
other terms are stated where the steps are defined. ∎

**Theorem 4, proof.** Correctness: Lemma 5.3. Time: Lemma 5.6 over the M + 1 layers, with the circuit's eps and the
O(N_b) and poly(n, L) factors absorbed into eps n. `cert_stage4.py` [E] evaluates every term in outward-rounded
intervals on 6000 kappa-pieces of [kappa_lo, 1 - kappa_lo] (h(kappa_lo) < 1 - delta checked), at

| s | alpha | mu | delta | E_det <= | binding |
|---|---|---|---|---|---|
| **11/100** | 5571847/10^7 | 2193169/10^7 | 15323/10^7 | **0.4998322131** | P6 0.499832213, P3 0.499832185, P2 0.499831970 |
| 1/8 | 223753/400000 | 2215851/10^7 | 2969/2000000 | 0.4998357366 | P3, P6, P2 |

with xi = the certified lower bounds of Sec. 3.6 and lambda of Sec. 4.3. The claims 0.4998322132 and 0.4998357367
pass. The other terms: P1 0.219, Pscan 0.438, P5 0.4386, Kenum 0.4386, P4 0.398. ∎

**Must-fail controls (all rejected by `cert_stage4.py`):** K1 E_det - 1e-9; K2 mu + 1%; K3 xi = 0 gives E >= 1/2;
K4 delta doubled; K5 the kappa range cut to |kappa - 1/2| <= 1e-3 (the range certificate refuses); K6 the
deterministic claim at the randomized optimum's parameters (P6 too big); K7 N_b = 2e7; K8 lambda dropped (the
lambda-free bound is below the claim); K9 the randomized number claimed for the deterministic algorithm.

**Where the gain comes from.** At kappa = 1/2, P3 = 1/2 + mu(delta - alpha xi) and P2 = 1/2 - mu delta/2, so
balancing gives delta = 2 alpha xi/3 and a gain of about mu alpha xi/3 (1.8e-4 here; the certified 1.678e-4 also
pays for the kappa range and finite xi). The deterministic price is P6 = mu(2 - delta + J), one estimator step per
(c, round), which caps mu near 0.22 (the randomized algorithm runs at mu = 0.48). Stage 3's route had xi ~ 3.6e-5
at s = 1/2; Record 3's free choice of s (the s-cancellation of Sec. 2) lets the small-s circuit's xi ~ 4.5e-3
count in full.

## 6. The randomized exponent (Theorem 4R) and the balanced half-splits (A3)

- The randomized algorithm draws 2^{J M} poly uniformly random rounds instead of F_k and filters each with YL's
  multiply-add-shift hash at survival rate 1/T (pairwise independent over distinct keys) [cite YL Sec. 2.2].
- **The filter cap [proof] (from RESULT.md Sec. 1.6).** For c in C_k fix W_c of exactly ceil(T/(M + 1)) distinct
  keys. If Y members of W_c are compatible with the round and X of them survive, then E[X | Y] <= 2Y/T <= 2/(M+1) <= 1,
  and pairwise independence gives Pr[X > 0 | Y] >= E[X|Y]^2/E[X^2|Y] >= E[X|Y]/(1 + E[X|Y]) >= Y/(2T). So a round
  succeeds with probability >= E[Y]/(2T) >= 2^{-J M}/poly. *Gotcha:* without the cap |W_c| <= T/poly, Y can exceed
  T and Y/T is no longer a probability bound.
- **A3: balanced half-splits [proof].** Each round also draws uniform halvings of each of the four regions Hc,
  H \ Hc, Hbc, Hbar \ Hbc (and of Hbar, the outer halves); the u-list is restricted to records whose non-star
  counts are exactly half on each half of Hc and of H \ Hc, the v-list likewise on Hbc and Hbar \ Hbc. A compatible
  representation meets this with probability prod over the four regions of
  C(j, j/2) C(m_r - j, (m_r - j)/2)/C(m_r, m_r/2) >= 1/poly(M) (j the representation's count in a region of size
  m_r; parities fixed by rounding the region sizes). The restricted list is a product U^1 x U^2 of two half-lists
  of size |U|^{1/2}, so sorted-residue meet in the middle generates the filtered list in |U|^{1/2} poly + output:
  **P4 = mu J + log|U|/2**. The rounds lose only a poly factor.
- `cert_stage4.py` [E] (RAND rows): E <= 0.4996416843 at s = 11/100 (alpha = 5158197/10^7, mu = 4757627/10^7,
  delta = 7541/5000000) and 0.4996427664 at s = 1/8. Without A3, with Record 3's cruder list bound, it is
  0.4996681 / 0.4996676 [float].

## 7. Non-explicitness (A5)

- **What exists [proof, given Sec. 3].** For eps > 0: an integer k meeting Cor. 3.8's conditions and an exact
  integer circuit C* for P_{k^2 + c, s} with degree caps 2^{(l' + eps/4) N0}, 2^{(r' + eps/4) N0}. The existence
  proof is non-constructive at these places: the random designs (Lemma 3.5(c)), the random group elements of hole
  fixing (Lemma 3.3), the rebalancing recursion (whose 2^{o(d)} is ineffective), and "k large".
- **What DET4 hardcodes.** The pair (k, C*): a finite table of integers. Everything else is explicit: the rationals,
  the prime scan, the C_k, the splitter, the greedy per-piece families (computable in O_{N_b}(1) time), the estimator,
  the shift, the generation and the bisection.
- **Why it is a deterministic algorithm [arg, as S2 Sec. 8.3].** One finite program, no random bits, the same
  constant for every n, correct and within the time bound on every input; the theorem asserts that such a program
  exists (as Robertson-Seymour's cubic algorithms exist for each minor-closed class). We do not claim a runnable
  program: N0 >= 2.2e22 at eps = 1e-9, so verifying one candidate touches 2^{N0} rows.
- **n0.** Lower bounds only: q >= 1 needs n >= N_b/mu = 3.65e10; plus P0 >= x_0 and the thresholds of Secs. 1.4
  and 3.5. Lemma 3.4's "sufficiently large" makes n0 ineffective, as in S2/Stage 3.
- **The hidden constant.** Theorem 4's poly(n, L) 2^{(E4 + eps) n} hides an additive constant of order 2^{2^{33}} bit
  operations for the greedy per-piece families (Sec. 4.3, 2^{Theta(N_b)} at N_b = 8e9), on top of the hardcoded
  table. It is independent of n, so it does not touch the exponent; it is another reason no runnable program is
  claimed.

## 8. Stage 4+ (separate, optional): a family of two circuits

The idea is ours.
- **Mechanism.** Lemma 3.4 allows a finite family. Each member's V_rho is convex, but their minimum is not, and two
  circuits crossing near tau = 1/2 put the line's binding points on the trivial pairs while the middle is covered by
  two different circuits. The line through the two trivial contacts then sits lower than any single circuit allows.
- **Certificate [iv], `cert_stage4plus.py`.** s = 11/100, rho1 = 49/20, rho2 = 11/4, t1 = 1531131/5000000,
  t2 = 7403119/10^7, middle vertex v = 5037/10^4. Proved: V_{rho1}(t1) <= t1 h(s); V_{rho2}(t2) <= (1 - t2)(1 - s);
  V_{rho1}(v) <= line(v) and V_{rho2}(v) <= line(v); slope 0.179769 in (-(1-s), h(s)); l = 0.277806215,
  r = 0.098037462 >= 0. By convexity V_{rho1} <= line on [t1, v] and V_{rho2} <= line on [v, t2], so the family
  condition of Lemma 3.4 holds with P = 2:

      xi_family(11/100) >= 0.0070361406     (single circuit 0.0044849038; [F1] every valid line <= 0.0070362061).

  Controls: one grid step past each contact BOTH members are refuted (C1, C2, which also gives [F1]); each member
  alone fails at the other's contact (C3), so the family is needed.
- **Theorem 4+ [proof, given Lemma 3.4 with P = 2, Lemmas 3.5, 3.5' for each member, and the rest of Theorem 4].**
  DET4 with this pair: E_det <= 0.4997369618 [iv] at alpha = 2782051/5000000, mu = 2192909/10^7,
  delta = 12011/5000000, same N_b and lambda; binding P2 0.4997366, P3 0.4997370, P6 0.4997369; gain 2.6304e-4.
  Controls K1-K4 rejected (K4: the single-circuit xi at these parameters gives 0.50005).
- Each member needs its own designs and hole fixing (a constant factor in the hardcoded table). Three-member
  families, on Stage 5's route, are certified in `stage5b.md`.

## 9. Checks

**Lean 4 (kernel-checked).** `lean/SubsetsumLean/Stage4*.lean` check every inequality of `cert_stage4.py` and
`cert_stage4plus.py` in the Lean kernel, with the controls refuted and only the standard axioms (propext,
Classical.choice, Quot.sound; `lean/axioms_stage4.out`, 131 theorems). Scope and the method (the [XI] claims by a
cell tree of Gibbs tangent planes and chords, 1635 leaves, not by the script's boxes) are in `lean/LEAN_SCOPE.md`;
`lean/check_stage4.sh` rebuilds and re-audits all of it in one command (about 30 min on the 8 GB Mac, < 3 GB).
The Lean check found the [F1] defect of Sec. 3.6 (a bracket, not a claim) and proves Lemma 4.2's S(q) bound for
every q, not only q <= 2^14.

All three scripts use the standard library (plus numpy in `check_stage4.py`), run under `nice -n 15`, < 300 MB.
- `cert_stage4.py` (about 20 s): [XI] at s = 1/8 and 11/100 with C1, C2 and [F1]; [LAM] lambda at N_b = 8e9 and
  S(q) <= 3q - 3 - 2 log2 q for q <= 2^14; [K] k_0 at eps = 1e-9; [E] both deterministic rows and both randomized
  rows; K1-K9. Output `cert_stage4.out`: CERTIFICATE PASS. `--search` re-runs the float parameter search.
- `cert_stage4plus.py` (about 10 s): Sec. 8. Output `cert_stage4plus.out`: STAGE 4+ CERTIFICATE PASS.
- `check_stage4.py` (about 6 min): output `check_stage4.out`: STAGE 4 CHECK PASS.
  - A: splitter, exhaustive over all K for (q, N_b) in {(2,4), (3,3), (3,4), (4,3), (5,2), (6,2), (7,2)}; control
    offset0.
  - B: the product family at s = 1/3 (Sec. 4.3); control offset0.
  - C: DET4 end to end at n = 14, M = 8, core a = 3 with s a = 1 (s = 1/3), b = 1, T = 253, against brute force.
    Every layer k = 3, 4, 5 uses its own (x, x') = (0,0), (0,1), (1,1), and every round of the fixed greedy family
    satisfies x' - x = sigma(k). The family is repeated D times and each copy gets its own residue from the
    fixed-point estimator (integer weights, B' bits).
    - Regime 'proof' (p in [P0, 2P0], P0 = 14): 40 instances (25 yes), 0 wrong answers, 0 layer-level violations,
      0 uncovered (c, y); Lemma 5.1's collision bound, Lemma 5.2's p/G, D <= the proof's D and Phi_0 <= 1/4 asserted;
      kept records at the best shift 285428 against an average of 300279.
    - Regime 'big' (p = 1013 >= 4T, so p >> T and each round covers a tiny part of Z_p): D = 142..180 copies,
      0 wrong answers, 0 uncovered.
    - Regime 'tight' (referee G2's test-coverage point): at toy sizes N/(M+1) is far below every layer's key count, so in
      the regimes above C_k is always the whole cube. Lemmas 5.2-5.4 use only that every c lies in some served C_k and
      that C_k's threshold is >= N/(M+1), so this regime takes T = 100, inputs with colliding block sums, and raises
      layer 4's threshold to the median key count (C_3 = C_5 = cube keep every c covered). Then |C_4| ranges over
      128-180 of 256: the estimator runs on the restricted universe C_4 x Z_p, with 12 instances, 0 wrong answers,
      0 layer-level violations, 0 uncovered (c, y) in C_k x Z_p, while 8 pairs (c, y) with c outside C_4 (never
      targeted) stay uncovered. Control dropcover in this regime is detected.
    - Controls, each detected: nocompat (wrong answers); wrongcore (u's core gets (1 - s) a non-stars: s and 1 - s
      swapped; layer-level violations); dropcover (one pick kept; uncovered pairs); noparity (rounds only with
      x' = x; the odd layer is uncovered); nofew (wrong answers); lowmult (D = 1 at p >= 4T; 712161 uncovered).
  - D: Lemma 3.2's padding; control c = k.
  - E: Lemma 3.3 at gate level on P_{6,1/3}.
  - F: Lemma 3.5 with random designs of the proof's size.
- **Limits.** The toy's PM is the trivial exact counter (Lemma 3.5 is tested separately in F); the end-to-end run uses
  q = 1 (the product with q = 2 is part B); asymptotic rates are not tested, only the logic.

## 10. What is not proved here

- **[arg]:** only the definitional item of Sec. 7 (that a non-explicit program with a hardcoded, proven-to-exist
  table counts as a deterministic algorithm), as in S2 Sec. 8.3.
- **[cite]:** (AL-B2) as stated in YL (AL25 App. B); S2 Lemma 9.1; AKKN16 Lemma 3.2; HS74; YL's counting and
  recovery; (K1)-(K3).
- **Not claimed:** optimality of any parameter; Record 3's 0.4996645 point (not certified at its s = 0.1179);
  families of more than two members (see `stage5b.md`); an explicit (constructive) version; any effective n0.
- **Review.** Two internal referee passes (G1, G2) on this text; every fix is applied (Sec. 0.1). A1-A4 were [arg] in
  the randomized precursor and are [proof] here. Internal referee passes are not peer review.
