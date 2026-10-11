# Stage 2b: an explicit deterministic Subset Sum algorithm in time 2^{0.49999834 n}

Draft, private. This document makes Stage 2 explicit. Stage 2 is `stage2.md` in this directory (in our working
tree, `stage2.md`), here **S2**. This document changes only the
partial-match subroutine PM. Everything else in S2 (Steps 0-6, Lemmas 2.1-7.2, Certificate 7.2) is used as
written. S2 Sec. 8 ("non-explicit") is superseded by this document.

Sources:
- **YL** = Ye-Li arXiv 2610.10446 v1: Sec. 3.5 (the circuit), Lemma 3.1, Lemma 3.4, Cor. 3.3, Sec. 4 (the
  numbers). Read from the TeX/PDF text.
- **AL25** = Alman-Li arXiv 2509.14489, App. B, pp. 45-49: Lemma B.2, Thm B.1, Lemma B.3. Read for this
  document. Only Lemma B.3's *special case* is used, and it is re-proved in Lemma E4. Thm B.2 and Lemma B.4,
  which carry the ineffective o(d), are not used.

Certificate: `../certificates/cert_explicit.py` (exact rationals, outward bounds, < 1 s). Toy test:
`../certificates/toy_explicit.py` (Sec. 10). Lean: `../lean/SubsetsumLean/Explicit.lean` kernel-checks the certificate's inequalities (Sec. 11).

**Labels.** [proof] = proved here; [cite] = taken from the named place; [arg] = argued, less than a full
proof (all listed in Sec. 9).

*Referee fixes (2026-10-10, two independent clean referees E1 and E2, both "confirmed with fixes").*
- (F1, E1-1) Lemma E1's potential uses 2^{-(ceil(2 t m_v) + T)}, so every operation is exact rational
  arithmetic. The tail loosens by 1, and E2(iii) carries T + 1 for T.
- (F2, E1-2 / E2-1) E2(v): the dominant left-degree term is the *first* one, 4 t_D t_Q m_x, whose exponent is
  L3. The range mu in [a, 2a] is stated, with the concavity argument. Both dominance inequalities are now
  certified (Certificate [A]) instead of cited.
- (F3, E1-3 / E2-6) Delta is per coordinate. The certificate prints Delta = 6.19e-4, the value used.
- (F4, E1-4 / E2-2) The padding and storage constants are stated (each at most 2^{N0}). The additive
  preprocessing cost and the multiplicative run-time constant are combined correctly in Sec. 7, so c = 4858.
- (F5, E1-5 / E2-3) New Lemma E6 bounds the preprocessing gate by gate, including the |V| ~ 2^N N^2 term and
  the size of the rationals. c_b <= 4 is now [proof], in the bit-operation model.
- (F6, E2-4) The windows need q | N0 = k(k+2), not q | k. The least even such k is
  k = 10045215487480163574218750 ~ 1.0045e25 (CRT), so N0 ~ 1.0091e50 (was 1e52) and n0 ~ 5.9e59 (was 5.8e61).
- (F7, E2-5) The certificate checks ln 2 >= 0.6931 and log2 e >= 1.4426 by exact series bounds; the vacuous
  assert is gone.
- (F8, E1-7) The S2 path is given for both layouts (above).
- (F9, E1-6 / E2-7) A gate-level end-to-end toy test of E1 + E2 + E3 + E4 at N = 8 now exists (Sec. 10).

## 0. Statement

**Definition (explicit).** An algorithm is *explicit* if it is a fully specified deterministic program. Every
object it uses is computed by the program itself, and every constant in its time bound is a stated number.

**Theorem E.** There is an explicit deterministic algorithm DET2-E that decides Subset Sum on every input in
time C_E * poly(n, L) * 2^{E n}, where:
- E <= 0.4999983316 (S2 Certificate 7.2[A]); with only xi > 0.00002 from YL's statement, E <= 0.4999983345
  (S2 Certificate 7.2[B]);
- C_E = 2^{c N0}, with N0 = k(k+2), k = 10045215487480163574218750 (so N0 ~ 1.0091e50), and c = 4858.

The algorithm first builds an input-independent integer circuit. It does this deterministically, in at most
2^{4 N0} bit operations (Lemma E6). [proof]

**Corollary.** Search is in the same time (S2 Corollary 2, unchanged). [proof]

*Status.* The algorithm can be written down. Its constant is galactic: the gain appears only for n > ~5.9e59
(Sec. 8). The point of the theorem is that nothing in it is shown to exist without being constructed. The
exponent is S2's: explicitness costs nothing in the exponent.

*What was non-explicit in S2, and what replaces it.*

| S2 Sec. 8.1 item | replaced by |
|---|---|
| Sec. 3.5 random orderings (D, Q prefixes; union bound) | Lemma E1, pessimistic estimators on i.i.d. lists |
| hole fixing, random g_i (S2 Lemma 9.1(a)) | Lemma E3, greedy choice of flips |
| AL25 Thm B.2 rebalancing (min over an unstated tree; o(d)) | Lemma E4, explicit threshold rule with an effective constant |
| "kappa sufficiently large" (ineffective) | explicit k and eps' = 10^-13 (Certificate [A]) |
| Cor. 3.2's hardcoded circuit for P_{kappa^2+2kappa}, N' >= 2.2e22 | not needed: the rebalanced tree is enumerated implicitly at the input's length (Lemma E5) |

## 1. What is cited

- **(S)** S2's algorithm and its analysis. S2 uses PM only through this bound [proof, by inspection of S2
  Lemma 6.1(h) and Lemma 5.3]: PM counts keyed compatible pairs exactly, in time
  C * poly * (2^{(dL'+eps) n'} |A| + 2^{(dR'+eps) n'} |B|) with eps = 10^-9, for S2's rational pair
  (dL', dR') = (0.007275870560, 0.492684058989). Here n' is the padded length and C is any constant. A
  constant C only multiplies S2's time bound.
- **(Y1) YL Sec. 3.5, exactness [cite; tested in `ye-li-audit/yl_circuit.py` and `../certificates/toy_explicit.py`].** Let
  L_D be a list of bN-subsets in which every query of the type has a fitting member. For each D and each mu,
  let Q_{D,mu} be a list of 2 mu N-subsets of the complement of D covering all its mu N-subsets. Then the
  gates (D, Q, sigma), with D(y) := the first fitting D in the list and Q_D(U) := the first superset in the
  list, give an exact integer circuit for the type's submatrix. The proof uses only coverage and first fit, so
  it does not depend on how the lists were chosen.
- **(Y2) YL Sec. 3.5, right degree [cite].** deg_R(colour (mu, theta)) <= 2^{N R(mu,theta)}, with
  R = b - 1/2 + 2a + h(a, mu - a) + h(mu, theta - mu). This holds for any lists.
- **(Y3) YL Sec. 3.5, the left-degree reduction [cite].** For a row x and colour (mu, theta),
  deg_L <= sum over D in L_D of #{Q in Q_{D,mu} : #1(x|Q) = theta N}. Every list Q_{D,mu} has the same length.
  The colours have mu in [a, 2a]: U consists of the aN ones of y outside D plus some of its aN zeros there.
- **(Y4) YL Lemma 3.4, the tree [cite].** Take a finite family of coloured exact circuits for M, each colour
  with max degrees (a, b), all entries >= 1. Let *any* rule choose a circuit t at each node of depth d and
  weight lambda, and let the children of colour zeta get weight lambda b/a. The resulting tree computes M^{⊗D}
  exactly, and deg_L + lambda deg_R <= G_D(lambda), where G_0 = 1 + lambda and
  G_d(lambda) = sum_zeta a_{t,zeta} G_{d-1}(lambda b_{t,zeta}/a_{t,zeta}).
- **(Y5) YL Lemma 3.1 and Cor. 3.3 [cite].** These are the grouping (left factor (k+1)^{kD}) and the keyed count.
- **(Y6) YL Sec. 4 [cite].** V(tau) <= Vbar(tau). Here Vbar is the two-segment function through
  V(0), V(1/2), V(1); it is convex, and its anchors are the table values (used as upper bounds, + 1e-20). YL's
  a, b have denominator 10^26, so q := lcm(4, 10^26) = 10^26. (The two dominance inequalities of Sec. 3.5 are
  no longer cited: Certificate [A] checks them.)
- **(L) S2 Lemma 9.1(b)-(d) [proof there].** Given flips g_1..g_J whose window translates cover X x Y, the
  2^J - 1 signed, restricted copies sum to an exact circuit, and each colour's degrees do not increase.

## 2. Lemma E1 (deterministic covering-and-sampling lists) [proof]

*Setting.*
- A finite candidate set S.
- Coverage constraints u in U: "some list member covers u", with p_u := Pr_{s uniform in S}[s covers u] >= p.
- Sampling constraints v in V: rational weights w_v : S -> [0,1], with mean m_v := E_s w_v(s).
- An integer T >= 1 and the length t := ceil(T/p).

If |U| e^{-T} + |V| 2^{-T} < 1, the following list s_1, ..., s_t has the two properties below:
- (i) every u is covered;
- (ii) sum_i w_v(s_i) < ceil(2 t m_v) + T <= 2 t m_v + T + 1 for every v.

*The list.* Each s_i minimises Phi_i, where

    Phi_i := sum_u [u not covered by s_1..s_i] * (1 - p_u)^{t-i}
           + sum_v 2^{-(ceil(2 t m_v) + T)} * prod_{j<=i} (1 + w_v(s_j)) * (1 + m_v)^{t-i}.

Every quantity here is rational (p_u, m_v and w_v are rational, and the exponents are integers), so Phi is
computed exactly; Lemma E6 bounds the cost.

*Proof.* Fix s_1..s_{i-1} and draw s uniformly. Then the expectation of Phi_i is Phi_{i-1}. Indeed,
E[covered-indicator complement] = 1 - p_u on an uncovered u, and E[1 + w_v(s)] = 1 + m_v. So the minimiser
satisfies Phi_i <= Phi_{i-1}.

At the start, Phi_0 <= |U| (1 - p)^t + sum_v 2^{-(ceil(2tm)+T)} e^{tm}. Here (1-p)^t <= e^{-pt} <= e^{-T}, and
e^{tm} 2^{-ceil(2tm)} <= e^{tm} 2^{-2tm} = 2^{tm(log2 e - 2)} <= 1. So Phi_0 < 1, and therefore Phi_t < 1.

At the end, every term is nonnegative, so each term is below 1:
- an uncovered u would contribute exactly 1, so every u is covered;
- since 1 + w >= 2^w on [0,1], the v-term is >= 2^{sum_i w_v(s_i) - ceil(2tm_v) - T}, so the sum is below
  ceil(2tm_v) + T. ∎

YL use ordered prefixes, sampled without replacement. E1 uses i.i.d. lists instead, and it gives the same
tail up to the additive 1. Repeated list members are harmless: first fit uses only the first copy, and a
later copy's gates have a zero right side, so they are removed.

## 3. Lemma E2 (explicit window circuit) [proof, given (Y1)-(Y3), (Y6) and Certificate [A]]

Let N be a multiple of q, and let eps' <= 1/20.

*The window* (as in YL Lemma 3.4) is a product X0 x Y0:
- rows with |#1(x) - N/2| <= eps' N;
- queries with |S(y)| = N/2 and |#0(y) - N/4|, |#1(y) - N/4| <= eps' N.

*Construction.* For each type (w, z0, z1), where the row weight is w N, the query has z0 N zeros and z1 N
ones, and z0 + z1 = 1/2:
- **D level.** Build L_D by E1 with T = N^2:
  - candidates: all bN-subsets;
  - U: the queries of the type;
  - V: (row x, mu, theta), with weight w_x(D) := Pr_{Q uniform 2 mu N-subset of the complement of D}
    [#1(x|Q) = theta N].
- **Q level.** For each D in L_D and each mu, build Q_{D,mu} by E1 with T = N^2:
  - candidates: the 2 mu N-subsets of the complement of D;
  - U: its mu N-subsets;
  - V: (pattern on the complement of D, theta), with indicator weights;
  - the length depends only on mu.

Colours are tagged by the type.

*Claims.*
- (i) **Exact** on X0 x Y0: by (Y1) and E1(i).
- (ii) **Right degree** <= 2^{N R(mu,theta)}: by (Y2).
- (iii) **Left degree.** By (Y3) and E1(ii) applied twice, as in YL's derivation,
  deg_L <= sum_{D in L_D} (2 t_Q w_x(D) + N^2 + 1) <= 4 t_D t_Q m_x + 2 (N^2+1) t_Q + (N^2+1) t_D,
  where m_x = E_D w_x(D) is the hypergeometric probability over a uniform 2 mu N-set Q. By the identity
  C(K,k) C(N-K,n-k)/C(N,n) = C(n,k) C(N-n,K-k)/C(N,K) with K = wN, together with C(N-n, .) <= 2^{N-n} and
  C(N, wN) >= 2^{N h(w)}/(N+1), we get m_x <= (N+1) 2^{N(1-h(w))} 2^{-2 mu N} C(2 mu N, theta N).
- (iv) **Lengths.** Lower-bound each binomial in p by 2^{mh}/(m+1), and use t = ceil(T/p) <= 2T/p. Then:
  - t_D <= 2 N^2 (N+1)^3 2^{N E1(z)}, with E1(z) = h(b) - h(z0,a) - h(z1,a) - h(1/2, 1-b-2a);
  - t_Q <= 2 N^2 (N+1) 2^{N(h(1-b,mu) - 2 mu)}.
- (v) **The first term dominates in every window type.** Write the three terms of (iii) in their order there.
  The first is at most 16 N^4 (N+1)^5 2^{N L3}, with
  L3 := E1(z) + h(1-b,mu) - 4 mu + h(2mu,theta) + 1 - h(w).
  - First minus third, in exponent: L3 - E1(z) = h(1-b,mu) - 4mu + h(2mu,theta) + 1 - h(w) >= h(1-b,mu) - 4mu,
    since h(2mu,theta) >= 0 and 1 - h(w) >= 0. This is > 0 for every mu in [a, 2a] (the range of (Y3)):
    mu -> h(1-b,mu) - 4mu is concave, it is >= h(1-b,2a)/2 - 4a at mu = a (concavity with h(1-b,0) = 0) and
    h(1-b,2a) - 8a at mu = 2a, and h(1-b,2a) > 8a (Certificate [A]: the margin is >= 7.26e-4).
  - First minus second: L3 - (h(1-b,mu) - 2mu) >= E1(z) - 2mu >= E1(z) - 4a >= E1(1/4) - 4a > 0, since
    mu <= 2a, and h(z0,a) + h(z1,a) <= 2 h(1/4,a) by concavity of h(., a) (so E1(z) >= E1(1/4)), and
    E1(1/4) > 4a (Certificate [A]: the margin is >= 3.81e-3).
  - The second term is at most 4 (N+1)^5 2^{N(h(1-b,mu) - 2mu)} and the third at most 2 (N+1)^7 2^{N E1(z)}.
    Both exponents are below L3, so deg_L <= 22 (N+1)^9 2^{N L3} <= 48 (N+1)^9 2^{N L3}.
- (vi) **Window loss.** Two effects:
  - the row effect is 1 - h(1/2 + eps') <= (2eps')^2/(2 ln 2 (1 - 4eps'^2)), from the power series;
  - the query effect is E1(z) - E1(1/4) <= eps'^2 a/((1/4 - eps')(1/4 - eps' - a) ln 2), by Taylor's theorem
    (d^2/dz^2 h(z,a) = -a/(z(z-a) ln 2), and the first order cancels because z0 + z1 = 1/2).

  Call the sum eps_win. The certificate evaluates it with the certified bound ln 2 >= 0.6931.
- (vii) **Volume.** There are at most (N+1)^2 colours and at most (N+1)^3 types. So

      Upsilon_window(tau) <= 48 (N+1)^14 2^{N(V(tau) + eps_win)} <= 2^{N(Vbar(tau) + eps_win + eps_poly)},

  with eps_poly := (5 + 15 log2(N+1))/N, since 48 <= 2^5 (N+1).

*Cost.* Lemma E6.

## 4. Lemma E3 (explicit hole fixing) [proof]

For a flip f in {0,1}^N, the map x -> x xor f, y -> y xor f (on S(y)) preserves P_{N,1/2}. A pair (x, y) is
covered by f iff x xor f is in X0 and y xor f is in Y0. Since x xor f and (y xor f)|S are uniform when f is,
Hoeffding's bound shows that at most 2^N (2e^{-2eps'^2 N} + 2e^{-4eps'^2 N}) flips miss a given pair.
Transitivity is not used.

Greedy set cover: repeatedly take the flip that covers the most uncovered pairs. By averaging over f, each step
covers at least a (1 - delta) fraction of the uncovered pairs, where delta := 4e^{-2eps'^2 N}. After J steps, at
most 2^{2.5N} delta^J pairs remain uncovered. So J = floor(2.5N/(2 eps'^2 N log2 e - 2)) + 1 flips cover
everything (the certificate uses log2 e >= 1.4426, certified). The cost is in Lemma E6.

Then (L) gives an exact coloured circuit C3 for P_{N,1/2} with
Upsilon_C3(tau) <= 2^{N(Vbar(tau) + eps_V)}, where eps_V := eps_win + J/N + eps_poly.

*Alternative [arg].* Interval flips (Hobby-Rice) plus a rectangle-partition protocol, with no
inclusion-exclusion. This would make the hole term about 1/eps' instead of 1/eps'^2. It is not needed here:
at the design of Sec. 6 the hole term J/N0 is about 9e-25.

## 5. Lemma E4 (three-piece rebalancing with an effective constant) [proof]

*Family.* Take three circuits:
- (M, I), with Upsilon_1(tau) = C(N,N/2)^tau <= 2^{N v1(tau)}, v1 = tau;
- (I, M), with Upsilon_2 = 2^{N v2(tau)}, v2 = (1-tau)/2;
- C3, with Upsilon_3 <= 2^{N v3(tau)}, v3 = Vbar + eps_V.

Put c := min(v1, v2, v3).

*Hypotheses, checked by Certificate [A].*
- Put tau1 := the crossing of v3 with v1, and tau2 := the crossing of v3 with v2. The certificate checks
  0 < tau1 < 1/3 < tau2 < 1.
- Vbar is convex, so v3 - v1 and v3 - v2 are convex. Hence c = v1 on [0, tau1], c = v3 on [tau1, tau2], and
  c = v2 on [tau2, 1].
- Write A := {0, tau1, tau2, 1} (that is, tau_0 < tau_1 < tau_2 < tau_3) and c_i := c(tau_i). The chord
  slopes s_i := (c_i - c_{i-1})/(tau_i - tau_{i-1}) satisfy s1 > s2 > s3. This is AL25 Lemma B.3's
  condition 2; condition 1 holds by construction.

*Rule.* At a node of remaining depth d and weight lambda, put ell := log2 lambda / (N d). Choose the piece t
with x_{t} <= ell < x_{t-1}, where x_0 = +inf, x_3 = -inf, and x_1, x_2 are dyadic rationals within a
quarter of the gap of the midpoints (s1+s2)/2 and (s2+s3)/2. Use circuit t (1 = (M,I), 2 = C3, 3 = (I,M)).

*Claim.* For all D and lambda, G_D(lambda) <= D_inf sum_{tau in A} 2^{N D c(tau)} lambda^{1-tau}, with
log2 D_inf <= N (d*(r_max + 2) + 4). Here (all per coordinate):
- Delta := min_i(tau_i - tau_{i-1}) * min_i(s_i - s_{i+1})/4;
- r_max := max over t and tau in A of v_t(tau) - c(tau);
- d* := floor(r_max/Delta) + 1;
- and N Delta >= 1 is assumed (Certificate [A]).

*Proof (AL25 Lemma B.3, in the tau-form; this corrects AL's exponent swap, AUDIT_YELI D1).* Put
f_tau(d) := 2^{N d c(tau)} lambda^{1-tau}. Then log2 f_{tau_i} - log2 f_{tau_{i-1}} = (tau_i - tau_{i-1}) N d (s_i - ell).

By the rule, every tau in A outside {tau_{t-1}, tau_t} has f_tau(d) <= 2^{-N d Delta} * f at the nearer of
those two points:
- on the left, s_j - ell >= (s_{t-1} - s_t)/4 for every j <= t-1;
- on the right, s_j - ell <= -(s_t - s_{t+1})/4 for every j >= t+1.

Now induct, with D_0 = 1, since 1 + lambda = f_0(0) + f_1(0). Using (Y4) and the hypothesis for depth d-1,

    G_d <= D_{d-1} sum_{tau in A} Upsilon_t(tau) 2^{N(d-1) c(tau)} lambda^{1-tau},

because sum_zeta a (lambda b/a)^{1-tau} = Upsilon_t(tau) lambda^{1-tau}. At the endpoints of piece t we
have Upsilon_t <= 2^{N c}. At the other points of A, Upsilon_t <= 2^{N r_max} 2^{N c}. So
D_d <= D_{d-1} (1 + 2^{1 + N(r_max - Delta d)}). Summing the logarithms:
- each term with d <= d* is at most N r_max + 2, since 1 + 2^{1+x} <= 2^{2+x} for x >= 0;
- for d > d*, r_max - Delta d < -Delta (d - d*), so the terms sum to at most
  (2/ln 2) sum_{j>=1} 2^{-N Delta j} <= (2/ln 2)/(2^{N Delta} - 1) <= 2/ln 2 < 4, since N Delta >= 1.

∎

*Degrees.* Take lambda := 2^{ceil(N D (dL' - dR'))}. The certificate checks c(tau) <= tau dL' + (1-tau) dR' + eps_V
on A. Then every term of the claim is <= 2 * 2^{N D (dL' + eps_V)}. Hence:
- deg_L <= 8 D_inf 2^{N D (dL' + eps_V)};
- deg_R <= G/lambda <= 8 D_inf 2^{N D (dR' + eps_V)}.

*Exact arithmetic.* The rule compares log2 of a product of integer degrees with a dyadic rational. This is
done exactly, by raising both sides to the dyadic denominator, in poly(N D) bit operations.

## 6. Lemma E5 (explicit PM) [proof, given (Y4), (Y5)]

*Setup.*
- N0 := k(k+2) = k^2 + 2k, with k even and q | N0. (The windows need q | N0, not q | k. With q = 10^26 = 2^26 5^26
  and k = 2m, q | 4m(m+1) iff 2^24 5^26 | m(m+1). As m and m+1 are coprime, each prime power divides one of
  them, which leaves four residue classes of m modulo 2^24 5^26. The least m > 0 among them has 5^26 | m and
  2^24 | m+1, giving k = 10045215487480163574218750 ~ 1.0045e25 and N0 ~ 1.0091e50.)
- The base family is the one of E4 at N = N0, built by E2 and E3 and stored as adjacency lists, sorted by row
  and by query.

*Enumerators.*
- For a row of P_{k^2 D, 1/2}, list its (k+1)^{kD} Lemma 3.1 descriptions, form each embedded row of
  M^{⊗D}, and walk the E4 tree depth first. At each node apply the rule, list the stored gates of the chosen
  circuit that are incident to the current block, and recurse with the child weight.
- For a query, do the same with its single description.
- Padding to n'' = k^2 ceil((n'+2)/k^2) is as in YL Cor. 3.2.
- Cor. 3.3 then counts exactly.

*No dead branches.* Every row and every query of P_{N0,1/2}^{⊗j} has a 1. So in any exact circuit for it,
every row and every query has an incident gate. Hence every partial path extends to a gate, and the walk
costs O(D) times the number of gates it reports.

*Exponents per coordinate of k^2 D.*
- eps_L = 2dL'/k + (1 + 2/k) eps_V + log2(k+1)/k;
- eps_R = 2dR'/k + (1 + 2/k) eps_V.

*Constants independent of n.* Each is a stated number:
- rebalancing: 8 D_inf <= 2^{4855 N0} (Certificate [A]);
- padding: n'' - n' <= k^2 + 1 coordinates, each multiplying a degree by at most 2 (every degree exponent per
  coordinate is below 1), so a factor <= 2^{k^2+2} <= 2^{N0};
- storage access: the stored family has at most 2^{3 N0} records of at most 4 N0 bits (Lemma E6), so one lookup
  by binary search costs at most 3 N0 comparisons of 4 N0 bits, 12 N0^2 <= 2^{N0} bit operations per reported
  gate.

So the run-time constant is C_run <= 2^{(4855 + 1 + 1) N0} = 2^{4857 N0}.

**Certificate [A]** (`cert_explicit.py`), at k = 10045215487480163574218750 and eps' = 10^-13:
- k is even and 10^26 | N0; ln 2 >= 0.6931 and log2 e >= 1.4426;
- YL's parameter conditions hold, E1(1/4) - 4a >= 3.81e-3 and h(1-b,2a) - 8a >= 7.26e-4;
- Lemma E6's hypotheses: H(b) <= 0.0745 <= 1/10, 1 - b <= 1/100, J <= N0/8,
  15 + 31 log2(N0+1) + log2 J <= 0.49 N0, Vbar(0) + eps_V <= 1/2;
- J = 8.665e25 and eps_V <= 8.88e-25;
- tau1 = 0.331682606, tau2 = 0.501373046; the structure and secant checks pass;
- Delta >= 6.19e-4 per coordinate (N0 Delta >= 1), r_max = 1, d* = 1616, and log2(8 D_inf) <= 4855 N0;
- **eps_L <= 9.26e-24 and eps_R <= 9.86e-25, both <= 10^-9.** [proof by exact computation]
- c = 4855 + 3 = 4858, and n0 = 2 c N0 / g <= 5.89e59 (Sec. 8).

Must-fail controls, each rejected:
- [C1] k = 115940: grouping too costly;
- [C2] eps' = 1e-4: window loss too large;
- [C3] eps' = 1e-27: no valid J;
- [C4] dR' lowered by 1e-11: the secant check fails;
- [C5] the D_inf bound lowered by 50;
- [C6] k = 10^25: q does not divide N0;
- [C7] the claim H(b) <= 0.07 (its certified lower bound exceeds 0.07).

## 7. Lemma E6 (preprocessing cost) and the proof of Theorem E

**Lemma E6 [proof, bit-operation model: an add or compare of B-bit integers costs B, a multiply B^2].**
Assume H(b) <= 1/10, 1 - b <= 1/100, J <= N/8, 2^15 (N+1)^31 J <= 2^{0.49 N} and Vbar(0) + eps_V <= 1/2 (all
certified at N = N0). Then building E2, E3 and (L), and sorting the adjacency lists, costs at most 2^{4N} bit
operations, and the stored family has at most 2^{3N} edges.

*Proof.* Polynomial factors are written as powers of (N+1).
- *Rationals.* In one run of E1, write every term of Phi_i over the common denominator
  Lambda := |S|^t (prod_mu Den_mu)^t 2^{2t+T}, where Den_mu <= 2^N is the denominator of the weights of colour
  mu (a binomial coefficient) and |S| <= 2^N. Every p_u, m_v and w_v(s) is a fraction over |S|, |S| Den_mu or
  Den_mu, so every term is an integer over Lambda. Since T <= t, Lambda has at most
  tN + tN(N+1) + 2t + T <= 3N^2 t bits. Each term is at most 4^t (as prod(1+w) <= 2^t and (1+m)^t <= 2^t),
  and Phi has at most 2^{2N} terms, so every numerator has at most B := 4 N^2 t bits.
- *One run of E1.* At step i, the coefficients (1-p_u)^{t-i} and 2^{-(...)} prod(1+w_v) (1+m_v)^{t-i} are
  recomputed by at most t multiplications each, and each candidate s is scored by |U| + |V| multiply-adds. Over
  the t steps this is at most t (t + |S|) (|U| + |V|) * 2 B^2 bit operations. The weights w_v(s) (hypergeometric
  ratios) and the coverage tests cost (N+1)^8 per pair (v, s) or (u, s), which is dominated.
- *D level.* Per type, t_D <= 2N^2 (N+1)^3 2^{N h(b)} (since E1(z) <= h(b)), |S| <= 2^{N h(b)},
  |U| <= 2^{1.5N} and |V| <= 2^N (N+1)^2: this is the |V| ~ 2^N N^2 term. With B = 4N^2 t_D the run costs at
  most 2^{11} (N+1)^{26} 2^{N(4 h(b) + 1.5)}. There are at most (N+1)^3 types, so the D level costs at most
  2^{11} (N+1)^{29} 2^{1.9 N}.
- *Q level.* Per (type, D, mu), every one of |S|, |U|, |V|/(N+1) and t_Q/(2N^2(N+1)) is at most 2^{(1-b)N},
  so one run costs at most 2^{11} (N+1)^{20} 2^{5(1-b)N}. There are at most (N+1)^4 t_D such runs, so the Q
  level costs at most 2^{12} (N+1)^{30} 2^{N(h(b) + 5(1-b))} <= 2^{12} (N+1)^{30} 2^{0.15 N}.
- *Window gates.* Summing (vii) at tau = 1 and tau = 0, the window circuit has at most
  2^N Upsilon(1) + 2^{1.5N} Upsilon(0) <= 2^{N(1 + 0.01)} + 2^{N(1.5 + 1/2)} <= 2^{2N+1} edges. Each right
  column is produced by the sum over the at most 2^{aN} sets U of YL's formula, so the gates cost at most
  (N+1)^4 2^{aN} 2^{2N+1} <= (N+1)^4 2^{2.01 N}.
- *Hole fixing (E3).* Each of the J greedy steps scores 2^N flips against at most 2^{2.5N} pairs, with
  (N+1)^2 bit operations per membership test: at most J (N+1)^2 2^{3.5 N}.
- *Assembly (L) and storage.* The 2^J - 1 copies each transport and restrict at most 2^{2N+1} edges at (N+1)^2
  bit operations per edge: at most (N+1)^2 2^{J + 2N + 1}. The stored family therefore has at most 2^{J+2N+1}
  <= 2^{3N} edges (as J <= N/8), and sorting it costs at most (N+1)^3 2^{J+2N+1} * 3N.
- *Total.* Every line is at most 2^15 (N+1)^31 J 2^{3.5N} or smaller, and 2^15 (N+1)^31 J <= 2^{0.49 N}, so
  the sum of the seven lines is at most 7 * 2^{3.99 N} <= 2^{4N}. ∎

So c_b <= 4, in the stated model. A word-RAM implementation changes this only by a polynomial factor in N0,
which the 2^{0.01 N0} slack absorbs.

**Proof of Theorem E.** DET2-E is S2's DET2, with PM := the PM of Lemma E5 at the design of Certificate [A].
- **Correctness.** As in S2 Lemma 5.3: it uses only that PM counts exactly (Cor. 3.3), which holds for any
  exact circuit.
- **Time.** By (S), with eps = 10^-9 >= max(eps_L, eps_R) and C = C_run <= 2^{4857 N0}, S2 Certificate 7.2
  gives a run time of at most 2^{4857 N0} poly(n, L) 2^{E n}, with E <= 0.4999983316 ([A]) or
  E <= 0.4999983345 ([B]).
- **Preprocessing.** It is input-independent and is added once: at most 2^{4 N0} (Lemma E6).
- **Total.** 2^{4 N0} + 2^{4857 N0} poly 2^{E n} <= 2 * 2^{4857 N0} poly 2^{E n} <= 2^{4858 N0} poly 2^{E n}.
  So c = 4858: the additive preprocessing costs one unit of N0, not 4.
- **Explicitness.** k, eps', T, every list (E1), the flips (E3) and the rule (E4) are computed. No step
  asserts existence without construction. ∎

## 8. Growing N0, and the trade-off

The construction works at any k with q | k(k+2). Certificate [T] tabulates eps_m = max(eps_L, eps_R) at the
best grid eps'. It also gives the balanced gain g = (xi' - 2eps_m)/(12 + 2(xi' - 2eps_m)) (S2 Lemma 7.1 with
slack eps_m) and n0 := 2 c N0 / g, beyond which the constant 2^{c N0} costs at most half of g.
- **YL's (a, b), q = 10^26 [proof for the numbers].** At k = 10045215487480163574218750: eps_m = 8.7e-24,
  g = 1.66667e-6, c = 4858, n0 ~ 5.9e59.
- **D4 rationals a = 1/2635, 1 - b = 1/110, q = 115940 [CONDITIONAL].** This needs an interval
  certificate of xi at those (a, b). AUDIT_YELI D4 reports xi = 2.00340e-5 in floating point, and Vbar must be
  recomputed. The rows use YL's anchors, so they are approximate.
  - There is no gain below k ~ 3.7e6, where the grouping term log2(k+1)/k dominates.
  - At k = 3.7e6 (N0 = 1.4e13): g = 5.2e-7, n0 ~ 2.6e23.
  - At k = 1.5e7: g = 1.36e-6, n0 ~ 1.6e24.
- **Rate [arg].** eps_m(N0) = Theta(log N0 / sqrt N0): the grouping term is log2 k / k with k ~ sqrt N0, and
  the window and hole terms balance at eps' ~ N0^{-1/4}, giving O(N0^{-1/2}). Choosing
  N0(n) ~ (n log n)^{2/3} balances the loss against the construction constant c N0/n. The exponent is
  then 1/2 - xi/(12 + 2xi) + O((log n)^{2/3} n^{-1/3}). Any N0(n) -> infinity with N0(n) = o(n) gives the limit
  1/2 - xi/(12 + 2xi) ~ 0.4999983333 (with xi' = 2e-5). Faster growth is impossible: the stored base has
  >= 2^{N0} rows.

## 9. What is not proved here

- Cited: YL Sec. 3.5's exactness and its right-degree and left-degree reductions, YL Lemma 3.1, Lemma 3.4's
  tree recursion, Cor. 3.3, and the Sec. 4 anchors (all audited in AUDIT_YELI); and S2. The two dominance
  inequalities are now certified, not cited.
- [arg] items:
  - the D4 rows of [T] are conditional;
  - the rate in Sec. 8;
  - B7 is mentioned only as an alternative.
- Lemma E6 is a proof in the stated bit-operation model; it is an operation count, not an implementation.
- The certificate checks the arithmetic; the toy test (Sec. 10) checks the constructions at N = 8 only.

## 10. Toy test (`../certificates/toy_explicit.py`)

At N = 8, a = 1/8, b = 1/2 and eps' = 1/8 (9 window types), exact integers and rationals throughout:
- **E1 + E2.** Every D-list and Q-list is built by Lemma E1 with the ceil exponent. Phi_0 < 1, Phi never
  rises, every constraint is covered, and every sampling sum is below ceil(2tm) + T. The Ye-Li gates give
  L R = M on all 182 x 980 window pairs and 0 off it. The right degree meets (Y2) in every colour (tight), and
  the left degree meets E2(iii)'s bound.
- **E3 + (L).** Greedy flips: J = 6, and every step covers at least (1 - delta) of the uncovered pairs. The
  63 signed restricted copies, multiplied out over all 256 x 1120 pairs of P_{8,1/2}, equal M, and no colour's
  degree grows.
- **E4.** (a) A depth-2 tree for M (x) M with root C3 and children chosen by the threshold rule is exact on
  4000 sampled pairs (2000 of them ones), and deg_L + lambda deg_R <= G_2(lambda). At N = 8, C3 lies above
  min(v1, v2) everywhere, so the rule only picks trivial pieces there. (b) The three-piece claim is therefore
  also tested on a family in which C3 is on the hull (the YL-shaped family of `ye-li-audit/yl_rebalance.py`): for d <= 14
  and 41 values of lambda, G_d <= D_d sum_A 2^{N d c} lambda^{1-tau}, with the induction's D_d.
- Must-fail controls: dropping every D that fits one query, or every Q that contains one U, breaks exactness;
  the unsigned sum of copies differs from M; and the E4 bound with D_d := 1 is violated.
- The run takes about 25 s and 200 MB.

## 11. Lean

`../lean/SubsetsumLean/Explicit.lean` kernel-checks Certificate [A]'s inequalities and its controls, without
`sorry` or `native_decide`. `../lean/LEAN_SCOPE.md` lists what is kernel-checked and what stays on paper.

## 12. Improvement: a sharper rebalancing constant [proof; certificate `../certificates/cert_explicit_b16.py`, its inequalities Lean-checked (Sec. 13.8)]

This section is separate from Theorem E, whose statement (c = 4858) stays as certified and kernel-checked above.
It re-derives this improvement and certifies it at design [A].

**Lemma E4' (per-pair form of E4).** Same family, rule and A as E4, with fixed dyadic thresholds x1, x2. For
piece t and an off point tau_j of A, let delta_{t,j} be the least value, over piece t's threshold region of ell,
of the chord sum sum_i (tau_i - tau_{i-1}) |s_i - ell| between tau_j and the nearer endpoint of piece t (it is
attained at the threshold nearer to tau_j, as the sum is linear in ell there), and r_{t,j} := v_t(tau_j) - c(tau_j).
Assume v_t <= c at piece t's endpoints, every delta_{t,j} > 0, and N min delta >= 1. Let
d1 := max over r_{t,j} > 0 of floor(r_{t,j}/delta_{t,j}) + 1 and S := sum_{d=1}^{d1} max_{t,j} (r_{t,j} - d delta_{t,j})^+.
Then log2(8 D_inf) <= S N + 2 d1 + 6.

*Proof.* E4's induction, keeping each off point separately: at depth d the off-point term is at most
2^{N r_{t,j}} f_j(d) <= 2^{N(r_{t,j} - d delta_{t,j})} f_near(d), so
D_d <= D_{d-1} max_t (1 + sum_j 2^{N(r_{t,j} - d delta_{t,j})}). There are at most two off points, so each factor
is at most 3 * 2^{N max_{t,j}(r_{t,j} - d delta_{t,j})^+}; for d <= d1 this contributes at most
N max(...)^+ + log2 3. For d > d1, r_{t,j} - d delta_{t,j} < -delta_min (d - d1), and the factors multiply to at
most 2^{(2/ln 2)/(2^{N delta_min} - 1)} <= 2^3. Adding 3 for the factor 8 gives the claim. ∎

**Padding and storage, sharpened.** A padded coordinate multiplies the PM time by at most 2^{dR' + eps} <= 2^{1/2},
so padding costs at most 2^{(k^2+2)/2}; one storage lookup costs at most 12 N0^2 bit operations.

**Certificate [B16]** (`../certificates/cert_explicit_b16.py`, exact rationals, at design [A]): x1, x2 dyadic (2^-40) within a
quarter of the slope gaps; all six delta_{t,j} > 0 (the least is 0.0012); d1 = 3; **S = 0.496664**, so
log2(8 D_inf) <= 0.496664 N0 + 12 (E4: 4855 N0). Then log2 C_run <= 0.996664 N0. Controls: S <= 0.49 and
thresholds placed at the slopes themselves are rejected.

**Consequence.** The run time is at most 2^{4 N0} + 2^{0.9967 N0} poly(n, L) 2^{E n}, with the same E. The
preprocessing 2^{4 N0} is additive and paid once, so it must not be multiplied by the gain.

**Definition of n0 (Secs. 12 and 13).** Let 2^B bound the build (B = c_b N0, c_b = 4), C the multiplicative
run-time constant and g := 1/2 - E the gain. Then

    n0 := max(2 (B + 1)/(1 - g), 2 (log2 C + 1)/g).

For n >= n0, both 2^B and C 2^{E n} poly(n, L) are at most 2^{(1/2 - g/2) n - 1} poly(n, L). So the run time is
below **2^{(1/2 - g/2) n} poly(n, L)**: n0 is where the constant has used up at most half of the gain. It is *not*
where the run time reaches 2^{E n}, which happens only as n -> infinity. Here n0 <= 1.21e56 (with g >= 1.6667e-6,
below 1/2 - 0.4999983316; the run time is then below 2^{0.4999991667 n} poly(n, L)). Theorem E's accounting gives
5.9e59. As a single multiplicative constant, C_E = 2^{(4 + o(1)) N0}, i.e. c ~ 4 instead of 4858.

**Not folded into this section.** B17 (A9's halving splitter in place of YL Lemma 3.1, N0 = q) and A19 (a ladder of base
lengths) change Lemma E5's reduction itself. They are written out in Sec. 13 (refereed twice, fixes applied).

## 13. Smaller n0 (the small-q + POS variant) [certificate `../certificates/cert_explicit_b17.py`, its inequalities Lean-checked (Sec. 13.8); two clean referees, fixes applied]

This section is separate from Theorem E (Secs. 0-11) and from Sec. 12. Each variant below is a different explicit
algorithm with its own exponent E, its own constant and its own n0. n0 is Sec. 12's threshold,
n0 := max(2 (B + 1)/(1 - g), 2 (log2 C + 1)/g), with g = 1/2 - E, B = c_b N0 (c_b = 4, Lemma E6; the build is
additive and paid once) and C the multiplicative run-time constant. The ladder rows add two things: B = c_b N0 + 1
(the Delta and tail circuits, 13.6) and a third term (T0 + q)/pi (every PM length must hold the ladder, 13.6).

**Read each row as a pair (E, n0).** For n >= n0 the run time is below 2^{(1/2 - g/2) n} poly(n, L) (last
column), and it approaches 2^{E n} only as n grows. A smaller n0 comes with a *weaker* E: the two cannot be mixed.

| variant | N0 | E <= | gain g >= | n0 <= | for n >= n0, time < | label |
|---|---|---|---|---|---|---|
| [A'] YL (a, b), Lemma 3.1', E3, E4's constant | 10^26 | 0.4999983345 (S2 7.2[B]) | 1.6655e-6 | 5.84e35 | 2^{0.4999991672 n} | [proof] |
| [A'] same, B16's constant (Sec. 12) | 10^26 | 0.4999983345 | 1.6655e-6 | 1.20e32 | 2^{0.4999991672 n} | [proof] |
| D4 (q = 115940), Lemma 3.1', E3 | 2.4e11 | 0.4999994073 | 5.927e-7 | 8.18e17 | 2^{0.4999997036 n} | [proof] |
| D4, Lemma 3.1', POS union (13.5) | 1.2e8 | 0.4999989913 | 1.0087e-6 | 2.35e14 | 2^{0.4999994956 n} | [proof] |
| D4, Lemma 3.1', POS, ladder (13.6) | 3.8e9 | 0.4999983549 | 1.6451e-6 | 1.59e11 | 2^{0.4999991774 n} | [proof] |
| q = 2664, Lemma 3.1', E3 | 3.6e11 | 0.4999992172 | 7.828e-7 | 9.11e17 | 2^{0.4999996086 n} | [proof] |
| q = 2664, Lemma 3.1', POS | 8.7e7 | 0.4999992295 | 7.706e-7 | 2.26e14 | 2^{0.4999996147 n} | [proof] |
| q = 2664, Lemma 3.1', POS, ladder | 3.5e8 | **0.4999985715** | 1.4285e-6 | **4.90e10** | 2^{0.4999992857 n} | [proof] |

**Headline, stated correctly.** The smallest n0 is **4.90e10, and it goes with E <= 0.4999985715** (gain
1.43e-6; time below 2^{0.49999929 n} poly(n, L) for n >= 4.90e10). At Theorem E's exponent E <= 0.4999983345 (S2
7.2[B]), the smallest n0 proved here is **1.20e32** (the [A'] row with Sec. 12's constant). The ladder rows do not
reach that exponent: their eps_m (1.5e-7 at D4, 1.4e-6 at q = 2664) costs 2.0e-8 and 2.4e-7 in E.

The small-q rows use S2 Lemma 6.1 with a general threshold gamma (13.7); all rows use E2-E6 as written, re-checked at
each new N0 and (a, b). Every number is printed by the certificate (exact rationals, exit 0, 9 must-fail controls),
which also checks each table row's E and n0 as upper bounds.

*Referee fixes (2026-10-11, two independent clean referees N1 and N2; verdicts CONFIRMED or CONFIRMED WITH FIXES,
no defect that changes a certified number).*
- (G1, N1-1 / N2-D4) The headline paired n0 = 4.9e10 with the wrong exponent; n0 was described as where the run time
  reaches 2^{E n}. Now every row is an (E, n0) pair and n0's meaning is stated (above, and Sec. 12).
- (G2, N2-D4) Sec. 12 and Sec. 13 had different n0 formulas (a "+2" in one only). Both now use the one definition
  of Sec. 12, derived from "each term at most half the bound".
- (G3, N2-D5) The ladder's conditions are in n0: n' + 2 >= T0 + q (third term (T0 + q)/pi), and the build of the
  Delta and tail circuits (B = c_b N0 + 1, all built once, up front; 13.6).
- (G4, N1-5) Lemma P2 now states that C_W must compute M_W exactly everywhere, zero off the window (13.5).
- (G5, N1-6) The walk-cost bound for the M_W pieces no longer uses E5's "no dead branches" (13.5).
- (G6, N1-7) Lemma 3.1'(a) needs |S(y)| = n'/2 exactly; S2 Lemma 3.2 gives it, and the padding keeps it (13.2).
- (G7, N1-4) "log2 C <= 0.6 N_min + ..." was wrong at q = 2664 (it is 0.94 N_min, N_min = 13 q). The bound is now
  stated per row (13.6).
- (G8, N2-D6) Lemma E4'' states u_{i,t} at every point of A, including when (I, M) stands in for piece 2 (13.6).
- (G9, N1-2 / N2-D1) `../certificates/cert_explicit_b17.py` loads `cert_eps.py` from its own directory (here `../certificates/cert_eps.py`, S2's own certificate).
- (G10, N1-3 / N2-D2) The false label "n0 with E4 <= 6e29" is gone; the certificate now tests n0 <= 5.84e35.
- (G11, N2-D3) YL's table match is certified at the stated 2e-17 (it was checked only to 1e-12).

### 13.1 Lemma 3.1' (halving splitter with the canonical-member rule) [proof]

*Statement.* Let n' = sum of leaf sizes G_1, ..., G_D, all even, and fix a binary tree T with these leaves. Let F be
the family of "members": a member chooses, at every internal node U of T (|U| = u, left subtree of total size w),
an offset i in [0, u), and sends the w cyclically consecutive elements of U starting at its i-th element to the left
child and the other u - w to the right child (children keep the induced cyclic order). Then:
- (a) for every query y with |S(y)| = n'/2 there is a member under which every leaf j holds exactly G_j/2 positions
  of S(y). The *canonical member* m(y) takes, at each node in preorder, the least such offset; it is computed in
  O(n' depth) time;
- (b) |F| = prod over internal nodes of u. For D equal leaves G and the floor/ceil halving tree,
  log2 |F| <= (D - 1) log2 G + (9/4)(D - 1) - log2 D <= D (log2 G + 9/4);
- (c) if C is a circuit for P_{G_1,1/2} (x) ... (x) P_{G_D,1/2} (exact, or POS as in 13.5), then C' with gates (m, e),
  L'[x, (m, e)] := L_C[pi_m x, e] and R'[(m, e), y] := [m = m(y)] R_C[e, pi_m y], is a circuit of the same kind for
  P_{n',1/2}, with deg_R(C') <= deg_R(C) and deg_L(C') <= |F| deg_L(C). Here pi_m reorders the coordinates leaf by
  leaf.

*Exactly half (the hypothesis of (a)).* (a) needs |S(y)| = n'/2 exactly, while S2's PM interface (S) allows
||S(y)| - n'/2| <= 1. The queries S2 actually builds have exactly n'/2 specified positions (S2 Lemma 3.2), and
the padding of 13.2 keeps this. So (a) applies to every query PM receives.

*Proof.* (a) Induct down the tree; at a node U with |S cap U| = u/2 put f(i) := |S cap window_i|. One cyclic step
removes one element and adds one, so |f(i+1) - f(i)| <= 1, and each element lies in exactly w of the u windows, so
the average of f over i in [0, u) is w (u/2)/u = w/2, an integer. So f takes the value w/2 (discrete intermediate
value theorem on the cycle), and the rest then holds (u - w)/2 positions of S. (b) Put T(m) := sum over internal
nodes of log2 m_v (m_v = leaves below v). Claim T(m) <= (9/4)(m - 1) - log2 m: m = 1 is trivial, and the step from
floor(m/2), ceil(m/2) needs m^2/(floor(m/2) ceil(m/2)) <= 2^{9/4}; the left side is 4 for even m and at most 9/2 for
odd m, and 2^{9/4} > 4.75. Then log2 |F| = (D - 1) log2 G + T(D). (c) Under m(y) every leaf is a half-stars query, so
pi_{m(y)} y is a column of the product; matching is coordinate-wise, so M(pi x, pi y) = P(x, y), and only member
m(y) meets y on the right. ∎

**GOTCHA (the breaking site is the right side of (c)).** A query must use ONE member, m(y). If it used every
balancing member, the count of a pair would be multiplied by the number of balancing members, which varies with y:
the circuit is then not exact (it is still POS, 13.5). Rows are tagged by member and meet a query only under m(y).

The certificate checks (a) exhaustively for leaf sizes (4,4,4), (4,4,4,4), (6,4,2,2), (8,4,2) (0 failures; with
offset 0 only, failures appear: control K3) and (b)'s inequality as an integer inequality for D <= 400 (with 2 in
place of 9/4 it fails at D = 3: control K4).

### 13.2 Lemma E5' (the reduction at N0 = q) [proof, given (Y4), Cor. 3.3]

E5 changes in three places; everything else (the base family of E4 at N = N0, the depth-first walk, no dead
branches, Cor. 3.3) is as written.
- *Setup.* N0 is any multiple of q (the windows need only q | N0; E2's 4 | N comes with q = lcm(4, ...)). There is no
  k: Lemma 3.1 needs N0 = k^2 + 2k, i.e. N0 + 1 a square, which fails at N0 = 10^26 (control K1).
- *Padding.* Pad once, to n'' := N0 ceil((n' + 2)/N0) (as YL Cor. 3.2, with N0 for k^2), so n'' - n' <= N0 + 1, and
  D := n''/N0. Each padded coordinate costs at most 2^{1/2} (Sec. 12), so padding costs <= 2^{(N0+1)/2}.
  n' is even (n' = 2m - 2j) and so is n'', so n'' - n' is even. Every row gets 0 on the padding; every query gets
  '0' (specified, always matching) on half of the padding and '*' on the other half. So the padded query has
  exactly n''/2 specified positions, as Lemma 3.1'(a) needs, and matching is unchanged.
- *Grouping.* Lemma 3.1' with D leaves of size N0 replaces Lemma 3.1. The groups are no longer padded from k^2 to
  k^2 + 2k, so the terms 2dL'/k, 2dR'/k and the factor (1 + 2/k) disappear, and log2(k+1)/k becomes
  (log2 N0 + 9/4)/N0:

      eps_L = eps_V + (log2 N0 + 9/4)/N0,        eps_R = eps_V.

  The row enumerator lists every member (|F| <= 2^{n''(log2 N0 + 9/4)/N0}, each in poly(n) time) and walks the E4
  tree on pi_m x; the query enumerator computes m(y) and walks once.
- *Constant.* C = 8 D_inf * 2^{(N0+1)/2} * 12 N0^2, with log2(8 D_inf) <= L_D N0 (E4) or S N0 + 2 d1 + 6 (Sec. 12).

### 13.3 Every condition re-checked at N0 = q = 10^26, YL's (a, b) (Certificate [A']) [proof by exact computation]

- q | N0, 4 | N0 (and q does not divide 5e25: control K2); ln 2 and log2 e bounds; YL's parameter conditions; both
  Sec. 3.5 dominances (margins 3.81e-3, 7.26e-4); Lemma E6's H(b) <= 1/10 and 1 - b <= 1/100.
- eps' = 2e-7, J = 2.17e13 <= N0/8, and E6's numeric hypotheses (15 + 31 log2(N0+1) + log2 J <= 0.49 N0,
  Vbar(0) + eps_V <= 1/2).
- eps_V = 3.32e-13; the three-piece structure, the dyadic thresholds, all delta_{t,j} > 0, the secant check with S2's
  pair (dL', dR'), N0 Delta >= 1 and N0 min delta >= 1.
- eps_L, eps_R <= 3.33e-13 <= 1e-9, so S2 Certificate 7.2 applies verbatim: E <= 0.4999983345 ([B]; [A] gives
  0.4999983316 with the table's xi).
- L_D = 4855, S = 0.496664, d1 = 3. n0 <= 5.84e35 with E4's constant and <= 1.20e32 with B16's, both with E <= 0.4999983345 (Theorem E: 5.9e59;
  Sec. 12: 1.21e56).

### 13.4 Small q: certifying xi is required, and it holds [proof by exact computation]

*Required.* E2(vii) bounds the volume by Vbar, the two-segment function through V(0), V(1/2), V(1) at the circuit's
own (a, b). (Y6) supplies these only at YL's (a, b). At D4 the anchors differ, and S2's pair (dL', dR') fails the
secant check against them (control K5): it is not admissible for the D4 circuit. So new anchors and a new pair
are needed, and S2 must be run with the new xi'.

**Lemma V (anchors by concavity).** For rational (a, b) satisfying YL's conditions, V(tau) = tau E1(1/4) +
(1 - tau)(b - 1/2 + 2a) + max_K f_tau, with f_tau := tau l + (1 - tau) r, l := h(1-b, mu) + h(2mu, theta) - 4mu,
r := h(a, mu-a) + h(mu, theta-mu), and K := {a <= mu <= 2a, mu <= theta <= 2mu}. Since h(u, v) = u H(v/u) is the
perspective of a concave function, h is jointly concave, so f_tau is concave on K, and for any x0 at which f_tau is
differentiable,

    max_K f_tau <= f_tau(x0) + max over the four vertices v of K of grad f_tau(x0) . (v - x0).

*Proof.* The first-order condition of concavity, and a linear function on a polygon peaks at a vertex. ∎

The certificate encloses every log2 by exact series (60 terms) and uses x0 = (5a/3, 5a/2) at tau = 0 (gradient 0),
a float Newton point at tau = 1/2, and the vertex (2a, 2a) at tau = 1 (where 1 - b > 10a makes the gradient point
out of K). Each anchor is rounded up to the grid 10^-18, and the tau = 1/2 point to the grid a * 10^-15, so the
numbers are short rationals. Validation at YL's (a, b): each bound is >= the table value and within 2e-17 of it
(certified at 2e-17; the largest difference is 1.83e-17).

| (a, 1-b) | q | anchors <= | pair (12 places, rounded up) | xi'' |
|---|---|---|---|---|
| D4 (1/2635, 1/110) | 115940 | 0.492649114629, 0.249979138138, 0.007614630691 | (0.007312448730, 0.492647483328) | 2.003397e-5 |
| (1/2664, 1/111) | 2664 | 0.492712073011, 0.249979140283, 0.007548534581 | (0.007249488875, 0.492710444464) | 2.003333e-5 |

Both satisfy YL's conditions, both dominances (D4: 3.85e-3, 7.31e-4) and E6's H(b), 1 - b conditions. So **xi'' >=
2.0033e-5 holds at both** (the claim xi'' >= 2.004e-5 is rejected: control K6). This closes Sec. 8's "CONDITIONAL"
and B17's block 2. It does not certify YL's own table: (Y6) is still cited for [A'].

### 13.5 POS: hole fixing as a plain union, placed after the tree [proof, given (Y4)]

**Lemma P1 (S2 needs only a POS counter).** Call a circuit POS for a 0/1 matrix P if L, R are integer and L R >= 0
with supp(L R) = supp(P). With a POS circuit, Cor. 3.3's sum equals sum over keyed pairs of (L R)[x, y], which is
>= 0 and is > 0 iff some keyed compatible pair exists, on every sublist. S2 uses PM only through Lemma 5.3 (a count
> 0 gives a compatible keyed pair; a kept solution gives a count >= 1) and Cor. 2's bisection (positivity on
sublists). Both hold verbatim. Coefficients stay below 2^{O(n)}. ∎ [proof, by inspection of S2 Lemma 5.3 and Cor. 2;
S2's interface (S) then reads "PM returns a nonnegative integer, positive iff a keyed compatible pair exists".]

**Lemma P2 (union after the tree).** Let W = X0 x Y0 be E2's window at length N, M_W := P_{N,1/2} restricted to W,
and F E3's greedy flips (J of them, covering every pair). Build E4's tree on the three pieces (M_W, I), C_W (E2's
window circuit, no E3 copies), (I, M_W): by (Y4), applied to the matrix M_W, it computes M_W^{(x)D} exactly, i.e.
P^{(x)D} on X0^D x Y0^D and 0 elsewhere. For f = (f_1..f_D) in F^D let copy_f be the tree conjugated by f (flip row
bits and specified query bits). Then sum_f copy_f = P^{(x)D} * prod_i #{g in F : (g x_i, g y_i) in W}, which is POS
because F covers every block pair. Degrees grow by at most J^D on each side. ∎

*Exactness everywhere, not only on the window.* (Y4) is applied to the matrix M_W on all of {0,1}^N x Y, so each of
the three pieces must compute M_W exactly there, including 0 at every pair off W. E2(i) states exactness only on
X0 x Y0. Off W it holds because E2 builds gates only for window types (w, z0, z1): a left gate of type
(w, z0, z1) is incident only to rows of weight w N, and a right gate only to queries of that type. So a row outside
X0 or a query outside Y0 has no incident gate of C_W, and C_W gives 0 there, as M_W does. (M_W, I) and (I, M_W)
are M_W itself on one side.

*Walk cost (replaces E5's "no dead branches" for these pieces).* E5 bounds the depth-first walk by the gates it
reports, because in an exact circuit for P^{(x)j} every row and query has a 1, so every partial path extends. That
fails here: M_W has zero rows (every x outside X0), so a partial path can die. Bound the partial paths instead. A
partial path of depth j is a gate of the depth-j tree incident to the current row (or query), so their number is at
most E4's bound at depth j. That bound, D_j sum_A 2^{N j c(tau)} lambda^{1-tau}, is nondecreasing in j (D_j is,
c >= 0, and the depth-0 bound G_0 = sum_A lambda^{1-tau} >= 1 from tau = 1). So the walk visits at most (D + 1) G_D
partial paths, a factor D + 1 = poly(n) over E5's bound, times J^D for the union. The same argument covers the
ladder (13.6), with E4'''s bound in place of E4's.

**GOTCHA (the breaking site is (Y4)'s colour recursion).** (Y4) writes M (x) M' = sum over colours of M_zeta (x) M',
with SIGNED colour classes M_zeta; it needs every child circuit to compute M' exactly. If the children were POS, the
signed classes would make entries negative (A12's counterexample). So every piece must be exact on the window
product, and the union must come after the whole tree. Lemma 3.1' comes after the union.

*Accounting.* eps_V^{POS} := eps_win + eps_poly (no J/N0 term), and the union adds log2 J/N0 per coordinate to both
eps_L and eps_R. So eps' can be ~1e-4 at N0 ~ 1e8, where E3 would need J/N0 small. Lemma E6 holds without its (L)
assembly line (the J <= N/8 hypothesis is no longer used). E3 at the POS design's N0 gives no gain (control K7).

### 13.6 A19: a ladder of base lengths [proof for the POS small-q variant; the rest downgraded]

**Lemma E4'' (level-dependent tree).** Let the tensor levels have lengths N_1, ..., N_L (root first), level i with
its own pieces C_{i,1}, C_{i,2}, C_{i,3} for P_{N_i,1/2} (exact on level i's window, as in 13.5) and
Upsilon_{i,t}(tau) <= 2^{N_i u_{i,t}(tau)} on A. Keep E4's anchor set A, c, chord slopes and dyadic thresholds from
the N0 family, and let the rule at a node of level i use ell := log2 lambda / l_i, where l_i := N_i + ... + N_L.
Put omega_{i,t} := max over t's endpoints e of (u_{i,t}(tau_e) - c(tau_e))^+. Then
G <= prod_i phi_i * sum_{tau in A} 2^{l_1 c(tau)} lambda^{1-tau}, with

    phi_i := max_t ( 2^{N_i omega_{i,t}} + sum over t's off points j of 2^{N_i (u_{i,t}(tau_j) - c(tau_j)) - l_i delta_{t,j}} ).

*Every point of A, every piece.* u_{i,t} must be defined, and bound Upsilon_{i,t}, at all four points of A, not only
at t's endpoints; the off points enter phi_i. For the window circuit, u is Vbar + eps_V(N_i) (E2(vii)). For
(M, I) and (I, M), u is tau and (1 - tau)/2 (their exact volumes). When (I, M) stands in for piece 2 on the Delta
level, its off-point values are its own: u - c = 1/2 at tau_0 = 0 and 0 at tau_3 = 1, so u - c <= 1/2 per coordinate
there. The certificate charges N_sw/2 bits for this, which is valid; its endpoint overshoot is (1 - 3 tau1)/2 (at
tau1; 0 at tau2).

*Proof.* (Y4)'s recursion is level by level, so a different family per level changes nothing in its proof. Put
f_tau(l) := 2^{l c(tau)} lambda^{1-tau}; then log2 f_{tau_i}(l) - log2 f_{tau_{i-1}}(l) = (tau_i - tau_{i-1}) l (s_i - ell),
so at the chosen piece t each off point satisfies f_j(l_i) <= 2^{-l_i delta_{t,j}} f_near(l_i) (Sec. 12's per-pair
argument with N d replaced by l_i). The inductive step gives sum_tau Upsilon_{i,t}(tau) 2^{l_{i+1} c(tau)}
lambda^{1-tau} = sum_tau 2^{N_i (u - c)(tau)} f_tau(l_i); endpoint terms are at most 2^{N_i omega} f_tau, and each off
term is a multiple of an endpoint's f; collecting gives the factor phi_i. ∎

*Design (certified).* D main levels of length N0, then a level of length Delta in qZ cap [0, N0) chosen from n (it
removes the padding: n'' - n' <= q + 1, so padding costs <= (q+1)/2 bits), then a tail N_j := q floor(N0 (3/4)^j / q)
while E6's hypotheses hold (T0 := sum of the tail ~ 3 N0).
- Main levels: l >= T0 + N0 and every pair has r/delta <= 2.08 < 3, so their factors multiply to < 2 (checked:
  max(N0 r - T0 delta) <= -64).
- Tail levels: pieces 1, 3 are exact (omega = 0); piece 2 is the POS window circuit at N_j with e' = 2^{-s}, so its
  overshoot is N_j (eps_V(N_j) - eps_V(N0)) bits; each tail level also adds log2 J_j (union) and one splitter node
  (<= log2(5 N0) bits).
- The Delta level: for Delta >= N_sw = 2^K (K least with E6's hypotheses and Vbar(0) + eps_V <= 1/2 uniformly), a POS
  window circuit at length Delta; below N_sw, (I, M) in the role of piece 2 (overshoot (1 - 3 tau1)/2 per
  coordinate).
- *Build.* Every circuit the ladder can use is built once, up front, before any input is read: the main family at
  N0, the tail circuits, and a window circuit for every Delta in qZ cap [N_sw, N0). So there is no per-n' build at
  run time. Each has a length L that is a multiple of q below N0, and costs at most 2^{4 L} (Lemma E6; the
  certificate checks its hypotheses at each tail length, and uniformly for Delta >= N_sw). Over the distinct
  multiples of q up to N0 - q this is at most 2^{4 (N0 - q)}/(1 - 2^{-4q}) for the tail and the same for the Delta
  circuits, together at most 2^{4 N0}. The whole build is at most 2^{4 N0 + 1}: B = c_b N0 + 1.
- *Length.* The ladder needs room: n'' = D N0 + Delta + T0 with D >= 0 and padding n'' - n' <= q + 1 requires
  n' + 2 >= T0 + q. S2 calls PM only with n' = 2m - 2j >= m > pi n - 2 (S2 Step 0 and Lemma 3.2, j <= m/2), so
  n >= (T0 + q)/pi suffices. This is the third term of n0 for the ladder rows; it does not bind (4.6e10 at D4 and
  4.2e9 at q = 2664, against n0 = 1.59e11 and 4.90e10).
- Lemma 3.1' with the tree [main block | Delta | tail chain] gives the main block's D (log2 N0 + 9/4) bits per Lemma
  3.1'(b), one node of size n'' (a poly(n) factor), and the chain.

*Result.* D4: N0 = 3.8e9, log2 C <= 1.30e5 bits (rebalancing + union 7.09e4 = 0.612 N_min, with N_min = q; padding
5.8e4), E <= 0.4999983549, g = 1.645e-6, **n0 <= 1.59e11**. q = 2664: N0 = 3.5e8, log2 C <= 3.5e4 (rebalancing +
union 3.25e4 = 0.939 N_min, with N_min = 13 q; padding 1.3e3), E <= 0.4999985715, g = 1.4285e-6, **n0 <= 4.90e10**.
Without the tail the single-scale constant is 0.4967 N0 (control K8).

*Labels kept honest.*
- Lemma E4'' and the POS small-q ladder rows: [proof] (certified).
- A19's stated rate "log2 C = O(log^2 N0)" holds only in N0 for fixed q: here log2 C is dominated by O(q) (the bottom
  of the tail and the padding), not by log^2 N0. [proof, per certified row only: the rebalancing + union bits are
  0.612 N_min (D4) and 0.939 N_min (q = 2664), plus (q+1)/2 for padding and the chain. No general bound of the
  form c N_min is claimed; the O(log^2 N0) shape alone is A19's [arg].]
- A19 with E3 hole fixing (the "O(sqrt N0)" row): not certified; [arg].
- A19 at YL's (a, b): NOT available. Every level length must be a multiple of q = 10^26 = N0, so there is no tail
  without A18's rounding, which is [arg]. A19's 8e26 row is therefore [arg].

### 13.7 What changed in S2, and the weakest step

- The small-q rows use S2 Lemma 6.1 with gamma := 2(xi' - 2 eps)/3 (instead of 2 xi'/3), pi just below
  3/(12 + 2(xi' - 2 eps)), the new pair, and eps := max(eps_L, eps_R) ~ 1e-7 to 6e-6 (instead of 1e-9). Lemma 6.1's
  proof is symbolic in gamma, pi, eps and the pair (gamma enters only as the few-sums threshold, Steps 2 and 6;
  Lemma 3.5 needs only dL', dR' >= 0 and dL' + dR' <= 1/2 - 2 xi'). Then E = max of Lemma 6.1's terms, computed
  exactly. [proof, by inspection of S2; S2 Certificate 7.2 itself is not re-run with these parameters.]
- Weakest steps, in order: (1) this reading of S2 Lemma 6.1 and Lemma 5.3 with new constants and a POS counter (by
  inspection, not by S2's owner); (2) Lemma P2's placement of the union after the tree (proved here, but only A12's
  toy has exercised a POS assembly at gate level; our toy test does not cover it, though referee N1's gate-level toy
  at N = 4 (depth 2, union after the tree, Lemma 3.1' with the canonical member) found no violation in 6000 pairs); (3) Lemma V uses YL's V formula at
  a new (a, b), i.e. (Y2)-(Y3) for general rational (a, b), which YL state but which we have tested only at their own
  point and at N = 8.
- None of this changes Theorem E or Sec. 12.

### 13.8 Lean

`../lean/SubsetsumLean/ExplicitN0.lean` and `ExplicitAnchors.lean` (generated by `../lean/gen_explicit_n0.py`, with
definitions in `ExplicitN0Defs.lean`) kernel-check the inequalities of `../certificates/cert_explicit_b16.py` and
`../certificates/cert_explicit_b17.py`, without `sorry` or `native_decide`, and every theorem uses only `propext`,
`Classical.choice` and `Quot.sound`. Lean recomputes every number from the inputs (the rounded anchors, x0, and each
row's N0 and e'): Sec. 12's S, d1 and n0; [A']; every table row's E and n0, with the ladder's tail and switch length;
and S2 Lemma 6.1's terms with the real log2 3. Lemma V's tangent bounds are checked as real inequalities with the
real log and binary entropy. The controls D1, D2, K1, K2 and K4 to K9 are proved false (K7 for every e' of the grid).
On paper only: the lemmas themselves (that the formulas are the costs), Lemma V's concavity step and YL's V formula
at a general (a, b), and Lemma 3.1'(b) beyond D = 400. The splitter's exhaustive check [G] and K3 stay in Python
(`../lean/LEAN_SCOPE.md`).
