# Closed ideas

These are routes to deterministic Subset Sum faster than meet-in-the-middle that we examined and found do not work.
Each row gives the reason. A closure holds only inside its stated model or route. None of them is a lower bound for
Subset Sum in general. An idea that breaks a stated hypothesis is not covered by its row.

**Status labels.**
- [proof]: a complete argument.
- [cert]: an exact or interval certificate.
- [exp]: a decisive toy experiment.
- [arg]: a short argument, not written as a full proof.

**Contributing.** If you find a mistake in a closure, or an idea that escapes one of the stated hypotheses, please
send the argument. Corrections will be credited.

## 1. Derandomising the 2^{0.489995 n} construction (openai/math #138)

| idea | why it fails | status |
|---|---|---|
| Listing aliases one by one, made deterministic | The number of aliases is about 2^n/P, and this must be <= 2^{tau n}, so the modulus has eta >= 1 - tau > 1/2. Any deterministic check per frequency or per residue mod P then costs >= 2^{eta n} > 2^{n/2} | [proof] |
| Exact counting modulo deterministically chosen moduli, then removing aliases and false hits | Subtracting aliases needs M >= 2^{(1-tau) n}. Exact counting of one residue class mod M costs >= min(nM, 2^{n/2}) by every known method (DP over residues, MITM counting, M Fourier frequencies). CRT does not help: the bin count mod M is not a function of the bin counts mod its factors | [arg] |
| The 3SUM greedy-chain trick (prime-at-a-time with an exact counting oracle) | It needs a polynomial-size query set and a counting oracle. Here the queries are the 2^{n/2} half-sums, and the oracle is the bin count itself, so the route is circular | [arg] |
| Deterministic isolation by a poly-size list of poly-bounded weightings | Isolating every family needs at least n / log2(n N0) weightings. Split [n] into that many blocks, and in each block pick A_j ≠ B_j of equal weight (pigeonhole). The family of all choices then defeats every weighting. The checksum would stay randomized in any case | [proof] (lower bound) |
| "P' has only about 0.057 n bits, so exact counts are cheap" | 0.057 n is the block size, and P' has about 0.028 n bits. Exact class counts by DP control the cost, but they do not show that the unknown alias hits the chosen class. That needs the universal covering, at 2^{0.085 n}. So P', the block and the filter can be derandomised, but the checksum walls above still stand | [arg], [exact] |

## 2. Covering choices inside the derandomisations

| idea | why it fails | status |
|---|---|---|
| Stage 2: one covering of the translates of the prefix-sum set, reused in every layer | The layer of a hit depends on the prefix c_pre, so the covering must range over pairs (c_pre, shift) | [exp] toy control `sigma` of `certificates/check_stage2.py`: 42 misses |
| Stage 1 / Stage 2: a single best residue, or a covering of one shift (y = 0) only | It misses solutions | [exp] controls `single` and `oneshift` of `certificates/check_stage1.py` and `certificates/check_stage2.py` |
| Stage 2: Ye–Li's own prefix n/3 with the deterministic covering | The covering costs 2^{2m} = 2^{2n/3} > 2^{n/2}. The prefix must stay below n/4 | [cert] control C3 of `cert_eps.py`, `stage2_C3` in Lean |
| Stage 2: prefix exactly n/4 | The covering then costs 2^{n/2}, so there is no saving | [cert] control C2, `stage2_C2` |
| Stage 1: CJRS's printed rounding (0.1579, 0.2427) | g < 0.0101 there, so the stated value needs the exact roots or a better rational point | [cert] C1, `stage1_C1` |

## 3. Templates that cannot give Stage 2

| idea | why it fails | status |
|---|---|---|
| Global-representation templates (the RW26 kind) | Their certificates need eps-sparse danger, which a worst-case instance need not have | [arg] |

**Notation for Secs. 4 to 16.** Stage numbers are those of the README. "Record 3" is the unpublished reduction of Ye
and Li's project that Stages 4 to 5b port to a deterministic algorithm (README, Credits; only its number 0.4996645 is
public). On that route, D1 is Stage 4's estimator, with one filter residue per round; D2 is a variant in which rounds
share residues. xi is the partial-match circuit gain, mu the block fraction, alpha the core fraction and kappa the layer.

## 4. Stage 2 route: the residue covering (Ye-Li at s = 1/2)

| idea | why it fails | status |
|---|---|---|
| A Fourier / small-bias certificate in place of the greedy residue covering of the layer key sets | At a fixed layer, sum over nonzero frequencies of the key set's Fourier mass, divided by its size, grows like 2^{0.4m} (257 to 782 from m = 12 to 16, near a random set's value even for powers of 2). Certifying hits for all shifts then needs a residue set of size about 2^{0.8m}. The tempting sign-free bound min_r r^{-k} prod \|1 + r e(theta_i)\| is invalid: Cauchy needs the max over \|x\| = r, and off the real axis the factors are not symmetric | [float] + [arg]; the invalidity is [proof] |
| Moving the solution's sign pattern by prefix flips (negating z_i on a set f) | The flipped instance's layer keys are a translate of the original ones, which shift-universality of the covering already handles; nothing is gained | [proof] |
| Choosing the covering digit by digit or prime by prime (the 3SUM chain technique) so that it costs 2^m | The potential (number of uncovered (prefix pattern, shift) pairs) does not factor over CRT digits. The prefix-averaged potential is computable in 2^m poly, but it certifies coverage only for most prefixes, and the solution's prefix is adversarial. Retrying on several prefix blocks does not help: the adversary picks a bad pattern per block | [arg] |
| A weaker prefix filter, modulus p = N 2^{-eps m}, to cheapen the covering | The balance point moves the right way, but the main term gains +eps pi, so the exponent increases with eps at eps = 0 | [arg] |
| An interval (or Bohr-set) class set R = [0, L) mod p in place of the greedy covering | R hits every translate iff the key set's max cyclic gap is <= L. On the two-scale family (z = 2^i on half the coordinates, B 2^i on the rest) the normalised gap grows like 2^{0.4m} (7.1 at m = 8, 75.1 at m = 16), against ln-scale for random sets. Bohr sets repair one scale, but multi-scale inputs need many frequencies, and certifying those for every prefix is enumeration again | [exp] + [arg] |
| Any covering certified by checking each restriction's key set separately | Such a check costs at least the sum of the key-set sizes over all restrictions, about 2^{2m}/poly. Beating it needs a cover correct by proof for every Hamming-sphere sum set mod p, a worst-case Fourier-uniformity statement that is not available (square-root cancellation is not known; Cauchy-Davenport is additive; the pigeonhole A + B = Z_M forces M <= 2^{m/2}) | [arg] (barrier) |
| A c-independent representation set (every a in a fixed set is a representation of every c), so the covering costs 2^m and the prefix can pass n/4 | The cover picks some representation whose layer is not chosen, so the split must be common to all layers, and layers above density 1/2 appear. With the generous hull of known circuits, the best common split gives excess exactly 0, i.e. plain meet-in-the-middle, for every m | [float] within the known circuit families + [arg] |
| Middle grounds between c-dependent and c-independent covers: complement pairs; a covering-radius certificate per shift; a second-moment DP over differences | Complement pairs force C x C to hit every 2y-translate, so \|C\| >= sqrt(p) (filter density 1/sqrt(N)). A covering radius (1/2 + delta)m costs 1.985 delta m, forcing delta < 1e-5 and about 1e10 hits. The second-moment DP certifies only a 1 - 1/mu fraction of patterns | [arg] |
| Beating xi/4 on the Stage 2 template (one prefix representation filter, universal covering, partial-match gain xi) | Two-sided: a c-dependent key set costs >= 2^{2m}/poly to certify (row above), so m <= n/4 and gain <= xi/4, which outer dedupe attains; a c-independent one gives gain 0 (row above). On dissociated instances the many-sums cost is exactly 2^{n/2 - xi m}. Beating xi/4 needs a saving that is not a prefix representation filter | [arg] (barrier) |
| A deficient prefix makes the covering cheaper | The key sets for all c can be computed by a signed DP in 2^{2m - d(P)} poly, but the worst case is d = 0, so the 2^{2m} term stands | [arg] |
| Two prefix filters with moduli p p' (CRT) | Coverage of the sumset of the two key sets needs a universe of size 2^{2m} p p': the same wall at prefix 2m | [arg] |

## 5. Stage 2 route: dichotomy and dedupe

| idea | why it fails | status |
|---|---|---|
| A meet-in-the-middle few-sums branch that splits the deficient prefix between its two sides | By superadditivity of deficiency it saves at most (d(P1) + d(P2))/2 <= gamma m/2, half of what is needed. Choosing the least deficient sub-block instead scales the gain down with the block | [proof] |
| The four-block dichotomy (deficient blocks kept whole on each side), gain xi/(6 + 2 xi) | Correct, but superseded and strictly worse: outer-sum dedupe drops the dichotomy and reaches xi/(4 + 2 xi) (E <= 0.4999949918 against 0.4999966627 at Ye-Li's xi) | [cert] (exact rationals) |
| A cheaper residue covering (prefix up to n/3) with any meet-in-the-middle few-sums branch | With MITM few-sums the class ceiling is xi pi/(1 + 2 pi), which is xi/6 at pi = 1/4 and still xi/6 at pi = 1/3 (n/3-blocks cannot tile both halves). Under outer dedupe the fit pi < 0.2509 coincides with the covering wall, so a cheaper covering would also need an unbalanced split | [arg] |
| Deduping the PREFIX (block) parts by sum, as well as the outer parts | Rows and queries must keep the prefix parts: merging by prefix sum loses compatibility options. Dedupe is safe only outside the prefix | [arg]; on the Record 3 route the controls in Sec. 9 detect it |
| A native density-s partial-match circuit in place of padding layers to density 1/2 | Layers with s < 1/2 already save (1 - h(s))/2 through the binomial, and the padding transfer gives G_s >= G_{1/2}, so the max over layers sits at s = 1/2, where no padding is used. The worst case is unchanged. This closure is for the Stage 2 reduction, where the layer density is the adversary's; it does not apply to Record 3, where the circuit density is a design choice | [float] + [arg] |

## 6. Stage 2 route: the circuit gain xi and rebalancing

| idea | why it fails | status |
|---|---|---|
| Rebalancing beyond Alman-Li's Thm B.2 within the tree-of-colour-lists model | Their DP is the minimum over all per-node adaptive choices, and weak duality gives F_d >= Upsilon(tau)^d lambda^{1-tau}, attained up to 2^{o(d)}. No rebalancing that is a tree of the family's colour lists beats it | [proof], given Alman-Li Thm B.1 |
| L. Ye's quenched-Lyapunov "scripted rebalancing" (arXiv 2603.15565) as a source of extra xi | Its recursion is one circuit from a finite family per node with a scalar, clamped skew state: a tree of colour lists, so the row above applies (clamping restricts the model). Its gain over Alman-Li comes from a larger base family, not from rebalancing | [arg] |
| A finite family of circuits in the rebalancing step pushing xi past its members' V(1/2) | For any family containing the two trivial circuits, xi <= (OR benchmark at s) - min_t V_t(1/2). Positive superset-cover circuits attain this ceiling; nothing in the family can exceed it. (At s = 1/2 the family is worth +1.5%; on Record 3's route the same ceiling is 1.6x the single circuit, see Sec. 8) | [proof] (the ceiling) |
| Nesting a Ye-Li circuit for the bulk D in place of their (I, M) | Valid, but worth +0.02%: nesting must lower V(1/2), the inner density s' is pushed above 1/2 where its own gain vanishes (2.2e-6 at Ye-Li's s' = 0.5038, 0 at 0.51), and the outer gain falls as fast as the inner rises. An earlier x1.29 reading was an interpolation artefact | [float] + [proof] |
| Refining colours inside a lookup set Q by a fixed split Q = Q' u Q'' | The worst U is balanced for the split, and there the refined max of L + R equals the unrefined one (concavity of h) | [arg] |
| Small-coefficient (bounded) exact partial-match circuits as a route to large xi | A gamma_2 (factorisation-norm) bound gives dL + dR >= 0.3774 at s = 1/2 for coefficients 2^{o(n)}, i.e. xi <= 0.061. As a barrier this is far above the current xi, so spectral methods cannot cap xi near its value; large coefficients and positive circuits escape it anyway | [proof] (closed form checked against SVD for n <= 8) |
| A SUP-model circuit ((LR)_{xy} != 0 iff M_{xy} = 1) inside a deterministic Stage 2 | The keyed count sums signed nonzero entries over many pairs and can cancel to 0 on a yes-instance. Random rescaling repairs this only with randomness; the Hadamard square restores positivity but doubles both exponents. Deterministic use needs exact or positive (POS) circuits | [arg] |
| List-of-points lower bounds (Andoni-Laarhoven-Razenshteyn-Waingarten; Ahle-Knudsen) as a new barrier | They bound positive circuits only, where the classical nonnegative bound already gives V_POS(1/2) = 1/4; signed circuits are outside their model | [arg] |

## 7. Stage 2b (explicit Stage 2): constructions and constants

| idea | why it fails | status |
|---|---|---|
| A computer search for a small explicit base circuit | Ye-Li need integer windows with a ~ 1/2635 (N' >= ~1e5 before slack), the grouping overhead needs k ~ 6.6e7, and nonnegative circuits have dL + dR >= 1/2 at every size (classical nonnegative-rank bounds), so a small base must cancel. Explicitness has to come from derandomising the proof | [arg] (barrier) |
| Hole fixing by independent random flips, union-bounded over pairs, with a small copy count | Any such proof needs J = Omega(1/eps'^2) copies; with a quadratic window loss this forces N' = Omega(1/eps^2). A route barrier, not a circuit lower bound | [arg] |
| Exact-window hole fixing (eps' = 0) by greedy flip coverage plus the Alman-Li rectangle recursion | The per-query copy count grows like 2^{0.9N} (8 copies at N = 4, 126 at N = 8): with an exact window one flip hits a pair with probability ~N^{-1/2}, and the recursion fragments the queries | [exp] |
| Plain splitter (block-product) lookup families for Ye-Li Sec. 3.5 | Size is fine, but per-row colour balance fails: a row can contain a chosen block set in many blocks, so the excess over the stratified expectation multiplies up to 2^{2 mu n}. A t-wise splitter makes bad partitions only polynomially rare | [arg]; later made unnecessary by pessimistic-estimator covers |
| Positive (POS) sub-circuits inside Ye-Li Lemma 3.4's colour recursion (union of flip copies before rebalancing) | The colour classes are signed and sum to P; with positive children whose multiplicities differ, entries go negative. Toy: 3 negative entries; a gate-level toy with the union before the tree gives value 26 at a P = 0 entry. The union must come after the tree | [proof by counterexample], [exp] |
| Handling outside-window pairs with a restricted (I, M) positive circuit | It costs (1 - tau)(1/2 - c eps'^2); beating the circuit near tau1 needs eps' ~ 0.06, i.e. a window loss ~1e-2 >> xi | [arg] |
| The rectangle-protocol hole fixing with interval flips (5^{8/eps'} column copies) | Superseded and worse: a Tucker-lemma binary-search protocol is exact with no window loss and 2^{O(log^2 N')} copies; for the decision problem a plain union of interval-flip copies suffices | [arg] |
| Tuning the depth-independent thresholds of the three-piece rebalancing rule | A 40 x 40 threshold grid improves the constant only from 0.4967 N0 to 0.4953 N0 bits. (A depth-1-specific choice does reach 0.3293 N0) | [cert] (exact rationals) |
| "Positive pieces make the one-time rebalancing loss < 1 bit" at a single scale | Wrong at large N0: at the circuit's chord slope the best leaf is a positive line about 2x the hull gap above the tangent, a loss of 3.97e-5 N0 + O(1) bits; the earlier measurement stopped at N <= 4096, where granularity hides the linear term | [arg] + [float] |
| "Adding circuits to the family costs a much larger rebalancing constant" (up to 1.8e5 N with the single-gap rule) | An artefact of using one gap for every off point. Per-pair accounting gives 0.39-0.47 N (sum form) or 0.22-0.33 N (max form) for single, pair, triple and quadruple families alike | [float] |
| Smaller window modulus q (q >= 1/a) to shrink N0 | q >= den(a) >= 1/a and xi peaks at a = 3.75e-4, so q >= ~2400 for xi within 1%; the gain from smaller q is <= 13% | [float] |
| Mixing (M, I) and (I, M) on a trivial tail level to balance the overshoot at the two contacts | The best mixture overshoots 0.002452 per coordinate against 0.002476, a 1% gain; the floor is already within 6% | [proof] (arithmetic) |
| The geometric tail of trivial levels at Ye-Li's (a, b) (n0 ~ 6.6e29) | Superseded and worse at the same exponent: using the certified small-q ladder at a larger N0 gives n0 <= 3.65e11 for E <= 0.4999983345 | [cert] (exact rationals; rests on the certified xi at the small-q pair) |
| Rankin / saddle-point generating-function bounds for the type and colour sums | Inside the window the exponent varies by <= ~1 bit, so count x max is tight for types; the colour summand a^tau b^{1-tau} with 0 < tau < 1 is not a coefficient sum of a product generating function | [arg] |
| Shortening the effective D-list because late members are rarely first-fit | A late member stays first-fit for ~\|U\| p e^{-p i} queries, above the lookup count until i ~ ln(\|U\| p)/p, so rows still see ~0.99 N/p active members | [arg] |
| Widening the window once the type count no longer grows with it | The window loss grows as ~2.9 c bits (c = eps'^2 N) while the flip family's size does not shrink past c > 3/8; the optimum stays at c ~ 0.5, worth <= 1 bit | [arg] |
| Charging the splitter family and the positive flip union less than their multiplicity | Both multiplicities are real: every member's leaf covers every row, and a row sits in a constant fraction of the flip copies. Only the averaging of one-sided costs halves the splitter; the union is two-sided | [arg] |
| "Generating gates on demand moves 2^{aN} into the constant, so c_b ~ 2 is the floor" | Wrong: the window-gate count already contains the W-sum (emissions per colour equal the right-degree bound exactly, ratio 1.000 on toys), and on-demand overhead is polynomial given a first-fit index; c_b = 1.569 | [arg]; toy recount [exp] |
| Making colours one-sided, or merging colours into one with summed degrees | A query's right column spans every U in [A, 2A] through the inclusion-exclusion sign, so it cannot take one colour; merging loses at first order by Hölder, because the left- and right-dominant colours differ | [arg] |
| A first-fit-aware left-degree count | It lowers the lookup count only at theta in {mu, mu + 1}, while the Laplace window spans ~1e4 colours, so the volume gains nothing | [arg] |

## 8. Record 3 route: circuits and families

| idea | why it fails | status |
|---|---|---|
| Record 3's one-pass covering circuit at s = 1/2 (or s >= ~0.2) | Its gain over the OR benchmark is negative from s ~ 0.194 for one circuit (-7.3e-3 at s = 1/4) and from s ~ 0.221 for a continuum family. Ye-Li's 2.0e-5 at s = 1/2 belongs to a different construction (their Sec. 3.5 D/lookup family) | [float] |
| A non-linear cover rule b(m) (or a per-colour optimal block size) on top of a circuit family | +0.74% for a single circuit, but with a rho-family it adds <= 0.06%: the family already reaches the V(1/2) ceiling (Sec. 6, row 3) | [float] |
| Mixed-literal expansions (keep literals on T0 <= Y0, T1 <= Y1, expand the rest) | A strict generalisation of Record 3's gates, whose corner (t0, t1) = (0, k) is the optimum of the class at s = 1/8: every other split lowers the ceiling (0.0063 at t0 = 0.02k down to -0.020 for the x-only expansion); no other local optimum on the full grid | [float] |
| Two-level (weight) gates [x n C = sigma, \|x n (B - C)\| = e] | A row's degree is at least its degree in the plain pattern family on the C's; a term [x >= M] is expressible only if M is inside C. A weight test helps only on the column's own Y0, which is the exact-pattern circuit (gain 0) | [arg] |
| Averaging the circuit cost over (row weight, query type) cells to RAISE xi | The centre cell has probability >= 1/poly, so the line must still sit above the centre profile. Averaging removes losses (window, flips, union), never adds gain | [proof] |
| Dropping any one member of a certified family, or any one of the six Stage 5b families | Each member alone fails at the other members' contacts; replacing any one of the six families by its single circuit costs 1.0e-5 to 1.5e-4 in E; all single circuits give 0.4991471 | [cert] (controls KF, K7', [NEED], Stage 4+ C3) |

## 9. Record 3 route: rounds and round families

| idea | why it fails | status |
|---|---|---|
| A residue covering per round (replacing each random round's filter by its own universal covering) | In a typical round the solution has only a 2^{-J mu n} fraction of p compatible distinct keys, so a per-round covering needs 2^{J mu n} residues per round and multiplies the main term by that (about 2^{0.025 n} at the deterministic point). Coarsening the filter costs the same. Toy: 98-100 residues per round, 131571 passes against 115 | [arg] + [exp] |
| A group orbit as the deterministic round family | Equal incidence for every layer set K needs a group transitive on (kappa mu n)-subsets with kappa ~ 1/2; by Livingstone-Wagner and the classification of k-transitive groups only A_n and S_n qualify, both far too large. Toy: the Z_16 orbit of one round leaves 5478 of 12870 sets uncovered | [proof] (by citation) + [exp] |
| The first M rounds in lexicographic order | min over K of the coverage count is 0, with 9734 sets below the target | [exp] |
| Repairing the greedy round family's pair statistics by composing with a merely transitive (cyclic) group | Exact round-pair energy at B = 16: x1.086 of random (+0.0074 per coordinate), above the 0.005 kill rule; a 2-transitive affine group gives +0.0001. Single-round orbits are far off under both groups | [exp] |

## 10. Record 3 route: the residue step and the 2^{2 mu n} wall (D1)

| idea | why it fails | status |
|---|---|---|
| Using the key-shift structure (signed sums are a c-shifted subset sum) to break the covering wall | Compatibility is a condition on K, so the usable keys are an XOR-translate of the compatible set, different for each c. A potential over every (c, residue) has output size 2^{mu n} p however it is computed (a Walsh-Hadamard transform over c saves nothing) | [arg] |
| Choosing each round's residue from one global histogram of compatible keys | The potential's universe is (c, y) with y the unknown shift, so weights differ per (c, y) after the first step and every update touches 2^{mu n} p entries | [arg] |
| A sparse two-phase residue estimator (scatter pairs while covered sets are sparse, then uncovered sets) | The covered-sparse phase ends after a 2^{-gamma M} fraction; the uncovered-sparse phase needs sum_f P_f(c) >= (1 - J) M ln 2; the middle ~25% of rounds pay the full cost. No shift-oblivious first phase exists | [arg] |
| A pairwise-independent residue sequence (Ghaffari-Grunau-Rozhon-style estimators) for the residue step | It leaves a 1/L fraction of (c, y) uncovered by Chebyshev; repairing that is again a greedy cover at cost \|U\| per step | [arg] |
| One canonical block part per distinct block sum, shrinking the estimator's universe to N x p | Exact and free, but worth 0: the residue step binds at d = 0 and kappa = 1/2, where nothing shrinks (identical to 9 digits on the certified menu). The sumset structure of S_{c,f} does not shrink the universe either | [proof] + [float] |
| A smaller prime p to lower the residue-step term | It trades the residue step against the filter term one for one, and the filter term's slack is only alpha xi mu | [arg] |

## 11. Record 3 route: estimators with shared residues (D2) and design energy

| idea | why it fails | status |
|---|---|---|
| D2 by one round-independent universal covering of the union of all layer key sets | The key carries a split-dependent shift sum over Hbar of (1 - c_i) z_i, so a hit for one shift is usable only in rounds with that split. Grouping by split leaves J_H = 1 - h(s_bar) (about 45% of J) in the main term or the construction. Balancing the split forces a non-core density t != 1/2 (t = 0.89 at alpha = 1/2, s = 0.11), raising the binding circuit line by ((1 - alpha)/2)(1 - h(t)) mu, about 0.125 mu against alpha xi mu ~ 3.5e-3 mu | [arg]; [float] for the J split |
| One residue shared by all rounds | (c, y) is covered only if r - y lies in the union T_c of shifted keys, and T_c misses residues even for random z (about 16 per c in the toy), so at least p/\|T_c\| residue classes are needed. Toy: fails on all six input families; same-split grouping degrades 2.4x | [exp] |
| Pricing the D2 design energy with the i.i.d. (pooled per-coordinate) product model | Exponentially wrong at Record 3's real parameters: rounds fix all part sizes and per-part counts, so labels are uniform over arrangements of a fixed type, and the exact exponent e_avg (method of types) is <= the i.i.d. one by 0.06-0.09 per block coordinate. Agreement on toys (0.93-1.09) does not transfer, because the toys sit far from the boundary | [proof] (e_avg <= log2 pi_0) + [float] (gap) |
| D2 at s = 0.11 with the residue-step term simply dropped (alpha = 0.5848, E 0.4998081889) | The design energy there is 2^{+0.0094 mu n} for every input, so "E_c R_c <= poly" is false at that point and the dropped term binds. With the constraint certified, the best D2 row is E <= 0.4998083100 at alpha = 0.5665; the constraint is a cliff in alpha (E jumps ~1e-4 at 0.568) | [proof] (exponent) + [cert] (the corrected row); the violation at 0.5848 is a float primal check |
| A tiered estimator without a per-pattern fallback | max over c of the design energy is exponential (+0.016 to +0.024 per block coordinate) at every Record 3 point; only the c-average is polynomial, so the per-c D1 fallback is necessary | [float] |
| The outer-dedupe D2 row at (alpha, mu) = (0.90, 0.2475), saving 9.93e-4 | Infeasible: with p ~ N the design energy enters at d = 0 with excess 1 + e_avg ~ +0.215 at alpha = 0.9, so the residue step is ~0.548 > 1/2 and only the core-free centre design survives (E = 0.5). Re-optimised with the energy as a hard term: E 0.49909187 (saving 9.08e-4) at (0.90, 0.225); D2's edge over D1 shrinks from x1.24 to x1.13 | [float] |
| Any round family, grouping or estimator that pushes the design energy below the random-round value | The agreement kernel W is positive semidefinite, so the family energy is p \|\|mu_G\|\|^2 >= p \|\|P mu_G\|\|^2 = p S_rand for every group (P the symmetrisation, mu_G the kernel mean embedding). Explicit families can at best reach the random value (and one does). Within this reduction it moves only with the label law (alpha, s, kappa) and p | [proof] (barrier); [exp] greedy groups never go below |
| The design-independent bound on the averaged energy (dominate each round by a Bernoulli product) | Exponentially loose: 1 + S* is 4.8-17.4 against 1.05-2.27 for the pooled value, because the core cell's agreement probability (0.625, and 0.78 at s = 1/8) is far above the pooled 0.48; usable only if p <= 2^{0.678 m} | [float] |
| A pointwise Fourier-fooling target (every product test within p^{-1/2}) for the round family | Too strong: random families of the same size miss it on structured z. The energy needs only the L2 (sum over frequencies) form, a pairwise-round statistic | [exp] |
| "max over c of R_c <= 1.13 p/D_min" as a law | False: half-tiny z at m = 20 gives 3.71 against 3.39; only the mean is flat in m | [exp] |

## 12. Record 3 route: dedupe and blocks

| idea | why it fails | status |
|---|---|---|
| Deduping on the block side (one u and one v per key after filtering), or merging block parts with equal keys | Loses compatibility options, hence completeness: 3 wrong answers and 6388 layer-level violations at n = 18; on the Stage 5 brute force the control is detected 15 times | [exp] (controls dedupekey, blockdedupe) |
| A deduped set straddling the u and v sides | Creates pseudo-solutions (4/4 targeted instances) | [exp] (control straddle) |
| Taking the MOST deficient block as P | The outer lists are then not bounded by \|Sigma(P)\|: list-bound violations on 18/36 instances (Stage 5 brute force) and 42 violations at n = 18. P must be the least deficient | [exp] (control mostdef) |
| Dedupe on one side only | E = 0.70 > 1/2 | [cert] (Stage 5 control K4) |
| Outer dedupe with no cores at any layer | E >= 1/2: dedupe alone gains nothing | [cert] (Stage 5 control K3) |
| "With outer dedupe the saving reaches mu alpha xi" for symmetric cores | Without the few/many cut every kappa must be covered; with symmetric cores the off-centre curvature caps the saving at mu xi/2 (second order, attained at kappa ~ 1/2 +- 0.028, alpha = 1/2), whatever alpha is allowed: certified 4.9453e-4 against mu xi/2 = 4.967e-4. The ceiling mu alpha xi needs asymmetric cores | [cert] (controls K6, K6b) + [arg] (closed form) |
| The design set {0, alpha} per layer (global alpha or core-free) | Leaves a gap just past the last feasible menu pair (kappa ~ 0.4485 and ~0.551): the rigorous bound on that design set is about 0.49924, above the printed float 0.49919788. Intermediate alphas per layer repair it | [cert] (control K5b) |
| Two dedupe blocks per outer side | The extra d-bonus (j - 1) mu (1 - h(kappa)) is ~0 at the central binding layer, and the fit (1 - mu)(1/2 - \|w\|) >= 2 mu caps mu: no help for the asymmetric-core rows (it does help the symmetric row R1b) | [proof] (Stage 5) + [float] (Stage 5b) |
| Dedupe blocks Q' smaller than P (to lift the randomized side condition mu <~ 1/3) | Deficiency is superadditive, which bounds big sets by small ones, the wrong direction. On random small-range inputs every M-set is deficient but small sets are not: need 5.03, found <= 1.91 at n = 60. This concerns the randomized row only | [proof] + [exp] |
| Stage 4 Lemma 5.2 (distinct residues) used as written at p ~ N | It assumes p <= \|W_c\|, which fails when N < 2(M + 1) x_0 (nearly constant blocks); hit on 18 brute-force runs. Repaired by the min(p, \|W_c\|) form at no cost | [proof] + [exp] |

## 13. Record 3 route: cores, layers and parameters (must-fail controls)

| idea | why it fails | status |
|---|---|---|
| Record 3's circuit gain with xi = 0 | E >= 1/2 | [cert] (Stage 4 control K3) |
| The deterministic claim at the randomized optimum's parameters, or the randomized number claimed for the deterministic algorithm | The residue step (one estimator step per (c, round)) is too big there; it caps mu near 0.22, against 0.48 randomized | [cert] (Stage 4 controls K6, K9) |
| Doubling delta, or cutting the layer range to \|kappa - 1/2\| <= 1e-3 | Both rejected; the range certificate refuses the narrow range | [cert] (Stage 4 controls K4, K5) |
| Per-piece round families at N_b = 2e7 | lambda = 7.0e-6 and the claim fails | [cert] (Stage 4 control K7) |
| Forcing x' = x (no parity bit) in the round compatibility | A layer with k - a odd has no compatible round and its c is never found | [exp] (control noparity) |
| A single copy of the round family (D = 1) | sum_f \|S_{c,f}\| is only >= p/G and Phi_0 < 1 fails: 712161 pairs (c, y) uncovered | [exp] (control lowmult) |
| Covering the universe {0,1}^M x Z_p instead of C_k x Z_p | Outside C_k nothing guarantees many residues and Phi_0 < 1 fails; in the tight regime pairs outside C_4 stay uncovered | [proof] + [exp] (control dropcover) |
| Non-cyclic windows (no splitter search) | 3230 of 4096 sets unbalanced at q = 3, N_b = 4 | [exp] (control offset0) |
| Swapping s and 1 - s on the u-side core | Layer-level violations | [exp] (control wrongcore) |
| Equal keys without the compatibility check; dropping the few-sums branch (before dedupe) | Wrong answers | [exp] (controls nocompat, nofew) |
| The upper bracket on xi computed through the witness colours' own values | The line need only pass above the trivial lines at the contacts; the earlier brackets were about 3e-8 too small (0.0043428848, 0.0044849401). Found by the Lean check | [cert] |
| Asymmetric cores with an equal outer split, or kappa-adaptive design with s1 = s2 | Both freedoms carry the gain: w = 0 gives E = 0.50256-0.50275, s1 = s2 gives 0.50474, diagonal menu pairs only give 0.50388, a 3-point menu gives 0.49997 | [float] |
| The Stage 4+ pair with the single circuit's xi | E = 0.50005 | [cert] (Stage 4+ control K4) |
| Every (l, r) raised by 0.01; mu raised by 1% | 0.5000000054; 0.4986356679 on the Stage 5b row | [cert] (controls K9, K2) |

## 14. Record 3 route: explicit build (windows and averaging)

| idea | why it fails | status |
|---|---|---|
| Assuming Record 3's circuit has a second-order window loss, as Ye-Li's does | With Stage 4 Lemma 3.3/3.5' as written the loss is first order, ~1.0 eps' (slopes -0.914 and +0.720 in the query type at the contacts): the expansion treats Y1 and Y0 asymmetrically, so no z0 + z1 = 1/2 cancellation. An explicit N0 projection without this term is off by 2-5 orders | [float] |
| Repairing the first-order window loss with a per-query-type rho alone | A linear rho(k1) cancels k1 > s/2 only for C in [34.9, 56.3], and k1 < s/2 needs C outside that range: infeasible; corners stay at +0.09 to +0.24 eps' | [arg]; [float] check |
| "The per-cell (frame, rho) repair leaves a first-order residual 0.003 eps'" | A rho-grid artefact: with a continuous rho search the residual is ~0.35 eps'^2. A first-order LP shows one of the two frames always admits a cancelling rho (except on the tie line 11.0 dw = 21.8 dk) | [float] + [arg] |
| The average-over-types form without per-cell frame and rho | Fails by O(1e-2): naive +3.07e-2, frame only +1.35e-2, dropping the rarity +3.28e-2 at s = 11/100; on the Stage 5b families the identity frame gives +8.8e-4 to +9.6e-4 at r = 4e-3 | [float] (must-fail controls) |
| Memoising each record's degree on the exact rebalancing parameter lambda | The exact lambda leaves ~C(depth + #colours, #colours) states, i.e. a polynomial with exponent 2^{O(N0)}; lambda must be rounded to powers of 2 (loss 1/N0 per coordinate) | [arg] |

## 15. Isolation and generic derandomisation

| idea | why it fails | status |
|---|---|---|
| Isolation for the 2^{0.49n} construction by exact-count weights and adaptive witness finding (Alon-Naor dilute-test-recurse; counting small primes not dividing S) | Both need an exact counting oracle, and that construction's only counter is the randomized checksum, which the walls of Sec. 1 already block; oblivious isolating families are impossible, so only adaptive schemes remain | [arg] |
| A generic randomized-to-deterministic simulation (the L = RL = BPL line of results) | It costs a polynomial blow-up T -> T^c, which destroys every exponent here; the random objects are also not read once | [arg] |

## 16. Literature tools that do not transfer

| idea | why it fails | status |
|---|---|---|
| Alman-Li's Strassen calculus (arXiv 2605.21738) for an effective rebalancing constant | Its Thm 4.1 is Strassen duality with an o(n) term and no bound; the authors say the techniques are not yet effective enough for algorithms | [arg] |
| Fomin-Lokshtanov-Panolan-Saurabh separating collections for explicit coverings | Overhead 2^{O((p + q)/log log(p + q))}, i.e. 1/log log N per coordinate, far above xi | [arg] |
| Explicit near-optimal coverings (Kuzjurin; Gordon-Kuperberg-Patashnik(-Spencer); Grable's NC nibble) to remove the ln factor | All are for fixed block and set sizes, not the linear regime; none is also a per-row sampler | [arg] |
| Explicit balanced or k-wise families (Alon-Gutner, Naor-Schulman-Srinivasan splitters, Burjons-Rossmanith, almost k-wise permutations) as the round family | Each costs 2^{Theta(m)} or more for k-sets with k = Theta(m) (NSS: ~600 extra bits per block against a ~130-bit budget), and none controls a pair statistic across rounds | [arg] |
| Fourier-shape PRGs (Gopalan-Kane-Meka; Lee-Viola) for the round family | They do not keep the K-regularity the residue estimator needs | [arg] |
| Near-linear conditional expectations for sparse covering programs (Chen-Harris, Thm 2.16) to lower the build constant | Per-update cost is linear in the column's nonzeros, exactly the incremental construction already used; it cannot beat c_b = 1.569 | [arg] |
