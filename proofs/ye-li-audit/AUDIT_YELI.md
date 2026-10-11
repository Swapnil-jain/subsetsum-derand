# Adversarial audit: Ye-Li Proposition 4.2 (2026-10-10)

**Target.** Ye and Li, "Subset Sum via Partial Match", arXiv 2610.10446. **v1 is the only version** (7 Oct 2026; the arXiv
abs page was checked on 2026-10-10). The auditor read the full TeX source of v1 (`main.tex`; no ancillary files or code).
The auditor also read the parts of Alman-Li, arXiv 2509.14489 (AL25, FOCS 2025) that Prop. 4.2 imports:
- Appendix A;
- Appendix B, Def. B.1 through Thm B.2, in full;
- the statement and overview of Thm 6.1. The full proof of Thm 6.1 was not read.

No third-party code was run. All scripts here are our own reimplementations, run on the Mac, each under 30 s and under 100 MB.

Numbering in v1 (shared counter per section):
- Def. 2.1: admissible pair.
- Thm 2.2: the reduction.
- Lemma 3.1: block grouping.
- Cor. 3.2: enumeration, which hardcodes the circuit.
- Cor. 3.3: circuit to partial match.
- Lemma 3.4: colored transfer, which covers hole fixing and rebalancing.
- Sec. 3.5: the EXACT_Z circuit.
- Thm 4.1: main theorem.
- Prop. 4.2: the target.

## Verdict

**Prop. 4.2 HOLDS.** No claim-level defect was found. The minor defects below are presentational or concern explicitness; none
of them changes the statement or ξ.

Two imported results were checked only partway:
- AL25 Thm B.2. Statement and proof were read, and the result was tested numerically.
- AL25 Thm 6.1. Only the statement and proof overview were read. A self-contained replacement is given in D2.

Both are in a refereed FOCS paper. Neither is a gap specific to Ye-Li.

**What Prop. 4.2 states, with quantifiers:**
- (δ_L, δ_R) = (0.0072758705596…, 0.4926840589880…) is an admissible pair (Def. 2.1).
- Admissible means: for every ε > 0 there EXISTS a deterministic algorithm that counts keyed half-star partial-match pairs in
  time poly(n + L + log(|A|+|B|)) · (2^{(δ_L+ε)n}|A| + 2^{(δ_R+ε)n}|B|).
- δ_L + δ_R = 1/2 - 2ξ, with ξ = 2.00352261400514…e-5 > 0.00002.

**Consequence for our Stage 2.** The condition Stage 2 was waiting on is met. The deterministic
2^{(1/2 - ξ/(12+2ξ) + o(1))n} = 2^{0.49999833n} algorithm now rests on three things:
- our own reduction, which JUDGE_S1 confirmed with fixes S1-S4;
- Prop. 4.2, audited here;
- AL25 Thm B.2 and Thm 6.1, refereed and used within their stated hypotheses.

Stage 2 uses nothing beyond what Prop. 4.2 states (section 5). One caveat must go into any write-up: the algorithm is
deterministic but **non-explicit**. It hardcodes a constant-size circuit that is only shown to exist, and no feasible search
finds it (section 3). "There exists a deterministic algorithm" is true. "Here is one you can run" is not.

## 1. Dependency chain and status

| step | content | status | evidence |
|---|---|---|---|
| Sec. 3.5, exactness | L R = f_y(x) over Z. Per query, D(y) leaves an zeros and an ones outside. Inclusion-exclusion over U, with A_1 ⊆ U ⊆ A_1 ∪ A_0, and each U assigned to exactly one lookup set Q | **re-derived, correct** | `yl_circuit.py`: exact gate-by-gate product. n = 8: all 420 queries × 256 rows. n = 12: 400 queries × 4096 rows. 0 mismatches. Controls: 'drop' 6720 and 16832 mismatches; 'double' 5696 at n = 12 (vacuous at n = 8, where the greedy lists are partitions) |
| Sec. 3.5, right degree | 2^{(b-1/2+2a)n} C(an,(μ-a)n) C(μn,(θ-μ)n) per colour (μ, θ); one sign (-1)^{μn-an} per colour | **correct** | derivation; `yl_circuit.py` asserts the bound and the sign for every colour (max ratio 1.000, i.e. tight) |
| Sec. 3.5, left degree | Two-level sampling-without-replacement tail Pr[X > 2km + T] ≤ e^{-T}. The argument runs: Maclaurin, then E e^w ≤ 1 + (e-1)m, then Markov, using e - 1 < 2. Three-term bound; uniform D and then uniform Q gives a uniform 2μn-set; central-row hypergeometric bound ≤ (n+1) 2^{-2μn} C(2μn, θn) | **re-derived, correct** | derivation (no numerical test: the bound is asymptotic) |
| Sec. 3.5, volume | The third left term dominates for every colour. This needs E1 := h(b) - 2h(1/4,a) - h(1/2,1-b-2a) > 4a, and h(1-b,μ) ≥ (μ/2a) h(1-b,2a) > 4μ (concavity). V(τ) is a max of affine functions, so it is convex | **correct** | `yl_numbers.py`: E1 = 0.005333 > 4a = 0.001518; min over μ of h(1-b,μ) - 4μ = 7.3e-4 > 0 |
| Sec. 3.5, windows | Per (row weight, query type) circuits, colour-tagged. The right bound is unchanged; the left bound changes by 2^{n(1-h(w))}; continuity | **correct** | derivation |
| Lemma 3.4, hole fixing | Window to full P_{n,1/2}. Holes are 2^{-Ω(ε'^2 n)} fractions of whole rows and columns. Flips and permutations act bitransitively and fix the matrix | **correct as used** (minor D2) | AL25 Thm 6.1 statement: degree × (nm)^{O(1/log(1/ε))} = 2^{O(1/ε'^2)} here, matching Ye-Li |
| Lemma 3.4, tree recursion | deg_L + λ deg_R ≤ Σ_ζ a_ζ F_{d-1}(λ b_ζ/a_ζ). Colours are tensored with their own subtree; max of a sum ≤ sum of maxes | **re-derived, correct** | derivation |
| Lemma 3.4, numerical rebalancing | F_d(λ) ≤ 2^{o(d)} max_τ Υ(τ)^d λ^{1-τ}, Υ = min over circuits | **correct as used** (minor D1) | AL25 Thm B.2 (read). `yl_rebalance.py`: gap (1/d) log F_d - bound → 0 like ~1/d (≤ 0.008 at d = 256) on a Ye-Li-shaped family and 4 random families with straddling lists; weak duality holds |
| Lemma 3.4, final step | With λ = 2^{Nd(δ_L-δ_R)}: deg_L ≤ 2^{Nd(δ_L+ε1)+o(d)} and deg_R ≤ 2^{Nd(δ_R+ε1)+o(d)}, whenever min{V, τ, (1-τ)/2} ≤ τδ_L + (1-τ)δ_R for all τ. Quantifier order: ε1, then k, then d | **correct** | derivation |
| Lemma 3.1 | Sorted cyclic dealing gives W_d - W_1 ≤ k; padding counts lie in [0, 2k]; the left factor is (k+1)^{kd} | **correct** | `yl_grouping.py`: exhaustive over all descriptions for (k,d) in {(2,1..4), (4,1), (4,2), (6,1)}, 0 violations; end-to-end matching at k = d = 2, 0 mismatches |
| Cor. 3.2 / 3.3 | Hardcode one circuit for P_{k^2+2k,1/2}; tensor power; padding n' = k^2⌈(n+2)/k^2⌉ is valid because \|S\| ∈ n/2 ± 1. Exponents: δ_L + 3ε/4, δ_R + ε/2. The keyed count sums per (key, gate) label | **correct** | derivation |
| Sec. 4, numbers | V(0), V(1/2), V(1), μ*, θ* = 4μ/3, τ_±, δ_L, δ_R, ξ. Two-segment convex bound; secant domination | **reproduced to 20 digits** | `yl_numbers.py`: 60-digit decimal recomputation of every table entry. The closed form for V(0) is the same as ours: (2 + log2 6)a = (3 + log2 3)a. Grid cross-check of the anchors (closed form ≥ grid, gap < 1e-7). Secant ≥ min{true V, τ, (1-τ)/2} at 201 values of τ (max excess -8.3e-7) |

ξ = 2.0035226140051e-5. Then 1/2 - ξ/9 + 1e-9 = 0.4999977749 < 1/2 - 1/450000. Thm 4.1's arithmetic is confirmed.

## 2. Quantifiers, constants, determinism, size

- **Quantifiers.** K(1/2) is "∀ε ∃n0 ∀n ≥ n0 ∃ circuit". Lemma 3.4 picks ε1, then k (with q | k, so q | k^2+2k), then d → ∞,
  and AL25's o(d) depends only on the fixed family. That order is consistent. Def. 2.1 is "∀ε ∃ deterministic algorithm"
  and is existential in the algorithm. No quantifier swap was found.
- **Constants.**
  - 4a ≤ 1-b < 1/2 + 2a, 1-b > 10a, and both dominance inequalities hold with margin (`yl_numbers.py`).
  - Ye-Li's statement V(0) = b - 1/2 + (2 + log2 6)a is right: max over θ gives μ, and max over μ of h(a,μ-a) + μ is at
    μ = 5a/3, giving a(1 + log2 3).
  - The middle-anchor quadratic 37μ^2 + (27(1-b) - 10a)μ - 54a(1-b) = 0 re-derives from the stationarity condition
    27/64 (1-b-μ)(2a-μ) = μ(μ-a), and the θ* = 4μ/3 optimum re-derives as well.
- **Deterministic?** Yes, in the sense of Def. 2.1. The partial-match algorithm (Cor. 3.2 + 3.3) is: enumerate gates of a
  fixed hardcoded circuit's tensor power, then sort and sum. No coins. The randomness in Ye-Li is confined to:
  - Thm 2.2's filter and its repetitions, which our Stage 2 replaces;
  - the existence proofs of the circuit: random orderings with a union bound (Sec. 3.5) and random symmetries (hole fixing).
- **Size.** Per record: 2^{(δ_L+ε)n'} or 2^{(δ_R+ε)n'} gate enumerations, each poly(n). Gate names and coefficients have
  O(n) bits.

## 3. Explicitness: existence only, and the finite search

The hardcoded circuit C* for P_{N',1/2}, N' = k^2 + 2k, is **only shown to exist**. A finite search would find it:
- Enumerate candidate integer pairs (L, R) for P_{N',1/2} in order of size.
- For each, check L R = P_{N',1/2} exactly and the max degrees ≤ 2^{(δ+ε/4)N'}.
- Because "sufficiently large k" is ineffective (it hides the hole-fixing constant 2^{O(1/ε'^2)}, the Stirling terms and
  the 2^{o(d)} of AL25), the search must dovetail over k = 2, 4, 6, …. It terminates because K(1/2) membership guarantees a
  witness for every large k.

Alternatively, derandomise each existence step: conditional expectations for the Sec. 3.5 orderings, and exhaustive choice
of the hole-fixing symmetries. Either way the cost is at least 2^{Θ(N')}.

**How large.** Cor. 3.2 needs log2(k+1)/k ≤ ε/4 and (2/k)(δ_R + ε/4) ≤ ε/4.
- For our Stage 2 the partial-match slack must be well below the gain ξπ/3 ≈ 1.67e-6. With ε = 1.6e-6 this gives
  k ≈ 6.6e7, so N' ≈ 4.3e15. For ε = 1e-7 it gives N' ≈ 1.5e18.
- Merely verifying one candidate touches 2^{N'} rows × C(N', N'/2) 2^{N'/2} columns.
- With the paper's 26-digit a and b, the window circuits additionally need block lengths divisible by q = lcm(4, 10^26).

**No box search is needed, and none is feasible.** The existence of the deterministic algorithm, which is all Prop. 4.2 and
our Stage 2 claim, does not require running the search. No computer can run it. We therefore ship no box script. The
small-n exactness checks above are the only meaningful computations, and they finish on the Mac.

## 4. Defects

| # | location | issue | severity | evidence |
|---|---|---|---|---|
| D1 | Lemma 3.4, "Numerical rebalancing" | AL25 Thm B.2 is restated as a list lemma, with hypotheses changed from "contains the two trivial decompositions" to "endpoint lists are termwise monotone". The restatement is faithful to what AL's proof uses, and Ye-Li's family includes (M,I) and (I,M) anyway. Note that AL25 Thm B.1 as printed defines ρ(α) = Σ nnz(U)^α nnz(V)^{1-α}, but its induction yields Σ nnz(U)^{1-α} nnz(V)^α; the exponents are swapped. Ye-Li's τ-form (Υ = Σ a^τ b^{1-τ} with λ^{1-τ}) is the consistent one. AL's Lemma B.4 proof is a sketch ("It's not hard to verify…") | minor | AL25 pp. 45-50; `yl_rebalance.py` (gap → 0 as ~1/d; weak duality never violated) |
| D2 | Lemma 3.4, hole fixing | Cites AL25 Thm 6.1, which is stated over a field. Ye-Li assert that the proof partitions the matrix into disjoint rectangles, so integer coefficients survive. That is consistent with AL's overview (recursive split into (S'∖σS) × T' and (S'∩σS) × (T'∖σT)); the full proof was not read. **Self-contained fix:** take J = O(1/ε'^2) random flip patterns covering every (row, query) pair (union bound, as each misses with probability 2^{-Ω(ε'^2 n)}). Then write 1 - Π_j(1 - X_j(x)Y_j(y)) by inclusion-exclusion: 2^J signed copies restricted to (∩X_j) × (∩Y_j). The result is exact over Z, the blow-up is constant, and colours are tagged per copy | minor | AL25 Thm 6.1 statement; derivation |
| D3 | Sec. 3.5, Cor. 3.2 | The circuit is non-explicit (union bound and random symmetries). "Sufficiently large k" is ineffective. The paper never says that the deterministic algorithm is non-constructive | minor (claim-preserving: Def. 2.1 is existential) | section 3 |
| D4 | Sec. 4 parameters | a and b have denominator 10^26, which forces window lengths that are multiples of 4·10^26. This is harmless but needless: a = 1/2635 and 1-b = 1/110 satisfy all conditions with q = 115940 and ξ = 2.00340e-5 (loss 1.3e-9) | minor | computed with the same formulas as `yl_numbers.py` |
| D5 | Sec. 1, Cor. 1.3 vs Thm 2.2 | "Append" vs "prepend" for the dummy pairs (1,-1); the intro sketch uses prefix n/3 informally | minor (cosmetic) | text |
| D6 | **our** AUDIT.md sec. 2(b) | "hardcoded constant-size object (Cor. 3.3)" should be **Cor. 3.2** (Cor. 3.3 is circuit → partial match). JUDGE_S1.md cites "Cor. 3.5", which does not exist in v1 | minor (ours) | numbering list above |
| D7 | **our** JUDGE_S1.md "Finite search" | It says the search terminates "because YL's construction (random orderings, union bound) proves that such a circuit exists". Existence also needs hole fixing (random symmetries) and AL25 rebalancing, and the search must dovetail over k because "large k" is ineffective. "Runs in constant time" is true but galactic: N' ≳ 4e15 | minor (ours) | section 3 |

No claim-level defect.

## 5. Does our Stage 2 use only what Prop. 4.2 states?

**Yes.** Stage 2 uses exactly these things:
1. **Def. 2.1 admissibility of the stated pair.**
   - It needs a deterministic, exact count of keyed compatible pairs, linear in |A| and |B|, with poly(n + L) overhead.
   - It runs at padded length n' = (2-2s)m with half the positions specified. That is the input class of Def. 2.1 for any
     length, so our prefix m = πn ≈ n/4 (instead of Ye-Li's n/3) is irrelevant to Prop. 4.2.
   - Keys are the full 2^{o(n)}-bit integers. Our Lemma U class filter only decides which records are generated; the
     count is over equal full keys.
2. **δ_L + δ_R = 1/2 - 2ξ**, used for the many-sums exponent n/2 + (1-ξ)m - log N.
3. **The individual values δ_L and δ_R**, used for ℓ_s ∈ [0, n-m] and the partial-list sizes. Prop. 4.2 states "the pair
   above", so these values are part of the statement.
   - Re-check of the right partial list: n/4 + m(3/4 + s/2 - h(s)/4 - ξ(1-s)) ≤ n/4 + m(3/4 - ξ/2), matching JUDGE fix S2.
4. **Slack ε**, which must be chosen ≪ ξπ/3. Def. 2.1 quantifies over every ε, so this is allowed.

Stage 2 uses nothing from Thm 2.2's randomized parts, from Ye-Li's n/3 split, or from their filter.

**Update to JUDGE fix S4.** Replace "conditional on YL Prop. 4.2 (unaudited)" with:

> "uses YL Prop. 4.2 (audited 2026-10-10: holds), which imports AL25 Thm B.2 and Thm 6.1 (refereed). The algorithm is
> deterministic but non-explicit (hardcoded circuit of length ≥ 10^15, shown to exist)."

## 6. Files (all ours; exit 0 = pass; all pass)

- `yl_numbers.py`: 60-digit recomputation of every Sec. 4 number, the parameter conditions, the anchors by grid, and secant
  domination with the true V. About 2 s.
- `yl_circuit.py`: Sec. 3.5 circuit built with deterministic greedy covers. It checks exact L R = P over Z gate by gate, the
  right-degree bound and colour signs, and two negative controls. About 7 s.
- `yl_rebalance.py`: AL25 Thm B.2 in Ye-Li's list form, exact lattice recursion up to d = 256, five families. About 26 s.
- `yl_grouping.py`: Lemma 3.1 bookkeeping, exhaustive, plus end-to-end matching. About 3 s.
