# Deterministic Subset Sum below meet-in-the-middle

**Swapnil Jain. Private draft, not published.**

Horowitz and Sahni's meet-in-the-middle (1974) decides Subset Sum deterministically in 2^{n/2} poly(n) time.
Every known algorithm that beats it is randomized. We give two deterministic results.

**Stage 1.** This derandomises Chen, Jin, Randolph and Servedio (CJRS, arXiv 2301.07134, Sec. 4).

- **Result.** Subset Sum is decided deterministically in O(2^{n/2} n^{-gamma}) for every gamma < 0.0101041782.
- **Model.** CJRS's model: l-bit inputs on l-bit words, l = poly(n), circuit RAM and word RAM.
- **What it answers.** The question of CJRS Sec. 6 for their Sec. 4 saving.

**Stage 2.** This derandomises Ye and Li (arXiv 2610.10446).

- **Result.** Subset Sum is decided deterministically in O(2^{0.49999834 n}).
- **Model.** Ye–Li's model: total input length 2^{o(n)}, negative integers allowed.
- **Non-explicit.** The algorithm is a fixed, finite program that uses no randomness. However, it hardcodes a
  circuit that is only proven to exist.

**Stage 2b.** This makes Stage 2 explicit.

- **Result.** The same exponent, E <= 0.4999983316, by a fully specified deterministic program: time
  2^{c N0} poly(n, L) 2^{E n} with N0 = k(k+2) ~ 1.0091e50 (k = 10045215487480163574218750) and c = 4858.
- **Galactic.** The constant 2^{4858 N0} is stated but astronomically large: the gain over 2^{n/2} appears only
  for n > n0 ~ 5.9e59 (n0 is where the constant costs at most half the gain). This is a statement about
  explicitness, not a practical algorithm.
- **What changed.** Every randomized or merely existential step of Ye–Li's circuit is constructed:
  pessimistic-estimator lists, greedy hole fixing, and an explicit three-piece rebalancing rule with an effective
  constant (`PROOF/stage2b-explicit.md`).
- **Smaller n0, at a price in E (Secs. 12-13).** Variants of the construction trade exponent for threshold. Each
  n0 belongs to its own E: below, n0 is where the run time drops below 2^{(1/2 - g/2) n} poly(n, L), with gain
  g = 1/2 - E. It is not where the run time reaches 2^{E n}.

| variant | E <= | n0 <= | for n >= n0, time < |
|---|---|---|---|
| Theorem 2b (c = 4858) | 0.4999983316 | 5.9e59 | 2^{0.49999917 n} |
| Sec. 12: sharper rebalancing constant (B16) | 0.4999983316 | 1.21e56 | 2^{0.49999917 n} |
| Sec. 13 [A']: halving splitter, N0 = q = 10^26 | 0.4999983345 | 1.20e32 | 2^{0.49999917 n} |
| Sec. 13: D4 (q = 115940), POS union, ladder | 0.4999983549 | 1.59e11 | 2^{0.49999918 n} |
| Sec. 13: q = 2664, POS union, ladder | 0.4999985715 | 4.90e10 | 2^{0.49999929 n} |

  So at Theorem 2's exponent (E <= 0.4999983345, S2 Certificate 7.2[B]) the smallest proved n0 is 1.20e32; the
  smallest n0 overall, 4.90e10, needs the weaker E <= 0.4999985715. The full table, with the E3 and POS-only rows,
  is in `PROOF/stage2b-explicit.md` Sec. 13.

## Status

| | claim | review | Lean |
|---|---|---|---|
| Stage 1 | O(2^{n/2} n^{-gamma}) for every gamma < gamma*, gamma* in [0.0101041782, 0.0101041783] | two independent internal referee passes, CONFIRMED WITH FIXES; fixes applied | exponent certificate kernel-checked |
| Stage 2 | O(2^{0.49999834 n}), exponent E <= 0.4999983316, saving >= 1.66e-6 | independently refereed (3 clean passes); conditional on Ye–Li Prop. 4.2 (its proof) and its dL/dR table; non-explicit | exponent certificate kernel-checked |
| Stage 2b | the same E, explicit, constant 2^{4858 N0} with N0 ~ 1.0091e50 (n0 ~ 5.9e59) | independently refereed (2 clean passes, CONFIRMED WITH FIXES, no claim-level defect; all fixes applied); same Ye–Li conditions as Stage 2, minus non-explicitness | design certificate kernel-checked; gate-level toy test at N = 8 |
| Stage 2b, Secs. 12-13 | smaller n0, each with its own E (table above; e.g. n0 <= 1.20e32 at E <= 0.4999983345, n0 <= 4.90e10 at E <= 0.4999985715) | independently refereed (2 clean passes; CONFIRMED or CONFIRMED WITH FIXES, one claim-level wording defect in the headline, now fixed; all fixes applied); Lemma V uses Ye–Li's V formula at a new (a, b) [cite] | both certificates' inequalities kernel-checked, including Lemma V's anchors with the real log; the splitter's exhaustive check stays in Python |

"Referee pass" means an adversarial check by a separate review pass of our own. It is not peer review.

**Novelty.** A literature search on 2026-10-10 found no earlier deterministic algorithm with either bound. That is
evidence, not proof.

## Credits

- **Stage 1: Xi Chen, Ce Jin, Tim Randolph and Rocco A. Servedio** (arXiv 2301.07134).
  - The algorithm, its constants, every lemma used, and the cost accounting are theirs. They are cited fact by fact
    in `PROOF/stage1.md` Sec. 1.
  - **New here:** the deterministic prime (Lemma 2.1), the bound on W'(T) for every T at once (Lemma 2.2), and the
    universal residue covering with the best shift (Lemmas 2.3 and 2.4). Together these replace CJRS's random
    prime and their s(l) random residues. Also new: the certificate.
  - Lemma 2.3 is greedy set cover (Johnson 1974, Lovász 1975, Chvátal 1979), and Lemma 2.4 is an averaging step.
    What is new is applying them to the family T × Z_p.
- **Stage 2: Ye and Li** (arXiv 2610.10446).
  - From them: the representation on a prefix, the layers, the partial-match subroutine with its hardcoded circuit,
    the few-sums branch (via Austrin, Kaski, Koivisto and Nederlof, Lemma 3.2), and above all Prop. 4.2.
  - Prop. 4.2 uses Alman and Li (arXiv 2509.14489, FOCS 2025), Thm B.2.
  - **New here:** the deterministic filter, made of three parts:
    - a collision-bounded prime;
    - layer families defined by a residue threshold;
    - one universal covering per layer, from Stage 1.
  - Also new: the re-derivation of Ye–Li's exponent at prefix 0.2499 n, the certificate, and an inclusion-exclusion
    replacement for Alman–Li Thm 6.1 (`PROOF/stage2.md` Sec. 9).
- **OpenAI's openai/math preprint** (October 2026) gave the randomized 2^{0.489995 n} Subset Sum construction (problem
  #138). Auditing where that construction uses randomness is what led us to the covering tool used here.
  This package does not derandomise that construction (`CLOSED_IDEAS.md`).
- The Lean log bounds (`lean/SubsetsumLean/Basic.lean`) are copied from our 3SUM package. They rest on Mathlib.

`NOTICE` lists exactly what is new.

## 1. Results

**Theorem 1 (Stage 1; `PROOF/stage1.md`).** For every constant gamma < gamma* := g(eps1*, eps2*), there is a
deterministic algorithm that decides Subset Sum on n integers in time O(2^{n/2} n^{-gamma}). It finds a solution in
the same time. Here (eps1*, eps2*) is the root of CJRS's Equations (3) and (4), and

    g(e1, e2) = min(lambda0/2, delta/2, theta0),       beta = 1/H((1+e2)/4),
    lambda0 = (1-e1)/2 * beta * (1 - H((1-e2)/2)),     delta = (1 - H((1-e1)/2)) * beta,
    theta0 = (1 - e1/2) * beta - 1 - lambda0.

The certificate gives gamma* in [0.0101041782, 0.0101041783]. The rational point (0.15792, 0.24267) alone gives
every gamma <= 0.0101. CJRS's printed rounding (0.1579, 0.2427) does not: there g < 0.0101.

Not claimed:
- anything at gamma = gamma* itself;
- that CJRS's roots maximise g;
- anything about CJRS's Sec. 3 and Sec. 5 savings (n^{-1/2} and n^{-0.5023}), which stay randomized.

The word RAM version (Corollary 2) rests on CJRS's Observation 4, which CJRS only sketch.

**Theorem 2 (Stage 2; `PROOF/stage2.md`).** There is a deterministic algorithm that decides Subset Sum in
O(2^{0.49999834 n}) bit operations on every input of total length 2^{o(n)}. Its time is poly(n, L) 2^{E n} with
E <= 0.4999983316, at prefix m = 0.2499 n. It finds a solution in the same time.

The theorem has three conditions (Theorem 2b below removes the second and third):
- It is conditional on Ye–Li Prop. 4.2, through its proof and its dL/dR table. We audited Prop. 4.2
  (`PROOF/ye-li-audit/`), but did not re-prove it.
- The program is **non-explicit**. It hardcodes an exact integer circuit for P_{N', 1/2} with
  N' = kappa^2 + 2 kappa >= 2.2035e22. Ye–Li's proof shows that this circuit exists, but does not construct it. So
  we can prove that the program exists, but we cannot write it down or run it (`PROOF/stage2.md` Sec. 8).
- The O(.) constant is ineffective.

The deterministic covering costs 2^{2m}, which forces the prefix down from Ye–Li's n/3 to 0.2499 n. So the saving
is about xi/12, against Ye–Li's randomized xi/9.

**Theorem 2b (Stage 2b; `PROOF/stage2b-explicit.md`).** There is an explicit deterministic algorithm that
decides Subset Sum in time 2^{c N0} poly(n, L) 2^{E n}, with E <= 0.4999983316 (as in Theorem 2), N0 = k(k+2),
k = 10045215487480163574218750 and c = 4858. It builds an input-independent circuit in at most 2^{4 N0} bit
operations (Lemma E6), then runs Stage 2 with that circuit enumerated implicitly.
- Still conditional on Ye–Li Prop. 4.2's proof and table, exactly as Theorem 2.
- The constant: 4855 N0 from rebalancing, N0 each for padding and storage access, and N0 for the additive
  preprocessing. Every one is a stated number; none is optimised.
- Referee fixes applied: exact-rational potential (ceil), corrected term order in the left-degree dominance, the
  q | k(k+2) window condition (which lowered N0 from 1e52 to 1.0091e50), and a written-out preprocessing count.

**Correction found by the Lean check.** An earlier draft stated N' >= 2.2036e22. The exact value is
N' = 22035779076245688040224, about 2.20358e22, so the bound is N' >= 2.2035e22 (`stage2_K`). The figure 2.2036e22
is proved false (`stage2_K_fails_N`), and the text now carries the corrected figure. Nothing else depends on it:
N' only measures how far the circuit is from explicit.

## 2. How to verify

    make check        # certificates, logic checks, Stage 2b certificate + toy test; standard-library Python, ~5 min, < 1 GB
    make lean-sync    # the generated Lean files equal what the generators produce from cert/
    make lean         # Lean 4 kernel check; needs elan (Lean v4.34.1), ~4 min, peak RSS < 3 GB
    make all          # all three

- `cert/cert_gamma.py` is the Stage 1 exponent certificate. It uses exact-rational interval arithmetic with outward
  rounding, and checks [A], [B] and the must-fail controls [C1] and [C2].
- `cert/cert_eps.py` is the Stage 2 exponent certificate. It uses exact rationals, and covers [A], [B], the block
  length [K], and the must-fail controls [C1] to [C8].
- `cert/cert_explicit.py` is the Stage 2b design certificate: exact rationals with certified ln 2 and entropy
  bounds, Certificate [A] (the design, the constant c and n0) and must-fail controls [C1] to [C7].
- `cert/cert_explicit_b16.py` (Sec. 12) and `cert/cert_explicit_b17.py` (Sec. 13) certify the smaller-n0 variants:
  the per-pair rebalancing constant, the halving splitter, the anchors at new (a, b) by concavity, the POS union and
  the ladder. Each table row's E and n0 is checked as an upper bound; controls D1, D2 and K1 to K9.
  `cert/toy_explicit.py` builds Lemmas E1 to E4 gate by gate at N = 8 and multiplies L R out against M, with four
  must-fail controls (`make explicit`).
- `cert/check_stage1.py` and `cert/check_stage2.py` run the algorithms against brute force at toy sizes, with
  negative controls that must miss. They check logic, not asymptotics.
- `PROOF/ye-li-audit/yl_*.py` are the numeric checks of our Ye–Li audit.
- `lean/` holds the kernel check. `lean/LEAN_SCOPE.md` says exactly what is kernel-checked and what stays paper
  proof. In short, it checks every inequality of the five certificates, with refuted controls. All 94 theorems use
  only `propext`, `Classical.choice` and `Quot.sound` (or a subset), and `leanchecker` replays all 11 modules.
  - For Stage 2b, that the certified formulas are the losses of Lemmas E1 to E6 is a paper proof.
  - That the certified terms are the running times of the algorithms is a paper proof.
  - So are CJRS's and Ye–Li's cited facts.
  - The last continuity step for the exact Stage 1 root is also on paper. Every gamma < 0.0101041782 is
    kernel-checked without it.

## 3. Files

| path | content |
|---|---|
| `PROOF/stage1.md` | Theorem 1, full proof, every claim labelled |
| `PROOF/stage2.md` | Theorem 2, full proof, non-explicitness stated precisely |
| `PROOF/stage2b-explicit.md` | Theorem 2b: the explicit construction, Lemmas E1 to E6, referee fixes; Secs. 12-13, smaller n0 |
| `PROOF/ye-li-audit/` | our adversarial audit of Ye–Li Prop. 4.2 and its scripts |
| `cert/` | the five certificates (with transcripts `*.out`), the two logic checks and the Stage 2b toy test |
| `lean/` | Lake project (Lean v4.34.1, Mathlib v4.34.1), generators `gen_stage1.py` / `gen_stage2.py` / `gen_explicit.py` / `gen_explicit_n0.py`, `LEAN_SCOPE.md` |
| `CLOSED_IDEAS.md` | routes to deterministic Subset Sum that we closed, with reasons |

Some cross-references in the proofs point to working notes that are not included here: `../AUDIT.md`,
`../JUDGE_S1.md`, `../RANDOMNESS_LEDGER.md` and `../judge_checks/`. Others refer to files by bare name.
`cert_gamma.py`, `cert_eps.py`, `check_stage1.py` and `check_stage2.py` are in `cert/`. `AUDIT_YELI.md` and
`yl_*.py` are in `PROOF/ye-li-audit/`.

**Working on this problem?** Read `CLOSED_IDEAS.md` first.
