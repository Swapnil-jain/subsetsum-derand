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

## Status

| | claim | review | Lean |
|---|---|---|---|
| Stage 1 | O(2^{n/2} n^{-gamma}) for every gamma < gamma*, gamma* in [0.0101041782, 0.0101041783] | two independent internal referee passes, CONFIRMED WITH FIXES; fixes applied | exponent certificate kernel-checked |
| Stage 2 | O(2^{0.49999834 n}), exponent E <= 0.4999983316, saving >= 1.66e-6 | independently refereed (3 clean passes); conditional on Ye–Li Prop. 4.2 (its proof) and its dL/dR table; non-explicit | exponent certificate kernel-checked |

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

The theorem has three conditions:
- It is conditional on Ye–Li Prop. 4.2, through its proof and its dL/dR table. We audited Prop. 4.2
  (`PROOF/ye-li-audit/`), but did not re-prove it.
- The program is **non-explicit**. It hardcodes an exact integer circuit for P_{N', 1/2} with
  N' = kappa^2 + 2 kappa >= 2.2035e22. Ye–Li's proof shows that this circuit exists, but does not construct it. So
  we can prove that the program exists, but we cannot write it down or run it (`PROOF/stage2.md` Sec. 8).
- The O(.) constant is ineffective.

The deterministic covering costs 2^{2m}, which forces the prefix down from Ye–Li's n/3 to 0.2499 n. So the saving
is about xi/12, against Ye–Li's randomized xi/9.

**Erratum found by the Lean check.** `PROOF/stage2.md` (lines 92 and 500) states N' >= 2.2036e22. The exact value
is N' = 22035779076245688040224 = 2.20358e22, so the true bound is N' >= 2.2035e22 (`stage2_K`). The figure
2.2036e22 is proved false (`stage2_K_fails_N`). Nothing else depends on it: N' only measures how far the circuit is
from explicit.

## 2. How to verify

    make check        # certificates + brute-force logic checks; pure standard-library Python, ~3.5 min, < 1 GB
    make lean-sync    # the generated Lean files equal what the generators produce from cert/
    make lean         # Lean 4 kernel check; needs elan (Lean v4.34.1), ~2 min, peak RSS < 3 GB
    make all          # all three

- `cert/cert_gamma.py` is the Stage 1 exponent certificate. It uses exact-rational interval arithmetic with outward
  rounding, and checks [A], [B] and the must-fail controls [C1] and [C2].
- `cert/cert_eps.py` is the Stage 2 exponent certificate. It uses exact rationals, and covers [A], [B], the block
  length [K], and the must-fail controls [C1] to [C8].
- `cert/check_stage1.py` and `cert/check_stage2.py` run the algorithms against brute force at toy sizes, with
  negative controls that must miss. They check logic, not asymptotics.
- `PROOF/ye-li-audit/yl_*.py` are the numeric checks of our Ye–Li audit.
- `lean/` holds the kernel check. `lean/LEAN_SCOPE.md` says exactly what is kernel-checked and what stays paper
  proof. In short, it checks every inequality of both certificates, with refuted controls. All 35 theorems use only
  `propext`, `Classical.choice` and `Quot.sound`, and `leanchecker` replays all 6 modules.
  - That the certified terms are the running times of the algorithms is a paper proof.
  - So are CJRS's and Ye–Li's cited facts.
  - The last continuity step for the exact Stage 1 root is also on paper. Every gamma < 0.0101041782 is
    kernel-checked without it.

## 3. Files

| path | content |
|---|---|
| `PROOF/stage1.md` | Theorem 1, full proof, every claim labelled |
| `PROOF/stage2.md` | Theorem 2, full proof, non-explicitness stated precisely |
| `PROOF/ye-li-audit/` | our adversarial audit of Ye–Li Prop. 4.2 and its scripts |
| `cert/` | the two certificates (with transcripts `*.out`) and the two logic checks |
| `lean/` | Lake project (Lean v4.34.1, Mathlib v4.34.1), generators `gen_stage1.py` / `gen_stage2.py`, `LEAN_SCOPE.md` |
| `CLOSED_IDEAS.md` | routes to deterministic Subset Sum that we closed, with reasons |

Some cross-references in the proofs point to working notes that are not included here: `../AUDIT.md`,
`../JUDGE_S1.md`, `../RANDOMNESS_LEDGER.md` and `../judge_checks/`. Others refer to files by bare name.
`cert_gamma.py`, `cert_eps.py`, `check_stage1.py` and `check_stage2.py` are in `cert/`. `AUDIT_YELI.md` and
`yl_*.py` are in `PROOF/ye-li-audit/`.

**Working on this problem?** Read `CLOSED_IDEAS.md` first.
