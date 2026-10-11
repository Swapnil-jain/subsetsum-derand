# Deterministic Subset Sum below meet-in-the-middle

**Swapnil Jain. Private draft, not published.**

Horowitz and Sahni's meet-in-the-middle (1974) decides Subset Sum deterministically in 2^{n/2} poly(n) time. Every
known algorithm that beats it is randomized. This repository gives deterministic algorithms below it, in six stages.

**Headline.** Subset Sum is decided deterministically, and a solution is found, in poly(n, L) 2^{(E + eps) n} bit
operations for every eps > 0, with

    E <= 0.4986298176        (gain 1/2 - E >= 1.3702e-3; Stage 5b)

The algorithm is **non-explicit**: it is one fixed, finite program that uses no randomness, but it hardcodes an exact
integer circuit that is only proven to exist. It is built on Ye and Li's unpublished "Record 3" reduction, which we
reconstructed, proved and re-certified (Credits). It has had one internal referee pass.

**Working on this problem?** Read [docs/CLOSED_IDEAS.md](docs/CLOSED_IDEAS.md) first: it lists the routes we closed,
with the reason for each.

## Results

Model (Ye–Li Sec. 2) for Stages 2 to 5b: integers z_1, ..., z_n (negatives allowed) and a target, total input length
L = 2^{o(n)}, bit operations. Stage 1 is in CJRS's model (l-bit inputs on l-bit words, l = poly(n)). Every exponent is
an upper bound, certified in outward-rounded or exact arithmetic and rounded up. "Referee pass" means an adversarial
check by a separate review pass of our own. It is not peer review.

| stage | deterministic bound | rests on | referee passes | Lean (kernel-checked) |
|---|---|---|---|---|
| 1 (`proofs/stage1.md`) | O(2^{n/2} n^{-gamma}) for every gamma < 0.0101041782 | CJRS Sec. 4, cited fact by fact; Observation 4 (word RAM, sketched by CJRS) for the word-RAM corollary | 2, CONFIRMED WITH FIXES | the exponent certificate, except the last continuity step for the exact root |
| 2 (`proofs/stage2.md`) | E <= 0.4999983316 | Ye–Li Prop. 4.2 (its proof) and its dL/dR table | 3 clean passes | the exponent certificate |
| 2b (`proofs/stage2b-explicit.md`) | the same E, **explicit** (table below) | as Stage 2, minus non-explicitness | 2, CONFIRMED WITH FIXES; Secs. 12-13: 2 | the design certificate; both smaller-n0 certificates |
| 3 (`proofs/stage3.md`) | E3 <= 0.499990922021 | a modified proof of Ye–Li Prop. 4.2 (a generalised Sec. 3.5, then Ye–Li's Lemma 3.4, Lemma 3.1, Cor. 3.2 and Cor. 3.3 as cited), plus the [arg] rounding and window steps of its Sec. 2.2 | 2 per component, CONFIRMED WITH FIXES; the package as a whole was not refereed | every inequality of the certificate, the xi certificate included |
| 4 (`proofs/stage4.md`) | E <= 0.4998322132 (Stage 4+: 0.4997369618) | the Record 3 route, re-derived and proved here; the cited (AL-B2) rebalancing statement of Ye–Li (from Alman–Li App. B), Stage 2's Lemma 9.1, AKKN16 Lemma 3.2; one [arg] (Sec. 7) | 2 (G1, G2), fixes applied | every inequality of both certificates (131 theorems) |
| 5 (`proofs/stage5.md`) | E <= 0.4989524521 | Stage 4 and what it cites | 2 clean passes, confirmed | every inequality of the certificate (83 theorems) |
| **5b** (`proofs/stage5b.md`) | **E <= 0.4986298176** | Stage 5, Stage 4 and what they cite; Lemma 5b.1 (proved here) | 1, CONFIRMED | Lemma 5b.1 for the six families, row R4b-min and its controls (107 theorems; rows R3, R4, R4b in Python only) |

Stages 2 to 5b find a solution in the same time. In Stages 4 to 5b the time is poly(n, L) 2^{(E + eps) n} for every
eps > 0, and the round-family loss (lambda, at piece length 8e9) is inside every printed E.

**Explicit and non-explicit.**
- **Explicit:** Stage 1 and Stage 2b. Stage 2b runs in time 2^{c N0} poly(n, L) 2^{E n} with E <= 0.4999983316,
  N0 = k(k+2) ~ 1.0091e50 (k = 10045215487480163574218750) and c = 4858. It constructs every randomized or merely
  existential step of Ye–Li's circuit (pessimistic-estimator lists, greedy hole fixing, an explicit three-piece
  rebalancing rule with an effective constant). The constant is galactic. Each n0 below belongs to its own E: n0 is
  where the run time drops below 2^{(1/2 - g/2) n} poly(n, L), with gain g = 1/2 - E.

  | variant | E <= | n0 <= | for n >= n0, time < |
  |---|---|---|---|
  | Theorem 2b (c = 4858) | 0.4999983316 | 5.9e59 | 2^{0.49999917 n} |
  | Sec. 12: sharper rebalancing constant | 0.4999983316 | 1.21e56 | 2^{0.49999917 n} |
  | Sec. 13: halving splitter, N0 = q = 10^26 | 0.4999983345 | 1.20e32 | 2^{0.49999917 n} |
  | Sec. 13: q = 115940, positive union, ladder | 0.4999983549 | 1.59e11 | 2^{0.49999918 n} |
  | Sec. 13: q = 2664, positive union, ladder | 0.4999985715 | 4.90e10 | 2^{0.49999929 n} |

- **Non-explicit:** Stages 2, 3, 4, 5 and 5b. Each is one fixed, finite program with no random bits, correct and
  within the time bound on every input, but it hardcodes an exact integer circuit (and, from Stage 4 on, a finite
  table) whose existence is proved and which we cannot write down. That such a program counts as a deterministic
  algorithm is the one definitional [arg] step of Stage 2 Sec. 8.3 and Stage 4 Sec. 7. Their constants and n0 are
  ineffective. Stage 2's circuit has size N' >= 2.2035e22.

### What each stage rests on, exactly

- **Stage 1** derandomises CJRS Sec. 4: it replaces only their random prime and their s(l) random residues, by a
  deterministic prime and a universal residue covering with the best shift. Nothing is claimed at gamma = gamma*
  itself, nor about CJRS's Sec. 3 and Sec. 5 savings. Lean checks every gamma < 0.0101041782 without the last
  continuity step.
- **Stage 2** is conditional on Ye–Li Prop. 4.2, through its proof and its dL/dR table. We audited Prop. 4.2
  (`proofs/ye-li-audit/`) but did not re-prove it. The deterministic covering costs 2^{2m}, which forces the prefix
  down from n/3 to 0.2499 n, so the saving is about xi/12 against Ye–Li's randomized xi/9.
- **Stage 3** adds the outside-sum dedupe and a re-tuned Ye–Li circuit, each refereed separately. Its headline rests
  on a **modified** proof of Prop. 4.2, not on Prop. 4.2 as stated, and the rounding and window steps of its Sec. 2.2
  are [arg]. With Prop. 4.2 as stated (conditional exactly as Stage 2), the dedupe alone gives
  E <= 0.499994991801. Its circuit has N' >= 2.2035e22 as a lower bound only.
- **Stages 4 to 5b** use the Record 3 route instead of Stage 3's. Every step of the reduction is re-derived and proved
  in `proofs/stage4.md` (A1-A4 were argued in the randomized precursor and are proofs here). What remains cited is
  (AL-B2), Ye–Li's statement of Alman–Li's App. B rebalancing; our Stage 2 Lemma 9.1 (hole fixing); AKKN16 Lemma 3.2;
  Ye–Li's counting and recovery; and three standard facts (primes in [x, 2x], fast multiplication, a Chernoff bound).
  The one [arg] step is the non-explicitness convention above. Stage 5's second-order closed forms (mu xi/2,
  3 mu xi/4) are [arg]; the certified rows do not use them. In Stage 5b, Stage 4 Lemma 3.4 is applied with three
  members per density; Stage 4 proves it for any finite family, but its brute force exercises at most two.

## Credits

- **Stage 1: Xi Chen, Ce Jin, Tim Randolph and Rocco A. Servedio** (CJRS, arXiv 2301.07134).
  - The algorithm, its constants, every lemma used, and the cost accounting are theirs. They are cited fact by fact
    in `proofs/stage1.md` Sec. 1.
  - **Ours:** the deterministic prime (Lemma 2.1), the bound on W'(T) for every T at once (Lemma 2.2), and the
    universal residue covering with the best shift (Lemmas 2.3 and 2.4), which together replace CJRS's random prime
    and random residues; and the certificate. Lemma 2.3 is greedy set cover (Johnson 1974, Lovász 1975,
    Chvátal 1979) and Lemma 2.4 is an averaging step; what is new is applying them to the family T x Z_p.
- **Stages 2 and 3: Lixi Ye and Baitian Li** (arXiv 2610.10446).
  - From them: the representation on a prefix, the layers, the partial-match subroutine with its hardcoded circuit,
    the few-sums branch (via Austrin, Kaski, Koivisto and Nederlof, Lemma 3.2), and above all Prop. 4.2 and the
    circuit of its Sec. 3.5, which Stage 3 re-tunes.
  - **Alman and Li** (arXiv 2509.14489, FOCS 2025): Thm B.2, used inside Ye–Li Prop. 4.2, and the
    rebalancing statement (AL-B2) that Stages 4 to 5b cite.
  - **OpenAI's openai/math preprint** (October 2026) gave a randomized 2^{0.489995 n} Subset Sum construction.
    Auditing where that construction uses randomness led us to the covering tool used here. This package does not
    derandomise that construction (`docs/CLOSED_IDEAS.md`, Sec. 1).
  - **Ours:** the deterministic filter (a collision-bounded prime, layer families by a residue threshold, one
    universal covering per layer); the re-derivation of Ye–Li's exponent at a general prefix; the inclusion-exclusion
    replacement for Alman–Li Thm 6.1 (`proofs/stage2.md` Sec. 9); the explicit construction of Stage 2b and its
    smaller-n0 variants; the outside-sum dedupe and the re-tune of Stage 3; the certificates.
- **Stages 4 to 5b: built on Ye and Li's unpublished "Record 3" reduction.** Four separate things, kept apart because
  only the first two can be checked by a reader of the paper:
  - **What is public: the number.** The only Record 3 result in print is the numerical candidate 0.499664500303...,
    quoted in the AI-disclosure section of Lixi Ye and Baitian Li, arXiv 2610.10446 v1, "Subset Sum via Partial
    Match". No reduction, circuit or proof of it is published.
  - **What the disclosure says.** Inside Ye and Li's project, on 28 September 2026, the AI model "GPT-6 astra ultra"
    found "a reduction showing that ordinary subset sum could also break meet-in-the-middle using the same P_1
    circuit improvement"; "Record 3 contains a detailed reduction at 06:22, and the numerical candidate
    0.499664500303... at 06:42, where the complete formal proof is explicitly still pending". The same passage says
    the project had moved from s = 1/2 to s = 1/8 and that "the broader criterion allows any fixed s in (0, 1/2]". So
    the reduction is credited, by its authors, to an AI model working in their project, and it is unproved there.
  - **What we reconstructed and re-certified.** The specifics were read in a shared chat transcript of Record 3, which
    is not part of the paper or of any publication, so their attribution cannot be checked from anything published.
    We re-derived every one of them and certified the numbers independently; the ideas remain Record 3's (Ye and Li's
    project), not ours:
    - the block representation (c_i = l_i + r_i with l in {0,1}, r in {-1,0,1}) on a mu n block, few/many sums on the
      block, the kappa-layer pigeonhole and enumeration;
    - balanced splits H / Hbar with cores at a chosen density s, the round count J, filtering without isolation or
      fingerprints, and the tensor circuit C_core (x) (I, P_1) inside the symmetric (R^T (x) L, L^T (x) R) circuit;
    - the s-cancellation identity, the cost functions and the saving coefficients mu alpha/3,
      mu alpha(1-alpha)/(2-alpha), (3 - 2 sqrt 2)/2;
    - the details of the one-pass covering circuit family (cover size k + rho(m - k), degree formulas, the trivial
      pairs (h(s), 0), (0, 1 - s)), which `proofs/stage4.md` Lemma 3.5 proves;
    - xi(1/8) and xi(0.11), certified here by branch and bound (xi >= 0.0043428267 and 0.0044849038), with Record 3's
      floats 0.004342871357 and 0.004484944104 inside our brackets.
  - **What is ours.**
    - The proofs of every step the earlier write-up left as [arg]: the density-s Lemmas 3.1 and 3.4 with unbalanced
      queries (A1), the left-degree concentration (A2), the balanced half-splits (A3), and the fixed round family
      with its multiplicity and loss (A4). The published Ye–Li paper supplies the half-stars framework these adapt to
      density s: Def. 2.1, Lemma 3.1 (block grouping), Cor. 3.2, Cor. 3.3, Lemma 3.4.
    - The repairs: the filter cap (randomized), Phi's universe restricted to the good c, the prime p ~ T with the
      collision count, the parity bit sigma, the fixed-point estimator, the enumeration of compatible K, the
      poly(n, L) factors.
    - The whole deterministic port and its exponents, the certificates and the brute-force checks.
    - Stage 4+ and Stage 5b: families of circuits on this route, Lemma 5b.1 and their certificates. Stage 5: the
      outside-sum dedupe (from our Stage 3) ported to this route, with two blocks per side as a variant, and the
      kappa-adaptive core menu with per-side densities and an unequal outer split.
  - So the reduction and the circuit family are presented here as Record 3's (Ye and Li's project, AI-found per
    their disclosure, proof pending there), only the number is public, and we claim as ours only the proofs of the
    [arg] steps, the repairs, the certificates and the deterministic port.
- **Mathlib** (leanprover-community) and Lean 4. The Lean log bounds (`lean/SubsetsumLean/Basic.lean`) are copied
  from our 3SUM package and rest on Mathlib.

`NOTICE` lists exactly what is whose. A literature search on 2026-10-10 found no earlier deterministic algorithm
below meet-in-the-middle; that is evidence, not proof.

## How to verify

Requires Python 3.9 or newer; numpy only for `check_stage4.py` and `check_stage5.py` (`pip install -r
requirements.txt`; tested with numpy 2.0.2). Lean needs elan with Lean v4.34.1 (pinned in `lean/lean-toolchain`) and
fetches prebuilt Mathlib v4.34.1 oleans (about 7 GB; Mathlib itself is not in the repository).

    make check        # every certificate against its transcript, the brute-force checks, the tests (~20 min, < 1 GB)
    make lean-sync    # the generated Stage 1-3 Lean files equal what the generators produce from certificates/
    make lean         # Lean 4 kernel check of every stage, one module at a time; LONG (about 3 hours on an 8 GB laptop)
    make all          # all three

Single stages: `make certs logic explicit stage3 stage4 stage5 stage5b tests`; Lean by stage: `make lean-123`
(about 4 min), `make lean-stage4` (about 30 min), `make lean-stage5` (about 70 min), `make lean-stage5b` (about 90 min, one module
at a time; our Stage 5b audit ran on a larger Linux machine, `lean/LEAN_SCOPE.md`). Every Lean
module is built under `lean/build_watch.sh` (nice -n 19, one thread, aborts above 3 GB RSS), and `lean/axioms_ok.sh`
fails unless every printed theorem uses only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no
`native_decide`.

What is kernel-checked and what stays a paper proof is in `lean/LEAN_SCOPE.md`. In short, Lean checks every
inequality of every certificate, with the must-fail controls proved false. That the certified terms are the running
times of the algorithms is a paper proof, and so are the cited facts.

## Files

| path | content |
|---|---|
| `proofs/stage1.md` ... `proofs/stage5b.md` | one proof document per stage, every claim labelled [proof], [arg], [cite], [iv] (interval-checked) or [exp] |
| `proofs/ye-li-audit/` | our adversarial audit of Ye–Li Prop. 4.2 and its scripts |
| `certificates/` | Stages 1 to 3: the certificates (transcripts `*.out`), the logic checks and the Stage 2b toy test |
| `certificates/stage4/`, `stage5/`, `stage5b/` | the Stage 4 to 5b certificates and brute-force checks with their transcripts; `*_vendored.py` are verbatim, hash-checked copies of the earlier stages' scripts |
| `lean/` | the Lake project, its generators `gen_*.py`, the one-command checks `check_stage4.sh`, `check_stage5.sh`, `check_stage5b.sh`, and `LEAN_SCOPE.md` |
| `tests/` | the README's headline numbers against the transcripts |
| `docs/CLOSED_IDEAS.md` | routes we closed, with reasons |
| `CORRECTIONS.md` | defects we found and fixed ourselves |

Some proofs mention working notes that are not included (`AUDIT.md`, `JUDGE_S1.md`, `RANDOMNESS_LEDGER.md`,
`judge_checks/`), and labels such as A22 or A39 name entries of our internal notes; each proof says what it uses from
them. Comments and transcripts that name `derand/stageN/` refer to `certificates/stageN/`.

## License

Apache-2.0 (`LICENSE`). Author: Swapnil Jain.
