# What the Lean files check, and what they do not

Lean 4 v4.34.1 with Mathlib v4.34.1. No `sorry`, no `native_decide`, no `admit`, and no added axioms.
`SubsetsumLean/Axioms.lean` prints the axioms of all 94 theorems listed below. Each one uses only `propext`,
`Classical.choice` and `Quot.sound`, or a subset of them (`axioms.out`). `lake env leanchecker
SubsetsumLean.<Module>` replays every module through the kernel, and all 11 pass. `--fresh`, which would also re-check Mathlib, was not run.

## Kernel-checked

**Shared (`Basic.lean`).**
- `log_mem` gives rational bounds on `Real.log`, proved from Mathlib's series remainder bound. It is copied from the
  3SUM package.
- `Hb_mem` gives rational bounds on binary entropy in bits, from two log bounds.
- `Hb_mono` shows that H is increasing on `[0, 1/2]`, from Mathlib's `Real.binEntropy_strictMonoOn`.
- Each numeric bound is a `decide +kernel` on exact rationals, using a 60-term series.

**Stage 1 (`Stage1Defs.lean`, `Stage1Points.lean`, `Stage1.lean`) covers `derand/stage1/cert_gamma.py` in full.**

The numbers are those of `cert_gamma.py`, and `gen_stage1.py` re-checks each one with the kernel's own formula
before writing it.

| theorem | statement |
|---|---|
| `stage1_A` | [A] P = (0.15792, 0.24267) is admissible: 0 < e1, e2 < 1, 1 < beta < 4/3, lambda0 > 0, theta0 > 0, and g(P) > 0.0101 |
| `stage1_A_sharp` | g(P) > 0.01010384768 |
| `stage1_box` | [B] at every real point of the box e1 in [0.157920369638, 0.157920369640], e2 in [0.242668928272905, 0.242668928287458], the point is admissible with saving 0.0101041782, and each of the three terms is < 0.0101041783 |
| `stage1_curve` | for every e1 in the box, F4(e1, c) < 0 < F4(e1, d) (Equation (4) at the two e2-edges) |
| `stage1_slice_a`, `stage1_slice_b` | at e1 = a and at e1 = b, (4) changes sign on a slice of width 1e-21, and (3) is < 0 (at a) or > 0 (at b) on the whole slice |
| `stage1_gamma` | for every gamma < 0.0101041782, there is a rational admissible point with g > gamma, together with a rational lambda that satisfies Lemma 6.2's three inequalities |
| `lemma_6_2`, `lemma_6_2_rational` | PROOF.md Lemma 6.2, as algebra |
| `stage1_C1` | must fail: g(0.1579, 0.2427) > 0.0101 is false |
| `stage1_C2` | must fail: g > 0.010105 is false at the box corner |
| `stage1_box_fails_U` | must fail: g > 0.0101041783 is false at the box corner |
| `stage1_A_fails_next` | must fail: g(P) > 0.01010384769 is false |

**Stage 2 (`Stage2Defs.lean`, `Stage2.lean`) covers `derand/stage2/cert_eps.py` in full, controls C1 to C8 included.**

Ye–Li's true constants xi, dL and dR are variables. Each theorem's only assumptions about them are its stated
hypotheses: the 20-place table truncation for each, `t <= true < t + 1e-20`, or only `xi > 0.00002`.

| theorem | statement |
|---|---|
| `stage2_A` | [A] at pi = 0.2499, xi' = 2.0035e-5, eps = 1e-9: every side condition holds, and every term of Lemma 6.1 is < 0.49999834. The `T_hist` term uses the real log2 3, bounded through `3^200 < 2^317` |
| `stage2_A_sharp` | every term is < 0.499998332, so the gain is > 1.668e-6 |
| `stage2_B` | [B] the same with xi' = 2e-5, given xi > 0.00002 |
| `stage2_K` | [K] kappa_0 = 148444531984 is even and satisfies both conditions of Cor. 3.2, kappa_0 - 2 fails the second, and N' >= 2.2035e22 |
| `stage2_C1` to `stage2_C8` | the eight must-fail controls of `cert_eps.py`, each proved false. C6 and C8: some pair allowed by the table lies above the rounded-down pair. C7: xi' = 2.1e-5 breaks dl + dr <= 1/2 - 2 xi' |
| `stage2_A_fails_next` | must fail: every term < 0.4999983315 is false |
| `stage2_K_fails_N` | must fail: N' >= 2.2036e22 is false. N' is exactly 22035779076245688040224, so PROOF.md's "N' >= 2.2036e22" rounds the wrong way. The true bound is 2.2035e22 |

**Explicit Stage 2 (`ExplicitDefs.lean`, `Explicit.lean`) covers `cert/cert_explicit.py`'s Certificate [A] in
full, controls C1 to C7 included.**

`ExplicitDefs.lean` defines every quantity of the certificate over `ℚ` by the script's formulas (eps_win, eps_V,
tau1, tau2, the chord slopes, Delta, r_max, L_D, eps_L, eps_R, c, the gain). The integer witnesses (J, d*, and
the bit lengths used as log2 bounds) are fields, and `DesignOK` states the property each must have, so Lean does
not trust the script's choice of them. `gen_explicit.py` runs the script, re-checks every entropy bound with the
kernel's own formula, and writes `Explicit.lean`.

| theorem | statement |
|---|---|
| `explicit_A` | [A] at k = 10045215487480163574218750, eps' = 1e-13: k even, 10^26 \| N0, `N0+1 <= 2^lgN` etc., `J (2 eps'^2 N0 log2e - 2) > 2.5 N0`, 0 < tau1 < 1/3 < tau2 < 1, convexity, s1 > s2 > s3, the secant at tau1 and tau2, N0 Delta >= 1, `d* Delta > r_max`, L_D <= 4855, eps_L and eps_R <= 1e-9, k^2+2 <= N0, Lemma E6's numeric hypotheses, c <= 4858 |
| `explicit_A_n0` | the gain is > 0 and n0 = 2 c N0 / g <= 5.89e59 |
| `ln2_bounds` | 0.6931 <= ln 2, 1.4426 <= 1/ln 2 < 3/2 (the real constants, from `log_two_mem`) |
| `explicit_dom1` | Ye-Li's E1(1/4) = H(b) - 2 (1/4) H(4a) - (1/2) H(2(1-b-2a)) > 4a + 0.003814, real binary entropy |
| `explicit_dom2` | (1-b) H(2a/(1-b)) > 8a + 0.000726 |
| `explicit_Hb` | H(b) <= 1/10 (Lemma E6) |
| `explicit_params` | Ye-Li's parameter conditions and 1 - b <= 1/100 |
| `explicit_C1` to `explicit_C7` | the seven must-fail controls of `cert_explicit.py`, each proved false: eps_L > 1e-9 at k = 115940 and at eps' = 1e-4; no valid J at eps' = 1e-27 (even with log2 e < 3/2); the secant fails with dR' - 1e-11; L_D <= 4805 is false; 10^26 does not divide N0 at k = 10^25; H(b) <= 0.07 is false |
| `Hb_symm`, `Hb_ge_of`, `Hb_le_of` | H(1-x) = H(x), and moving an entropy bound to a nearby point of [0, 1/2] |

**Smaller n0 (`ExplicitN0Defs.lean`, `ExplicitAnchors.lean`, `ExplicitN0.lean`) covers `cert/cert_explicit_b16.py`
(PROOF Sec. 12) and `cert/cert_explicit_b17.py` (PROOF Sec. 13): every inequality, controls D1, D2, K1, K2 and K4
to K9 included.** Theorems are in namespace `SS.N0`.

`ExplicitN0Defs.lean` defines every rational quantity of both scripts over `ℚ` by the scripts' formulas: the
three-piece structure with its six per-pair gaps and excesses, d1, S, Delta, L_D (Lemma E4'), the hull pair and
xi'', J, eps_V, Lemma E6's hypotheses, S2 Lemma 6.1 with a general gamma, the ladder (the tail, the switch length,
the Delta level, the main levels and every bit of the constant), and n0. Only the inputs come from the scripts: the
anchors (rounded up to 10^-18), the points x0 of Lemma V, and each row's N0 and e'. Lean recomputes everything else,
including every integer the scripts choose (J, the tail lengths, K, d1, d*), so no choice is trusted.
`gen_explicit_n0.py` runs both scripts and writes the two generated files. Each log and entropy enclosure it writes is
first checked with the kernel's own formula, and each linear combination linarith must find is checked exactly
against its anchor.

| theorem | statement |
|---|---|
| `anchor_{YL,D4,q2664}_{0,h,1}` | Lemma V's tangent bound tau E1(1/4) + (1-tau)(b - 1/2 + 2a) + f_tau(x0) + grad f_tau(x0) . (v - x0), with the real log and binary entropy, is at most the certified anchor U at all four vertices v of K, for tau = 0, 1/2, 1 at Ye-Li's (a, b), D4 and q = 2664 |
| `anchor_K9` | must fail: the tau = 1/2 anchor at D4 below the value at the feasible point (3a/2, 9a/4) |
| `dom1_*`, `dom2_*`, `hb_*` | at D4 and q = 2664: E1(1/4) > 4a, h(1-b, 2a) > 8a (with margins) and H(b) <= 1/10 |
| `yl_match` | at Ye-Li's (a, b), each certified anchor is >= the table's truncation and within 2e-17 of it |
| `hull_D4`, `hull_q2664` | q = lcm(4, denominators), Ye-Li's parameter conditions and 1-b <= 1/100, the hull pair (dL'', dR'') and xi'' >= 2e-5 |
| `explicit_B16` | [B16] at design [A]: thresholds, endpoints, all six gaps > 0, N0 min delta >= 1, d1 = 3, S <= 0.4967, g > 0, n0 <= 1.21e56 |
| `splitter_family` | Lemma 3.1'(b) as (D prod m_v)^4 <= 2^(9(D-1)) for D <= 400 |
| `explicit_Aprime`, `explicit_Aprime_s2` | [A'] at N0 = q = 10^26: q \| N0, J <= N0/8, Lemma E6, the structure, the secant, eps_L, eps_R <= 1e-9, L_D = 4855, S <= 0.4967, d1 = 3, E <= 0.4999983345 (every real S2 term is at most E), n0 <= 5.84e35 (E4) and <= 1.20e32 (B16) |
| `row_{D4,q2664}_{E3,POS,POS_ladder}_ok` | each Sec. 13 table row: every check of `q_variant` (and of `ladder_bits` for the ladder rows), E <= its table value, n0 <= its table value, and every real S2 term (general gamma, real log2 3) at most E |
| `ladder_gain_D4` | the D4 ladder's n0 is at least 100 times smaller than the D4 POS row's |
| `B16_D1`, `B16_D2`, `K1`, `K2`, `K4` to `K8` | the scripts' must-fail controls, each proved false. K7 is checked for every e' of the script's grid, not only the best one. K1 is proved for every natural k |

## Paper proof only (not in Lean)

- **The cost model itself.** That g, and the nine terms of Stage 2, are the running-time exponents of the
  algorithms DET and DET2 is proved on paper: correctness, the covering Lemmas 2.1 to 2.4, and the time accounting
  (`PROOF/stage1.md` Secs. 2 to 5, `PROOF/stage2.md` Secs. 2 to 6). Lean checks the inequalities as formulas only.
- **Cited facts.** CJRS F1 to F10 and Observation 4 (word RAM). Ye–Li Prop. 4.2 and its proof, its dL/dR table,
  AL25 Thm B.2, and the existence of the non-explicit circuit.
- **Stage 1 root existence.** Lean checks every numeric fact behind it: the curve crosses the box, and (3) changes
  sign between the slices at a and b. The final step is on paper. That step uses continuity of the implicit
  function e2(e1), defined by (4), followed by the intermediate value theorem. Only the part
  0.0101041782 <= gamma < gamma* = 0.01010417823... depends on it. Every gamma < 0.0101041782 is fully
  kernel-checked (`stage1_gamma`).
- **Explicit Stage 2.** Everything in `PROOF/stage2b-explicit.md` except Certificate [A]'s arithmetic: that the
  formulas in `ExplicitDefs.lean` are the losses of Lemmas E1 to E6 (the window loss, the Hoeffding/greedy count
  behind J, the volume bound, the E4 induction, Lemma E6's operation count), Ye-Li's anchors V(0), V(1/2), V(1)
  (their 20-place truncations are inputs), and that k is the least even k with 10^26 \| k(k+2) (a CRT fact; any
  such k would do). The [T] trade-off table is printed by the script, not checked. `toy_explicit.py`, the
  gate-level toy test, stays in Python.
- **Smaller n0 (Secs. 12-13).** Lemmas E4', 3.1', E5', P1, P2 and E4'', and the reading of S2 Lemma 6.1 with a
  general gamma: that the formulas in `ExplicitN0Defs.lean` are the costs of the algorithms. Lemma V itself (f_tau is
  concave on K, so the tangent bound at the vertices bounds max_K f_tau) and the formula for V at a general (a, b)
  (Ye-Li's (Y2)-(Y3)). Lemma 3.1'(b) for D > 400 (the induction). The splitter's exhaustive check [G] (every
  half-set balanced for four leaf patterns) and its control K3 stay in Python; they are finite enumerations, not
  inequalities. The choice of each row's N0 and e' (a search) is not checked: any choice that passes gives a valid
  bound.
- **Stage 2 minimality of kappa_0.** This uses the fact that log2(k+1)/k decreases for k >= 1, which is on paper.
  Lean checks the value at kappa_0 and at kappa_0 - 2.
- `check_stage1.py` and `check_stage2.py`, the brute-force logic checks, stay in Python.

## Build on the 8 GB Mac

    export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$PATH
    lake exe cache get                       # prebuilt Mathlib oleans; never compile Mathlib
    ./build_watch.sh build                   # nice -n 19, one Lean thread, aborts above 3 GB RSS
    ./build_watch.sh env lean SubsetsumLean/Axioms.lean

The whole project builds in about 4 minutes. Peak RSS per step was 2.87 GB (the explicit modules: 2.86 GB), and most of that is mmapped Mathlib
oleans (`build_peak.log`).

The pinned Mathlib was fetched as a shallow clone of tag v4.34.1, at commit d13f23b, the commit in
`lake-manifest.json`. A full clone ran at about 10 MB/min.

`python3 gen_stage1.py`, `python3 gen_stage2.py`, `python3 gen_explicit.py` and `python3 gen_explicit_n0.py` regenerate the
five generated files from the certificate scripts. The three Sec. 12-13 modules build in about 2 minutes, peak RSS 2.86 GB.
