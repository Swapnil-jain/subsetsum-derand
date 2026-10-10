# What the Lean files check, and what they do not

Lean 4 v4.34.1 with Mathlib v4.34.1. No `sorry`, no `native_decide`, no `admit`, and no added axioms.
`SubsetsumLean/Axioms.lean` prints the axioms of all 52 theorems listed below. Each one uses only `propext`,
`Classical.choice` and `Quot.sound`, or a subset of them (`axioms.out`). `lake env leanchecker
SubsetsumLean.<Module>` replays every module through the kernel, and all 8 pass. `--fresh`, which would also re-check Mathlib, was not run.

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
- **Stage 2 minimality of kappa_0.** This uses the fact that log2(k+1)/k decreases for k >= 1, which is on paper.
  Lean checks the value at kappa_0 and at kappa_0 - 2.
- `check_stage1.py` and `check_stage2.py`, the brute-force logic checks, stay in Python.

## Build on the 8 GB Mac

    export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$PATH
    lake exe cache get                       # prebuilt Mathlib oleans; never compile Mathlib
    ./build_watch.sh build                   # nice -n 19, one Lean thread, aborts above 3 GB RSS
    ./build_watch.sh env lean SubsetsumLean/Axioms.lean

The whole project builds in about 2 minutes. Peak RSS per step was 2.87 GB (the explicit modules: 2.52 GB), and most of that is mmapped Mathlib
oleans (`build_peak.log`).

The pinned Mathlib was fetched as a shallow clone of tag v4.34.1, at commit d13f23b, the commit in
`lake-manifest.json`. A full clone ran at about 10 MB/min.

`python3 gen_stage1.py`, `python3 gen_stage2.py` and `python3 gen_explicit.py` regenerate the three generated files
from the certificate scripts.
