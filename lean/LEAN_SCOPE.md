# What the Lean files check, and what they do not

Lean 4 v4.34.1 with Mathlib v4.34.1. No `sorry`, no `native_decide`, no `admit`, and no added axioms.
For Stages 1 to 3, `SubsetsumLean/Axioms.lean` prints the axioms of all 141 theorems listed below. Each one uses only `propext`,
`Classical.choice` and `Quot.sound`, or a subset of them (`axioms.out`). `lake env leanchecker
SubsetsumLean.<Module>` replays every module through the kernel, and all 13 pass. `--fresh`, which would also re-check Mathlib, was not run.
Stages 4, 5 and 5b have their own axioms files (`Stage4Axioms.lean`, 131 theorems; `Stage5Axioms.lean`, 83;
`Stage5bAxioms.lean`, 107) and one-command checks (`check_stage4.sh`, `check_stage5.sh`, `check_stage5b.sh`), each
audited by `axioms_ok.sh`.

## Kernel-checked

**Shared (`Basic.lean`).**
- `log_mem` gives rational bounds on `Real.log`, proved from Mathlib's series remainder bound. It is copied from the
  3SUM package.
- `Hb_mem` gives rational bounds on binary entropy in bits, from two log bounds.
- `Hb_mono` shows that H is increasing on `[0, 1/2]`, from Mathlib's `Real.binEntropy_strictMonoOn`.
- Each numeric bound is a `decide +kernel` on exact rationals, using a 60-term series.

**Stage 1 (`Stage1Defs.lean`, `Stage1Points.lean`, `Stage1.lean`) covers `certificates/cert_gamma.py` in full.**

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
| `lemma_6_2`, `lemma_6_2_rational` | `proofs/stage2.md` Lemma 6.2, as algebra |
| `stage1_C1` | must fail: g(0.1579, 0.2427) > 0.0101 is false |
| `stage1_C2` | must fail: g > 0.010105 is false at the box corner |
| `stage1_box_fails_U` | must fail: g > 0.0101041783 is false at the box corner |
| `stage1_A_fails_next` | must fail: g(P) > 0.01010384769 is false |

**Stage 2 (`Stage2Defs.lean`, `Stage2.lean`) covers `certificates/cert_eps.py` in full, controls C1 to C8 included.**

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
| `stage2_K_fails_N` | must fail: N' >= 2.2036e22 is false. N' is exactly 22035779076245688040224, so the earlier "N' >= 2.2036e22" rounds the wrong way. The true bound is 2.2035e22 |

**Explicit Stage 2 (`ExplicitDefs.lean`, `Explicit.lean`) covers `certificates/cert_explicit.py`'s Certificate [A] in
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

**Smaller n0 (`ExplicitN0Defs.lean`, `ExplicitAnchors.lean`, `ExplicitN0.lean`) covers `certificates/cert_explicit_b16.py`
(proofs/stage2b-explicit.md Sec. 12) and `certificates/cert_explicit_b17.py` (proofs/stage2b-explicit.md Sec. 13): every inequality, controls D1, D2, K1, K2 and K4
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

**Stage 3 (`Stage3Defs.lean`, `Stage3.lean`) covers `certificates/cert_stage3.py` in full: the re-tuned xi certificate, the
exponent, the fallbacks and the controls.** These two modules contribute 47 of the 141 theorems and 2 of the 13 modules counted above.

`Stage3Defs.lean` proves the general facts once:
- Gibbs' inequality `h(n, k) <= k (-log2 p) + (n - k)(-log2 (1 - p))` (`gibbs_nat`, `ent_le`, from `log x <= x - 1`);
- rational enclosures of `h(c, x)` (`hh_mem`);
- `h(c, k) = c H(k/c)` and `h(n, k) <= n`;
- the vertex bound for affine functions on the colour polygon (`quad_le`);
- `line_of_U`: the six majorant bounds and A > 0 imply Ye-Li Lemma 3.4's hypothesis
  `min(tau L + (1 - tau) R, tau, (1 - tau)/2) <= line(tau)` for every tau in [0, 1] and every colour, where L is the
  true max of the three left terms, with `max(A, 0)`;
- `xi_le_of_F1`: lower bounds just outside the crossings bound xi for every valid line.

`gen_stage3.py` re-checks every log enclosure with the kernel's formulas before writing `Stage3.lean`.

| theorem | statement |
|---|---|
| `s3_params`, `s3_E1`, `s3_Hr`, `s3_Apos` | [P]; enclosures of E1 and H(1/r); A(mu) > 0 on [a1, a1 + a0] |
| `s3_U{1,2,3}_t{1,2}` | [U] g_i(t1) <= t1 and g_i(t2) <= (1 - t2)/2 at every real point of the polygon |
| `s3_line`, `s3_xi` | [L] Lemma 3.4's hypothesis for the re-tuned circuit; dL = line(1), dR = line(0) >= 0, xi_cert = 1/4 - (dL + dR)/2 |
| `s3_F1` | [F1] every line satisfying that hypothesis has xi <= xi_max < xi_cert (1 + 1e-4) |
| `s3_E3`, `s3_gain` | [S3] Theorem 3: Lemma 3.5's hypotheses, the fit and every cost term <= E3 = 0.499990922021, with no Ye-Li table input; the gain is >= 9.0779e-6 |
| `s3_fit_tail`, `s3_fit_small` | the fit for n >= 414 (closed form) and for each 202 <= n < 414 at m = 2 floor(pi n/2) |
| `s3_K` | Cor. 3.2 at the new pair: kappa_0 = 148444531984 meets both conditions, and kappa_0 - 2 fails the second |
| `s3_FA`, `s3_FB` | fallbacks E <= 0.499994991801 (table hypotheses as in `stage2_A`) and E <= 0.4999950006 (xi > 2e-5) |
| `s3_K1` to `s3_K11`, `s3_C34` | the script's must-fail controls, each proved false |


**Stage 4 (`Stage4Check`, `Stage4Probs`, `Stage4Cells_*`, `Stage4Defs`, `Stage4ECheck`, `Stage4ERows`, `Stage4EDefs`,
`Stage4Base`, `Stage4XI`, `Stage4E`, `Stage4`) covers `certificates/stage4/cert_stage4.py` and `cert_stage4plus.py` in
full, controls included.** Namespace `SS4`. `Stage4Axioms.lean` prints the axioms of all 131 theorems: each uses only
`propext`, `Classical.choice`, `Quot.sound` (`axioms_stage4.out`). One command: `./check_stage4.sh`.

The scripts prove [XI] by branch and bound over thousands of boxes with float logs; Lean checks the same claims by a
different certificate built for the kernel (`gen_stage4_cells.py`). The colour polygon `Poly4` is covered by a
binary tree of boxes (1635 leaves over the eight contact claims, cut into 119 modules of at most 40 leaves); on a
leaf the four plus-sign entropy terms are bounded by Gibbs tangent planes at rational points and the minus-sign term
`h(1 - m, b - m)` by its chord, which is valid because `h` is jointly concave (`hh_chord`, proved from Mathlib's
concavity of `negMulLog`); the two affine majorants are checked at the box corners. `chk_sound` proves once that a
passing tree gives `G4 = tau max(L, 0) + (1 - tau) R ≤ T` on the whole polygon; the trees are checked by
`decide +kernel` in modules that import no analysis. The exponent [E] uses a second checker (`ERow.chkE`, 60 to 166
kappa-pieces per row, monotonicity of `H` on `[0, 1/2]` and the kappa ↦ 1 - kappa symmetry).

| theorem | statement |
|---|---|
| `V_s11_t1`, `V_s11_t2`, `V_s8_t1`, `V_s8_t2` | [XI] contacts: `V(t1) ≤ t1 h(s)` (with a rational `hsLo ≤ h(s)`), `V(t2) ≤ (1 - t2)(1 - s)` over the whole polygon, s = 11/100 and 1/8 |
| `V_p1_t1`, `V_p1_v`, `V_p2_v`, `V_p2_t2` | Stage 4+: member rho = 49/20 at t1 and at v, member 11/4 at v and t2 |
| `line_s11`, `line_s8`, `line_plus` | Lemma 3.4's hypothesis `min{V, tau h(s), (1 - tau)(1 - s)} ≤ line` for every tau (one circuit; the family) |
| `xi_s11`, `xi_s8`, `xi_plus` | the pairs `l = line(1)`, `r = line(0) ≥ 0` and xi ≥ 0.0044849038, 0.0043428267, 0.0070361406 |
| `C1_*`, `C2_*`, `C1_plus`, `C2_plus`, `C3_plus` | must fail, proved false with explicit colours: one grid step past each contact; each Stage 4+ member alone at the other's contact |
| `F1_s11`, `F1_s8`, `F1_plus` | every valid line has xi ≤ 0.0044849681, 0.0043428942, 0.0070362061 |
| `lam_s11`, `lam_s8`, `lam_plus` | lambda ≤ 2.3978e-8 at N_b = 8e9 (real logs) |
| `splitter_S` | Lemma 4.2, S(q) ≤ 3q - 3 - 2 log2 q for EVERY q ≥ 1 (the script checks q ≤ 2^14 in floats) |
| `K_s11`, `K_s8` | [K]: k_0, c, both conditions of Cor. 3.8 at eps = 1e-9, k_0 - den fails (b), N0 ≥ 2.2035e22 and not ≥ 2.2036e22 |
| `E_D11`, `E_D8`, `E_R11`, `E_R8`, `E_Dplus`, `range_*` | [E]: every cost term of `proofs/stage4.md` Sec. 5.3 ≤ the claim for every kappa in [kappa_lo, 1 - kappa_lo], and H(kappa_lo) < 1 - delta |
| `headline_D11`, `headline_Dplus` | Theorems 4 and 4+ in plain numbers: P3, P4, P6 ≤ 0.4998322132 and ≤ 0.4997369618 |
| `Kc1_D11` to `Kc9_D11`, `Kc1_Dplus`, `Kc2_Dplus`, `Kc_delta_Dplus`, `Kc4_Dplus` | the exponent controls, each proved false (K1 at claim - 3e-7 for Theorem 4 and - 4e-7 for 4+; K8 as the lower bound mu lambda ≥ 5.258e-9) |

Found by the Lean check: `cert_stage4.py`'s [F1] used the witness colours' own values instead of the trivial lines
and printed brackets about 3e-8 too small; fixed in the script and `proofs/stage4.md` Sec. 3.6. No claim changed.

Not in Lean for Stage 4: everything in `proofs/stage4.md` except the certificates' arithmetic, i.e. that `G4`,
`P3R`, `P4dR`, `P6R`, `P4rR` and `lamR` are the costs of DET4 (Secs. 1-7), the cited items of its Sec. 0.2, and
`check_stage4.py` (brute force, stays in Python). `leanchecker` replayed `Stage4Check`, `Stage4Defs`, `Stage4EDefs`,
`Stage4ECheck`, `Stage4Base`, `Stage4XI`, `Stage4E` and `Stage4`; on `Stage4ERows` it exceeded 3 GB and was stopped
(that module is kernel-checked by its build, like every `Stage4Cells_*` module). Peak RSS of any Stage 4 build step:
2979 MB, of which about 680 MB is the `lake` process itself.

**Stage 5 (`Stage5Probs`, `Stage5Cells_*`, `Stage5ECheck`, `Stage5Data`, `Stage5Rows_*`, `Stage5Refs_*`,
`Stage5EDefs`, `Stage5Base`, `Stage5XI`, `Stage5Ctl_0`, `Stage5Ctl_1`, `Stage5E`, `Stage5`) covers
`certificates/stage5/cert_stage5.py` in full: R1, R1b, R2, R3, the seven menu circuits and the family, [LAM], and the controls
K1-K8, C1-C3.** Namespace `SS5`. `Stage5Axioms.lean` prints the axioms of all 83 theorems below: each uses only
`propext`, `Classical.choice`, `Quot.sound` (`axioms_stage5.out`). One command: `./check_stage5.sh`.

[XI] uses Stage 4's method and checker unchanged (`gen_stage5_cells.py`): the twelve contact claims of the six new menu
circuits (s = 2/25, 19/200, 13/125, 111/1000, 59/500, 29/200) are cell trees with 2840 leaves in 210 modules of at most
40 leaves, proved by `SS4.chk_sound`. The menu's s = 1/8 circuit is Stage 4's (same rho, t1, t2), and the single
s = 11/100 circuit and the family are Stage 4's too (`SS4.line_s11`, `line_s8`, `line_plus`, `C3_plus`).

The exponent rows use a new light checker, `Row.chk` (`gen_stage5.py`). A layer kappa is **covered** (`Covered`) when
some design of the row's menu is good there: an alpha of the menu, two menu circuits (only `c1 = c2` and `w = 0` for
the symmetric rows R1, R1b) and a real w, such that the design is valid (`a = 0` or `0 < t < 1`; each outer side holds
j blocks, `j mu ≤ (1 - mu)(1/2 - |w|)`) and P3, P4, P6 are at most the claim. The terms are those of cert_stage5.py,
with the real binary entropy, the real log2 3, lambda = 2.3983e-8, and the circuits' (s, l, r) data. Since every
term increases with l and r, the data's upper bounds on line(1), line(0) suffice (`xi_*`, `lr_*`). A piece of
[0, 1/2] carries one design (menu indices and a rational w), an upper bound on H at its right end, and for `a > 0`
lower bounds on H(t) at both ends (H is concave). For `a = 0`, `t = kappa` and the terms are exact in H(kappa), which
covers the tail [0, 2/5]. The symmetry kappa ↦ 1 - kappa swaps the circuits and negates w (`row_covered`). Pieces:
R1 489, R1b 161, R2 20, R3 32, chosen greedily and each re-checked exactly before Lean runs. The script's 6000 pieces
were not needed, because each row's true sup is 4e-7 to 1.3e-6 below its claim.

The must-fail checker `Row.refute` proves more than the script's controls. At one kappa, every design of the menu
fails for every real w and every lambda ≥ 0. It uses three lower bounds: P3 is at least the mean of its two lines, or
the larger line moved by the largest |w| the fit allows, and P6 is the third.

| theorem | statement |
|---|---|
| `hs_m*`, `hb_C_*` | H(s) of the six new densities (60-term series), and every circuit's `hsLo ≤ H(s) ≤ hsHi` |
| `V_m*_t1`, `V_m*_t2` | [XI] contacts `V(t1) ≤ t1 hsLo`, `V(t2) ≤ (1 - t2)(1 - s)` over the whole polygon, six circuits |
| `line_m*` | Lemma 3.4's hypothesis `min{V, tau h(s), (1 - tau)(1 - s)} ≤ line` for every tau |
| `xi_m*` | xi ≥ 0.0039112900, 0.0043321461, 0.0044574234, 0.0044845813, 0.0044446847, 0.0036893196, and `line(1) ≤ C.l`, `line(0) ≤ C.r` |
| `lr_s11`, `lr_s8`, `lr_plus` | the row data bound Stage 4's lines (xi there: `SS4.xi_s11`, `xi_s8`, `xi_plus`) |
| `C1_*`, `C2_*` | controls C1, C2 for all seven menu circuits, s = 1/8 included: one 1e-4 step past each contact is refuted with an explicit colour |
| `lam5` | lambda ≤ 2.3983e-8 at N_b = 8e9 for every a_b + b_b = N_b/2, real logs (Lemma 3.3) |
| `ab_integral`, `window` | a_b = alpha N_b/2 and s a_b are integers for every alpha and circuit; s rho < 1/2 for every circuit |
| `E_R1`, `E_R1b`, `E_R2`, `E_R3` | P1 = mu, P5 = Pscan = 2 mu and Kenum = mu(2 + lambda) are at most the claim, and every kappa in [0, 1] is covered. Claims: 0.4995054714, 0.4993293934, 0.4991541425, **0.4989524521** |
| `K1_R1`, `K1_R1b`, `K1_R2`, `K1_R3` | each claim minus 2e-6 is refuted, at kappa = 0.4708524, 0.4847785, 0.4982435, 0.4885747 |
| `K2`, `K4`, `K5`, `K5b`, `K6`, `K6b`, `K7` | R2 with mu + 1%; one-sided dedupe against 1/2 (at kappa = 1/2); the design set {0, 97/100}; the earlier float D1 point against 0.49919788; R1 against the ceiling 1/2 - mu (19/20) xi; R1 with alpha 19/20 alone; R3 with the family's (l, r) replaced by the single circuit's: each refuted |
| `K3`, `K8` | no cores: every core-free design has P3 ≥ 1/2 at kappa = 1/2; R1b's two blocks per side do not fit at mu = 0.201 for any w |
| `same_ctl` | each control row is the certified row with only the stated change |
| `chk_sound`, `row_covered`, `refute_sound`, `refute_alphas` | soundness of the two checkers |

K1 refutes the claim minus 2e-6, not the script's 1e-9. The script's K1 tests its own piece bound. The true sup lies
4e-7 to 1.3e-6 below each claim, so only a gap of that size can be proved false. K6's target uses the certified lower
bound on xi, so the true ceiling is no larger than the target.

Found by the Lean check: no defect in cert_stage5.py, and no number changed. A printing nit: the script prints its
xi and l bounds rounded to the nearest 10th digit. For example it prints xi(2/25) >= 0.0039112901, but the exact bound is
0.00391129006. Lean proves the values rounded down, so its last digit can be 1 lower. The computation itself uses the
full floats.

Not in Lean for Stage 5: everything in `proofs/stage5.md` except the certificate's arithmetic, i.e. that
these terms are the costs of the algorithm (Lemmas 2.1-3.5), and `check_stage5.py` (brute force, stays in Python).
`leanchecker` replayed all 53 Stage 5 modules other than the cell trees, and all 53 pass. Those are Stage5ECheck,
Stage5EDefs, Stage5Data, every `Stage5Rows_*` and `Stage5Refs_*`, Stage5Base, Stage5XI, Stage5Ctl_0, Stage5Ctl_1,
Stage5E and Stage5. The `Stage5Cells_*` modules are kernel-checked by their builds, as in Stage 4. The highest peak
RSS of any Stage 5 step was 3065 MB, in one cell module's build, and about 680 MB of that is `lake` itself. No step was
aborted.

**Stage 5b (`Stage5bProbs`, `Stage5bCells_*`, `Stage5bDefs`, `Stage5bData`, `Stage5bRows_*`, `Stage5bRefs_*`,
`Stage5bBase`, `Stage5bFam_*`, `Stage5bCtl_*`, `Stage5bE`, `Stage5b`) covers `certificates/stage5b/cert_stage5b.py` for the
theorem row R4b-min: Lemma 5b.1 for its six families, the row for every kappa in [0, 1], and its controls.** Namespace
`SS5b`. `Stage5bAxioms.lean` prints the axioms of all 107 theorems below: each uses only `propext`,
`Classical.choice`, `Quot.sound` (`axioms_stage5b.out`). One command: `./check_stage5b.sh`. Generators:
`gen_stage5b_cells.py`, then `gen_stage5b.py` (about 12 min).

Lemma 5b.1 is `SS4.line_fam3` (`Stage5bDefs.lean`): if each member is below the line at both ends of its interval,
the two trivial pieces are below it at `v0` and `v3`, and `r, l ≥ 0`, then for every tau in [0, 1] some member or a
trivial piece is below the line. The member statements are 36 cell trees (six per family, Stage 4's method and
checker unchanged), 5125 leaves in 331 modules of at most 40 leaves, assembled in 36 more. The row reuses Stage 5's checker
`Row.chk` and `Row.refute` unchanged: it reads only each circuit's (s, H(s) bounds, l, r), so a family enters exactly
as a single circuit does, with (l, r) the family's line (`xi_*`). The two densities without a family (2/25, 19/200)
use Stage 5's circuits `SS5.C_m80`, `SS5.C_m95`. Pieces: 59.

| theorem | statement |
|---|---|
| `line_fam3` | Lemma 5b.1 with three members |
| `V_f*_ia`, `V_f*_ib` | member i of each family is below the line at both ends of its interval, over the whole colour polygon |
| `fam_f104`, ..., `fam_f145`, `fam_f110` | Lemma 3.4's hypothesis on [0, 1] for the families at s = 13/125, 111/1000, 59/500, 1/8, 29/200, 11/100 |
| `xi_*`, `hb_C_*` | xi of each family's line, the row data carry exactly (l, r), and `hsLo ≤ H(s) ≤ hsHi` for every new circuit |
| `F1_*`, `F1x_*` | [F1]: every line satisfying the hypothesis with that family has xi at most the certified value plus about 4e-6 (from explicit colours at the two breakpoints around 1/2); so the family's line lowered by 1e-5 fails |
| `NEED_*_i` | [NEED]: inside member i's interval there is a tau where both other members (explicit colours) and both trivial pieces are above the line, so no member can be dropped |
| `ab_integral5b`, `window5b` | a_b = alpha N_b/2 and s a_b are integers for every alpha and circuit; s rho < 1/2 for every member |
| `E_R4bmin` | Theorem 5b-F: P1, P5, Kenum and, for every kappa in [0, 1], P3, P4, P6 are at most **0.4986298176** |
| `K1b`, `K2b`, `K7pb`, `K9b`, `KFb_*` | refuted: the claim minus 2e-6; mu + 1%; every family replaced by its single circuit; every (l, r) + 1/100; each of the six families alone replaced by its single circuit |
| `same_ctl5b` | each control row is R4b-min with only the stated change |

Where it ran: the Stage 5b modules were built and the axioms audited on a separate Linux machine (Lean v4.34.1, the
same pinned Mathlib, sources identical to these), in one parallel `lake build` of exactly the module list of
`check_stage5b.sh`, then `lake env lean SubsetsumLean/Stage5bAxioms.lean` and `axioms_ok.sh`: AXIOMS: PASS (107
theorems, standard axioms only). On an 8 GB laptop, `check_stage5b.sh` builds them one at a time (the cell
modules and the f104 analysis modules were also built that way). `leanchecker` was not run on Stage 5b.

Not in Lean for Stage 5b: rows R3, R4 and R4b, the families at 2/25 and 19/200 (R4b-min does not use them), and
everything in `proofs/stage5b.md` except the certificate's arithmetic for R4b-min. The convexity that Lemma 5b.1 needs
is proved in Lean for each colour (`G4` is affine in tau), so it is inside `line_fam3`.

## Paper proof only (not in Lean)

- **The cost model itself.** That g, and the nine terms of Stage 2, are the running-time exponents of the
  algorithms DET and DET2 is proved on paper: correctness, the covering Lemmas 2.1 to 2.4, and the time accounting
  (`proofs/stage1.md` Secs. 2 to 5, `proofs/stage2.md` Secs. 2 to 6). Lean checks the inequalities as formulas only.
- **Cited facts.** CJRS F1 to F10 and Observation 4 (word RAM). Ye–Li Prop. 4.2 and its proof, its dL/dR table,
  AL25 Thm B.2, and the existence of the non-explicit circuit.
- **Stage 1 root existence.** Lean checks every numeric fact behind it: the curve crosses the box, and (3) changes
  sign between the slices at a and b. The final step is on paper. That step uses continuity of the implicit
  function e2(e1), defined by (4), followed by the intermediate value theorem. Only the part
  0.0101041782 <= gamma < gamma* = 0.01010417823... depends on it. Every gamma < 0.0101041782 is fully
  kernel-checked (`stage1_gamma`).
- **Explicit Stage 2.** Everything in `proofs/stage2b-explicit.md` except Certificate [A]'s arithmetic: that the
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
- **Stage 3.** Several steps are proved on paper only (`proofs/stage3.md` Secs. 2 to 4):
  - that g_1, g_2 and g_3 over the polygon are the colour profile of the generalised Sec. 3.5;
  - the rounding (rho) and window steps;
  - Ye-Li Lemma 3.4 and Cor. 3.2/3.3 themselves;
  - that the nine terms are DET3's running-time exponents.
  The majorant controls C1 and C2 stay in Python. A failed majorant is not a false claim, so `s3_F1` is the
  refuted statement behind them. `check_stage3.py` and `check_circuit.py` also stay in Python.
- **Stage 2 minimality of kappa_0.** This uses the fact that log2(k+1)/k decreases for k >= 1, which is on paper.
  Lean checks the value at kappa_0 and at kappa_0 - 2.
- `check_stage1.py` and `check_stage2.py`, the brute-force logic checks, stay in Python.

## Build on the 8 GB Mac

    export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin:$PATH
    lake exe cache get                       # prebuilt Mathlib oleans; never compile Mathlib
    ./build_watch.sh build                   # nice -n 19, one Lean thread, optional RSS abort (set LIMIT_MB=3072 on an 8 GB machine)
    ./build_watch.sh env lean SubsetsumLean/Axioms.lean

The whole project builds in about 4 minutes. Peak RSS per step was 2.87 GB (the explicit modules: 2.86 GB), and most of that is mmapped Mathlib
oleans (`build_peak.log`).

The pinned Mathlib was fetched as a shallow clone of tag v4.34.1, at commit d13f23b, the commit in
`lake-manifest.json`. A full clone ran at about 10 MB/min.

`python3 gen_stage1.py`, `python3 gen_stage2.py`, `python3 gen_explicit.py` and `python3 gen_explicit_n0.py` regenerate the
five generated files from the certificate scripts. The three Sec. 12-13 modules build in about 2 minutes, peak RSS 2.86 GB.
