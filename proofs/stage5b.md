# Stage 5b: rho-families at every menu density, on Stage 5's deterministic route

Stage 5b is Stage 5 (`stage5.md`) with each single circuit of its menu replaced, where that helps, by a family of three
Record 3 circuits (Stage 4 Lemma 3.4 with P = 3). Bases: Stage 5 and Stage 4 (`stage4.md`). Credit: as Stage 4
(`stage4.md`, CREDIT). Stage 5b adds nothing to the Record 3 attribution: the family idea on this route, its
certificate at every menu density, Lemma 5b.1 and the certificate here are ours.

**Review.** One internal referee pass, CONFIRMED; its wording fixes are applied. Internal referee passes are not peer
review.

Scripts: `certificates/stage5b/` (certificate `cert_stage5b.py`, output `cert_stage5b.out`). Lean:
`lean/SubsetsumLean/Stage5b*.lean`. Labels as in Stage 5: [proof], [arg], [cite], [iv], [float].

## Summary of the result

- **Best certified deterministic E [iv]: 0.4986298176** (saving >= 1.3702e-3, +31% over Stage 5's R3 1.0475e-3;
  8.2x Stage 4). Row R4b-min: three-member rho-families at 13/125, 11/100, 111/1000, 59/500, 1/8, 29/200, Stage 5's
  single circuits at 2/25, 19/200, mu = 199/1000, alpha menu {0, ..., 9/10, 93/100, 95/100, ..., 99/100}.

  | row | menu | mu | E_det <= | saving |
  |---|---|---|---|---|
  | R3 (Stage 5, re-run) | 7 single circuits + the Stage 4+ pair at 11/100 | 1/5 | 0.4989524521 | 1.0475e-3 |
  | R4 | 8 triple families | 1/5 | 0.4986354853 | 1.3645e-3 |
  | R4b | 8 triple families, finer alpha menu near 1 | 199/1000 | 0.4986298176 | 1.3702e-3 |
  | **R4b-min (theorem)** | 6 triple families + 2 single circuits | 199/1000 | **0.4986298176** | **1.3702e-3** |

- **The families, re-derived.** Each family's Stage 4 Lemma 3.4 condition (the AL25 B.2 min inside the sup) is proved by a
  piecewise certificate (Lemma 5b.1 below: convex pieces on covering intervals, each checked at both ends with
  Stage 4's prover), so the J = 3 case is a written lemma. s rho < 1/2 holds for
  every member (largest 0.406 at 29/200 x 14/5). The families enter Stage 5's asymmetric cores and outer dedupe
  unchanged (Stage 5's `E_row` is used verbatim). The float search's numbers reproduce exactly.
- **Correction to the float search [float].** Not all eight families are needed. The ones at 2/25, 19/200, 1/8 and 29/200 can each be
  dropped alone at no cost, but they are substitutes (dropping all four costs 2.2e-4). Six suffice, and each of the
  six is needed (control KF, +1.0e-5 to +1.5e-4).
- **The window loss is first order, and out of scope here.** On Record 3's route the window loss (eps_win ~ 1.0 eps')
  changes only the RATE in Stage 4 Lemma 3.5'. The non-explicit theorem needs only eps_win -> 0 as eps' -> 0 (uniform
  continuity), with one eps' for the finite family. So it does not touch this or any certified E (Sec. 3).
- **Controls (all pass).** Per family: [F1] (any valid line has xi within ~2e-6 of the certified one; (l, r) - 1e-5
  is refuted) and [NEED] (each member is needed for its line). Per row: K1 (claim - 1e-9 rejected, all four rows),
  K2 (mu + 1%), K7' (all singles: 0.4991471), KF (each family needed), K9 ((l, r) + 0.01). The vendored Stage 4 and
  Stage 5 scripts are hash-identical to the current `certificates/stage4/cert_stage4.py` (corrected [F1]) and
  `certificates/stage5/cert_stage5.py`.
- **Binding.** P3 at kappa ~ 0.498, design (49/50, 11/100, 111/1000). P6 = 0.498377 is the D1 wall, 2.5e-4 below, so
  circuit gains alone can add at most ~2.5e-4.
- **Weakest step.** Inherited: everything Stage 5 rests on (Record 3's reduction, Stage 4's cited (AL-B2), S2 Lemma
  9.1, the non-explicitness convention). New here: Lemma 5b.1 is elementary, so the weakest new link is Stage 4
  Lemma 3.4 applied with P = 3 per density, which needs each member's window circuit (Lemma 3.5') and its own designs
  and hole fixing. Proved in Stage 4 for any finite P, but only P <= 2 was exercised there, and nothing here is
  brute-forced. In Lean (`lean/LEAN_SCOPE.md`, Stage 5b): Lemma 5b.1 for the six families of R4b-min, the row
  R4b-min and its controls. Rows R3, R4, R4b and the two families R4b-min does not use are checked in Python only.

## 0. Statement

**Theorem 5b-F (row R4b) [proof, given Stage 5 and what it cites; numbers [iv]].** Stage 5's DET5 (one dedupe block
per outer side, D1 estimator) with Stage 5's design table, where the circuit menu has the eight densities
s in {2/25, 19/200, 13/125, 11/100, 111/1000, 59/500, 1/8, 29/200}, the six densities 13/125, 11/100, 111/1000, 59/500,
1/8, 29/200 each served by the three-member family of Sec. 1 and 2/25, 19/200 by Stage 5's single circuits,
mu = 199/1000 and the per-layer alpha menu {0, 1/10, ..., 9/10, 93/100, 95/100, 96/100, 97/100, 98/100, 99/100}, runs
deterministically in poly(n, L) 2^{(E + eps) n} with **E <= 0.4986298176** (saving >= 1.3702e-3; row R4b-min).
The float search's rows are reproduced: R4b (families at all eight densities) gives the same bound, and R4 (all eight, mu = 1/5,
Stage 5's R2 alpha menu) gives E <= 0.4986354853. All improve Stage 5's R3 (E <= 0.4989524521).

**Correction to the float search [float; only KF, "each of the six is needed", is certified].** "Eight families" is more than the bound uses. In R4b, replacing the family at 2/25,
19/200, 1/8 or 29/200 alone by its single circuit leaves the bound unchanged; the four are substitutes (replacing all
four costs 2.2e-4, binding then moves to kappa 0.472 with the pair (13/125, 29/200)). A greedy pass keeps six; each of
the six is needed (control KF).

The theorem is non-explicit in exactly Stage 4 Sec. 7's sense; nothing here adds an explicit construction.

## 1. The family circuits

Each density s has members rho_1 < rho_2 < rho_3 (`FAM_DATA`), a rational line line(tau) = r + (l - r) tau and four
rational breakpoints 0 < v_0 < v_1 < v_2 < v_3 < 1.

**Lemma 5b.1 (piecewise certificate for Stage 4 Lemma 3.4 with a finite family) [proof].** Let V_1, ..., V_J be
convex on [0, 1] and l, r >= 0. Put P_0(tau) := tau h(s), P_i := V_i (1 <= i <= J), P_{J+1}(tau) := (1 - tau)(1 - s).
If P_0(v_0) <= line(v_0), V_i(v_{i-1}) <= line(v_{i-1}) and V_i(v_i) <= line(v_i) for each i, and
P_{J+1}(v_J) <= line(v_J), then min{V_1, ..., V_J, tau h(s), (1 - tau)(1 - s)} <= line on [0, 1].
*Proof.* The intervals [0, v_0], [v_0, v_1], ..., [v_J, 1] cover [0, 1]. On the i-th, P_i - line is convex (line is
affine), so it is at most its larger end value, which is <= 0: for P_0 the ends are P_0(0) - r = -r <= 0 and the
hypothesis at v_0; for P_{J+1} the hypothesis at v_J and P_{J+1}(1) - l = -l <= 0. The minimum is at most the piece of
whichever interval holds tau. ∎
Stage 4+'s certificate is the case J = 2 with v_0, v_2 on the trivial lines; Stage 4's single circuit is J = 1. No
slope condition is needed (Stage 4 used one only because its line was pinned to the two trivial contacts).

**Application [proof, given Stage 4 Lemmas 3.4, 3.5, 3.5' and [iv]].** V_i is Stage 4 Lemma 3.5''s central profile
for rho_i, a max of functions affine in tau, hence convex. Stage 4's prover `Land.prove` (vendored verbatim) bounds
G >= tau max(L, 0) + (1 - tau) R, so it bounds V_i. `cert_stage5b.py` proves the nine statements of Lemma 5b.1 (l >= 0 and r >= 0 are one statement) at every
density in intervals. Then Stage 4 Lemma 3.4 with P = 3 gives (l, r) in K(s); all members are built as decompositions of the same M^{(x)d} (take tensor powers to a common d and n, as Alman-Li Thm B.2 requires, with one eps' for the family). Its hypothesis is per member: each
rho_i needs Lemma 3.5''s window circuit, whose proof uses b <= k1 + rho k0 <= s rho + 2 eps' < 1/2 - eps', so it needs
rho > 1 and **s rho < 1/2 for every member**. The largest product is 29/200 * 14/5 = 0.406; asserted in the code.

| s | rho members | l <= | r <= | xi >= family | xi >= single | used in R4b-min |
|---|---|---|---|---|---|---|
| 2/25 | 47/20, 5/2, 14/5 | 0.2406856510 | 0.0681705340 | 0.0066615026 | 0.0039112901 | single |
| 19/200 | 12/5, 51/20, 14/5 | 0.2604263800 | 0.0834568450 | 0.0070296616 | 0.0043321462 | single |
| 13/125 | 12/5, 51/20, 11/4 | 0.2715549720 | 0.0917467450 | 0.0071234134 | 0.0044574235 | family |
| 11/100 | 12/5, 51/20, 11/4 | 0.2784538020 | 0.0971963110 | 0.0071329226 | 0.0044849038 | family |
| 111/1000 | 12/5, 51/20, 11/4 | 0.2795623830 | 0.0981018290 | 0.0071303496 | 0.0044845814 | family |
| 59/500 | 12/5, 51/20, 11/4 | 0.2870191370 | 0.1044047710 | 0.0070802815 | 0.0044446847 | family |
| 1/8 | 12/5, 51/20, 11/4 | 0.2939787930 | 0.1106383960 | 0.0069736271 | 0.0043428267 | family |
| 29/200 | 49/20, 13/5, 14/5 | 0.3089388000 | 0.1305108810 | 0.0063676821 | 0.0036893197 | family |

All eight families are certified (the two unused ones are kept as facts). The 11/100 triple supersedes Stage 4+'s
pair (xi 0.0070361406).

**Gotcha (at `FAM_DATA` in the code).** The middle member covers only about 0.013 of tau around 1/2. A breakpoint
outside the overlap of the adjacent pieces' valid ranges makes the prover fail, never pass wrongly.

## 2. Combination with Stage 5

Nothing in Stage 5's proof depends on how (l, r) in K(s) was obtained.
- **Asymmetric cores (Stage 5 Lemma 3.4).** The core circuit C(s1) on Hc and C(s2) on Hbc are now exact integer
  circuits obtained from Stage 4 Lemma 3.4's recursion over a three-member family (plus the two trivial circuits).
  The recursion produces one exact circuit for M_0^{(x) d}; the tensor product with (I, P_1) on the non-cores is
  exact as before, with the degrees of Stage 5 Lemma 3.2 at the family's (l_i, r_i).
- **Outer dedupe (Stage 5 Lemmas 2.1-2.4, 3.1).** Untouched: it lives outside the block and never sees the circuit.
- **Round families (Stage 5 Lemma 3.3).** Design-blind except for integrality: a_b = alpha N_b/2 and s a_b must be
  integers for every alpha in the menu and every s. Asserted for every row at N_b = 8 * 10^9.
- **Binding.** P3 at kappa ~ 0.498 with design (alpha, s1, s2) = (49/50, 11/100, 111/1000); P6 = 0.498377 (the D1
  wall) is 2.5e-4 below.
- **Costs.** `E_row` of `cert_stage5.py` (vendored verbatim as `stage5_cert_vendored.py`) evaluates P3, P4, P6, P1,
  P5, Kenum and the tails per piece in intervals; it reads only (s, l, r) of a circuit. R3 re-runs to Stage 5's
  certified 0.4989524520.
- **Hardcoded table (Stage 4 Sec. 7).** Six densities times three members plus two single circuits, each with its own designs and hole
  fixing: a larger finite table, the same non-explicit argument.

## 3. The window loss is first order, and does not touch this theorem [proof of the scope; the loss figures are [float]]

On Record 3's route the window circuit's loss is eps_win ~ 1.0 eps' (no z0 + z1 = 1/2 cancellation),
against ~2.9 eps'^2 for YL's circuit. Stage 4 Lemma 3.5' needs only that for every eps_1 there is some eps' > 0 with
loss <= eps_1/2; that follows from uniform continuity whatever the rate, since c eps' -> 0 as eps' -> 0. Lemma 3.4
then takes eps_1 -> 0 before k and d grow, and eps_1 is absorbed into the theorem's eps. A finite family needs one
eps' for all members (the least of three), which exists. So the rate enters only an explicit n0 or N0, not Theorem 5b-F or any
certified E.

## 4. Controls (each must be rejected; all are in `cert_stage5b.py`)

- **[F1] per family.** Rigorous lower bounds on min{...} at the breakpoints (trivial lines exactly, members by an
  explicit colour evaluated in intervals) bound the xi of any valid line for that family from above; the gap to the
  certified xi is ~2e-6, and the line with (l, r) lowered by 1e-5 is refuted.
- **[NEED] per member.** Inside each member's own interval there is a tau where every other piece is rigorously above
  the line, so no member can be dropped from the certified line.
- **Rows.** K1: claim - 1e-9 rejected for R3, R4, R4b, R4b-min. On R4b-min: K2 mu + 1% (0.4986356679); K7' every
  family replaced by the single circuit at its density (0.4991471390); KF(s) each of the six families alone replaced
  by its single circuit (+1.0e-5 to +1.5e-4, all rejected); K9 every (l, r) raised by 0.01 (0.5000000054).
- **Sanity.** The vendored files are hash-identical to `certificates/stage4/cert_stage4.py` and `certificates/stage5/cert_stage5.py`;
  R3 re-runs to 0.4989524520.

## 5. Not proved here

- Everything Stage 5 and Stage 4 cite or leave as [arg] (AL-B2, S2 Lemma 9.1, non-explicitness), inherited.
- Optimality of the families, breakpoints or menus.
- Any explicit construction, n0 or N0.
