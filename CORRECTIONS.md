# Corrections

Defects that we found and fixed ourselves, in the proofs, the certificates and their descriptions. None of them
changes a headline exponent. Each fix is also stated at the place it applies.

## Found by the Lean check

- **Stage 2, the circuit size N'.** An earlier draft stated N' >= 2.2036e22. The exact value is
  N' = 22035779076245688040224, about 2.20358e22, so the bound is N' >= 2.2035e22. Lean proves the corrected bound
  (`stage2_K`) and proves the old figure false (`stage2_K_fails_N`). N' only measures how far the circuit is from
  explicit; nothing else depends on it (`proofs/stage2.md`, `proofs/stage3.md`).
- **Stage 4, the [F1] brackets.** `certificates/stage4/cert_stage4.py` computed its upper brackets on xi (the bound on
  every valid line, a must-fail control) from the witness colours' own values instead of the trivial lines, and
  printed brackets about 3e-8 too small (0.0043428848 and 0.0044849401). The line need only pass above the trivial
  lines at the contacts. Fixed in the script and in `proofs/stage4.md` Sec. 3.6. No claim changed. Stage 5 and
  Stage 5b vendor the corrected script; Stage 5 never calls [F1], so none of its numbers moved.
- **Stage 4, Lemma 4.2.** The script checks the bound S(q) <= 3q - 3 - 2 log2 q for q <= 2^14 only; Lean proves it
  for every q.
- **Stage 5, printed digits.** `cert_stage5.py` prints its xi and l bounds rounded to the nearest 10th digit (for
  example xi(2/25) >= 0.0039112901, where the exact bound is 0.00391129006). Lean proves the values rounded down, so
  its last digit can be one lower. The computation uses the full values; no number changed.

## Found by our referee passes and brute-force checks

- **Stage 2b, the explicit construction.** The potential is now an exact rational (ceil), the term order in the
  left-degree dominance is corrected, the window condition q | k(k+2) is stated (it lowered N0 from about 1e52 to
  1.0091e50), and the preprocessing count is written out (`proofs/stage2b-explicit.md`).
- **Stage 2b, Secs. 12-13.** One claim-level wording defect in the headline of the smaller-n0 table, now fixed.
- **Stage 3, the fallback exponent.** A printed 0.4999949918 was a round-down; the fallback is stated at 12 places,
  E <= 0.499994991801 (`proofs/stage3.md` Sec. 0.1).
- **Stage 4, Lemma 5.2.** It assumed p <= |W_c| without saying so. That holds for p ~ T but fails at p ~ N once
  N < 2(M + 1) x_0, the regime Stage 5 uses. The lemma now states the step and gives the min(p, |W_c|) form, at no
  cost (`proofs/stage4.md` Lemma 5.2, `proofs/stage5.md` Lemma 2.4). The Stage 5 brute force hits this regime on 18
  runs.
- **Stage 4, referee fixes.** One-sided rounding in the residue estimator, the enumeration chain of the compatible K,
  the cost of the backward pass, the hidden 2^{2^33} constant, and a per-s bound lmax in the size certificate
  (`proofs/stage4.md` Sec. 0.1). A brute-force regime where C_k is a proper subset of the cube was added.
- **Stage 5, the layer range.** Without Stage 4's few/many cut, the layers run over all kappa, so an earlier
  "ceiling mu alpha xi" fails for symmetric cores: the saving is mu xi/2 there. The rows are stated as sups over all
  kappa in [0, 1] (`proofs/stage5.md` Sec. 5.3; controls K6, K6b).
- **Stage 5, the design set {0, alpha}.** An earlier float figure, 0.49919788, missed a gap near kappa = 0.4485; that
  design set's rigorous bound is 0.4992433. Intermediate alphas per layer repair it, and the certified row R2 is
  better than the old float (`proofs/stage5.md` Sec. 5.4; control K5b).
- **Stage 5b, the family count.** An earlier float search used families at all eight menu densities. Six suffice,
  and each of the six is needed (control KF); the theorem row R4b-min uses six (`proofs/stage5b.md` Sec. 0).
