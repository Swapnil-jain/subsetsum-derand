import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Stage 2: the exponent of the deterministic Ye-Li algorithm (`certificates/stage2/cert_eps.py`)

Cost terms per unit n at prefix m = pi n (PROOF.md Lemma 6.1), with gamma = 2 xi'/3:

    T_prefix = pi, T_prime = T_layers = T_cover = 2 pi, T_hist = log2(3) pi,
    T_left = 1/4 + pi/2, T_right = 1/4 + 3 pi/4,
    T_few = 1/2 - gamma pi/2, T_many = 1/2 - (xi' - gamma) pi + 2 eps pi.

`T_hist` uses the real `log2 3` here (`cert_eps.py` uses the bound 317/200, which `log2_3_lt` proves from
`3^200 < 2^317`). Ye-Li's true constants `xiT`, `dLT`, `dRT` (arXiv 2610.10446, Sec. 4) are not computed: they are
variables, constrained only by the hypotheses each theorem states (their 20-place table truncations, or just the
statement `xi > 0.00002` of Prop. 4.2).
-/

open Real

namespace SS

set_option exponentiation.threshold 400 in
/-- `log2 3 < 317/200`, from the integer comparison `3^200 < 2^317`. -/
lemma log2_3_lt : logb 2 3 < 317 / 200 := by
  have hN : (3 : ℕ) ^ 200 < 2 ^ 317 := by decide
  have h : ((3 : ℝ)) ^ 200 < (2 : ℝ) ^ 317 := by exact_mod_cast hN
  have h2 := Real.log_lt_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at h2
  have hl : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [Real.logb, div_lt_iff₀ hl]
  push_cast at h2
  linarith

/-- The nine cost terms of PROOF.md Lemma 6.1, in the order of `cert_eps.py`. -/
noncomputable def s2Terms (pi xi eps : ℝ) : List ℝ :=
  [pi, 2 * pi, 2 * pi, 2 * pi, logb 2 3 * pi, 1 / 4 + pi / 2, 1 / 4 + 3 / 4 * pi,
    1 / 2 - (2 / 3 * xi) * pi / 2, 1 / 2 - (xi - 2 / 3 * xi) * pi + 2 * eps * pi]

/-- Every check of `cert_eps.py`'s `check`: the side conditions of PROOF.md Lemma 3.5, `xi'` a lower bound on
Ye-Li's `xi`, the rational pair `(dl, dr)` termwise above Ye-Li's pair with `dl + dr <= 1/2 - 2 xi'` (admissible
by upward closure), and every cost term below `bound`. -/
structure CertEps (pi xi eps bound dl dr xiT dLT dRT : ℝ) : Prop where
  pi_pos : 0 < pi
  pi_le_third : pi ≤ 1 / 3
  pi_le_two_fifths : pi ≤ 2 / 5
  xi_nonneg : 0 ≤ xi
  xi_le : xi ≤ xiT
  dl_ge : dLT ≤ dl
  dr_ge : dRT ≤ dr
  pair : dl + dr ≤ 1 / 2 - 2 * xi
  terms_lt : ∀ t ∈ s2Terms pi xi eps, t < bound

/-- Each term below `bound` from explicit rational bounds (the `log2 3` term through `log2_3_lt`). -/
lemma s2Terms_lt {pi xi eps bound : ℝ} (hpi : 0 ≤ pi) (h1 : pi < bound) (h2 : 2 * pi < bound)
    (h5 : 317 / 200 * pi < bound) (h6 : 1 / 4 + pi / 2 < bound)
    (h7 : 1 / 4 + 3 / 4 * pi < bound) (h8 : 1 / 2 - (2 / 3 * xi) * pi / 2 < bound)
    (h9 : 1 / 2 - (xi - 2 / 3 * xi) * pi + 2 * eps * pi < bound) :
    ∀ t ∈ s2Terms pi xi eps, t < bound := by
  have hl : logb 2 3 * pi ≤ 317 / 200 * pi := mul_le_mul_of_nonneg_right log2_3_lt.le hpi
  intro t ht
  simp only [s2Terms, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

/-- The `many sums` term is the last one; a claim below it is false. -/
lemma s2_many_mem (pi xi eps : ℝ) :
    1 / 2 - (xi - 2 / 3 * xi) * pi + 2 * eps * pi ∈ s2Terms pi xi eps := by simp [s2Terms]

lemma s2_cover_mem (pi xi eps : ℝ) : 2 * pi ∈ s2Terms pi xi eps := by simp [s2Terms]

lemma s2_few_mem (pi xi eps : ℝ) : 1 / 2 - (2 / 3 * xi) * pi / 2 ∈ s2Terms pi xi eps := by simp [s2Terms]

/-! ## Ye-Li Cor. 3.2's block length (Certificate 7.2[K]) -/

/-- Cor. 3.2, first condition, for the rational pair: `(2/kappa)(max(dL', dR') + eps/4) <= eps/4`. -/
def kcond1 (dl dr eps κ : ℝ) : Prop := 2 / κ * (max dl dr + eps / 4) ≤ eps / 4
/-- Cor. 3.2, second condition: `log2(kappa + 1)/kappa <= eps/4`. -/
noncomputable def kcond2 (eps κ : ℝ) : Prop := logb 2 (κ + 1) / κ ≤ eps / 4

end SS
