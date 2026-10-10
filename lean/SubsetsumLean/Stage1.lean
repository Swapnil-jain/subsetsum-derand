import SubsetsumLean.Stage1Points

/-!
# Stage 1 headline: the exponent claim of Theorem 1 (PROOF.md, Sec. 6)

`stage1_gamma`: for every `gamma < 0.0101041782` there is a rational admissible point with `g > gamma`, and a rational
`lambda` with the three inequalities of Lemma 6.2. This is the exponent half of Theorem 1; that the algorithm DET
with these constants is correct and costs `O(2^{n/2} l^{-gamma})` is the paper proof (PROOF.md Secs. 2-5).
-/

open Real

namespace SS

lemma Admissible.mono {e1 e2 s s' : ℝ} (h : Admissible e1 e2 s) (hs : s' ≤ s) : Admissible e1 e2 s' :=
  { h with saving := lt_of_le_of_lt hs h.saving }

/-- Every `gamma < 0.0101041782` is achieved at the rational corner `(a, c)` of the certified root box. -/
theorem stage1_gamma (γ : ℝ) (hγ : γ < 101041782 / 10 ^ 10) :
    ∃ e1 e2 : ℚ, Admissible e1 e2 γ ∧ ∃ lam : ℚ, 2 * γ < lam ∧ (lam : ℝ) < lam0 e1 e2 ∧
      γ < delta e1 e2 / 2 ∧ γ < (lam : ℝ) / 2 ∧ γ < theta0 e1 e2 + (lam0 e1 e2 - lam) := by
  have hb := (stage1_box (157920369638 / 1000000000000) ⟨le_rfl, by norm_num⟩
    (242668928272905 / 1000000000000000) ⟨le_rfl, by norm_num⟩).1
  refine ⟨157920369638 / 1000000000000, 242668928272905 / 1000000000000000, ?_⟩
  push_cast
  have ha := hb.mono (s' := γ) (by norm_num at hγ ⊢; linarith)
  exact ⟨ha, lemma_6_2_rational ha.saving⟩

end SS
