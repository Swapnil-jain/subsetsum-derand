import SubsetsumLean.Stage4Defs
import SubsetsumLean.Stage4ECheck

/-!
# Stage 4: the exponent terms of PROOF.md Sec. 5.3 and the soundness of `ERow.chkE`

Per n, with `t = (kappa - alpha/2)/(1 - alpha)` and `J = H(kappa) - alpha H(s) - (1 - alpha) H(t)`:
- `P3 = 1/2 + mu (H(kappa) - alpha xi - (1 - alpha) H(t)/2 + (1 - alpha)/2 - 1 + delta + lambda)`;
- deterministic: `P4 = mu (J + lambda) + 1/4 + mu log2(3)/4`, `P6 = mu (2 - delta + J + lambda)`;
- randomized (A3): `P4 = 1/4 + mu (H(kappa) - (3/4) alpha H(s) + alpha s/4 - (3/4)(1 - alpha) H(t)
  + (1 - alpha) max(t, 1 - t)/4)`;
- constants `P1 = mu (1 - delta)`, `P2 = 1/2 - mu delta/2`, and (deterministic) `P5 = 2 mu`, `Pscan = mu (2 - delta)`,
  `Kenum = mu (2 + lambda)`.
`E_row` proves every term is at most the claim for every kappa in `[kappa_lo, 1 - kappa_lo]`.
-/

open Real

namespace SS4

open SS

theorem HbU.sound (x : ℚ) (e : HbU) (h : e.ok x = true) : Hb x ≤ e.hi := by
  simp only [HbU.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hx0, hx1⟩, h1⟩, h2⟩, hhi⟩, hA⟩ := h
  have a1 := logGe_sound h1
  have a2 := logGe_sound h2
  push_cast at a2
  have c1 := L2lo_le_log2
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hhi' : (0 : ℝ) ≤ e.hi := by exact_mod_cast hhi
  have hA' : -(x : ℝ) * e.l1 - (1 - x) * e.l2 ≤ e.hi * L2loQ := by exact_mod_cast hA
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have m1 := mul_le_mul_of_nonneg_left a1 hx0'.le
  have m2 := mul_le_mul_of_nonneg_left a2 (show (0 : ℝ) ≤ 1 - x by linarith)
  have m3 := mul_le_mul_of_nonneg_left c1 hhi'
  unfold Hb
  rw [div_le_iff₀ hL]
  nlinarith

theorem HbL.sound (x : ℚ) (e : HbL) (h : e.ok x = true) : (e.lo : ℝ) ≤ Hb x := by
  simp only [HbL.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hx0, hx1⟩, h1⟩, h2⟩, hlo⟩, hA⟩ := h
  have b1 := logLe_sound h1
  have b2 := logLe_sound h2
  push_cast at b2
  have c2 := log2_le_L2hi
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hlo' : (0 : ℝ) ≤ e.lo := by exact_mod_cast hlo
  have hA' : (e.lo : ℝ) * L2hiQ ≤ -(x : ℝ) * e.u1 - (1 - x) * e.u2 := by exact_mod_cast hA
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have m1 := mul_le_mul_of_nonneg_left b1 hx0'.le
  have m2 := mul_le_mul_of_nonneg_left b2 (show (0 : ℝ) ≤ 1 - x by linarith)
  have m3 := mul_le_mul_of_nonneg_left c2 hlo'
  unfold Hb
  rw [le_div_iff₀ hL]
  nlinarith

lemma Hb_symm4 (x : ℝ) : Hb (1 - x) = Hb x := by unfold Hb; rw [sub_sub_cancel]; ring

/-! ## The terms -/

noncomputable def tR (α κ : ℝ) : ℝ := (κ - α / 2) / (1 - α)
noncomputable def JR (α s κ : ℝ) : ℝ := Hb κ - α * Hb s - (1 - α) * Hb (tR α κ)
noncomputable def P3R (α μ δ ξ lam κ : ℝ) : ℝ :=
  1 / 2 + μ * (Hb κ - α * ξ - (1 - α) * Hb (tR α κ) / 2 + (1 - α) / 2 - 1 + δ + lam)
noncomputable def P4dR (α μ lam s κ : ℝ) : ℝ := μ * (JR α s κ + lam) + 1 / 4 + μ * (log 3 / log 2) / 4
noncomputable def P6R (α μ δ lam s κ : ℝ) : ℝ := μ * (2 - δ + JR α s κ + lam)
noncomputable def P4rR (α μ s κ : ℝ) : ℝ :=
  1 / 4 + μ * (Hb κ - 3 / 4 * α * Hb s + α * s / 4 - 3 / 4 * (1 - α) * Hb (tR α κ)
    + (1 - α) * max (tR α κ) (1 - tR α κ) / 4)

/-- Every kappa-dependent term of the row at `kappa` is at most the claim. -/
def ETerms (R : ERow) (κ : ℝ) : Prop :=
  P3R R.α R.μ R.δ R.ξ R.lam κ ≤ R.claim ∧
  (R.det = true → P4dR R.α R.μ R.lam R.s κ ≤ R.claim ∧ P6R R.α R.μ R.δ R.lam R.s κ ≤ R.claim) ∧
  (R.det = false → P4rR R.α R.μ R.s κ ≤ R.claim)

lemma tR_cast (α κ : ℚ) : ((tq α κ : ℚ) : ℝ) = tR α κ := by unfold tq tR; push_cast; ring

lemma tR_symm {α κ : ℝ} (hα : α < 1) : tR α (1 - κ) = 1 - tR α κ := by
  unfold tR
  have : (1 : ℝ) - α ≠ 0 := by linarith
  field_simp; ring

lemma ETerms_symm (R : ERow) (hα : (R.α : ℝ) < 1) (κ : ℝ) : ETerms R (1 - κ) ↔ ETerms R κ := by
  unfold ETerms P3R P4dR P6R P4rR JR
  rw [Hb_symm4, tR_symm hα, Hb_symm4, sub_sub_cancel, max_comm]

/-- One piece: the bounds at its ends give every term on the piece. -/
theorem piece_sound (R : ERow) (hα0 : (0 : ℝ) < R.α) (hα1 : (R.α : ℝ) < 1) (hμ : (0 : ℝ) < R.μ)
    (hs : (R.hsLo : ℝ) ≤ Hb R.s) (hl3 : log 3 / log 2 ≤ R.l3) (κa κb HK HT : ℚ) (hka : (R.α : ℝ) / 2 ≤ κa)
    (hb : (κb : ℝ) ≤ 1 / 2) (hHK : Hb κb ≤ HK) (hHT : (HT : ℝ) ≤ Hb (tR R.α κa))
    (h : R.pieceOK HK HT (tq R.α κa) = true) (κ : ℝ) (h1 : (κa : ℝ) ≤ κ) (h2 : κ ≤ κb) : ETerms R κ := by
  have h1α : (0 : ℝ) < 1 - R.α := by linarith
  have hk0 : (0 : ℝ) ≤ κ := by linarith
  -- H(kappa) ≤ HK and HT ≤ H(t)
  have eK : Hb κ ≤ HK := (Hb_mono hk0 h2 hb).trans hHK
  have ht0 : 0 ≤ tR R.α κa := by unfold tR; exact div_nonneg (by linarith) h1α.le
  have htt : tR R.α κa ≤ tR R.α κ := by unfold tR; exact div_le_div_of_nonneg_right (by linarith) h1α.le
  have ht12 : tR R.α κ ≤ 1 / 2 := by
    unfold tR; rw [div_le_iff₀ h1α]; linarith
  have eT : (HT : ℝ) ≤ Hb (tR R.α κ) := hHT.trans (Hb_mono ht0 htt ht12)
  have emax : max (tR R.α κ) (1 - tR R.α κ) ≤ 1 - ((tq R.α κa : ℚ) : ℝ) := by
    rw [tR_cast, max_le_iff]; constructor <;> linarith
  have hHbs := hs
  unfold ERow.pieceOK at h
  have mK := mul_le_mul_of_nonneg_left eK hμ.le
  have mT := mul_le_mul_of_nonneg_left eT (mul_nonneg hμ.le h1α.le)
  have mS := mul_le_mul_of_nonneg_left hHbs (mul_nonneg hμ.le hα0.le)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have c := h.1
    have c' : ((1 / 2 + R.μ * (HK - R.α * R.ξ - (1 - R.α) * HT / 2 + (1 - R.α) / 2 - 1 + R.δ + R.lam) : ℚ) : ℝ)
        ≤ R.claim := by exact_mod_cast c
    push_cast at c'
    unfold P3R; nlinarith
  · intro hd
    simp only [hd, ite_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, c4, c6⟩ := h
    have c4' : ((R.μ * (HK - R.α * R.hsLo - (1 - R.α) * HT + R.lam) + 1 / 4 + R.μ * R.l3 / 4 : ℚ) : ℝ)
        ≤ R.claim := by exact_mod_cast c4
    have c6' : ((R.μ * (2 - R.δ + (HK - R.α * R.hsLo - (1 - R.α) * HT) + R.lam) : ℚ) : ℝ) ≤ R.claim := by
      exact_mod_cast c6
    push_cast at c4' c6'
    have m3 := mul_le_mul_of_nonneg_left hl3 hμ.le
    unfold P4dR P6R JR
    constructor <;> nlinarith
  · intro hd
    simp only [hd, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, c4⟩ := h
    have c4' : ((1 / 4 + R.μ * (HK - 3 / 4 * R.α * R.hsLo + R.α * R.s / 4 - 3 / 4 * (1 - R.α) * HT
        + (1 - R.α) * (1 - tq R.α κa) / 4) : ℚ) : ℝ) ≤ R.claim := by exact_mod_cast c4
    push_cast at c4'
    rw [tR_cast] at c4' emax
    have mM := mul_le_mul_of_nonneg_left emax (mul_nonneg hμ.le h1α.le)
    unfold P4rR
    nlinarith

/-- The pieces cover `[ka, 1/2]`. -/
theorem chkE_sound (R : ERow) (hα0 : (0 : ℝ) < R.α) (hα1 : (R.α : ℝ) < 1) (hμ : (0 : ℝ) < R.μ)
    (hs : (R.hsLo : ℝ) ≤ Hb R.s) (hl3 : log 3 / log 2 ≤ R.l3) :
    ∀ (ps : List EP) (κa : ℚ), R.chkE κa ps = true → ps ≠ [] → (R.α : ℝ) / 2 ≤ κa →
      ∀ κ : ℝ, (κa : ℝ) ≤ κ → κ ≤ 1 / 2 → ETerms R κ := by
  intro ps
  induction ps with
  | nil => intro κa _ hne; exact absurd rfl hne
  | cons p ps ih =>
    intro κa h _ hka κ h1 h2
    simp only [ERow.chkE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hab, hb⟩, hk⟩, ht⟩, hpc⟩, hrest⟩ := h
    have hab' : (κa : ℝ) ≤ p.κb := by exact_mod_cast hab
    have hb' : (p.κb : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hb
    rcases le_total κ p.κb with hκ | hκ
    · have hT := HbL.sound _ _ ht
      rw [tR_cast] at hT
      exact piece_sound R hα0 hα1 hμ hs hl3 κa p.κb p.hk.hi p.ht.lo hka hb' (HbU.sound _ _ hk) hT hpc κ h1 hκ
    · rcases ps with _ | ⟨q, qs⟩
      · simp only [ERow.chkE, decide_eq_true_eq] at hrest
        have : (p.κb : ℝ) = 1 / 2 := by
          rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hrest
        have hκ' : κ = p.κb := by linarith
        have hT := HbL.sound _ _ ht
        rw [tR_cast] at hT
        exact piece_sound R hα0 hα1 hμ hs hl3 κa p.κb p.hk.hi p.ht.lo hka hb' (HbU.sound _ _ hk) hT hpc κ h1
          hκ'.le
      · exact ih p.κb hrest (List.cons_ne_nil q qs) (by linarith) κ hκ h2

/-- [E] for one row: every term, constant or not, is at most the claim on `[kappa_lo, 1 - kappa_lo]`. -/
theorem E_row (R : ERow) (κlo : ℚ) (ps : List EP) (hok : R.ok κlo = true) (h : R.chkE κlo ps = true)
    (hne : ps ≠ []) (hs : (R.hsLo : ℝ) ≤ Hb R.s) (hl3 : log 3 / log 2 ≤ R.l3) :
    ((R.μ : ℝ) * (1 - R.δ) ≤ R.claim ∧ 1 / 2 - (R.μ : ℝ) * R.δ / 2 ≤ R.claim ∧
      (R.det = true → 2 * (R.μ : ℝ) ≤ R.claim ∧ (R.μ : ℝ) * (2 - R.δ) ≤ R.claim ∧ (R.μ : ℝ) * (2 + R.lam) ≤ R.claim)) ∧
    ∀ κ : ℝ, (κlo : ℝ) ≤ κ → κ ≤ 1 - κlo → ETerms R κ := by
  unfold ERow.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨ha0, ha1⟩, hm⟩, hal⟩, -⟩, c1⟩, c2⟩, cdet⟩ := hok
  have ha0' : (0 : ℝ) < R.α := by exact_mod_cast ha0
  have ha1' : (R.α : ℝ) < 1 := by exact_mod_cast ha1
  have hm' : (0 : ℝ) < R.μ := by exact_mod_cast hm
  have hal' : (R.α : ℝ) / 2 ≤ κlo := by exact_mod_cast hal.le
  have c2' : ((1 / 2 - R.μ * R.δ / 2 : ℚ) : ℝ) ≤ R.claim := by exact_mod_cast c2
  push_cast at c2'
  refine ⟨⟨by exact_mod_cast c1, c2', ?_⟩, ?_⟩
  · intro hd
    simp only [hd, ite_true, Bool.and_eq_true, decide_eq_true_eq] at cdet
    obtain ⟨⟨d1, d2⟩, d3⟩ := cdet
    exact ⟨by exact_mod_cast d1, by exact_mod_cast d2, by exact_mod_cast d3⟩
  · intro κ h1 h2
    have half := chkE_sound R ha0' ha1' hm' hs hl3 ps κlo h hne hal'
    rcases le_total κ (1 / 2) with hk | hk
    · exact half κ h1 hk
    · rw [← ETerms_symm R ha1']
      exact half (1 - κ) (by linarith) (by linarith)

end SS4
