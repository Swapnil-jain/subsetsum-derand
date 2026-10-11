import SubsetsumLean.Stage4EDefs
import SubsetsumLean.Stage5ECheck

/-!
# Stage 5: the exponent terms of `derand/stage5/cert_stage5.py` over the reals, and the soundness of the checkers

`Good R lam claim a c1 c2 w κ`: the design `(a, c1, c2, w)` is valid at layer kappa and its terms P3, P4, P6 (with
`lambda = lam`, real binary entropy and the real `log2 3`) are at most `claim`. `Covered R κ`: some design of the row's
menu is good at kappa with the row's own lambda and claim.
- `chk_sound`: a passing `Row.chk` covers `[ka, kend]`; `row_covered` adds the symmetry `kappa ↦ 1 - kappa` (the two
  circuits swap and `w` changes sign), so pieces of `[0, 1/2]` cover all of `[0, 1]`.
- `refute_sound`: a passing `Row.refute` shows that at that kappa NO design of the menu is good, for any `w` and any
  `lambda ≥ 0`.
-/

open Real

namespace SS5

open SS SS4

/-! ## Binary entropy facts -/

lemma Hb_le_one (x : ℝ) : Hb x ≤ 1 := by
  rw [Hb_eq, div_le_one (Real.log_pos one_lt_two)]
  exact binEntropy_le_log_two

/-- `H` is concave, so on `[ta, tb]` it is at least its value at one end (monotone on each side of 1/2). -/
lemma Hb_ge_min {ta t tb : ℝ} (h0 : 0 ≤ ta) (h1 : ta ≤ t) (h2 : t ≤ tb) (h3 : tb ≤ 1) :
    min (Hb ta) (Hb tb) ≤ Hb t := by
  rcases le_total t (1 / 2) with h | h
  · exact (min_le_left _ _).trans (Hb_mono h0 h1 h)
  · refine (min_le_right _ _).trans ?_
    rw [← Hb_symm4 tb, ← Hb_symm4 t]
    exact Hb_mono (by linarith) (by linarith) (by linarith)

lemma HbL.range {x : ℚ} {e : HbL} (h : e.ok x = true) : (0 : ℝ) < x ∧ (x : ℝ) < 1 := by
  simp only [HbL.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by exact_mod_cast h.1.1.1.1.1, by exact_mod_cast h.1.1.1.1.2⟩

/-! ## The terms -/

noncomputable def t5R (a s1 s2 κ : ℝ) : ℝ := (κ - a * (s1 + 1 - s2) / 2) / (1 - a)

lemma t5_cast (a s1 s2 κ : ℚ) : ((t5 a s1 s2 κ : ℚ) : ℝ) = t5R a s1 s2 κ := by unfold t5 t5R; push_cast; ring

lemma t5R_zero (s1 s2 κ : ℝ) : t5R 0 s1 s2 κ = κ := by unfold t5R; ring

lemma t5R_symm (a s1 s2 κ : ℝ) (ha : a < 1) : t5R a s1 s2 (1 - κ) = 1 - t5R a s2 s1 κ := by
  unfold t5R
  have : (1 : ℝ) - a ≠ 0 := by linarith
  field_simp
  ring

lemma t5R_mono {a s1 s2 x y : ℝ} (ha : a < 1) (h : x ≤ y) : t5R a s1 s2 x ≤ t5R a s1 s2 y := by
  unfold t5R; exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- One line of P3: `1/2 + mu (base + (a/2)(sA - H(sB) + rA + lB)) + (1 - mu) w`, with `Hk = H(kappa)`, `Ht = H(t)`. -/
noncomputable def line5 (μ lam a sA rA lB HB w Hk Ht : ℝ) : ℝ :=
  1 / 2 + μ * (Hk - (1 - a) * Ht / 2 + (1 - a) / 2 - 1 + lam + a / 2 * (sA - HB + rA + lB)) + (1 - μ) * w

/-- P3: the larger of the u-line (`c1` left) and the v-line (`c2` left, `-w`), `+ os` on the v-line, minus the gain of
`j` dedupe blocks. -/
noncomputable def P3v (μ lam j os a s1 l1 r1 s2 l2 r2 w Hk Ht H1 H2 : ℝ) : ℝ :=
  max (line5 μ lam a s1 r1 l2 H2 w Hk Ht) (line5 μ lam a s2 r2 l1 H1 (-w) Hk Ht + os) - (j - 1) * μ * (1 - Hk)

noncomputable def Jv (a Hk Ht H1 H2 : ℝ) : ℝ := Hk - a / 2 * (H1 + H2) - (1 - a) * Ht

noncomputable def P4v (μ lam L3 w J : ℝ) : ℝ :=
  μ * (J + lam) + μ * (L3 + 1) / 4 + max μ ((1 - μ) * (1 / 2 + |w|) - μ)

noncomputable def P6v (μ lam Hk J : ℝ) : ℝ := μ * (1 + Hk + J + lam)

/-- The design `(a, c1, c2, w)` is valid at kappa and P3, P4, P6 (with `lambda = lam`) are at most `claim`. -/
def Good (R : Row) (lam claim : ℝ) (a : ℚ) (c1 c2 : Circ) (w κ : ℝ) : Prop :=
  (a = 0 ∨ (0 < t5R a c1.s c2.s κ ∧ t5R a c1.s c2.s κ < 1)) ∧
  (R.j : ℝ) * R.μ ≤ (1 - R.μ) * (1 / 2 - |w|) ∧
  P3v R.μ lam R.j R.osv a c1.s c1.l c1.r c2.s c2.l c2.r w (Hb κ)
    (Hb (t5R a c1.s c2.s κ)) (Hb c1.s) (Hb c2.s) ≤ claim ∧
  P4v R.μ lam (log 3 / log 2) w (Jv a (Hb κ) (Hb (t5R a c1.s c2.s κ)) (Hb c1.s) (Hb c2.s)) ≤ claim ∧
  P6v R.μ lam (Hb κ) (Jv a (Hb κ) (Hb (t5R a c1.s c2.s κ)) (Hb c1.s) (Hb c2.s)) ≤ claim

/-- `(a, c1, c2, w)` is a design of the row's menu. -/
def InMenu (R : Row) (a : ℚ) (c1 c2 : Circ) (w : ℝ) : Prop :=
  a ∈ R.alphas ∧ c1 ∈ R.circs ∧ c2 ∈ R.circs ∧ (R.sym = true → c1 = c2 ∧ w = 0)

/-- Layer kappa is served: some menu design is good with the row's lambda and claim. -/
def Covered (R : Row) (κ : ℝ) : Prop :=
  ∃ a : ℚ, ∃ c1 c2 : Circ, ∃ w : ℝ, InMenu R a c1 c2 w ∧ Good R R.lam R.claim a c1 c2 w κ

/-- Layer kappa is served with lambda = `lam` (used by the controls, which hold for every `lam ≥ 0`). -/
def CoveredL (R : Row) (lam κ : ℝ) : Prop :=
  ∃ a : ℚ, ∃ c1 c2 : Circ, ∃ w : ℝ, InMenu R a c1 c2 w ∧ Good R lam R.claim a c1 c2 w κ

/-! ## Symmetry -/

lemma P3v_swap (μ lam j a s1 l1 r1 s2 l2 r2 w Hk Ht H1 H2 : ℝ) :
    P3v μ lam j 0 a s2 l2 r2 s1 l1 r1 (-w) Hk Ht H2 H1 = P3v μ lam j 0 a s1 l1 r1 s2 l2 r2 w Hk Ht H1 H2 := by
  unfold P3v
  rw [neg_neg, add_zero, add_zero, max_comm]

lemma Good_symm (R : Row) (hos : R.osv = 0) (lam claim : ℝ) (a : ℚ) (ha : (a : ℝ) < 1) (c1 c2 : Circ)
    (w κ : ℝ) (h : Good R lam claim a c1 c2 w (1 - κ)) : Good R lam claim a c2 c1 (-w) κ := by
  obtain ⟨hv, hf, h3, h4, h6⟩ := h
  rw [t5R_symm _ _ _ _ ha, Hb_symm4, Hb_symm4] at h3 h4 h6
  rw [t5R_symm _ _ _ _ ha] at hv
  simp only [hos, Rat.cast_zero] at h3 ⊢
  refine ⟨?_, by rwa [abs_neg], ?_, ?_, ?_⟩
  · rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ⟨by linarith [hv.2], by linarith [hv.1]⟩
  · rw [hos, Rat.cast_zero, P3v_swap]; exact h3
  · unfold P4v Jv at h4 ⊢; rw [abs_neg, add_comm (Hb (c2.s : ℝ))]; exact h4
  · unfold P6v Jv at h6 ⊢; rw [add_comm (Hb (c2.s : ℝ))]; exact h6

/-! ## Soundness of one piece -/

/-- The rational terms bound the real ones (the case `a > 0`: entropy bounds in the monotone direction). -/
lemma terms_le {μ lam j os a s1 l1 r1 s2 l2 r2 w claim l3 L3 Hk Ht H1 H2 HK HT h1 h2 : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) (hj : 1 ≤ j)
    (eK : Hk ≤ HK) (eT : HT ≤ Ht) (e1 : h1 ≤ H1) (e2 : h2 ≤ H2) (eL : L3 ≤ l3)
    (cu : 1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1 + lam) + a / 2 * (s1 - h2 + r1 + l2)) + (1 - μ) * w
      - (j - 1) * μ * (1 - HK) ≤ claim)
    (cv : 1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1 + lam) + a / 2 * (s2 - h1 + l1 + r2)) - (1 - μ) * w
      + os - (j - 1) * μ * (1 - HK) ≤ claim)
    (c4 : μ * ((HK - a / 2 * (h1 + h2) - (1 - a) * HT) + lam) + μ * (l3 + 1) / 4 + max μ ((1 - μ) * (1 / 2 + |w|) - μ)
      ≤ claim)
    (c6 : μ * (1 + HK + (HK - a / 2 * (h1 + h2) - (1 - a) * HT) + lam) ≤ claim) :
    P3v μ lam j os a s1 l1 r1 s2 l2 r2 w Hk Ht H1 H2 ≤ claim ∧ P4v μ lam L3 w (Jv a Hk Ht H1 H2) ≤ claim ∧
      P6v μ lam Hk (Jv a Hk Ht H1 H2) ≤ claim := by
  have m1 := mul_le_mul_of_nonneg_left eK hμ0
  have m2 := mul_le_mul_of_nonneg_left eT (mul_nonneg hμ0 (by linarith : (0 : ℝ) ≤ 1 - a))
  have m3 := mul_le_mul_of_nonneg_left e1 (mul_nonneg hμ0 ha0)
  have m4 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hμ0 ha0)
  have m5 := mul_le_mul_of_nonneg_left eK (mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1) hμ0)
  have m6 := mul_le_mul_of_nonneg_left eL hμ0
  refine ⟨?_, ?_, ?_⟩
  · unfold P3v line5
    rw [sub_le_iff_le_add]
    apply max_le <;> nlinarith
  · unfold P4v Jv; nlinarith
  · unfold P6v Jv; nlinarith

/-- The case `a = 0`: `t = kappa`, `J = 0`, and the terms are exact in `H(kappa)`. -/
lemma terms_le0 {μ lam j os s1 l1 r1 s2 l2 r2 w claim l3 L3 Hk H1 H2 HK : ℝ}
    (hμ0 : 0 ≤ μ) (hj : 1 ≤ j) (eK : Hk ≤ HK) (eL : L3 ≤ l3)
    (cu : 1 / 2 + μ * ((HK / 2 - 1 / 2 + lam) + 0 / 2 * (s1 - 0 + r1 + l2)) + (1 - μ) * w
      - (j - 1) * μ * (1 - HK) ≤ claim)
    (cv : 1 / 2 + μ * ((HK / 2 - 1 / 2 + lam) + 0 / 2 * (s2 - 0 + l1 + r2)) - (1 - μ) * w
      + os - (j - 1) * μ * (1 - HK) ≤ claim)
    (c4 : μ * (0 + lam) + μ * (l3 + 1) / 4 + max μ ((1 - μ) * (1 / 2 + |w|) - μ) ≤ claim)
    (c6 : μ * (1 + HK + 0 + lam) ≤ claim) :
    P3v μ lam j os 0 s1 l1 r1 s2 l2 r2 w Hk Hk H1 H2 ≤ claim ∧ P4v μ lam L3 w (Jv 0 Hk Hk H1 H2) ≤ claim ∧
      P6v μ lam Hk (Jv 0 Hk Hk H1 H2) ≤ claim := by
  have m1 := mul_le_mul_of_nonneg_left eK hμ0
  have m5 := mul_le_mul_of_nonneg_left eK (mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1) hμ0)
  have m6 := mul_le_mul_of_nonneg_left eL hμ0
  refine ⟨?_, ?_, ?_⟩
  · unfold P3v line5
    rw [sub_le_iff_le_add]
    apply max_le <;> nlinarith
  · unfold P4v Jv; nlinarith
  · unfold P6v Jv; nlinarith

theorem piece_sound (R : Row) (hs : ∀ c ∈ R.circs, (c.hsLo : ℝ) ≤ Hb c.s) (hl3 : log 3 / log 2 ≤ R.l3)
    (hok : R.ok = true) (κa : ℚ) (p : EP) (h : R.pieceOK κa p = true) :
    ∀ κ : ℝ, (κa : ℝ) ≤ κ → κ ≤ p.κb → Covered R κ := by
  intro κ hκa hκb
  have hok' := hok
  simp only [Row.ok, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨⟨hμ0, hμ1⟩, -⟩, -⟩, -⟩, -⟩ := hok'
  have hμ0' : (0 : ℝ) ≤ R.μ := by exact_mod_cast hμ0.le
  have hμ1' : (R.μ : ℝ) < 1 := by exact_mod_cast hμ1
  unfold Row.pieceOK at h
  split at h
  next a c1 c2 ha hc1 hc2 =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsym, ha0⟩, ha1⟩, hj⟩, hfit⟩, hk0⟩, hab⟩, hb2⟩, hhk⟩, hterms⟩ := h
    have mem1 := List.mem_of_getElem? hc1
    have mem2 := List.mem_of_getElem? hc2
    have hmenu : InMenu R a c1 c2 p.w := by
      refine ⟨List.mem_of_getElem? ha, mem1, mem2, fun hs' => ?_⟩
      rcases hsym with hsym | ⟨hi, hw⟩
      · rw [hs'] at hsym; exact absurd hsym (by decide)
      · rw [hi] at hc1
        rw [hc1] at hc2
        exact ⟨Option.some.inj hc2, by exact_mod_cast hw⟩
    have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
    have ha1' : (a : ℝ) < 1 := by exact_mod_cast ha1
    have hj' : (1 : ℝ) ≤ R.j := by exact_mod_cast hj
    have hk0' : (0 : ℝ) ≤ κa := by exact_mod_cast hk0
    have hb2' : (p.κb : ℝ) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]; exact_mod_cast hb2
    have eK : Hb κ ≤ p.hk.hi := (Hb_mono (by linarith) hκb hb2').trans (HbU.sound _ _ hhk)
    have hfit' : (R.j : ℝ) * R.μ ≤ (1 - R.μ) * (1 / 2 - |(p.w : ℝ)|) := by
      have := (Rat.cast_le (K := ℝ)).mpr hfit; push_cast at this; linarith
    refine ⟨a, c1, c2, p.w, hmenu, ?_⟩
    have e1 := hs c1 mem1
    have e2 := hs c2 mem2
    split_ifs at hterms with hz
    · -- a = 0
      subst hz
      simp only [Row.termsOK, Bool.and_eq_true, decide_eq_true_eq] at hterms
      obtain ⟨⟨⟨cu, cv⟩, c4⟩, c6⟩ := hterms
      have cu' := (Rat.cast_le (K := ℝ)).mpr cu
      have cv' := (Rat.cast_le (K := ℝ)).mpr cv
      have c4' := (Rat.cast_le (K := ℝ)).mpr c4
      have c6' := (Rat.cast_le (K := ℝ)).mpr c6
      push_cast at cu' cv' c4' c6'
      have T := terms_le0 (μ := R.μ) (lam := R.lam) (j := R.j) (os := R.osv)
        (s1 := c1.s) (l1 := c1.l) (r1 := c1.r) (s2 := c2.s) (l2 := c2.l) (r2 := c2.r) (w := p.w)
        (claim := R.claim) (l3 := R.l3) (L3 := log 3 / log 2) (H1 := Hb c1.s) (H2 := Hb c2.s)
        hμ0' hj' eK hl3 (by linarith) (by linarith) (by linarith) (by linarith)
      refine ⟨Or.inl rfl, hfit', ?_⟩
      simp only [Rat.cast_zero, t5R_zero]
      exact T
    · -- a > 0
      simp only [Bool.and_eq_true, Row.termsOK, decide_eq_true_eq] at hterms
      obtain ⟨⟨hta, htb⟩, ⟨⟨⟨cu, cv⟩, c4⟩, c6⟩⟩ := hterms
      have ra := HbL.range hta
      have rb := HbL.range htb
      rw [t5_cast] at ra rb
      have la := HbL.sound _ _ hta
      have lb := HbL.sound _ _ htb
      rw [t5_cast] at la lb
      have tm1 := t5R_mono (s1 := c1.s) (s2 := c2.s) ha1' hκa
      have tm2 := t5R_mono (s1 := c1.s) (s2 := c2.s) ha1' hκb
      have eT : min ((p.ta.lo : ℚ) : ℝ) ((p.tb.lo : ℚ) : ℝ) ≤ Hb (t5R a c1.s c2.s κ) := by
        exact (min_le_min la lb).trans (Hb_ge_min ra.1.le tm1 tm2 rb.2.le)
      have cu' := (Rat.cast_le (K := ℝ)).mpr cu
      have cv' := (Rat.cast_le (K := ℝ)).mpr cv
      have c4' := (Rat.cast_le (K := ℝ)).mpr c4
      have c6' := (Rat.cast_le (K := ℝ)).mpr c6
      push_cast at cu' cv' c4' c6'
      have T := terms_le (μ := R.μ) (lam := R.lam) (j := R.j) (os := R.osv)
        (a := a) (s1 := c1.s) (l1 := c1.l) (r1 := c1.r) (s2 := c2.s) (l2 := c2.l) (r2 := c2.r) (w := p.w)
        (claim := R.claim) (l3 := R.l3) (L3 := log 3 / log 2) (Hk := Hb κ) (Ht := Hb (t5R a c1.s c2.s κ))
        (H1 := Hb c1.s) (H2 := Hb c2.s) hμ0' hμ1' ha0' ha1' hj' eK eT e1 e2 hl3
        (by linarith) (by linarith) (by linarith) (by linarith)
      refine ⟨Or.inr ⟨by linarith [ra.1], by linarith [rb.2]⟩, hfit', T⟩
  next => simp at h

/-- The pieces cover `[ka, kend]`. -/
theorem chk_sound (R : Row) (hs : ∀ c ∈ R.circs, (c.hsLo : ℝ) ≤ Hb c.s) (hl3 : log 3 / log 2 ≤ R.l3)
    (hok : R.ok = true) (κend : ℚ) :
    ∀ (ps : List EP) (κa : ℚ), R.chk κend κa ps = true → ps ≠ [] →
      ∀ κ : ℝ, (κa : ℝ) ≤ κ → κ ≤ κend → Covered R κ := by
  intro ps
  induction ps with
  | nil => intro κa _ hne; exact absurd rfl hne
  | cons p ps ih =>
    intro κa h _ κ h1 h2
    simp only [Row.chk, Bool.and_eq_true] at h
    obtain ⟨hp, hrest⟩ := h
    rcases le_total κ p.κb with hκ | hκ
    · exact piece_sound R hs hl3 hok κa p hp κ h1 hκ
    · rcases ps with _ | ⟨q, qs⟩
      · simp only [Row.chk, decide_eq_true_eq] at hrest
        have : (p.κb : ℝ) = κend := by exact_mod_cast hrest
        exact piece_sound R hs hl3 hok κa p hp κ h1 (by linarith)
      · exact ih p.κb hrest (List.cons_ne_nil q qs) κ hκ h2

/-- Covering `[0, 1/2]` covers `[0, 1]` (for a row without the K4 offset). -/
theorem row_covered (R : Row) (hos : R.osv = 0) (ha : ∀ a ∈ R.alphas, a < 1)
    (h : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 2 → Covered R κ) : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → Covered R κ := by
  intro κ h0 h1
  rcases le_total κ (1 / 2) with hk | hk
  · exact h κ h0 hk
  · obtain ⟨a, c1, c2, w, ⟨ma, m1, m2, msym⟩, hg⟩ := h (1 - κ) (by linarith) (by linarith)
    have ha1 : (a : ℝ) < 1 := by exact_mod_cast ha a ma
    refine ⟨a, c2, c1, -w, ⟨ma, m2, m1, fun hs => ?_⟩, Good_symm R hos _ _ a ha1 c1 c2 w κ ?_⟩
    · obtain ⟨e, ew⟩ := msym hs; exact ⟨e.symm, by rw [ew, neg_zero]⟩
    · exact hg

/-! ## Soundness of the must-fail checker -/

lemma refL_mem (R : Row) (κ HK : ℚ) :
    ∀ (ds : List (ℚ × Circ × Circ)) (hs : List (Option HbU)), refL R κ HK ds hs = true →
      ∀ d ∈ ds, ∃ e, R.refOne κ HK d e = true := by
  intro ds
  induction ds with
  | nil => intro _ _ d hd; exact absurd hd (by simp)
  | cons d ds ih =>
    intro hs h d' hd'
    rcases hs with _ | ⟨e, es⟩
    · simp [refL] at h
    · simp only [refL, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hd' with rfl | hd''
      · exact ⟨e, h.1⟩
      · exact ih es h.2 d' hd''

lemma mem_designs (R : Row) (a : ℚ) (c1 c2 : Circ) (w : ℝ) (h : InMenu R a c1 c2 w) :
    (a, c1, c2) ∈ R.designs := by
  obtain ⟨ma, m1, m2, msym⟩ := h
  unfold Row.designs
  refine List.mem_flatMap.mpr ⟨a, ma, List.mem_flatMap.mpr ⟨c1, m1, List.mem_filterMap.mpr ⟨c2, m2, ?_⟩⟩⟩
  cases hs : R.sym
  · simp
  · simp [(msym hs).1]

/-- The real core of the must-fail test (`a > 0`): lower bounds on P3 (two ways) and P6 contradict `Good`. -/
lemma ref_core {μ lam j os a s1 l1 r1 s2 l2 r2 w claim Hk Ht H1 H2 HK HT k1 k2 : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (ha0 : 0 ≤ a) (ha1 : a < 1) (hj : 1 ≤ j) (hlam : 0 ≤ lam)
    (eK : HK ≤ Hk) (eT : Ht ≤ HT) (e1 : H1 ≤ k1) (e2 : H2 ≤ k2)
    (hfit : j * μ ≤ (1 - μ) * (1 / 2 - |w|))
    (h3 : P3v μ lam j os a s1 l1 r1 s2 l2 r2 w Hk Ht H1 H2 ≤ claim)
    (h6 : P6v μ lam Hk (Jv a Hk Ht H1 H2) ≤ claim)
    (D : claim < ((1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s1 - k2 + r1 + l2))) +
          (1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s2 - k1 + l1 + r2)) + os)) / 2
          - (j - 1) * μ * (1 - HK) ∨
      claim < max (1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s1 - k2 + r1 + l2)))
          (1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s2 - k1 + l1 + r2)) + os)
          - (1 - μ) * (1 / 2 - j * μ / (1 - μ)) - (j - 1) * μ * (1 - HK) ∨
      claim < μ * (1 + HK + (HK - a / 2 * (k1 + k2) - (1 - a) * HT))) : False := by
  have m1 := mul_le_mul_of_nonneg_left eK hμ0.le
  have m2 := mul_le_mul_of_nonneg_left eT (mul_nonneg hμ0.le (by linarith : (0 : ℝ) ≤ 1 - a))
  have m3 := mul_le_mul_of_nonneg_left e1 (mul_nonneg hμ0.le ha0)
  have m4 := mul_le_mul_of_nonneg_left e2 (mul_nonneg hμ0.le ha0)
  have m5 := mul_le_mul_of_nonneg_left eK (mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1) hμ0.le)
  have ml := mul_nonneg hμ0.le hlam
  have hW : (1 - μ) * (1 / 2 - j * μ / (1 - μ)) = (1 - μ) / 2 - j * μ := by
    have : (1 : ℝ) - μ ≠ 0 := by linarith
    field_simp
  rw [hW] at D
  have hw : (1 - μ) * |w| ≤ (1 - μ) / 2 - j * μ := by linarith
  have hw1 := mul_le_mul_of_nonneg_left (neg_abs_le w) (by linarith : (0 : ℝ) ≤ 1 - μ)
  have hw2 := mul_le_mul_of_nonneg_left (neg_abs_le (-w)) (by linarith : (0 : ℝ) ≤ 1 - μ)
  rw [abs_neg] at hw2
  unfold P3v at h3
  obtain ⟨hU, hV⟩ := max_le_iff.mp (sub_le_iff_le_add.mp h3)
  unfold line5 at hU hV
  unfold P6v Jv at h6
  rcases D with D | D | D
  · nlinarith
  · rcases le_total (1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s1 - k2 + r1 + l2)))
        (1 / 2 + μ * ((HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1) + a / 2 * (s2 - k1 + l1 + r2)) + os) with hm | hm
    · rw [max_eq_right hm] at D; nlinarith
    · rw [max_eq_left hm] at D; nlinarith
  · nlinarith

/-- The same for `a = 0` (`t = kappa`, `J = 0`). -/
lemma ref_core0 {μ lam j os s1 l1 r1 s2 l2 r2 w claim Hk H1 H2 HK k1 k2 : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hj : 1 ≤ j) (hlam : 0 ≤ lam) (eK : HK ≤ Hk)
    (hfit : j * μ ≤ (1 - μ) * (1 / 2 - |w|))
    (h3 : P3v μ lam j os 0 s1 l1 r1 s2 l2 r2 w Hk Hk H1 H2 ≤ claim)
    (h6 : P6v μ lam Hk (Jv 0 Hk Hk H1 H2) ≤ claim)
    (D : claim < ((1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s1 - k2 + r1 + l2))) +
          (1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s2 - k1 + l1 + r2)) + os)) / 2
          - (j - 1) * μ * (1 - HK) ∨
      claim < max (1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s1 - k2 + r1 + l2)))
          (1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s2 - k1 + l1 + r2)) + os)
          - (1 - μ) * (1 / 2 - j * μ / (1 - μ)) - (j - 1) * μ * (1 - HK) ∨
      claim < μ * (1 + HK + 0)) : False := by
  have m1 := mul_le_mul_of_nonneg_left eK hμ0.le
  have m5 := mul_le_mul_of_nonneg_left eK (mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1) hμ0.le)
  have ml := mul_nonneg hμ0.le hlam
  have hW : (1 - μ) * (1 / 2 - j * μ / (1 - μ)) = (1 - μ) / 2 - j * μ := by
    have : (1 : ℝ) - μ ≠ 0 := by linarith
    field_simp
  rw [hW] at D
  have hw : (1 - μ) * |w| ≤ (1 - μ) / 2 - j * μ := by linarith
  have hw1 := mul_le_mul_of_nonneg_left (neg_abs_le w) (by linarith : (0 : ℝ) ≤ 1 - μ)
  have hw2 := mul_le_mul_of_nonneg_left (neg_abs_le (-w)) (by linarith : (0 : ℝ) ≤ 1 - μ)
  rw [abs_neg] at hw2
  unfold P3v at h3
  obtain ⟨hU, hV⟩ := max_le_iff.mp (sub_le_iff_le_add.mp h3)
  unfold line5 at hU hV
  unfold P6v Jv at h6
  rcases D with D | D | D
  · nlinarith
  · rcases le_total (1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s1 - k2 + r1 + l2)))
        (1 / 2 + μ * ((HK / 2 - 1 / 2) + 0 / 2 * (s2 - k1 + l1 + r2)) + os) with hm | hm
    · rw [max_eq_right hm] at D; nlinarith
    · rw [max_eq_left hm] at D; nlinarith
  · nlinarith

theorem refCore_sound (R : Row) (κ HK HT : ℚ) (hK : (HK : ℝ) ≤ Hb κ) (hμ0 : (0 : ℝ) < R.μ) (hμ1 : (R.μ : ℝ) < 1)
    (hj : 1 ≤ R.j) (a : ℚ) (c1 c2 : Circ) (h1 : Hb c1.s ≤ c1.hsHi) (h2 : Hb c2.s ≤ c2.hsHi)
    (hT : Hb (t5R a c1.s c2.s κ) ≤ HT) (h : R.refCore κ HK (a, c1, c2) HT = true) (lam : ℝ) (hlam : 0 ≤ lam)
    (w : ℝ) : ¬ Good R lam R.claim a c1 c2 w κ := by
  rintro ⟨-, hfit, h3, -, h6⟩
  have hj' : (1 : ℝ) ≤ R.j := by exact_mod_cast hj
  simp only [Row.refCore] at h
  split_ifs at h with hz
  · subst hz
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, D⟩ := h
    push_cast at h3 h6
    rw [t5R_zero] at h3 h6
    refine ref_core0 (os := R.osv) (k1 := c1.hsHi) (k2 := c2.hsHi) hμ0 hμ1 hj' hlam hK hfit h3 h6 ?_
    rcases D with (D | D) | D
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inl (by linarith)
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inr (Or.inl (by linarith))
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inr (Or.inr (by linarith))
  · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨ha0, ha1⟩, D⟩ := h
    have ha0' : (0 : ℝ) ≤ a := by exact_mod_cast ha0
    have ha1' : (a : ℝ) < 1 := by exact_mod_cast ha1
    refine ref_core (os := R.osv) (k1 := c1.hsHi) (k2 := c2.hsHi) hμ0 hμ1 ha0' ha1' hj' hlam hK hT h1 h2 hfit h3 h6 ?_
    rcases D with (D | D) | D
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inl (by linarith)
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inr (Or.inl (by linarith))
    · have D' := (Rat.cast_lt (K := ℝ)).mpr D; push_cast at D'; exact Or.inr (Or.inr (by linarith))

theorem refOne_sound (R : Row) (κ HK : ℚ) (hK : (HK : ℝ) ≤ Hb κ) (hμ0 : (0 : ℝ) < R.μ) (hμ1 : (R.μ : ℝ) < 1)
    (hj : 1 ≤ R.j) (a : ℚ) (c1 c2 : Circ) (h1 : Hb c1.s ≤ c1.hsHi) (h2 : Hb c2.s ≤ c2.hsHi) (e : Option HbU)
    (h : R.refOne κ HK (a, c1, c2) e = true) (lam : ℝ) (hlam : 0 ≤ lam) (w : ℝ) :
    ¬ Good R lam R.claim a c1 c2 w κ := by
  intro hg
  unfold Row.refOne at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨ha, ht⟩ | h
  · rcases hg.1 with hv | hv
    · exact ha hv
    · rw [← t5_cast] at hv
      rcases ht with ht | ht
      · exact absurd hv.1 (not_lt.mpr (by exact_mod_cast ht))
      · exact absurd hv.2 (not_lt.mpr (by exact_mod_cast ht))
  · rcases e with _ | e
    · exact refCore_sound R κ HK 1 hK hμ0 hμ1 hj a c1 c2 h1 h2 (by push_cast; exact Hb_le_one _) h lam hlam w hg
    · simp only [Bool.and_eq_true] at h
      have hT := HbU.sound _ _ h.1
      rw [t5_cast] at hT
      exact refCore_sound R κ HK e.hi hK hμ0 hμ1 hj a c1 c2 h1 h2 hT h.2 lam hlam w hg

/-- A passing `Row.refute` at kappa: no design of the menu is good there, for any `w` and any `lambda ≥ 0`. -/
theorem refute_sound (R : Row) (hs : ∀ c ∈ R.circs, Hb c.s ≤ c.hsHi) (κ : ℚ) (hk : HbL) (hts : List (Option HbU))
    (h : R.refute κ hk hts = true) :
    ∀ lam : ℝ, 0 ≤ lam → ∀ (a : ℚ) (c1 c2 : Circ) (w : ℝ), InMenu R a c1 c2 w → ¬ Good R lam R.claim a c1 c2 w κ := by
  intro lam hlam a c1 c2 w hm
  simp only [Row.refute, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hμ0, hμ1⟩, hj⟩, hko⟩, hL⟩ := h
  obtain ⟨e, he⟩ := refL_mem R κ hk.lo _ _ hL _ (mem_designs R a c1 c2 w hm)
  exact refOne_sound R κ hk.lo (HbL.sound _ _ hko) (by exact_mod_cast hμ0) (by exact_mod_cast hμ1) hj a c1 c2
    (hs c1 hm.2.1) (hs c2 hm.2.2.1) e he lam hlam w

/-- A row is refuted at kappa if each of its alphas is, as a one-alpha row (the cost terms do not see the menu). -/
theorem refute_alphas (R : Row) (hs : ∀ c ∈ R.circs, Hb c.s ≤ c.hsHi) (κ : ℚ)
    (h : ∀ a ∈ R.alphas, ∃ hk hts, ({ R with alphas := [a] } : Row).refute κ hk hts = true) :
    ∀ lam : ℝ, 0 ≤ lam → ¬ CoveredL R lam κ := by
  rintro lam hlam ⟨a, c1, c2, w, ⟨ma, m1, m2, ms⟩, hg⟩
  obtain ⟨hk, hts, hr⟩ := h a ma
  exact refute_sound { R with alphas := [a] } hs κ hk hts hr lam hlam a c1 c2 w
    ⟨List.mem_singleton_self a, m1, m2, ms⟩ hg

/-- At kappa = 1/2 (`H = 1`) a core-free design has P3 ≥ 1/2 (control K3). -/
lemma P3v_half_ge (μ lam j os s1 l1 r1 s2 l2 r2 w H1 H2 : ℝ) (hμ : 0 ≤ μ) (hlam : 0 ≤ lam) (hos : 0 ≤ os) :
    1 / 2 ≤ P3v μ lam j os 0 s1 l1 r1 s2 l2 r2 w 1 1 H1 H2 := by
  unfold P3v
  have hA := le_max_left (line5 μ lam 0 s1 r1 l2 H2 w 1 1) (line5 μ lam 0 s2 r2 l1 H1 (-w) 1 1 + os)
  have hB := le_max_right (line5 μ lam 0 s1 r1 l2 H2 w 1 1) (line5 μ lam 0 s2 r2 l1 H1 (-w) 1 1 + os)
  unfold line5 at hA hB ⊢
  nlinarith [mul_nonneg hμ hlam]

end SS5
