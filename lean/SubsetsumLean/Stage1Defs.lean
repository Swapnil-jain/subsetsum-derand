import SubsetsumLean.Basic

/-!
# Stage 1: the exponent of the deterministic CJRS Sec. 4 algorithm

The quantities of `cert_gamma.py` (CJRS arXiv 2301.07134, Sec. 4; `H` is binary entropy in bits):

    beta(e2)        = 1 / H((1 + e2)/4)
    lambda0(e1, e2) = (1 - e1)/2 * beta * (1 - H((1 - e2)/2))
    delta(e1, e2)   = (1 - H((1 - e1)/2)) * beta
    theta0(e1, e2)  = (1 - e1/2) * beta - 1 - lambda0
    g(e1, e2)       = min(lambda0/2, delta/2, theta0)                    (PROOF.md, Def. 6.1)

and CJRS's balancing equations (3) and (4), written as `F3 = 0` and `F4 = 0`.

The lemmas here are generic over `ℝ`: from bounds on `H` at the corners of a box `[a, b] × [c, d]` they bound every
term at every point of the box, using that `H` is increasing on `[0, 1/2]`. The generated file
`Stage1Points.lean` supplies the corner bounds (kernel-checked by `Hb_mem`) and closes each claim with `norm_num`
on rational literals.
-/

open Real

namespace SS

noncomputable def beta (e2 : ℝ) : ℝ := 1 / Hb ((1 + e2) / 4)
noncomputable def lam0 (e1 e2 : ℝ) : ℝ := (1 - e1) / 2 * beta e2 * (1 - Hb ((1 - e2) / 2))
noncomputable def delta (e1 e2 : ℝ) : ℝ := (1 - Hb ((1 - e1) / 2)) * beta e2
noncomputable def theta0 (e1 e2 : ℝ) : ℝ := (1 - e1 / 2) * beta e2 - 1 - lam0 e1 e2
/-- The saving exponent `g = min(lambda0/2, delta/2, theta0)` (PROOF.md, Def. 6.1). -/
noncomputable def g (e1 e2 : ℝ) : ℝ := min (min (lam0 e1 e2 / 2) (delta e1 e2 / 2)) (theta0 e1 e2)

/-- CJRS Equation (3): `(1 - H((1-e1)/2)) / ((1-e1)/2) = 1 - H((1-e2)/2)`, as `F3 = 0`. -/
noncomputable def F3 (e1 e2 : ℝ) : ℝ := (1 - Hb ((1 - e1) / 2)) / ((1 - e1) / 2) - (1 - Hb ((1 - e2) / 2))
/-- CJRS Equation (4): `1 + e1 - 3 H((1-e1)/2) = -2 H((1+e2)/4)`, as `F4 = 0`. -/
noncomputable def F4 (e1 e2 : ℝ) : ℝ := 1 + e1 - 3 * Hb ((1 - e1) / 2) + 2 * Hb ((1 + e2) / 4)

/-- What PROOF.md needs at a parameter point (Def. 6.1, Lemma 2.1(ii), Lemma 6.2), with the claimed saving `s`:
`0 < e1, e2 < 1`, `1 < beta < 4/3`, `lambda0 > 0`, `theta0 > 0` and `s < g`. -/
structure Admissible (e1 e2 s : ℝ) : Prop where
  e1_pos : 0 < e1
  e1_lt : e1 < 1
  e2_pos : 0 < e2
  e2_lt : e2 < 1
  beta_gt : 1 < beta e2
  beta_lt : beta e2 < 4 / 3
  lam0_pos : 0 < lam0 e1 e2
  theta0_pos : 0 < theta0 e1 e2
  saving : s < g e1 e2

/-! ## Interval lemmas -/

lemma mul_le_mul3 {x1 x y1 y : ℝ} (hx : x1 ≤ x) (hy : y1 ≤ y) (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1) :
    x1 * y1 ≤ x * y := mul_le_mul hx hy hy1 (hx1.trans hx)

/-- `H` on `[lo, hi] ⊆ [0, 1/2]` lies between its endpoint bounds. -/
lemma Hb_between {lo x hi L U : ℝ} (h0 : 0 ≤ lo) (h1 : lo ≤ x) (h2 : x ≤ hi) (h3 : hi ≤ 1 / 2)
    (hL : L ≤ Hb lo) (hU : Hb hi ≤ U) : L ≤ Hb x ∧ Hb x ≤ U :=
  ⟨hL.trans (Hb_mono h0 h1 (h2.trans h3)), (Hb_mono (h0.trans h1) h2 h3).trans hU⟩

/-- The box lemma. For `e1 ∈ [a, b]`, `e2 ∈ [c, d]` with `0 ≤ a`, `b < 1`, `0 ≤ c`, `d < 1`, and bounds
`A ∈ [Alo, ·]` at `(1+c)/4`, `[·, Ahi]` at `(1+d)/4`, `B` at `(1-d)/2` and `(1-c)/2`, `C` at `(1-b)/2` and
`(1-a)/2`, every term lies in the interval that naive interval arithmetic gives (as in `cert_gamma.py`). -/
theorem box_bounds {a b c d e1 e2 Alo Ahi Blo Bhi Clo Chi : ℝ}
    (ha : a ≤ e1) (hb : e1 ≤ b) (hc : c ≤ e2) (hd : e2 ≤ d) (ha0 : 0 ≤ a) (hb1 : b < 1) (hc0 : 0 ≤ c)
    (hd1 : d < 1) (hA1 : Alo ≤ Hb ((1 + c) / 4)) (hA2 : Hb ((1 + d) / 4) ≤ Ahi)
    (hB1 : Blo ≤ Hb ((1 - d) / 2)) (hB2 : Hb ((1 - c) / 2) ≤ Bhi)
    (hC1 : Clo ≤ Hb ((1 - b) / 2)) (hC2 : Hb ((1 - a) / 2) ≤ Chi)
    (hA0 : 0 < Alo) (hBh : Bhi ≤ 1) (hCh : Chi ≤ 1) :
    1 / Ahi ≤ beta e2 ∧ beta e2 ≤ 1 / Alo ∧
    (1 - b) / 2 * (1 / Ahi) * (1 - Bhi) ≤ lam0 e1 e2 ∧ lam0 e1 e2 ≤ (1 - a) / 2 * (1 / Alo) * (1 - Blo) ∧
    (1 - Chi) * (1 / Ahi) ≤ delta e1 e2 ∧ delta e1 e2 ≤ (1 - Clo) * (1 / Alo) ∧
    (1 - b / 2) * (1 / Ahi) - 1 - (1 - a) / 2 * (1 / Alo) * (1 - Blo) ≤ theta0 e1 e2 ∧
    theta0 e1 e2 ≤ (1 - a / 2) * (1 / Alo) - 1 - (1 - b) / 2 * (1 / Ahi) * (1 - Bhi) := by
  obtain ⟨A1, A2⟩ := Hb_between (lo := (1 + c) / 4) (x := (1 + e2) / 4) (hi := (1 + d) / 4)
    (by linarith) (by linarith) (by linarith) (by linarith) hA1 hA2
  obtain ⟨B1, B2⟩ := Hb_between (lo := (1 - d) / 2) (x := (1 - e2) / 2) (hi := (1 - c) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) hB1 hB2
  obtain ⟨C1, C2⟩ := Hb_between (lo := (1 - b) / 2) (x := (1 - e1) / 2) (hi := (1 - a) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) hC1 hC2
  have Apos : 0 < Hb ((1 + e2) / 4) := hA0.trans_le A1
  have Ahpos : 0 < Ahi := Apos.trans_le A2
  have be1 : 1 / Ahi ≤ beta e2 := one_div_le_one_div_of_le Apos A2
  have be2 : beta e2 ≤ 1 / Alo := one_div_le_one_div_of_le hA0 A1
  have i0 : 0 ≤ 1 / Ahi := by positivity
  have x1 : (1 - b) / 2 ≤ (1 - e1) / 2 := by linarith
  have x2 : (1 - e1) / 2 ≤ (1 - a) / 2 := by linarith
  have x0 : 0 ≤ (1 - b) / 2 := by linarith
  have y1 : 1 - Bhi ≤ 1 - Hb ((1 - e2) / 2) := by linarith
  have y2 : 1 - Hb ((1 - e2) / 2) ≤ 1 - Blo := by linarith
  have y0 : 0 ≤ 1 - Bhi := by linarith
  have z1 : 1 - Chi ≤ 1 - Hb ((1 - e1) / 2) := by linarith
  have z2 : 1 - Hb ((1 - e1) / 2) ≤ 1 - Clo := by linarith
  have z0 : 0 ≤ 1 - Chi := by linarith
  have w1 : 1 - b / 2 ≤ 1 - e1 / 2 := by linarith
  have w2 : 1 - e1 / 2 ≤ 1 - a / 2 := by linarith
  have w0 : 0 ≤ 1 - b / 2 := by linarith
  have L1 := mul_le_mul3 (mul_le_mul3 x1 be1 x0 i0) y1 (by positivity) y0
  have L2 := mul_le_mul3 (mul_le_mul3 x2 be2 (x0.trans x1) (i0.trans be1)) y2
    (mul_nonneg (x0.trans x1) (i0.trans be1)) (y0.trans y1)
  have D1 := mul_le_mul3 z1 be1 z0 i0
  have D2 := mul_le_mul3 z2 be2 (z0.trans z1) (i0.trans be1)
  have T1 := mul_le_mul3 w1 be1 w0 i0
  have T2 := mul_le_mul3 w2 be2 (w0.trans w1) (i0.trans be1)
  unfold theta0 delta
  unfold lam0 at L1 L2 ⊢
  exact ⟨be1, be2, L1, L2, D1, D2, by linarith, by linarith⟩

/-- `g` is at least `s` once each of its three terms is. -/
lemma g_ge {e1 e2 s : ℝ} (h1 : s ≤ lam0 e1 e2 / 2) (h2 : s ≤ delta e1 e2 / 2) (h3 : s ≤ theta0 e1 e2) :
    s ≤ g e1 e2 := le_min (le_min h1 h2) h3

lemma g_gt {e1 e2 s : ℝ} (h1 : s < lam0 e1 e2 / 2) (h2 : s < delta e1 e2 / 2) (h3 : s < theta0 e1 e2) :
    s < g e1 e2 := lt_min (lt_min h1 h2) h3

lemma g_le_lam {e1 e2 : ℝ} : g e1 e2 ≤ lam0 e1 e2 / 2 := (min_le_left _ _).trans (min_le_left _ _)
lemma g_le_delta {e1 e2 : ℝ} : g e1 e2 ≤ delta e1 e2 / 2 := (min_le_left _ _).trans (min_le_right _ _)
lemma g_le_theta {e1 e2 : ℝ} : g e1 e2 ≤ theta0 e1 e2 := min_le_right _ _

/-- The curve lemma: on `e1 ∈ [a, b]`, `F4(e1, c)` and `F4(e1, d)` are bounded through `H((1-e1)/2)`. -/
theorem F4_bounds {a b e1 e2 Clo Chi Elo Ehi : ℝ} (ha : a ≤ e1) (hb : e1 ≤ b) (ha0 : 0 ≤ a) (hb1 : b < 1)
    (hC1 : Clo ≤ Hb ((1 - b) / 2)) (hC2 : Hb ((1 - a) / 2) ≤ Chi)
    (hE1 : Elo ≤ Hb ((1 + e2) / 4)) (hE2 : Hb ((1 + e2) / 4) ≤ Ehi) :
    1 + a - 3 * Chi + 2 * Elo ≤ F4 e1 e2 ∧ F4 e1 e2 ≤ 1 + b - 3 * Clo + 2 * Ehi := by
  obtain ⟨C1, C2⟩ := Hb_between (lo := (1 - b) / 2) (x := (1 - e1) / 2) (hi := (1 - a) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) hC1 hC2
  unfold F4; constructor <;> linarith

/-- Equation (3) on a slice `e1 = a`, `e2 ∈ [s1, s2]`: `F3` is decreasing in `e2`. -/
theorem F3_bounds {a e2 s1 s2 Hlo Hhi Plo Phi : ℝ} (_ha0 : 0 ≤ a) (ha1 : a < 1) (h1 : s1 ≤ e2) (h2 : e2 ≤ s2)
    (hs1 : 0 ≤ s1) (hs2 : s2 < 1)
    (hH1 : Hlo ≤ Hb ((1 - a) / 2)) (hH2 : Hb ((1 - a) / 2) ≤ Hhi)
    (hP1 : Plo ≤ Hb ((1 - s2) / 2)) (hP2 : Hb ((1 - s1) / 2) ≤ Phi) :
    (1 - Hhi) / ((1 - a) / 2) - 1 + Plo ≤ F3 a e2 ∧ F3 a e2 ≤ (1 - Hlo) / ((1 - a) / 2) - 1 + Phi := by
  obtain ⟨P1, P2⟩ := Hb_between (lo := (1 - s2) / 2) (x := (1 - e2) / 2) (hi := (1 - s1) / 2)
    (by linarith) (by linarith) (by linarith) (by linarith) hP1 hP2
  have hp : 0 < (1 - a) / 2 := by linarith
  have q1 : (1 - Hhi) / ((1 - a) / 2) ≤ (1 - Hb ((1 - a) / 2)) / ((1 - a) / 2) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  have q2 : (1 - Hb ((1 - a) / 2)) / ((1 - a) / 2) ≤ (1 - Hlo) / ((1 - a) / 2) :=
    div_le_div_of_nonneg_right (by linarith) hp.le
  unfold F3; constructor <;> linarith

/-- PROOF.md Lemma 6.2: for `0 < gamma < g`, every `lambda ∈ (2 gamma, lambda0)` has
`min(delta/2, lambda/2, theta) > gamma` with `theta = theta0 + (lambda0 - lambda)`. -/
theorem lemma_6_2 {e1 e2 γ lam : ℝ} (hg : γ < g e1 e2) (hl1 : 2 * γ < lam) (hl2 : lam < lam0 e1 e2) :
    γ < delta e1 e2 / 2 ∧ γ < lam / 2 ∧ γ < theta0 e1 e2 + (lam0 e1 e2 - lam) := by
  have h2 := hg.trans_le g_le_delta
  have h3 := hg.trans_le g_le_theta
  exact ⟨h2, by linarith, by linarith⟩

/-- A rational `lambda` as in Lemma 6.2 exists (the algorithm needs a rational one). -/
theorem lemma_6_2_rational {e1 e2 γ : ℝ} (hg : γ < g e1 e2) :
    ∃ lam : ℚ, 2 * γ < lam ∧ (lam : ℝ) < lam0 e1 e2 ∧
      γ < delta e1 e2 / 2 ∧ γ < (lam : ℝ) / 2 ∧ γ < theta0 e1 e2 + (lam0 e1 e2 - lam) := by
  have h1 : 2 * γ < lam0 e1 e2 := by linarith [hg.trans_le g_le_lam]
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  exact ⟨q, hq1, hq2, lemma_6_2 hg hq1 hq2⟩

end SS
