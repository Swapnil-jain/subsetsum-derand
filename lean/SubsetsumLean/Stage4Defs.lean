import SubsetsumLean.Stage3Defs
import SubsetsumLean.Stage4Check
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Stage 4: soundness of the cell checker, the colour profile, and the general lemmas

`derand/stage4/PROOF.md` Secs. 3.5-3.6 and 8. The colour profile of the one-pass covering circuit at density `s`
(`k = s/2`, block size `b(m) = k + rho (m - k)`), per coordinate, on the polygon
`Poly4 = {k ≤ m ≤ 2k, m ≤ d ≤ b(m)}`:
- `L4 = h(1/2, d) + h(1/2, b - d) - h(1 - m, b - m)` (left), `R4 = h(k, m - k) + h(b - m, d - m)` (right);
- `G4 tau = tau max(L4, 0) + (1 - tau) R4`; `V(tau)` of Lemma 3.5' is its sup over `Poly4`.

Proved here:
- `logGe_sound`, `logLe_sound`, `Gib.sound`, `HLo.sound`: the rational certificates of `Stage4Check.lean` are true;
- `hh_chord`: `h(n, j)` is concave along segments (the perspective of `negMulLog`), so a chord bounds it below;
- `chk_sound`, `G4_le_of_cells`: a passing cell tree proves `G4 tau ≤ T` on the whole polygon;
- `line_single`, `line_family`: the contact bounds give Lemma 3.4's hypothesis
  `min{V, tau h(s), (1 - tau)(1 - s)} ≤ line` on `[0, 1]` (for one circuit, and for a family of two);
- `F1_of`: one grid step past the contacts, explicit colours bound every valid line's xi from above.
-/

open Real

namespace SS4

open SS

/-! ## The rational certificates are true -/

lemma p2_cast (k : ℤ) : ((p2 k : ℚ) : ℝ) = (2 : ℝ) ^ k := by
  unfold p2
  split_ifs with h
  · push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg h]
  · push_cast
    rw [one_div, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]

lemma lsumQ_eq (t : ℚ) (n : ℕ) : lsumQ t n = SS.lsum t n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lsumQ, SS.lsum, ih]

lemma lremQ_eq (t : ℚ) (n : ℕ) : lremQ t n = SS.lrem t n := rfl
lemma L2loQ_eq : L2loQ = SS.L2lo := rfl
lemma L2hiQ_eq : L2hiQ = SS.L2hi := rfl

/-- The series bounds behind `logGe` and `logLe`. -/
lemma log_series (x : ℚ) (k : ℤ) (hx : 0 < x) (ht : |1 - x / p2 k| < 1) :
    ((-(lsumQ (1 - x / p2 k) NT) - lremQ (1 - x / p2 k) NT + min (k * L2loQ) (k * L2hiQ) : ℚ) : ℝ) ≤ log x ∧
      log x ≤ ((-(lsumQ (1 - x / p2 k) NT) + lremQ (1 - x / p2 k) NT + max (k * L2loQ) (k * L2hiQ) : ℚ) : ℝ) := by
  have hb := SS.log_one_sub_mem (1 - x / p2 k) NT ht
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hp : (0 : ℝ) < (p2 k : ℝ) := by rw [p2_cast]; positivity
  have hy : (1 - (((1 - x / p2 k : ℚ)) : ℝ)) = (x : ℝ) / (p2 k : ℝ) := by push_cast; ring
  rw [hy] at hb
  have hlog : log (x : ℝ) = log ((x : ℝ) / (p2 k : ℝ)) + (k : ℝ) * log 2 := by
    rw [Real.log_div hxpos.ne' hp.ne', p2_cast, Real.log_zpow]; ring
  obtain ⟨l2a, l2b⟩ := SS.log_two_mem
  have hk := SS.kmul_mem k _ _ _ l2a l2b
  rw [lsumQ_eq, lremQ_eq, L2loQ_eq, L2hiQ_eq]
  push_cast
  rw [hlog]
  constructor <;> linarith [hb.1, hb.2, hk.1, hk.2]

theorem logGe_sound {x : ℚ} {k : ℤ} {l : ℚ} (h : logGe x k l = true) : (l : ℝ) ≤ log x := by
  simp only [logGe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, ht⟩, hl⟩ := h
  have hl' : (l : ℝ) ≤ ((-(lsumQ (1 - x / p2 k) NT) - lremQ (1 - x / p2 k) NT +
      min (k * L2loQ) (k * L2hiQ) : ℚ) : ℝ) := by exact_mod_cast hl
  exact hl'.trans (log_series x k hx ht).1

theorem logLe_sound {x : ℚ} {k : ℤ} {u : ℚ} (h : logLe x k u = true) : log x ≤ (u : ℝ) := by
  simp only [logLe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, ht⟩, hu⟩ := h
  have hu' : ((-(lsumQ (1 - x / p2 k) NT) + lremQ (1 - x / p2 k) NT +
      max (k * L2loQ) (k * L2hiQ) : ℚ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  exact (log_series x k hx ht).2.trans hu'

lemma L2lo_le_log2 : ((L2loQ : ℚ) : ℝ) ≤ log 2 := by rw [L2loQ_eq]; exact SS.log_two_mem.1
lemma log2_le_L2hi : log 2 ≤ ((L2hiQ : ℚ) : ℝ) := by rw [L2hiQ_eq]; exact SS.log_two_mem.2

/-- Gibbs' inequality with a certified tangent point: `h(n, j) ≤ j cp + (n - j) cq` for `0 ≤ j ≤ n`. -/
theorem Gib.sound (g : Gib) (hg : g.ok = true) {n j : ℝ} (hj : 0 ≤ j) (hjn : 0 ≤ n - j) :
    hh n j ≤ j * g.cp + (n - j) * g.cq := by
  simp only [Gib.ok, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨hp0, hp1⟩, h1⟩, h2⟩, hcp⟩, hcq⟩, hA⟩, hB⟩ := hg
  have a1 := logGe_sound h1
  have a2 := logGe_sound h2
  push_cast at a2
  have c1 := L2lo_le_log2
  have hp0' : (0 : ℝ) < g.p := by exact_mod_cast hp0
  have hp1' : (g.p : ℝ) < 1 := by exact_mod_cast hp1
  have hcp' : (0 : ℝ) ≤ g.cp := by exact_mod_cast hcp
  have hcq' : (0 : ℝ) ≤ g.cq := by exact_mod_cast hcq
  have hA' : -(g.l1 : ℝ) ≤ g.cp * L2loQ := by exact_mod_cast hA
  have hB' : -(g.l2 : ℝ) ≤ g.cq * L2loQ := by exact_mod_cast hB
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have gb : hh n j ≤ (-j * log (g.p : ℝ) - (n - j) * log (1 - (g.p : ℝ))) / log 2 :=
    hh_le_gibbs (n := n) hj (by linarith) hp0' hp1'
  have e1 : -log (g.p : ℝ) ≤ g.cp * log 2 := by nlinarith [mul_le_mul_of_nonneg_left c1 hcp']
  have e2 : -log (1 - (g.p : ℝ)) ≤ g.cq * log 2 := by nlinarith [mul_le_mul_of_nonneg_left c1 hcq']
  have m1 := mul_le_mul_of_nonneg_left e1 hj
  have m2 := mul_le_mul_of_nonneg_left e2 hjn
  have : (-j * log g.p - (n - j) * log (1 - g.p)) / log 2 ≤ j * g.cp + (n - j) * g.cq := by
    rw [div_le_iff₀ hL]; nlinarith [m1, m2]
  linarith

lemma hh_zero (c : ℝ) : hh c 0 = 0 := by unfold hh; simp

/-- A certified lower bound `lo ≤ h(c, x)` at rationals. -/
theorem HLo.sound (c x : ℚ) (e : HLo) (h : e.ok c x = true) : (e.lo : ℝ) ≤ hh c x := by
  unfold HLo.ok at h
  split_ifs at h with hx0
  · simp only [decide_eq_true_eq] at h
    rw [hx0]; push_cast; rw [hh_zero]; exact_mod_cast h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hx, hxc⟩, h1⟩, h2⟩, h3⟩, hlo⟩, hA⟩ := h
    have a1 := logGe_sound h1
    have b2 := logLe_sound h2
    have b3 := logLe_sound h3
    push_cast at b3
    have hx' : (0 : ℝ) < x := by exact_mod_cast hx
    have hxc' : (x : ℝ) < c := by exact_mod_cast hxc
    have hy : (0 : ℝ) < (c : ℝ) - x := by linarith
    have hc : (0 : ℝ) < c := by linarith
    have hlo' : (0 : ℝ) ≤ e.lo := by exact_mod_cast hlo
    have hA' : (e.lo : ℝ) * L2hiQ ≤ c * e.lc - x * e.ux - (c - x) * e.uy := by exact_mod_cast hA
    have c2 := log2_le_L2hi
    have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
    have m1 := mul_le_mul_of_nonneg_left a1 hc.le
    have m2 := mul_le_mul_of_nonneg_left b2 hx'.le
    have m3 := mul_le_mul_of_nonneg_left b3 hy.le
    have m4 := mul_le_mul_of_nonneg_left c2 hlo'
    unfold hh
    rw [le_div_iff₀ hL]
    nlinarith

/-! ## Concavity of `h(n, j)` along segments -/

/-- `q(a, b) = a log b - a log a`; `h(n, j) ln 2 = q(j, n) + q(n - j, n)`. -/
noncomputable def qf (a b : ℝ) : ℝ := a * log b - a * log a

lemma qf_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : qf a b = b * negMulLog (a / b) := by
  unfold qf negMulLog
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hb.ne']; field_simp; ring

lemma qf_concave {a0 b0 a1 b1 t : ℝ} (ha0 : 0 ≤ a0) (hb0 : 0 < b0) (ha1 : 0 ≤ a1) (hb1 : 0 < b1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * qf a0 b0 + t * qf a1 b1 ≤ qf ((1 - t) * a0 + t * a1) ((1 - t) * b0 + t * b1) := by
  have hB : 0 < (1 - t) * b0 + t * b1 := by
    rcases eq_or_lt_of_le ht0 with h | h
    · subst h; simp [hb0]
    · nlinarith [mul_pos h hb1, mul_nonneg (show (0 : ℝ) ≤ 1 - t by linarith) hb0.le]
  set B := (1 - t) * b0 + t * b1 with hBdef
  have hw0 : 0 ≤ (1 - t) * b0 / B := div_nonneg (mul_nonneg (by linarith) hb0.le) hB.le
  have hw1 : 0 ≤ t * b1 / B := div_nonneg (mul_nonneg ht0 hb1.le) hB.le
  have hw : (1 - t) * b0 / B + t * b1 / B = 1 := by rw [← add_div, ← hBdef]; exact div_self hB.ne'
  have hc := concaveOn_negMulLog.2 (Set.mem_Ici.mpr (div_nonneg ha0 hb0.le))
    (Set.mem_Ici.mpr (div_nonneg ha1 hb1.le)) hw0 hw1 hw
  simp only [smul_eq_mul] at hc
  have harg : (1 - t) * b0 / B * (a0 / b0) + t * b1 / B * (a1 / b1) = ((1 - t) * a0 + t * a1) / B := by
    field_simp
  rw [harg] at hc
  rw [qf_eq ha0 hb0, qf_eq ha1 hb1, qf_eq (by positivity) hB]
  have := mul_le_mul_of_nonneg_left hc hB.le
  have e : B * ((1 - t) * b0 / B * negMulLog (a0 / b0) + t * b1 / B * negMulLog (a1 / b1)) =
      (1 - t) * (b0 * negMulLog (a0 / b0)) + t * (b1 * negMulLog (a1 / b1)) := by
    field_simp
  linarith

lemma hh_qf (n j : ℝ) : hh n j = (qf j n + qf (n - j) n) / log 2 := by unfold hh qf; ring_nf

/-- `h` is concave along segments: the chord lies below. -/
theorem hh_chord {n0 j0 n1 j1 t : ℝ} (hn0 : 0 < n0) (hj0 : 0 ≤ j0) (hjn0 : j0 ≤ n0) (hn1 : 0 < n1)
    (hj1 : 0 ≤ j1) (hjn1 : j1 ≤ n1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * hh n0 j0 + t * hh n1 j1 ≤ hh ((1 - t) * n0 + t * n1) ((1 - t) * j0 + t * j1) := by
  rw [hh_qf, hh_qf, hh_qf]
  have c1 := qf_concave hj0 hn0 hj1 hn1 ht0 ht1
  have c2 := qf_concave (sub_nonneg.mpr hjn0) hn0 (sub_nonneg.mpr hjn1) hn1 ht0 ht1
  have e : (1 - t) * n0 + t * n1 - ((1 - t) * j0 + t * j1) = (1 - t) * (n0 - j0) + t * (n1 - j1) := by ring
  rw [e]
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hsum : (1 - t) * (qf j0 n0 + qf (n0 - j0) n0) + t * (qf j1 n1 + qf (n1 - j1) n1) ≤
      qf ((1 - t) * j0 + t * j1) ((1 - t) * n0 + t * n1) +
        qf ((1 - t) * (n0 - j0) + t * (n1 - j1)) ((1 - t) * n0 + t * n1) := by linarith
  calc (1 - t) * ((qf j0 n0 + qf (n0 - j0) n0) / log 2) + t * ((qf j1 n1 + qf (n1 - j1) n1) / log 2)
      = ((1 - t) * (qf j0 n0 + qf (n0 - j0) n0) + t * (qf j1 n1 + qf (n1 - j1) n1)) / log 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hsum hL.le

/-! ## The colour profile -/

noncomputable def bR (k ρ m : ℝ) : ℝ := k + ρ * (m - k)
noncomputable def L4 (k ρ m d : ℝ) : ℝ := hh (1 / 2) d + hh (1 / 2) (bR k ρ m - d) - hh (1 - m) (bR k ρ m - m)
noncomputable def R4 (k ρ m d : ℝ) : ℝ := hh k (m - k) + hh (bR k ρ m - m) (d - m)
/-- `tau max(L, 0) + (1 - tau) R`: a non-empty colour has left degree at least 1. -/
noncomputable def G4 (k ρ τ m d : ℝ) : ℝ := τ * max (L4 k ρ m d) 0 + (1 - τ) * R4 k ρ m d
/-- The central colour polygon of Lemma 3.5'. -/
def Poly4 (k ρ m d : ℝ) : Prop := k ≤ m ∧ m ≤ 2 * k ∧ m ≤ d ∧ d ≤ bR k ρ m

/-! ## Soundness of the cell checker -/

/-- The leaf majorant over the reals (the formula of `Uq`). -/
noncomputable def UR (P : Prob) (gA gB gC gD : Gib) (e0 e1 m0 m1 : ℚ) (m d : ℝ) : ℝ :=
  (P.τ : ℝ) * ((d * gA.cp + (1 / 2 - d) * gA.cq) + ((bR P.k P.ρ m - d) * gB.cp
      + (1 / 2 - (bR P.k P.ρ m - d)) * gB.cq) - (e0 + (e1 - e0) * (m - m0) / (m1 - m0)))
  + (1 - (P.τ : ℝ)) * (((m - P.k) * gC.cp + (P.k - (m - P.k)) * gC.cq)
      + ((d - m) * gD.cp + ((bR P.k P.ρ m - m) - (d - m)) * gD.cq))

noncomputable def RR (P : Prob) (gC gD : Gib) (m d : ℝ) : ℝ :=
  (1 - (P.τ : ℝ)) * (((m - P.k) * gC.cp + (P.k - (m - P.k)) * gC.cq)
      + ((d - m) * gD.cp + ((bR P.k P.ρ m - m) - (d - m)) * gD.cq))

lemma Uq_cast (P : Prob) (gA gB gC gD : Gib) (e0 e1 m0 m1 m d : ℚ) :
    ((Uq P gA gB gC gD e0 e1 m0 m1 m d : ℚ) : ℝ) = UR P gA gB gC gD e0 e1 m0 m1 m d := by
  unfold Uq UR bR Prob.bq; push_cast; ring

lemma Rq_cast (P : Prob) (gC gD : Gib) (m d : ℚ) : ((Rq P gC gD m d : ℚ) : ℝ) = RR P gC gD m d := by
  unfold Rq RR bR Prob.bq; push_cast; ring

lemma UR_aff (P : Prob) (gA gB gC gD : Gib) (e0 e1 m0 m1 : ℚ) (m d : ℝ) :
    UR P gA gB gC gD e0 e1 m0 m1 m d = UR P gA gB gC gD e0 e1 m0 m1 0 0
      + (UR P gA gB gC gD e0 e1 m0 m1 1 0 - UR P gA gB gC gD e0 e1 m0 m1 0 0) * m
      + (UR P gA gB gC gD e0 e1 m0 m1 0 1 - UR P gA gB gC gD e0 e1 m0 m1 0 0) * d := by
  unfold UR bR; ring

lemma RR_aff (P : Prob) (gC gD : Gib) (m d : ℝ) :
    RR P gC gD m d = RR P gC gD 0 0 + (RR P gC gD 1 0 - RR P gC gD 0 0) * m
      + (RR P gC gD 0 1 - RR P gC gD 0 0) * d := by
  unfold RR bR; ring

/-- An affine function below `T` at the four corners of a box is below `T` on the box. -/
lemma aff_box {A B C T m0 m1 d0 d1 m d : ℝ} (h00 : A + B * m0 + C * d0 ≤ T) (h01 : A + B * m0 + C * d1 ≤ T)
    (h10 : A + B * m1 + C * d0 ≤ T) (h11 : A + B * m1 + C * d1 ≤ T) (hm0 : m0 ≤ m) (hm1 : m ≤ m1)
    (hd0 : d0 ≤ d) (hd1 : d ≤ d1) : A + B * m + C * d ≤ T := by
  have hm : B * m ≤ B * m0 ∨ B * m ≤ B * m1 := by
    rcases le_total 0 B with hB | hB
    · exact Or.inr (mul_le_mul_of_nonneg_left hm1 hB)
    · exact Or.inl (mul_le_mul_of_nonpos_left hm0 hB)
  have hd : C * d ≤ C * d0 ∨ C * d ≤ C * d1 := by
    rcases le_total 0 C with hC | hC
    · exact Or.inr (mul_le_mul_of_nonneg_left hd1 hC)
    · exact Or.inl (mul_le_mul_of_nonpos_left hd0 hC)
  rcases hm with hm | hm <;> rcases hd with hd | hd <;> linarith

lemma bq_cast (P : Prob) (m : ℚ) : ((P.bq m : ℚ) : ℝ) = bR P.k P.ρ m := by
  unfold Prob.bq bR; push_cast; ring

/-- The facts `Prob.ok` gives, over the reals. -/
lemma prob_facts {P : Prob} (hP : P.ok = true) :
    (0 : ℝ) < P.k ∧ (1 : ℝ) ≤ P.ρ ∧ (0 : ℝ) ≤ P.τ ∧ (P.τ : ℝ) ≤ 1 ∧ bR P.k P.ρ (2 * P.k) ≤ 1 / 2 := by
  simp only [Prob.ok, Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hP
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4, ?_⟩
  have : ((P.bq (2 * P.k) : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h5
  rw [bq_cast] at this
  push_cast at this
  linarith

set_option maxHeartbeats 1000000 in
/-- A passing leaf proves `G4 ≤ T` on its box. -/
theorem leaf_sound (P : Prob) (hP : P.ok = true) (m0 m1 d0 d1 : ℚ) (gA gB gC gD : Gib) (h0 h1 : HLo)
    (h : leafOK P m0 m1 d0 d1 gA gB gC gD h0 h1 = true) (m d : ℝ) (hp : Poly4 P.k P.ρ m d)
    (hm0 : (m0 : ℝ) ≤ m) (hm1 : m ≤ m1) (hd0 : (d0 : ℝ) ≤ d) (hd1 : d ≤ d1) :
    G4 P.k P.ρ P.τ m d ≤ P.T := by
  obtain ⟨hk, hρ, hτ0, hτ1, hb2⟩ := prob_facts hP
  obtain ⟨pk, pm, pd, pb⟩ := hp
  simp only [leafOK, cornerOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkm0, hm01⟩, hm1k⟩, hgA⟩, hgB⟩, hgC⟩, hgD⟩, hh0⟩, hh1⟩, ⟨u00, r00⟩⟩, ⟨u01, r01⟩⟩,
    ⟨u10, r10⟩⟩, ⟨u11, r11⟩⟩ := h
  have hkm0' : (P.k : ℝ) ≤ m0 := by exact_mod_cast hkm0
  have hm01' : (m0 : ℝ) < m1 := by exact_mod_cast hm01
  have hm1k' : (m1 : ℝ) ≤ 2 * P.k := by exact_mod_cast hm1k
  -- the block size, and the ranges every entropy term needs
  have hbm : bR P.k P.ρ m ≤ bR P.k P.ρ (2 * P.k) := by
    unfold bR; nlinarith [mul_le_mul_of_nonneg_left pm (show (0 : ℝ) ≤ P.ρ by linarith)]
  have hd12 : d ≤ 1 / 2 := by linarith
  have hbd : bR P.k P.ρ m - d ≤ 1 / 2 := by linarith
  -- Gibbs on the four plus-sign terms
  have gA' := Gib.sound gA hgA (n := 1 / 2) (j := d) (by linarith) (by linarith)
  have gB' := Gib.sound gB hgB (n := 1 / 2) (j := bR P.k P.ρ m - d) (by linarith) (by linarith)
  have gC' := Gib.sound gC hgC (n := P.k) (j := m - P.k) (by linarith) (by linarith)
  have gD' := Gib.sound gD hgD (n := bR P.k P.ρ m - m) (j := d - m) (by linarith) (by linarith)
  -- the chord on the minus-sign term
  have e0 := HLo.sound _ _ h0 hh0
  have e1 := HLo.sound _ _ h1 hh1
  push_cast at e0 e1
  set t := (m - m0) / (m1 - m0) with htdef
  have hden : (0 : ℝ) < m1 - m0 := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hden.le
  have ht1 : t ≤ 1 := by rw [div_le_one hden]; linarith
  have hρ1 : (0 : ℝ) ≤ P.ρ - 1 := by linarith
  have hk1 : (2 : ℝ) * P.k ≤ 1 / 2 := by unfold bR at hb2; nlinarith
  have ch := hh_chord (n0 := 1 - m0) (j0 := (P.ρ - 1) * (m0 - P.k)) (n1 := 1 - m1) (j1 := (P.ρ - 1) * (m1 - P.k))
    (t := t) (by linarith) (mul_nonneg hρ1 (by linarith)) (by unfold bR at hb2; nlinarith)
    (by linarith) (mul_nonneg hρ1 (by linarith)) (by unfold bR at hb2; nlinarith) ht0 ht1
  have hn : (1 - t) * (1 - (m0 : ℝ)) + t * (1 - m1) = 1 - m := by
    rw [htdef]; field_simp; ring
  have hj : (1 - t) * ((P.ρ - 1) * ((m0 : ℝ) - P.k)) + t * ((P.ρ - 1) * (m1 - P.k)) = bR P.k P.ρ m - m := by
    rw [htdef]; unfold bR; field_simp; ring
  rw [hn, hj] at ch
  have hE : (h0.lo : ℝ) + ((h1.lo : ℝ) - h0.lo) * (m - m0) / (m1 - m0) ≤ hh (1 - m) (bR P.k P.ρ m - m) := by
    have : (h0.lo : ℝ) + ((h1.lo : ℝ) - h0.lo) * (m - m0) / (m1 - m0) = (1 - t) * h0.lo + t * h1.lo := by
      rw [htdef]; field_simp; ring
    rw [this]
    have q0 := mul_le_mul_of_nonneg_left e0 (show (0 : ℝ) ≤ 1 - t by linarith)
    have q1 := mul_le_mul_of_nonneg_left e1 ht0
    linarith only [ch, q0, q1]
  -- the two majorants
  have hL : L4 P.k P.ρ m d ≤ (d * gA.cp + (1 / 2 - d) * gA.cq) + ((bR P.k P.ρ m - d) * gB.cp
      + (1 / 2 - (bR P.k P.ρ m - d)) * gB.cq) - (h0.lo + (h1.lo - h0.lo) * (m - m0) / (m1 - m0)) := by
    unfold L4; linarith
  have hR : R4 P.k P.ρ m d ≤ ((m - P.k) * gC.cp + (P.k - (m - P.k)) * gC.cq)
      + ((d - m) * gD.cp + ((bR P.k P.ρ m - m) - (d - m)) * gD.cq) := by
    unfold R4; linarith
  have hU : (P.τ : ℝ) * L4 P.k P.ρ m d + (1 - P.τ) * R4 P.k P.ρ m d ≤ UR P gA gB gC gD h0.lo h1.lo m0 m1 m d := by
    unfold UR
    nlinarith [mul_le_mul_of_nonneg_left hL hτ0, mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 1 - P.τ by linarith)]
  have hRR : (1 - (P.τ : ℝ)) * R4 P.k P.ρ m d ≤ RR P gC gD m d := by
    unfold RR; exact mul_le_mul_of_nonneg_left hR (by linarith)
  -- the corners
  have cu : ∀ a b : ℚ, Uq P gA gB gC gD h0.lo h1.lo m0 m1 a b ≤ P.T →
      UR P gA gB gC gD h0.lo h1.lo m0 m1 a b ≤ P.T := by
    intro a b hab; rw [← Uq_cast]; exact_mod_cast hab
  have cr : ∀ a b : ℚ, Rq P gC gD a b ≤ P.T → RR P gC gD a b ≤ P.T := by
    intro a b hab; rw [← Rq_cast]; exact_mod_cast hab
  have hUT : UR P gA gB gC gD h0.lo h1.lo m0 m1 m d ≤ P.T := by
    have a00 := cu _ _ u00; have a01 := cu _ _ u01; have a10 := cu _ _ u10; have a11 := cu _ _ u11
    rw [UR_aff] at a00 a01 a10 a11 ⊢
    exact aff_box a00 a01 a10 a11 hm0 hm1 hd0 hd1
  have hRT : RR P gC gD m d ≤ P.T := by
    have a00 := cr _ _ r00; have a01 := cr _ _ r01; have a10 := cr _ _ r10; have a11 := cr _ _ r11
    rw [RR_aff] at a00 a01 a10 a11 ⊢
    exact aff_box a00 a01 a10 a11 hm0 hm1 hd0 hd1
  unfold G4
  rcases le_total (L4 P.k P.ρ m d) 0 with hl | hl
  · rw [max_eq_right hl]; linarith
  · rw [max_eq_left hl]; linarith

/-- Every polygon point of a box lies in its clipped box. -/
lemma clip_mem {P : Prob} (hP : P.ok = true) {m0 m1 d0 d1 : ℚ} {m d : ℝ} (hp : Poly4 P.k P.ρ m d)
    (hm0 : (m0 : ℝ) ≤ m) (hm1 : m ≤ m1) (hd0 : (d0 : ℝ) ≤ d) (hd1 : d ≤ d1) :
    ((max d0 m0 : ℚ) : ℝ) ≤ d ∧ d ≤ ((min d1 (P.bq m1) : ℚ) : ℝ) := by
  obtain ⟨hk, hρ, -, -, -⟩ := prob_facts hP
  obtain ⟨-, -, pd, pb⟩ := hp
  have hb : bR P.k P.ρ m ≤ bR P.k P.ρ m1 := by
    unfold bR; nlinarith [mul_le_mul_of_nonneg_left hm1 (show (0 : ℝ) ≤ P.ρ by linarith)]
  push_cast
  rw [bq_cast]
  exact ⟨max_le hd0 (by linarith), le_min hd1 (by linarith)⟩

/-- A passing cell tree proves `G4 ≤ T` at every polygon point of its box. -/
theorem chk_sound (P : Prob) (hP : P.ok = true) : ∀ (t : CT) (m0 m1 d0 d1 : ℚ), chk P t m0 m1 d0 d1 = true →
    ∀ m d : ℝ, Poly4 P.k P.ρ m d → (m0 : ℝ) ≤ m → m ≤ m1 → (d0 : ℝ) ≤ d → d ≤ d1 →
      G4 P.k P.ρ P.τ m d ≤ P.T := by
  intro t
  induction t with
  | none =>
    intro m0 m1 d0 d1 h m d hp hm0 hm1 hd0 hd1
    simp only [chk, decide_eq_true_eq] at h
    obtain ⟨c0, c1⟩ := clip_mem hP hp hm0 hm1 hd0 hd1
    have h' : ((min d1 (P.bq m1) : ℚ) : ℝ) < ((max d0 m0 : ℚ) : ℝ) := by exact_mod_cast h
    linarith
  | leaf gA gB gC gD h0 h1 =>
    intro m0 m1 d0 d1 h m d hp hm0 hm1 hd0 hd1
    simp only [chk] at h
    obtain ⟨c0, c1⟩ := clip_mem hP hp hm0 hm1 hd0 hd1
    exact leaf_sound P hP m0 m1 _ _ gA gB gC gD h0 h1 h m d hp hm0 hm1 c0 c1
  | sm l r ihl ihr =>
    intro m0 m1 d0 d1 h m d hp hm0 hm1 hd0 hd1
    simp only [chk, Bool.and_eq_true] at h
    obtain ⟨c0, c1⟩ := clip_mem hP hp hm0 hm1 hd0 hd1
    rcases le_total m (((m0 + m1) / 2 : ℚ) : ℝ) with hmm | hmm
    · exact ihl _ _ _ _ h.1 m d hp hm0 hmm c0 c1
    · exact ihr _ _ _ _ h.2 m d hp hmm hm1 c0 c1
  | sd l r ihl ihr =>
    intro m0 m1 d0 d1 h m d hp hm0 hm1 hd0 hd1
    simp only [chk, Bool.and_eq_true] at h
    obtain ⟨c0, c1⟩ := clip_mem hP hp hm0 hm1 hd0 hd1
    rcases le_total d (((max d0 m0 + min d1 (P.bq m1)) / 2 : ℚ) : ℝ) with hdd | hdd
    · exact ihl _ _ _ _ h.1 m d hp hm0 hm1 c0 hdd
    · exact ihr _ _ _ _ h.2 m d hp hm0 hm1 hdd c1

/-- The root box contains the whole polygon, so a passing tree proves `G4 ≤ T` on all of `Poly4`. -/
theorem G4_le_of_cells (P : Prob) (hP : P.ok = true) (t : CT) (a b c : ℚ) (ha : P.k = a) (hb : 2 * P.k = b)
    (hc : P.bq (2 * P.k) = c) (h : chk P t a b a c = true) :
    ∀ m d : ℝ, Poly4 P.k P.ρ m d → G4 P.k P.ρ P.τ m d ≤ P.T := by
  rw [← ha, ← hb, ← hc] at h
  intro m d hp
  obtain ⟨hk, hρ, -, -, -⟩ := prob_facts hP
  obtain ⟨pk, pm, pd, pb⟩ := hp
  have hbm : bR P.k P.ρ m ≤ bR P.k P.ρ (2 * P.k) := by
    unfold bR; nlinarith [mul_le_mul_of_nonneg_left pm (show (0 : ℝ) ≤ P.ρ by linarith)]
  refine chk_sound P hP t _ _ _ _ h m d ⟨pk, pm, pd, pb⟩ pk (by push_cast; linarith) (by linarith) ?_
  rw [bq_cast]; push_cast; linarith

/-! ## From the contacts to Lemma 3.4's hypothesis -/

/-- The colour value is affine in `tau`, so bounds at `ta ≤ tb` give the bound in between. -/
lemma G4_between {k ρ m d ta tb τ A σ : ℝ} (hab : ta ≤ τ) (hτb : τ ≤ tb)
    (ha : G4 k ρ ta m d ≤ A + σ * ta) (hb : G4 k ρ tb m d ≤ A + σ * tb) : G4 k ρ τ m d ≤ A + σ * τ := by
  unfold G4 at *
  have := SS.lin_le (A := max (L4 k ρ m d) 0 - R4 k ρ m d - σ) (C := R4 k ρ m d - A) (c := 0)
    (lo := ta) (hi := tb) (x := τ) (by linarith) (by linarith) hab hτb
  linarith

/-- Lemma 3.4's hypothesis for one circuit. The line through `(t1, A1)` and `(t2, A2)` with `A1 ≥ t1 h(s)`,
`A2 ≥ (1 - t2)(1 - s)` and slope in `[-(1 - s), h(s)]`, and the contact bounds `V(t1) ≤ A1`, `V(t2) ≤ A2`. -/
theorem line_single (k ρ hs s t1 t2 A1 A2 : ℝ) (h12 : t1 < t2)
    (hA1 : t1 * hs ≤ A1) (hA2 : (1 - t2) * (1 - s) ≤ A2)
    (hsl1 : (A2 - A1) / (t2 - t1) ≤ hs) (hsl2 : -(1 - s) ≤ (A2 - A1) / (t2 - t1))
    (c1 : ∀ m d, Poly4 k ρ m d → G4 k ρ t1 m d ≤ A1) (c2 : ∀ m d, Poly4 k ρ m d → G4 k ρ t2 m d ≤ A2) :
    ∀ τ : ℝ, (∀ m d, Poly4 k ρ m d → G4 k ρ τ m d ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1)) ∨
      τ * hs ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1) ∨
      (1 - τ) * (1 - s) ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1) := by
  intro τ
  set σ := (A2 - A1) / (t2 - t1) with hσ
  have hne : t2 - t1 ≠ 0 := (sub_pos.mpr h12).ne'
  have hA2' : A1 + σ * (t2 - t1) = A2 := by rw [hσ]; field_simp; ring
  rcases le_or_gt τ t1 with h | h
  · right; left; nlinarith
  rcases le_or_gt t2 τ with h' | h'
  · right; right; nlinarith
  left
  intro m d hp
  have := G4_between (A := A1 - σ * t1) (σ := σ) h.le h'.le (by linarith [c1 m d hp]) (by linarith [c2 m d hp])
  linarith

/-- Lemma 3.4's hypothesis for a family of two circuits: member 1 below the line at `t1` and `v`, member 2 at `v`
and `t2`. -/
theorem line_family (k ρ1 ρ2 hs s t1 t2 v A1 A2 : ℝ) (h12 : t1 < t2)
    (hA1 : t1 * hs ≤ A1) (hA2 : (1 - t2) * (1 - s) ≤ A2)
    (hsl1 : (A2 - A1) / (t2 - t1) ≤ hs) (hsl2 : -(1 - s) ≤ (A2 - A1) / (t2 - t1))
    (c1 : ∀ m d, Poly4 k ρ1 m d → G4 k ρ1 t1 m d ≤ A1)
    (c1v : ∀ m d, Poly4 k ρ1 m d → G4 k ρ1 v m d ≤ A1 + (A2 - A1) / (t2 - t1) * (v - t1))
    (c2v : ∀ m d, Poly4 k ρ2 m d → G4 k ρ2 v m d ≤ A1 + (A2 - A1) / (t2 - t1) * (v - t1))
    (c2 : ∀ m d, Poly4 k ρ2 m d → G4 k ρ2 t2 m d ≤ A2) :
    ∀ τ : ℝ, (∀ m d, Poly4 k ρ1 m d → G4 k ρ1 τ m d ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1)) ∨
      (∀ m d, Poly4 k ρ2 m d → G4 k ρ2 τ m d ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1)) ∨
      τ * hs ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1) ∨
      (1 - τ) * (1 - s) ≤ A1 + (A2 - A1) / (t2 - t1) * (τ - t1) := by
  intro τ
  set σ := (A2 - A1) / (t2 - t1) with hσ
  have hne : t2 - t1 ≠ 0 := (sub_pos.mpr h12).ne'
  have hA2' : A1 + σ * (t2 - t1) = A2 := by rw [hσ]; field_simp; ring
  rcases le_or_gt τ t1 with h | h
  · right; right; left; nlinarith
  rcases le_or_gt t2 τ with h' | h'
  · right; right; right; nlinarith
  rcases le_total τ v with hv | hv
  · left
    intro m d hp
    have := G4_between (A := A1 - σ * t1) (σ := σ) h.le hv (by linarith [c1 m d hp]) (by linarith [c1v m d hp])
    linarith
  · right; left
    intro m d hp
    have := G4_between (A := A1 - σ * t1) (σ := σ) hv h'.le (by linarith [c2v m d hp]) (by linarith [c2 m d hp])
    linarith

/-- A lower bound on one colour's `G4`, from bounds on its five entropy terms. -/
lemma G4_ge {k ρ τ m d a b c e f : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (ha : a ≤ hh (1 / 2) d)
    (hb : b ≤ hh (1 / 2) (bR k ρ m - d)) (hc : hh (1 - m) (bR k ρ m - m) ≤ c) (he : e ≤ hh k (m - k))
    (hf : f ≤ hh (bR k ρ m - m) (d - m)) : τ * (a + b - c) + (1 - τ) * (e + f) ≤ G4 k ρ τ m d := by
  unfold G4 L4 R4
  have h1 : τ * (a + b - c) ≤ τ * max (hh (1 / 2) d + hh (1 / 2) (bR k ρ m - d) - hh (1 - m) (bR k ρ m - m)) 0 :=
    mul_le_mul_of_nonneg_left ((by linarith : a + b - c ≤ _).trans (le_max_left _ _)) hτ0
  have h2 := mul_le_mul_of_nonneg_left (add_le_add he hf) (show (0 : ℝ) ≤ 1 - τ by linarith)
  linarith

/-- [F1]: if one grid step past each contact the trivial lines are beaten (a colour with value `G1 ≥ c1 h(s)` at
`tau = c1`, one with `G2 ≥ (1 - c2)(1 - s)` at `tau = c2`), then every line valid in the sense of `line_single` (or
`line_family`) is above `c1 h(s)` at `c1` and above `(1 - c2)(1 - s)` at `c2`, so its xi = (h(s) - s)/2 - (l + r)/2
is at most the chord value. `G1 ≤ line(c1)` is what validity gives when the colour's own disjunct holds. -/
theorem F1_of (hs s c1 c2 l r G1 G2 : ℝ) (hc12 : c1 < 1 / 2) (hc2 : 1 / 2 < c2)
    (hw1 : c1 * hs ≤ G1) (hw2 : (1 - c2) * (1 - s) ≤ G2)
    (ht1 : c1 * hs ≤ (1 - c1) * (1 - s)) (ht2 : (1 - c2) * (1 - s) ≤ c2 * hs)
    (hline1 : G1 ≤ r + c1 * (l - r) ∨ c1 * hs ≤ r + c1 * (l - r) ∨ (1 - c1) * (1 - s) ≤ r + c1 * (l - r))
    (hline2 : G2 ≤ r + c2 * (l - r) ∨ c2 * hs ≤ r + c2 * (l - r) ∨ (1 - c2) * (1 - s) ≤ r + c2 * (l - r)) :
    (hs - s) / 2 - (l + r) / 2 ≤
      (hs - s) / 2 - (c1 * hs + ((1 - c2) * (1 - s) - c1 * hs) * (1 / 2 - c1) / (c2 - c1)) := by
  have l1 : c1 * hs ≤ r + c1 * (l - r) := by
    rcases hline1 with h | h | h <;> linarith
  have l2 : (1 - c2) * (1 - s) ≤ r + c2 * (l - r) := by
    rcases hline2 with h | h | h <;> linarith
  have hd : 0 < c2 - c1 := by linarith
  have key : (c2 - c1) * (c1 * hs + ((1 - c2) * (1 - s) - c1 * hs) * (1 / 2 - c1) / (c2 - c1)) =
      (c2 - 1 / 2) * (c1 * hs) + (1 / 2 - c1) * ((1 - c2) * (1 - s)) := by field_simp; ring
  have key2 : (c2 - c1) * ((l + r) / 2) = (c2 - 1 / 2) * (r + c1 * (l - r)) + (1 / 2 - c1) * (r + c2 * (l - r)) := by
    ring
  have k1 := mul_le_mul_of_nonneg_left l1 (show (0 : ℝ) ≤ c2 - 1 / 2 by linarith)
  have k2 := mul_le_mul_of_nonneg_left l2 (show (0 : ℝ) ≤ 1 / 2 - c1 by linarith)
  have : c1 * hs + ((1 - c2) * (1 - s) - c1 * hs) * (1 / 2 - c1) / (c2 - c1) ≤ (l + r) / 2 := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_left hcon hd
    linarith
  linarith

end SS4
