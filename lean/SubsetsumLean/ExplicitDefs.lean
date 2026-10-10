import SubsetsumLean.Basic

/-!
# The explicit Stage 2 design (`cert/cert_explicit.py`, `PROOF/stage2b-explicit.md` Lemmas E2 to E6)

Every quantity of Certificate [A] is defined here over `ℚ`, by the same formulas as `cert_explicit.py`. The
integer witnesses (the hole-fixing count `J`, the rebalancing depth `d*`, and upper bounds `ℓ` on `log2 x` with
`x ≤ 2^ℓ`) are fields of `Design`; `DesignOK` states the property each witness must have, so a theorem about
`DesignOK` does not trust the script's choice of them.

The two analytic constants enter as rationals, `LN2lo = 0.6931 ≤ ln 2` and `LOG2Elo = 1.4426 ≤ log2 e`; the
theorem `ln2_bounds` in `Explicit.lean` proves both from `log_two_mem`. Ye-Li's anchors `V(0), V(1/2), V(1)`
enter as their 20-place truncations plus `1e-20`, i.e. as upper bounds.
-/

namespace SS

def LN2lo : ℚ := 6931 / 10000
def LOG2Elo : ℚ := 14426 / 10000
def V0u : ℚ := 49268569663735450584 / 10 ^ 20 + 1 / 10 ^ 20
def Vhu : ℚ := 24997913372377961141 / 10 ^ 20 + 1 / 10 ^ 20
def V1u : ℚ := 757766963945240565 / 10 ^ 20 + 1 / 10 ^ 20
/-- Ye-Li's `a` and `b` (Sec. 4), exact rationals with denominator `10^26`. -/
def aYL : ℚ := 37954865735953624129927 / 10 ^ 26
def bYL : ℚ := 99094548027616196930017929 / 10 ^ 26
/-- Stage 2's rational pair `(dL', dR')`. -/
def dLp : ℚ := 7275870560 / 10 ^ 12
def dRp : ℚ := 492684058989 / 10 ^ 12
def xiB : ℚ := 2 / 10 ^ 5

/-- PROOF E2(vi): row loss `(2e)^2 / (2 ln2 (1 - 4e^2))` plus query loss `e^2 a / ((1/4-e)(1/4-e-a) ln2)`. -/
def epsWin (e a : ℚ) : ℚ :=
  (2 * e) ^ 2 / (2 * LN2lo * (1 - (2 * e) ^ 2)) + e * e * a / ((1 / 4 - e) * (1 / 4 - e - a) * LN2lo)

/-- A design: block parameter `k` (base length `N0 = k^2 + 2k`), window half-width `e`, Ye-Li's `a`, the pair
`(dL, dR)`, and the integer witnesses. -/
structure Design where
  k : ℕ
  e : ℚ
  a : ℚ
  dL : ℚ
  dR : ℚ
  J : ℕ
  lgN : ℕ
  lgk : ℕ
  lgJ : ℕ
  dstar : ℕ

namespace Design
variable (d : Design)

def N : ℕ := d.k * d.k + 2 * d.k
def Nq : ℚ := (d.N : ℚ)
/-- Hoeffding exponent of E3 minus the per-flip 2: `2 e^2 N log2 e - 2` with `log2 e ≥ 1.4426`. -/
def den : ℚ := 2 * d.e * d.e * d.Nq * LOG2Elo - 2
/-- PROOF E3: `eps_V = eps_win + J/N + (5 + 15 log2(N+1))/N`. -/
def epsV : ℚ := epsWin d.e d.a + (d.J : ℚ) / d.Nq + (5 + 15 * (d.lgN : ℚ)) / d.Nq
def U0 : ℚ := V0u + d.epsV
def Uh : ℚ := Vhu + d.epsV
def U1 : ℚ := V1u + d.epsV
/-- The crossing of `Vbar + eps_V` with `tau`. -/
def t1 : ℚ := d.U0 / (1 + 2 * d.U0 - 2 * d.Uh)
/-- The crossing of `Vbar + eps_V` with `(1 - tau)/2` (on the second segment, else on the first). -/
def t2 : ℚ :=
  let r := (1 / 2 - 2 * d.Uh + d.U1) / (1 / 2 + 2 * d.U1 - 2 * d.Uh)
  if r < 1 / 2 then (1 / 2 - d.U0) / (2 * (d.Uh - d.U0) + 1 / 2) else r
def c1 : ℚ := d.t1
def c2 : ℚ := (1 - d.t2) / 2
def line (t : ℚ) : ℚ := t * d.dL + (1 - t) * d.dR
def s1 : ℚ := d.c1 / d.t1
def s2 : ℚ := (d.c2 - d.c1) / (d.t2 - d.t1)
def s3 : ℚ := -d.c2 / (1 - d.t2)
/-- PROOF E4: `Delta = min gap of A * min slope gap / 4`, per coordinate. -/
def Delta : ℚ := min d.t1 (min (d.t2 - d.t1) (1 - d.t2)) * min (d.s1 - d.s2) (d.s2 - d.s3) / 4
def v3 (t : ℚ) : ℚ := if t ≤ 1 / 2 then d.U0 + 2 * t * (d.Uh - d.U0) else d.Uh + 2 * (t - 1 / 2) * (d.U1 - d.Uh)
/-- `max_t (v_t(tau) - c(tau))` at one point of `A`. -/
def rAt (t c : ℚ) : ℚ := max (t - c) (max ((1 - t) / 2 - c) (d.v3 t - c))
def rmax : ℚ := max (d.rAt 0 0) (max (d.rAt d.t1 d.c1) (max (d.rAt d.t2 d.c2) (d.rAt 1 0)))
/-- `log2 (8 D_inf) / N0 ≤ LD` (PROOF E4 claim, plus 3 for the factor 8). -/
def LD : ℚ := (d.dstar : ℚ) * (d.rmax + 2) + 4 + 3
def epsL : ℚ := 2 * d.dL / d.k + (1 + 2 / (d.k : ℚ)) * d.epsV + (d.lgk : ℚ) / d.k
def epsR : ℚ := 2 * d.dR / d.k + (1 + 2 / (d.k : ℚ)) * d.epsV
/-- `c = L_D + 1 (padding) + 1 (storage) + 1 (additive preprocessing)` (PROOF Sec. 7). -/
def c : ℚ := d.LD + 3
def gain : ℚ := (xiB - 2 * max d.epsL d.epsR) / (12 + 2 * (xiB - 2 * max d.epsL d.epsR))

end Design

/-- Every check of Certificate [A] for a design, with the property each integer witness must have. -/
structure DesignOK (d : Design) (q : ℕ) (LDmax cmax : ℚ) : Prop where
  k_even : d.k % 2 = 0
  q_dvd : d.N % q = 0
  lgN : d.N + 1 ≤ 2 ^ d.lgN
  lgk : d.k + 1 ≤ 2 ^ d.lgk
  lgJ : d.J ≤ 2 ^ d.lgJ
  /-- E3: `J (2 e^2 N log2 e - 2) > 2.5 N`, so at most `2^{2.5N} delta^J < 1` pairs are left. -/
  den_pos : 0 < d.den
  J_ok : 5 / 2 * d.Nq < (d.J : ℚ) * d.den
  e_le : d.e ≤ 1 / 20
  struct : 0 < d.t1 ∧ d.t1 < 1 / 3 ∧ 1 / 3 < d.t2 ∧ d.t2 < 1 ∧ 2 * d.Uh ≤ d.U0 + d.U1 ∧ d.t1 ≤ 1 / 2
  slopes : d.s2 < d.s1 ∧ d.s3 < d.s2
  secant : d.c1 ≤ d.line d.t1 + d.epsV ∧ d.c2 ≤ d.line d.t2 + d.epsV
  NDelta : 1 ≤ d.Nq * d.Delta
  /-- `d* > r_max / Delta`, which is all the E4 induction uses of `d*`. -/
  dstar_ok : d.rmax < (d.dstar : ℚ) * d.Delta
  LD_le : d.LD ≤ LDmax
  epsL_le : d.epsL ≤ 1 / 10 ^ 9
  epsR_le : d.epsR ≤ 1 / 10 ^ 9
  pad : d.k * d.k + 2 ≤ d.N
  /-- Lemma E6's numeric hypotheses. -/
  e6 : 8 * d.J ≤ d.N ∧ (15 : ℚ) + 31 * d.lgN + d.lgJ ≤ 49 / 100 * d.Nq ∧ d.U0 ≤ 1 / 2
  c_le : d.c ≤ cmax

/-! ## Moving an entropy bound to a nearby point -/

open Real in
/-- `H(1 - x) = H(x)`. -/
lemma Hb_symm (x : ℝ) : Hb (1 - x) = Hb x := by
  unfold Hb; rw [sub_sub_cancel]; ring

/-- A lower bound at `r` holds at every `x` in `[r, 1/2]` (`H` increases on `[0, 1/2]`). -/
lemma Hb_ge_of {x r lo : ℝ} (h0 : 0 ≤ r) (hr : r ≤ x) (hx : x ≤ 1 / 2) (hlo : lo ≤ Hb r) : lo ≤ Hb x :=
  hlo.trans (Hb_mono h0 hr hx)

/-- An upper bound at `r` holds at every `x` in `[0, r]`, for `r ≤ 1/2`. -/
lemma Hb_le_of {x r hi : ℝ} (h0 : 0 ≤ x) (hr : x ≤ r) (hx : r ≤ 1 / 2) (hhi : Hb r ≤ hi) : Hb x ≤ hi :=
  (Hb_mono h0 hr hx).trans hhi

end SS
