import SubsetsumLean.Basic
import SubsetsumLean.Stage2Defs

/-!
# Stage 3: definitions and the general lemmas behind `cert/cert_stage3.py`

Stage 3 (`PROOF/stage3.md`) uses a re-tuned Ye-Li Sec. 3.5 circuit. Its colour profile has, per colour
`(mu, theta)` in the polygon `a1 ≤ mu ≤ a1 + a0, mu ≤ theta ≤ r mu`, the left exponent
`L = max(E1, max(A, 0), E1 + A + h(r mu, theta) - r mu)` and the right exponent
`R = E0 + h(a0, mu - a1) + h((r-1) mu, theta - mu)`, where `h(n, k) = n H(k/n)` in bits (`hh`). Ye-Li's Lemma 3.4
needs `min{V, tau, (1-tau)/2} ≤ line` on `[0, 1]`, with `V(tau)` the max over colours of `tau L + (1 - tau) R`.

Proved here, once and for all:
- `gibbs_nat`, `hh_le_gibbs`: Gibbs' inequality `h(n, k) ≤ k (-log2 p) + (n - k)(-log2 (1 - p))`;
- `ent_le`: the same with kernel-checked rational bounds on the two logs (`entOK`);
- `hh_mem`: rational enclosures of `h(c, x)` at rational points (`hhOK`);
- `hh_le_self`: `h(n, k) ≤ n`; `hh_eq_mul_Hb`: `h(c, k) = c H(k/c)`;
- `quad_le`: an affine function bounded at the four vertices is bounded on the polygon;
- `line_of_U`: the six bounds `g_i(t1) ≤ t1`, `g_i(t2) ≤ (1 - t2)/2` and `A > 0` give Lemma 3.4's hypothesis;
- `xi_le_of_F1`: two rigorous lower bounds on `V` just outside the crossings bound `xi` for every valid line;
- the Stage 3 cost terms `s3Terms` and the checks `CertS3`.
-/

open Real

namespace SS

/-! ## Entropy `h(n, k)` in bits -/

/-- `h(n, k) = n log2 n - k log2 k - (n - k) log2 (n - k)` (Mathlib's `log 0 = 0`, so `0 log 0 = 0`). -/
noncomputable def hh (n k : ℝ) : ℝ := (n * log n - k * log k - (n - k) * log (n - k)) / log 2

/-- Gibbs' inequality, natural logs: for `0 ≤ k ≤ n` and `0 < p < 1`. -/
lemma gibbs_nat {n k p : ℝ} (hk : 0 ≤ k) (hkn : k ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    n * log n - k * log k - (n - k) * log (n - k) ≤ -k * log p - (n - k) * log (1 - p) := by
  have hq0 : 0 < 1 - p := by linarith
  have lp : log p < 0 := Real.log_neg hp0 hp1
  have lq : log (1 - p) < 0 := Real.log_neg hq0 (by linarith)
  rcases eq_or_lt_of_le hk with h0 | hk0
  · subst h0
    simp only [zero_mul, sub_zero, neg_zero, sub_self, zero_sub]
    nlinarith [mul_nonneg hkn (neg_nonneg.mpr lq.le)]
  rcases eq_or_lt_of_le hkn with h1 | h1
  · subst h1
    simp only [sub_self, zero_mul, sub_zero, log_zero]
    nlinarith [mul_nonneg hk (neg_nonneg.mpr lp.le)]
  have hn : 0 < n := by linarith
  have hnk : 0 < n - k := by linarith
  have e1 := Real.log_le_sub_one_of_pos (show 0 < p * n / k by positivity)
  have e2 := Real.log_le_sub_one_of_pos (show 0 < (1 - p) * n / (n - k) by positivity)
  rw [Real.log_div (by positivity) hk0.ne', Real.log_mul hp0.ne' hn.ne'] at e1
  rw [Real.log_div (by positivity) hnk.ne', Real.log_mul hq0.ne' hn.ne'] at e2
  have m1 := mul_le_mul_of_nonneg_left e1 hk0.le
  have m2 := mul_le_mul_of_nonneg_left e2 hnk.le
  have f1 : k * (p * n / k - 1) = p * n - k := by field_simp
  have f2 : (n - k) * ((1 - p) * n / (n - k) - 1) = (1 - p) * n - (n - k) := by field_simp
  rw [f1] at m1
  rw [f2] at m2
  nlinarith [m1, m2]

lemma hh_le_gibbs {n k p : ℝ} (hk : 0 ≤ k) (hkn : k ≤ n) (hp0 : 0 < p) (hp1 : p < 1) :
    hh n k ≤ (-k * log p - (n - k) * log (1 - p)) / log 2 :=
  div_le_div_of_nonneg_right (gibbs_nat hk hkn hp0 hp1) (Real.log_pos one_lt_two).le

/-- `h(n, k) ≤ n` (Gibbs at `p = 1/2`). -/
lemma hh_le_self {n k : ℝ} (hk : 0 ≤ k) (hkn : k ≤ n) : hh n k ≤ n := by
  have g := hh_le_gibbs hk hkn (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hL : 0 < log (2 : ℝ) := Real.log_pos one_lt_two
  have e : log (1 / 2 : ℝ) = -log 2 := by rw [one_div, Real.log_inv]
  have e' : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [e', e] at g
  have : (-k * -log 2 - (n - k) * -log 2) / log 2 = n := by field_simp; ring
  linarith

/-- `h(c, k) = c H(k/c)` for `0 < k < c`. -/
lemma hh_eq_mul_Hb {c k : ℝ} (hk : 0 < k) (hkc : k < c) : hh c k = c * Hb (k / c) := by
  have hc : 0 < c := by linarith
  have hck : 0 < c - k := by linarith
  have e : 1 - k / c = (c - k) / c := by field_simp
  unfold hh Hb
  rw [e, Real.log_div hk.ne' hc.ne', Real.log_div hck.ne' hc.ne']
  field_simp
  ring

/-- The kernel-checked condition behind `ent_le`: log enclosures of `p` and `1 - p`, and rationals
`cp ≥ -log2 p`, `cq ≥ -log2 (1 - p)` (through `ln 2 ≥ L2lo`). -/
def entOK (p : ℚ) (k1 k2 : ℤ) (N : ℕ) (l1 u1 l2 u2 cp cq : ℚ) : Bool :=
  logOK p k1 N l1 u1 && logOK (1 - p) k2 N l2 u2 && decide (0 < p) && decide (p < 1) && decide (0 ≤ cp) &&
  decide (0 ≤ cq) && decide (-l1 ≤ cp * L2lo) && decide (-l2 ≤ cq * L2lo)

/-- Gibbs' inequality with rational coefficients: `h(n, k) ≤ k cp + (n - k) cq` whenever `0 ≤ k ≤ n`. -/
theorem ent_le (n k : ℝ) (p : ℚ) (k1 k2 : ℤ) (N : ℕ) (l1 u1 l2 u2 cp cq : ℚ) (hk : 0 ≤ k) (hkn : 0 ≤ n - k)
    (h : entOK p k1 k2 N l1 u1 l2 u2 cp cq = true) : hh n k ≤ k * cp + (n - k) * cq := by
  simp only [entOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hp0⟩, hp1⟩, hcp⟩, hcq⟩, hA⟩, hB⟩ := h
  obtain ⟨a1, -⟩ := log_mem (p : ℝ) p l1 u1 k1 N (l1 : ℝ) (u1 : ℝ) rfl rfl rfl h1
  obtain ⟨a2, -⟩ := log_mem (1 - (p : ℝ)) (1 - p) l2 u2 k2 N (l2 : ℝ) (u2 : ℝ) (by push_cast; ring) rfl rfl h2
  obtain ⟨c1, -⟩ := log_two_mem
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hp1' : (p : ℝ) < 1 := by exact_mod_cast hp1
  have hcp' : (0 : ℝ) ≤ cp := by exact_mod_cast hcp
  have hcq' : (0 : ℝ) ≤ cq := by exact_mod_cast hcq
  have hA' : -(l1 : ℝ) ≤ cp * L2lo := by exact_mod_cast hA
  have hB' : -(l2 : ℝ) ≤ cq * L2lo := by exact_mod_cast hB
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have g : hh n k ≤ (-k * log (p : ℝ) - (n - k) * log (1 - (p : ℝ))) / log 2 :=
    hh_le_gibbs (n := n) hk (by linarith) hp0' hp1'
  have e1 : -log (p : ℝ) ≤ cp * log 2 := by nlinarith [mul_le_mul_of_nonneg_left c1 hcp']
  have e2 : -log (1 - (p : ℝ)) ≤ cq * log 2 := by nlinarith [mul_le_mul_of_nonneg_left c1 hcq']
  have m1 := mul_le_mul_of_nonneg_left e1 hk
  have m2 := mul_le_mul_of_nonneg_left e2 hkn
  have : (-k * log p - (n - k) * log (1 - p)) / log 2 ≤ k * cp + (n - k) * cq := by
    rw [div_le_iff₀ hL]; nlinarith [m1, m2]
  linarith

/-- The kernel-checked condition behind `hh_mem`: log enclosures of `c`, `x`, `c - x` (all positive), and
`[lo, hi]` containing the resulting enclosure of `h(c, x)`. -/
def hhOK (c x : ℚ) (kc kx ky : ℤ) (N : ℕ) (lc uc lx ux ly uy lo hi : ℚ) : Bool :=
  logOK c kc N lc uc && logOK x kx N lx ux && logOK (c - x) ky N ly uy && decide (0 < x) && decide (x < c) &&
  decide (0 ≤ lo) && decide (0 ≤ hi) &&
  decide (lo * L2hi ≤ c * lc - x * ux - (c - x) * uy) && decide (c * uc - x * lx - (c - x) * ly ≤ hi * L2lo)

/-- Rigorous bounds `lo ≤ h(c, e) ≤ hi` for real expressions equal to rationals `0 < x < c`. -/
theorem hh_mem (c e : ℝ) (cq x : ℚ) (kc kx ky : ℤ) (N : ℕ) (lc uc lx ux ly uy lo hi : ℚ) (hc : c = cq)
    (he : e = x) (h : hhOK cq x kc kx ky N lc uc lx ux ly uy lo hi = true) : (lo : ℝ) ≤ hh c e ∧ hh c e ≤ hi := by
  simp only [hhOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hx0⟩, hxc⟩, hlo0⟩, hhi0⟩, hA⟩, hB⟩ := h
  obtain ⟨a1, b1⟩ := log_mem (cq : ℝ) cq lc uc kc N (lc : ℝ) (uc : ℝ) rfl rfl rfl h1
  obtain ⟨a2, b2⟩ := log_mem (x : ℝ) x lx ux kx N (lx : ℝ) (ux : ℝ) rfl rfl rfl h2
  obtain ⟨a3, b3⟩ := log_mem ((cq : ℝ) - x) (cq - x) ly uy ky N (ly : ℝ) (uy : ℝ) (by push_cast; ring) rfl rfl h3
  obtain ⟨c1, c2⟩ := log_two_mem
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hxc' : (x : ℝ) < cq := by exact_mod_cast hxc
  have hy : (0 : ℝ) < (cq : ℝ) - x := by linarith
  have hc0 : (0 : ℝ) < cq := by linarith
  have hA' : (lo : ℝ) * L2hi ≤ cq * lc - x * ux - (cq - x) * uy := by exact_mod_cast hA
  have hB' : (cq : ℝ) * uc - x * lx - (cq - x) * ly ≤ hi * L2lo := by exact_mod_cast hB
  have hlo0' : (0 : ℝ) ≤ lo := by exact_mod_cast hlo0
  have hhi0' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have m1 := mul_le_mul_of_nonneg_left a1 hc0.le
  have m2 := mul_le_mul_of_nonneg_left b1 hc0.le
  have m3 := mul_le_mul_of_nonneg_left a2 hx0'.le
  have m4 := mul_le_mul_of_nonneg_left b2 hx0'.le
  have m5 := mul_le_mul_of_nonneg_left a3 hy.le
  have m6 := mul_le_mul_of_nonneg_left b3 hy.le
  have m7 := mul_le_mul_of_nonneg_left c2 hlo0'
  have m8 := mul_le_mul_of_nonneg_left c1 hhi0'
  subst hc he
  unfold hh
  constructor
  · rw [le_div_iff₀ hL]; nlinarith
  · rw [div_le_iff₀ hL]; nlinarith

/-! ## Affine functions on an interval and on the colour polygon -/

lemma lin_le {A C c lo hi x : ℝ} (hlo : A * lo + C ≤ c) (hhi : A * hi + C ≤ c) (h1 : lo ≤ x) (h2 : x ≤ hi) :
    A * x + C ≤ c := by
  rcases le_total 0 A with h | h
  · nlinarith [mul_le_mul_of_nonneg_left h2 h]
  · nlinarith [mul_le_mul_of_nonpos_left h1 h]

/-- An affine function of `(mu, theta)` that is `≤ c` at the four vertices of
`{m0 ≤ mu ≤ m1, mu ≤ theta ≤ r mu}` is `≤ c` on the whole polygon. -/
lemma quad_le {A B C c m0 m1 r mu θ : ℝ}
    (v1 : A * m0 + B * m0 + C ≤ c) (v2 : A * m0 + B * (r * m0) + C ≤ c)
    (v3 : A * m1 + B * m1 + C ≤ c) (v4 : A * m1 + B * (r * m1) + C ≤ c)
    (h1 : m0 ≤ mu) (h2 : mu ≤ m1) (h3 : mu ≤ θ) (h4 : θ ≤ r * mu) : A * mu + B * θ + C ≤ c := by
  rcases le_total 0 B with hB | hB
  · have e : B * θ ≤ B * (r * mu) := mul_le_mul_of_nonneg_left h4 hB
    have := lin_le (A := A + B * r) (C := C) (c := c) (lo := m0) (hi := m1) (x := mu)
      (by linarith) (by linarith) h1 h2
    linarith
  · have e : B * θ ≤ B * mu := mul_le_mul_of_nonpos_left h3 hB
    have := lin_le (A := A + B) (C := C) (c := c) (lo := m0) (hi := m1) (x := mu)
      (by linarith) (by linarith) h1 h2
    linarith

/-! ## The re-tuned colour profile (`PROOF/stage3.md` Sec. 2) -/

/-- `E1 = H(b) - h(1/4, a0) - h(1/4, a1) - h(1/2, 1-b-a0-a1)`, with `omb = 1 - b`. -/
noncomputable def E1 (a0 a1 omb : ℝ) : ℝ := hh 1 (1 - omb) - hh (1 / 4) a0 - hh (1 / 4) a1 - hh (1 / 2) (omb - a0 - a1)
/-- `E0 = b - 1/2 + a0 + a1`, the stars of `D` per coordinate. -/
noncomputable def E0 (a0 a1 omb : ℝ) : ℝ := 1 / 2 - omb + a0 + a1
/-- `H(1/r)`. -/
noncomputable def Hr (r : ℝ) : ℝ := hh 1 (1 / r)
/-- `A(mu) = h(1-b, mu) - r mu H(1/r)`, the second left term. -/
noncomputable def Aex (omb r mu : ℝ) : ℝ := hh omb mu - r * mu * Hr r

def inPoly (a0 a1 r mu θ : ℝ) : Prop := a1 ≤ mu ∧ mu ≤ a1 + a0 ∧ mu ≤ θ ∧ θ ≤ r * mu

/-- The left exponent of a colour: the max of the three left terms, the second one being `max(A, 0)` because its
count `|Q|` is at least 1. -/
noncomputable def Lcol (a0 a1 omb r mu θ : ℝ) : ℝ :=
  max (E1 a0 a1 omb) (max (max (Aex omb r mu) 0) (E1 a0 a1 omb + Aex omb r mu + hh (r * mu) θ - r * mu))
/-- The right exponent of a colour. -/
noncomputable def Rcol (a0 a1 omb r mu θ : ℝ) : ℝ := E0 a0 a1 omb + hh a0 (mu - a1) + hh ((r - 1) * mu) (θ - mu)

/-- The three majorised pieces (in `g1`, `g2` the right entropy is replaced by its bound `(r - 1) mu`). -/
noncomputable def g1 (a0 a1 omb r tau mu _θ : ℝ) : ℝ :=
  tau * E1 a0 a1 omb + (1 - tau) * (E0 a0 a1 omb + hh a0 (mu - a1) + (r - 1) * mu)
noncomputable def g2 (a0 a1 omb r tau mu _θ : ℝ) : ℝ :=
  tau * (hh omb mu - r * mu * Hr r) + (1 - tau) * (E0 a0 a1 omb + hh a0 (mu - a1) + (r - 1) * mu)
noncomputable def g3 (a0 a1 omb r tau mu θ : ℝ) : ℝ :=
  tau * (E1 a0 a1 omb + hh omb mu - r * mu * Hr r + hh (r * mu) θ - r * mu) +
    (1 - tau) * (E0 a0 a1 omb + hh a0 (mu - a1) + hh ((r - 1) * mu) (θ - mu))

/-- The line through `(t1, t1)` and `(t2, (1 - t2)/2)`. -/
noncomputable def lineF (t1 t2 tau : ℝ) : ℝ := t1 + (tau - t1) * (((1 - t2) / 2 - t1) / (t2 - t1))

/-- An affine function of `tau` below the line at `t1` and `t2` is below it in between. -/
lemma affine_mid {t1 t2 tau Lx R : ℝ} (h12 : t1 < t2) (ha : t1 ≤ tau) (hb : tau ≤ t2)
    (u1 : t1 * Lx + (1 - t1) * R ≤ t1) (u2 : t2 * Lx + (1 - t2) * R ≤ (1 - t2) / 2) :
    tau * Lx + (1 - tau) * R ≤ lineF t1 t2 tau := by
  have hd : 0 < t2 - t1 := by linarith
  set s := ((1 - t2) / 2 - t1) / (t2 - t1) with hs
  have hl : t1 + (t2 - t1) * s = (1 - t2) / 2 := by rw [hs]; field_simp; ring
  have ph1 : t1 * Lx + (1 - t1) * R - t1 ≤ 0 := by linarith
  have ph2 : t2 * Lx + (1 - t2) * R - t1 - (t2 - t1) * s ≤ 0 := by linarith
  have key : (t2 - t1) * (tau * Lx + (1 - tau) * R - t1 - (tau - t1) * s) =
      (tau - t1) * (t2 * Lx + (1 - t2) * R - t1 - (t2 - t1) * s) +
        (t2 - tau) * (t1 * Lx + (1 - t1) * R - t1) := by ring
  have k1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) ph2
  have k2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb) ph1
  have : (t2 - t1) * (tau * Lx + (1 - tau) * R - t1 - (tau - t1) * s) ≤ 0 := by linarith
  have : tau * Lx + (1 - tau) * R - t1 - (tau - t1) * s ≤ 0 := by
    by_contra hc; have hc' := not_le.mp hc; nlinarith
  unfold lineF; rw [← hs]; linarith

/-- **Lemma 3.4's hypothesis from the six majorant bounds.** If `A > 0` on the polygon and each `g_i` is at
most `t1` at `t1` and at most `(1 - t2)/2` at `t2` on the polygon, then for every `tau ∈ [0, 1]` and every
colour, `min(tau L + (1 - tau) R, tau, (1 - tau)/2) ≤ line(tau)`. -/
theorem line_of_U (a0 a1 omb r t1 t2 : ℝ) (h12 : t1 < t2) (ht2 : t2 < 1)
    (hs1 : ((1 - t2) / 2 - t1) / (t2 - t1) ≤ 1) (hs2 : -1 / 2 ≤ ((1 - t2) / 2 - t1) / (t2 - t1))
    (hA : ∀ mu θ, inPoly a0 a1 r mu θ → 0 < Aex omb r mu)
    (U11 : ∀ mu θ, inPoly a0 a1 r mu θ → g1 a0 a1 omb r t1 mu θ ≤ t1)
    (U21 : ∀ mu θ, inPoly a0 a1 r mu θ → g2 a0 a1 omb r t1 mu θ ≤ t1)
    (U31 : ∀ mu θ, inPoly a0 a1 r mu θ → g3 a0 a1 omb r t1 mu θ ≤ t1)
    (U12 : ∀ mu θ, inPoly a0 a1 r mu θ → g1 a0 a1 omb r t2 mu θ ≤ (1 - t2) / 2)
    (U22 : ∀ mu θ, inPoly a0 a1 r mu θ → g2 a0 a1 omb r t2 mu θ ≤ (1 - t2) / 2)
    (U32 : ∀ mu θ, inPoly a0 a1 r mu θ → g3 a0 a1 omb r t2 mu θ ≤ (1 - t2) / 2) :
    ∀ tau, 0 ≤ tau → tau ≤ 1 → ∀ mu θ, inPoly a0 a1 r mu θ →
      min (tau * Lcol a0 a1 omb r mu θ + (1 - tau) * Rcol a0 a1 omb r mu θ) (min tau ((1 - tau) / 2)) ≤
        lineF t1 t2 tau := by
  intro tau h0 h1 mu θ hP
  have hd : 0 < t2 - t1 := by linarith
  set s := ((1 - t2) / 2 - t1) / (t2 - t1) with hs
  have hl : t1 + (t2 - t1) * s = (1 - t2) / 2 := by rw [hs]; field_simp; ring
  rcases le_or_gt tau t1 with ha | ha
  · apply min_le_of_right_le; apply min_le_of_left_le
    unfold lineF; rw [← hs]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hs1)]
  rcases le_or_gt t2 tau with hb | hb
  · apply min_le_of_right_le; apply min_le_of_right_le
    unfold lineF; rw [← hs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show (0 : ℝ) ≤ s + 1 / 2 by linarith)]
  apply min_le_of_left_le
  obtain ⟨p1, p2, p3, p4⟩ := hP
  have hR : hh ((r - 1) * mu) (θ - mu) ≤ (r - 1) * mu := hh_le_self (by linarith) (by linarith)
  have hAp := hA mu θ ⟨p1, p2, p3, p4⟩
  have hmax : max (Aex omb r mu) 0 = Aex omb r mu := max_eq_left hAp.le
  have c1 : ∀ t, t ≤ 1 → t * E1 a0 a1 omb + (1 - t) * Rcol a0 a1 omb r mu θ ≤ g1 a0 a1 omb r t mu θ := by
    intro t ht; unfold Rcol g1; nlinarith [mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 1 - t by linarith)]
  have c2 : ∀ t, t ≤ 1 → t * max (Aex omb r mu) 0 + (1 - t) * Rcol a0 a1 omb r mu θ ≤ g2 a0 a1 omb r t mu θ := by
    intro t ht; rw [hmax]; unfold Rcol g2 Aex
    nlinarith [mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 1 - t by linarith)]
  have c3 : ∀ t, t * (E1 a0 a1 omb + Aex omb r mu + hh (r * mu) θ - r * mu) +
      (1 - t) * Rcol a0 a1 omb r mu θ = g3 a0 a1 omb r t mu θ := by
    intro t; unfold Rcol g3 Aex; ring
  have hP' : inPoly a0 a1 r mu θ := ⟨p1, p2, p3, p4⟩
  unfold Lcol
  rcases max_choice (E1 a0 a1 omb) (max (max (Aex omb r mu) 0)
      (E1 a0 a1 omb + Aex omb r mu + hh (r * mu) θ - r * mu)) with e | e <;> rw [e]
  · exact affine_mid h12 ha.le hb.le ((c1 t1 (by linarith)).trans (U11 mu θ hP'))
      ((c1 t2 (by linarith)).trans (U12 mu θ hP'))
  rcases max_choice (max (Aex omb r mu) 0) (E1 a0 a1 omb + Aex omb r mu + hh (r * mu) θ - r * mu) with e | e <;>
    rw [e]
  · exact affine_mid h12 ha.le hb.le ((c2 t1 (by linarith)).trans (U21 mu θ hP'))
      ((c2 t2 (by linarith)).trans (U22 mu θ hP'))
  · exact affine_mid h12 ha.le hb.le ((c3 t1).le.trans (U31 mu θ hP')) ((c3 t2).le.trans (U32 mu θ hP'))

/-- **The must-fail bound for xi.** If `V` exceeds `s1` at `s1` and `(1 - s2)/2` at `s2` (witnessed by two
colours), then every line `dr + tau (dl - dr)` satisfying Lemma 3.4's hypothesis has
`xi = 1/4 - (dl + dr)/2 ≤ 1/4 - chord(1/2)`, the chord through `(s1, s1)` and `(s2, (1 - s2)/2)`. -/
theorem xi_le_of_F1 (a0 a1 omb r s1 s2 dl dr m1 θ1 m2 θ2 : ℝ)
    (hP1 : inPoly a0 a1 r m1 θ1) (hP2 : inPoly a0 a1 r m2 θ2)
    (hs1 : 0 ≤ s1) (hs1' : s1 < 1 / 3) (hs2 : 1 / 3 < s2) (hs2' : s2 ≤ 1) (h12' : 1 / 2 ≤ s2)
    (lb1 : s1 < s1 * (E1 a0 a1 omb + Aex omb r m1 + hh (r * m1) θ1 - r * m1) + (1 - s1) * Rcol a0 a1 omb r m1 θ1)
    (lb2 : (1 - s2) / 2 <
      s2 * (E1 a0 a1 omb + Aex omb r m2 + hh (r * m2) θ2 - r * m2) + (1 - s2) * Rcol a0 a1 omb r m2 θ2)
    (hline : ∀ tau, 0 ≤ tau → tau ≤ 1 → ∀ mu θ, inPoly a0 a1 r mu θ →
      min (tau * Lcol a0 a1 omb r mu θ + (1 - tau) * Rcol a0 a1 omb r mu θ) (min tau ((1 - tau) / 2)) ≤
        dr + tau * (dl - dr)) :
    1 / 4 - (dl + dr) / 2 ≤ 1 / 4 - (s1 + (1 / 2 - s1) * ((1 - s2) / 2 - s1) / (s2 - s1)) := by
  have L3le : ∀ mu θ, E1 a0 a1 omb + Aex omb r mu + hh (r * mu) θ - r * mu ≤ Lcol a0 a1 omb r mu θ := by
    intro mu θ; unfold Lcol; exact (le_max_right _ _).trans (le_max_right _ _)
  have f1 : s1 < s1 * Lcol a0 a1 omb r m1 θ1 + (1 - s1) * Rcol a0 a1 omb r m1 θ1 := by
    nlinarith [mul_le_mul_of_nonneg_left (L3le m1 θ1) hs1]
  have f2 : (1 - s2) / 2 < s2 * Lcol a0 a1 omb r m2 θ2 + (1 - s2) * Rcol a0 a1 omb r m2 θ2 := by
    nlinarith [mul_le_mul_of_nonneg_left (L3le m2 θ2) (show (0 : ℝ) ≤ s2 by linarith)]
  have l1 := hline s1 hs1 (by linarith) m1 θ1 hP1
  have l2 := hline s2 (by linarith) hs2' m2 θ2 hP2
  rw [min_eq_right (le_trans (min_le_left _ _) f1.le), min_eq_left (by linarith)] at l1
  rw [min_eq_right (le_trans (min_le_right _ _) f2.le), min_eq_right (by linarith)] at l2
  have hd : 0 < s2 - s1 := by linarith
  have hz : (s2 - s1) * (s1 + (1 / 2 - s1) * ((1 - s2) / 2 - s1) / (s2 - s1)) =
      (s2 - 1 / 2) * s1 + (1 / 2 - s1) * ((1 - s2) / 2) := by field_simp; ring
  have hm : (s2 - s1) * ((dl + dr) / 2) = (s2 - 1 / 2) * (dr + s1 * (dl - dr)) + (1 / 2 - s1) * (dr + s2 * (dl - dr)) := by
    ring
  have k1 := mul_le_mul_of_nonneg_left l1 (show (0 : ℝ) ≤ s2 - 1 / 2 by linarith)
  have k2 := mul_le_mul_of_nonneg_left l2 (show (0 : ℝ) ≤ 1 / 2 - s1 by linarith)
  have : (s2 - s1) * (s1 + (1 / 2 - s1) * ((1 - s2) / 2 - s1) / (s2 - s1)) ≤ (s2 - s1) * ((dl + dr) / 2) := by
    linarith
  have := le_of_mul_le_mul_left this hd
  linarith

/-! ## The Stage 3 exponent (`PROOF/stage3.md` Theorem 3) -/

/-- The nine cost terms of Theorem 3, in the order of `cert_stage3.py`'s `terms`. -/
noncomputable def s3Terms (pi xi eps : ℝ) : List ℝ :=
  [pi, 2 * pi, logb 2 3 * pi, 1 - 3 * pi, 3 / 2 * pi, pi / 2 + 1 - 3 * pi, logb 2 3 * pi / 2 + 1 - 3 * pi,
    logb 2 3 * pi / 2 + pi, 1 / 2 - xi * pi + 2 * eps * pi]

/-- Every check of `cert_stage3.py`'s `check`: Lemma 3.5's hypotheses for the rational pair `(dl, dr)`, which lies
termwise above an admissible pair `(dLlo, dRlo)` with `dl + dr ≤ 1/2 - 2 xi'`, `xi' ≤ xiT`; `4 pi < 1`; the fit of
Lemma 3.3 (with `g = dr - dl`, `f(0) = 2g`, `f(1/2) = 3/2 + g`); and every cost term `≤ bound`. -/
structure CertS3 (pi xi eps bound dl dr dLlo dRlo xiT : ℝ) : Prop where
  pi_pos : 0 < pi
  pi_le_third : pi ≤ 1 / 3
  four_pi : 4 * pi < 1
  xi_nonneg : 0 ≤ xi
  xi_le : xi ≤ xiT
  dl_ge : dLlo ≤ dl
  dr_ge : dRlo ≤ dr
  dl_nonneg : 0 ≤ dl
  dr_nonneg : 0 ≤ dr
  pair : dl + dr ≤ 1 / 2 - 2 * xi
  g_lt : dr - dl < 1 / 2
  fit_lo : (4 - 2 * (dr - dl)) * pi < 1
  fit_hi : (2 + (3 / 2 + (dr - dl))) * pi < 1
  terms_le : ∀ t ∈ s3Terms pi xi eps, t ≤ bound

lemma s3Terms_le {pi xi eps bound : ℝ} (hpi : 0 ≤ pi) (h1 : pi ≤ bound) (h2 : 2 * pi ≤ bound)
    (h3 : 317 / 200 * pi ≤ bound) (h4 : 1 - 3 * pi ≤ bound) (h5 : 3 / 2 * pi ≤ bound)
    (h6 : pi / 2 + 1 - 3 * pi ≤ bound) (h7 : 317 / 200 * pi / 2 + 1 - 3 * pi ≤ bound)
    (h8 : 317 / 200 * pi / 2 + pi ≤ bound) (h9 : 1 / 2 - xi * pi + 2 * eps * pi ≤ bound) :
    ∀ t ∈ s3Terms pi xi eps, t ≤ bound := by
  have hl : logb 2 3 * pi ≤ 317 / 200 * pi := mul_le_mul_of_nonneg_right log2_3_lt.le hpi
  intro t ht
  simp only [s3Terms, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

lemma s3_many_mem (pi xi eps : ℝ) : 1 / 2 - xi * pi + 2 * eps * pi ∈ s3Terms pi xi eps := by simp [s3Terms]
lemma s3_cover_mem (pi xi eps : ℝ) : 2 * pi ∈ s3Terms pi xi eps := by simp [s3Terms]

/-- The fit for every `n ≥ n0` (Lemma 3.3): if `c pi n0 ≤ n0 - 2` and `c pi ≤ 1`, then `c m ≤ n - 2` for every
`n ≥ n0` and every `0 ≤ m ≤ pi n`. -/
lemma fit_tail {c pi n0 n m : ℝ} (hc : 0 ≤ c) (hcp : c * pi ≤ 1) (h0 : c * pi * n0 ≤ n0 - 2) (hn : n0 ≤ n)
    (hm : m ≤ pi * n) : c * m ≤ n - 2 := by
  have := mul_le_mul_of_nonneg_left hm hc
  nlinarith [mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 1 - c * pi by linarith)]

end SS
