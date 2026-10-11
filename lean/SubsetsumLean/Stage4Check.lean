import Mathlib.Algebra.Order.Field.Rat

/-!
# Stage 4: the computable cell checker behind [XI] (no analysis imported)

This module is deliberately light (rationals only), so the generated `Stage4Cells_*` modules, which evaluate the
checker by `decide +kernel`, stay well under the 3 GB build limit. `Stage4Defs.lean` proves the checker sound.

A *problem* is `(k, rho, tau, T)`: the colour polygon `{k ≤ m ≤ 2k, m ≤ d ≤ b(m)}` with `b(m) = k + rho (m - k)`
(`k = s/2`), the weight `tau`, and the target `T`. `chk` walks a binary tree of boxes. Each node first clips its
d-range to `[max d0 m0, min d1 (b m1)]` (every polygon point of the box stays inside); `none` asserts the clipped box
is empty, `sm`/`sd` split m or d at the midpoint, and a `leaf` carries
- four Gibbs coefficient pairs (`Gib`): `h(n, j) ≤ j cp + (n - j) cq`, with `cp ≥ -log2 p`, `cq ≥ -log2 (1 - p)`
  certified by lower bounds on `log p`, `log (1 - p)`;
- two lower bounds (`HLo`) on `h(1 - m, b(m) - m)` at `m0` and `m1`, whose chord bounds the concave term below;
and checks the two resulting affine bounds at the four corners of the box.
-/

namespace SS4

/-- A rational literal `a / b`, cheap to elaborate. -/
def Q (a : Int) (b : Nat) : ℚ := (a : ℚ) / (b : ℚ)

/-- `2^k` for an integer `k`, in `ℚ`. -/
def p2 (k : ℤ) : ℚ := if 0 ≤ k then (2 : ℚ) ^ k.toNat else 1 / (2 : ℚ) ^ (-k).toNat

/-- `∑_{i<n} t^(i+1)/(i+1)` (the same recursion as `SS.lsum`). -/
def lsumQ (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lsumQ t n + t ^ (n + 1) / ((n : ℚ) + 1)

/-- The tail bound `|t|^(n+1) / (1 - |t|)` (as `SS.lrem`). -/
def lremQ (t : ℚ) (n : ℕ) : ℚ := |t| ^ (n + 1) / (1 - |t|)

/-- The bounds on `log 2` of `SS.L2lo`, `SS.L2hi`. -/
def L2loQ : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 - 1 / 10 ^ 42
def L2hiQ : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 + 1 / 10 ^ 42

/-- Series terms in every log bound of the cell certificates. -/
def NT : ℕ := 30

/-- `l ≤ log x`, by the series of `log (1 - t)` at `t = 1 - x / 2^k`. -/
def logGe (x : ℚ) (k : ℤ) (l : ℚ) : Bool :=
  decide (0 < x) && decide (|1 - x / p2 k| < 1) &&
  decide (l ≤ -(lsumQ (1 - x / p2 k) NT) - lremQ (1 - x / p2 k) NT + min (k * L2loQ) (k * L2hiQ))

/-- `log x ≤ u`. -/
def logLe (x : ℚ) (k : ℤ) (u : ℚ) : Bool :=
  decide (0 < x) && decide (|1 - x / p2 k| < 1) &&
  decide (-(lsumQ (1 - x / p2 k) NT) + lremQ (1 - x / p2 k) NT + max (k * L2loQ) (k * L2hiQ) ≤ u)

/-- Gibbs data: tangent point `p`, `l1 ≤ log p`, `l2 ≤ log (1 - p)`, and `cp, cq ≥ 0` with `-l1 ≤ cp L2lo`,
`-l2 ≤ cq L2lo`. -/
structure Gib where
  p : ℚ
  k1 : ℤ
  k2 : ℤ
  l1 : ℚ
  l2 : ℚ
  cp : ℚ
  cq : ℚ

def Gib.ok (g : Gib) : Bool :=
  decide (0 < g.p) && decide (g.p < 1) && logGe g.p g.k1 g.l1 && logGe (1 - g.p) g.k2 g.l2 &&
  decide (0 ≤ g.cp) && decide (0 ≤ g.cq) && decide (-g.l1 ≤ g.cp * L2loQ) && decide (-g.l2 ≤ g.cq * L2loQ)

/-- A lower bound `lo ≤ h(c, x)`: `lc ≤ log c`, `log x ≤ ux`, `log (c - x) ≤ uy` (or `x = 0`, where `h = 0`). -/
structure HLo where
  kc : ℤ
  kx : ℤ
  ky : ℤ
  lc : ℚ
  ux : ℚ
  uy : ℚ
  lo : ℚ

def HLo.ok (c x : ℚ) (e : HLo) : Bool :=
  if x = 0 then decide (e.lo ≤ 0) else
  decide (0 < x) && decide (x < c) && logGe c e.kc e.lc && logLe x e.kx e.ux && logLe (c - x) e.ky e.uy &&
  decide (0 ≤ e.lo) && decide (e.lo * L2hiQ ≤ c * e.lc - x * e.ux - (c - x) * e.uy)

/-- A contact problem `(k, rho, tau, T)`. -/
structure Prob where
  k : ℚ
  ρ : ℚ
  τ : ℚ
  T : ℚ

def Prob.bq (P : Prob) (m : ℚ) : ℚ := P.k + P.ρ * (m - P.k)

def Prob.ok (P : Prob) : Bool :=
  decide (0 < P.k) && decide (1 ≤ P.ρ) && decide (0 ≤ P.τ) && decide (P.τ ≤ 1) && decide (P.bq (2 * P.k) ≤ 1 / 2)

/-- The affine majorant of `tau L + (1 - tau) R` on a leaf (first component) and of `(1 - tau) R` (second). -/
def Uq (P : Prob) (gA gB gC gD : Gib) (e0 e1 m0 m1 m d : ℚ) : ℚ :=
  P.τ * ((d * gA.cp + (1 / 2 - d) * gA.cq) + ((P.bq m - d) * gB.cp + (1 / 2 - (P.bq m - d)) * gB.cq)
      - (e0 + (e1 - e0) * (m - m0) / (m1 - m0)))
  + (1 - P.τ) * (((m - P.k) * gC.cp + (P.k - (m - P.k)) * gC.cq)
      + ((d - m) * gD.cp + ((P.bq m - m) - (d - m)) * gD.cq))

def Rq (P : Prob) (gC gD : Gib) (m d : ℚ) : ℚ :=
  (1 - P.τ) * (((m - P.k) * gC.cp + (P.k - (m - P.k)) * gC.cq)
      + ((d - m) * gD.cp + ((P.bq m - m) - (d - m)) * gD.cq))

def cornerOK (P : Prob) (gA gB gC gD : Gib) (e0 e1 m0 m1 m d : ℚ) : Bool :=
  decide (Uq P gA gB gC gD e0 e1 m0 m1 m d ≤ P.T) && decide (Rq P gC gD m d ≤ P.T)

def leafOK (P : Prob) (m0 m1 d0 d1 : ℚ) (gA gB gC gD : Gib) (h0 h1 : HLo) : Bool :=
  decide (P.k ≤ m0) && decide (m0 < m1) && decide (m1 ≤ 2 * P.k) &&
  gA.ok && gB.ok && gC.ok && gD.ok &&
  h0.ok (1 - m0) ((P.ρ - 1) * (m0 - P.k)) && h1.ok (1 - m1) ((P.ρ - 1) * (m1 - P.k)) &&
  cornerOK P gA gB gC gD h0.lo h1.lo m0 m1 m0 d0 && cornerOK P gA gB gC gD h0.lo h1.lo m0 m1 m0 d1 &&
  cornerOK P gA gB gC gD h0.lo h1.lo m0 m1 m1 d0 && cornerOK P gA gB gC gD h0.lo h1.lo m0 m1 m1 d1

/-- The cell tree. -/
inductive CT where
  | none
  | leaf (gA gB gC gD : Gib) (h0 h1 : HLo)
  | sm (l r : CT)
  | sd (l r : CT)

/-- The checker on the box `[m0, m1] × [d0, d1]`. -/
def chk (P : Prob) : CT → ℚ → ℚ → ℚ → ℚ → Bool
  | .none, m0, m1, d0, d1 => decide (min d1 (P.bq m1) < max d0 m0)
  | .leaf gA gB gC gD h0 h1, m0, m1, d0, d1 =>
      leafOK P m0 m1 (max d0 m0) (min d1 (P.bq m1)) gA gB gC gD h0 h1
  | .sm l r, m0, m1, d0, d1 =>
      chk P l m0 ((m0 + m1) / 2) (max d0 m0) (min d1 (P.bq m1)) &&
      chk P r ((m0 + m1) / 2) m1 (max d0 m0) (min d1 (P.bq m1))
  | .sd l r, m0, m1, d0, d1 =>
      chk P l m0 m1 (max d0 m0) ((max d0 m0 + min d1 (P.bq m1)) / 2) &&
      chk P r m0 m1 ((max d0 m0 + min d1 (P.bq m1)) / 2) (min d1 (P.bq m1))

/-- One `sm` step of `chk`, with the child boxes given as rationals (so a tree can be checked in parts). -/
theorem chk_sm (P : Prob) (l r : CT) (m0 m1 d0 d1 mm a c : ℚ) (hmm : (m0 + m1) / 2 = mm)
    (ha : max d0 m0 = a) (hc : min d1 (P.bq m1) = c) (hl : chk P l m0 mm a c = true)
    (hr : chk P r mm m1 a c = true) : chk P (.sm l r) m0 m1 d0 d1 = true := by
  simp only [chk, hmm, ha, hc, hl, hr, Bool.and_self]

/-- One `sd` step of `chk`. -/
theorem chk_sd (P : Prob) (l r : CT) (m0 m1 d0 d1 a c dm : ℚ) (ha : max d0 m0 = a)
    (hc : min d1 (P.bq m1) = c) (hdm : (a + c) / 2 = dm) (hl : chk P l m0 m1 a dm = true)
    (hr : chk P r m0 m1 dm c = true) : chk P (.sd l r) m0 m1 d0 d1 = true := by
  simp only [chk, ha, hc, hdm, hl, hr, Bool.and_self]

end SS4
