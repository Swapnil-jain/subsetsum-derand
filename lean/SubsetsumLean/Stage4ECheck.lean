import SubsetsumLean.Stage4Check

/-!
# Stage 4: the computable checker behind the exponent [E] (rationals only)

`cert_stage4.py` [E] bounds every cost term of PROOF.md Sec. 5.3 over the layer range `[kappa_lo, 1 - kappa_lo]`. The
terms are symmetric under `kappa ↦ 1 - kappa` (which maps `t ↦ 1 - t`), increase with `H(kappa)` and decrease with
`H(t)`, so on a piece `[ka, kb] ⊆ [kappa_lo, 1/2]` it is enough to use an upper bound on `H(kb)` and a lower bound on
`H(t(ka))` (`H` increases on `[0, 1/2]`). `ERow.chkE` walks the pieces from `kappa_lo` to `1/2`.
-/

namespace SS4

/-- `H(x) ≤ hi` (bits), from lower bounds on `log x`, `log (1 - x)`. -/
structure HbU where
  k1 : ℤ
  k2 : ℤ
  l1 : ℚ
  l2 : ℚ
  hi : ℚ

def HbU.ok (x : ℚ) (e : HbU) : Bool :=
  decide (0 < x) && decide (x < 1) && logGe x e.k1 e.l1 && logGe (1 - x) e.k2 e.l2 && decide (0 ≤ e.hi) &&
  decide (-x * e.l1 - (1 - x) * e.l2 ≤ e.hi * L2loQ)

/-- `lo ≤ H(x)`, from upper bounds on `log x`, `log (1 - x)`. -/
structure HbL where
  k1 : ℤ
  k2 : ℤ
  u1 : ℚ
  u2 : ℚ
  lo : ℚ

def HbL.ok (x : ℚ) (e : HbL) : Bool :=
  decide (0 < x) && decide (x < 1) && logLe x e.k1 e.u1 && logLe (1 - x) e.k2 e.u2 && decide (0 ≤ e.lo) &&
  decide (e.lo * L2hiQ ≤ -x * e.u1 - (1 - x) * e.u2)

/-- One row of [E]: parameters, `xi` (a certified lower bound), `lambda` (an upper bound), `hsLo ≤ H(s)`,
`l3 ≥ log2 3`, deterministic or randomized, and the claim. -/
structure ERow where
  α : ℚ
  μ : ℚ
  δ : ℚ
  ξ : ℚ
  lam : ℚ
  s : ℚ
  hsLo : ℚ
  l3 : ℚ
  det : Bool
  claim : ℚ

/-- `t = (kappa - alpha/2) / (1 - alpha)`. -/
def tq (α κ : ℚ) : ℚ := (κ - α / 2) / (1 - α)

/-- The kappa-dependent terms with `HK ≥ H(kappa)`, `HT ≤ H(t)` and `1 - ta ≥ max(t, 1 - t)`. -/
def ERow.pieceOK (R : ERow) (HK HT ta : ℚ) : Bool :=
  decide (1 / 2 + R.μ * (HK - R.α * R.ξ - (1 - R.α) * HT / 2 + (1 - R.α) / 2 - 1 + R.δ + R.lam) ≤ R.claim) &&
  (if R.det then
    decide (R.μ * (HK - R.α * R.hsLo - (1 - R.α) * HT + R.lam) + 1 / 4 + R.μ * R.l3 / 4 ≤ R.claim) &&
    decide (R.μ * (2 - R.δ + (HK - R.α * R.hsLo - (1 - R.α) * HT) + R.lam) ≤ R.claim)
  else
    decide (1 / 4 + R.μ * (HK - 3 / 4 * R.α * R.hsLo + R.α * R.s / 4 - 3 / 4 * (1 - R.α) * HT
      + (1 - R.α) * (1 - ta) / 4) ≤ R.claim))

/-- A piece `[ka, kb]`: the upper bound at `kb` and the lower bound at `t(ka)`. -/
structure EP where
  κb : ℚ
  hk : HbU
  ht : HbL

/-- The pieces cover `[ka, 1/2]` contiguously and every piece passes. -/
def ERow.chkE (R : ERow) : ℚ → List EP → Bool
  | κa, [] => decide (κa = 1 / 2)
  | κa, p :: ps => decide (κa ≤ p.κb) && decide (p.κb ≤ 1 / 2) && p.hk.ok p.κb && p.ht.ok (tq R.α κa) &&
      R.pieceOK p.hk.hi p.ht.lo (tq R.α κa) && R.chkE p.κb ps

/-- The constant terms and the row's side conditions. -/
def ERow.ok (R : ERow) (κlo : ℚ) : Bool :=
  decide (0 < R.α) && decide (R.α < 1) && decide (0 < R.μ) && decide (R.α / 2 < κlo) && decide (κlo ≤ 1 / 2) &&
  decide (R.μ * (1 - R.δ) ≤ R.claim) && decide (1 / 2 - R.μ * R.δ / 2 ≤ R.claim) &&
  (if R.det then decide (2 * R.μ ≤ R.claim) && decide (R.μ * (2 - R.δ) ≤ R.claim) &&
    decide (R.μ * (2 + R.lam) ≤ R.claim) else true)

end SS4
