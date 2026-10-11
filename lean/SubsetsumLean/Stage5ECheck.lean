import SubsetsumLean.Stage4ECheck

/-!
# Stage 5: the computable checkers behind the exponent rows (rationals only)

`certificates/stage5/cert_stage5.py` bounds, per layer kappa, the cost terms of a design `(a, c1, c2, w)`: a core fraction
`a` from the row's menu, two menu circuits `c1, c2` (density `s`, line values `l = line(1)`, `r = line(0)`) and an outer
split `w`. With `t = (kappa - a (s1 + 1 - s2)/2) / (1 - a)`:
- `base = H(kappa) - (1 - a) H(t)/2 + (1 - a)/2 - 1 + lambda`,
- `u = 1/2 + mu (base + (a/2)(s1 - H(s2) + r1 + l2)) + (1 - mu) w`, `v = 1/2 + mu (base + (a/2)(s2 - H(s1) + l1 + r2)) - (1 - mu) w`,
- `P3 = max(u, v) - (j - 1) mu (1 - H(kappa))`, `J = H(kappa) - (a/2)(H(s1) + H(s2)) - (1 - a) H(t)`,
- `P4 = mu (J + lambda) + mu (log2 3 + 1)/4 + max(mu, (1 - mu)(1/2 + |w|) - mu)`, `P6 = mu (1 + H(kappa) + J + lambda)`;
a design is valid if `a = 0` or `0 < t < 1`, and `j mu ≤ (1 - mu)(1/2 - |w|)` (each outer side holds j blocks).
Every term increases with `H(kappa)`, `l`, `r` and decreases with `H(t)` and `H(s)` (for `0 ≤ a < 1`, `mu ≥ 0`), so on a
piece `[ka, kb] ⊆ [0, 1/2]` an upper bound on `H(kb)` and lower bounds on `H(t(ka))`, `H(t(kb))` (H is concave, so its
minimum on `[t(ka), t(kb)]` is at an end) bound every term. For `a = 0`, `t = kappa` and the terms are exact in `H(kappa)`
(`J = 0`), so no bound on `H(t)` is needed; that is how the tails `kappa ≤ 2/5` are covered.

`Row.chk` walks the pieces of `[0, 1/2]` (the other half follows by the symmetry `kappa ↦ 1 - kappa`, which swaps the
two circuits and negates `w`). `Row.refute` is the must-fail checker: at one kappa, every design of the menu has a
term above the target (for every `w`, and for every `lambda ≥ 0`).
-/

namespace SS5

open SS4

/-- A menu circuit: density `s`, `hsLo ≤ H(s) ≤ hsHi`, and the line values `l ≥ line(1)`, `r ≥ line(0)`. -/
structure Circ where
  s : ℚ
  hsLo : ℚ
  hsHi : ℚ
  l : ℚ
  r : ℚ
deriving DecidableEq

/-- One exponent row: `mu`, `j` dedupe blocks per side, `lambda` (an upper bound), `l3 ≥ log2 3`, the claim,
symmetric designs only (`c1 = c2`, `w = 0`) or not, the alpha menu and the circuits. `osv` is added to the v-line:
0 for every certified row, `mu` for control K4 (the v-list not deduped). -/
structure Row where
  μ : ℚ
  j : ℕ
  lam : ℚ
  l3 : ℚ
  claim : ℚ
  sym : Bool
  osv : ℚ
  alphas : List ℚ
  circs : List Circ

/-- `t = (kappa - a (s1 + 1 - s2)/2) / (1 - a)`. -/
def t5 (a s1 s2 κ : ℚ) : ℚ := (κ - a * (s1 + 1 - s2) / 2) / (1 - a)

/-- The rational terms, given `B ≥ base`, `Jq ≥ J`, `HK ≥ H(kappa)`. -/
def Row.termsOK (R : Row) (a : ℚ) (c1 c2 : Circ) (w B Jq HK : ℚ) : Bool :=
  decide (1 / 2 + R.μ * (B + a / 2 * (c1.s - c2.hsLo + c1.r + c2.l)) + (1 - R.μ) * w
      - ((R.j : ℚ) - 1) * R.μ * (1 - HK) ≤ R.claim) &&
  decide (1 / 2 + R.μ * (B + a / 2 * (c2.s - c1.hsLo + c1.l + c2.r)) - (1 - R.μ) * w + R.osv
      - ((R.j : ℚ) - 1) * R.μ * (1 - HK) ≤ R.claim) &&
  decide (R.μ * (Jq + R.lam) + R.μ * (R.l3 + 1) / 4 + max R.μ ((1 - R.μ) * (1 / 2 + |w|) - R.μ) ≤ R.claim) &&
  decide (R.μ * (1 + HK + Jq + R.lam) ≤ R.claim)

/-- A piece `[ka, kb]` with its design (indices into the menus), the bound at `kb` and, for `a > 0`, at `t(ka)`, `t(kb)`. -/
structure EP where
  κb : ℚ
  ia : ℕ
  i1 : ℕ
  i2 : ℕ
  w : ℚ
  hk : HbU
  ta : HbL
  tb : HbL

def Row.pieceOK (R : Row) (κa : ℚ) (p : EP) : Bool :=
  match R.alphas[p.ia]?, R.circs[p.i1]?, R.circs[p.i2]? with
  | some a, some c1, some c2 =>
    (!R.sym || (decide (p.i1 = p.i2) && decide (p.w = 0))) && decide (0 ≤ a) && decide (a < 1) &&
    decide (1 ≤ R.j) && decide ((R.j : ℚ) * R.μ ≤ (1 - R.μ) * (1 / 2 - |p.w|)) &&
    decide (0 ≤ κa) && decide (κa ≤ p.κb) && decide (p.κb ≤ 1 / 2) && p.hk.ok p.κb &&
    (if a = 0 then R.termsOK a c1 c2 p.w (p.hk.hi / 2 - 1 / 2 + R.lam) 0 p.hk.hi
     else
      p.ta.ok (t5 a c1.s c2.s κa) && p.tb.ok (t5 a c1.s c2.s p.κb) &&
      R.termsOK a c1 c2 p.w (p.hk.hi - (1 - a) * min p.ta.lo p.tb.lo / 2 + (1 - a) / 2 - 1 + R.lam)
        (p.hk.hi - a / 2 * (c1.hsLo + c2.hsLo) - (1 - a) * min p.ta.lo p.tb.lo) p.hk.hi)
  | _, _, _ => false

/-- The pieces cover `[ka, kend]` contiguously and every piece passes. -/
def Row.chk (R : Row) (κend : ℚ) : ℚ → List EP → Bool
  | κa, [] => decide (κa = κend)
  | κa, p :: ps => R.pieceOK κa p && R.chk κend p.κb ps

/-- The constant terms `P1 = mu`, `P5 = Pscan = 2 mu`, `Kenum = mu (2 + lambda)`, and `0 < mu < 1`, `lambda ≥ 0`. -/
def Row.ok (R : Row) : Bool :=
  decide (0 < R.μ) && decide (R.μ < 1) && decide (0 ≤ R.lam) && decide (R.μ ≤ R.claim) &&
  decide (2 * R.μ ≤ R.claim) && decide (R.μ * (2 + R.lam) ≤ R.claim)

/-! ## The must-fail checker -/

/-- The designs of a row's menu, in a fixed order: every `a`, every ordered pair (only `c1 = c2` if symmetric). -/
def Row.designs (R : Row) : List (ℚ × Circ × Circ) :=
  R.alphas.flatMap fun a => R.circs.flatMap fun c1 =>
    R.circs.filterMap fun c2 => if R.sym && !decide (c1 = c2) then none else some (a, c1, c2)

/-- Lower bounds at one kappa, for every `w` and `lambda ≥ 0`, given `HK ≤ H(kappa)` and `HT ≥ H(t)`: P3 is at least the
mean of its two lines, and at least the larger line moved by the largest `|w|` the fit allows; P6 is the third test. -/
def Row.refCore (R : Row) (κ HK : ℚ) (d : ℚ × Circ × Circ) (HT : ℚ) : Bool :=
  let a := d.1
  let c1 := d.2.1
  let c2 := d.2.2
  let B : ℚ := if a = 0 then HK / 2 - 1 / 2 else HK - (1 - a) * HT / 2 + (1 - a) / 2 - 1
  let Jq : ℚ := if a = 0 then 0 else HK - a / 2 * (c1.hsHi + c2.hsHi) - (1 - a) * HT
  let u := 1 / 2 + R.μ * (B + a / 2 * (c1.s - c2.hsHi + c1.r + c2.l))
  let v := 1 / 2 + R.μ * (B + a / 2 * (c2.s - c1.hsHi + c1.l + c2.r)) + R.osv
  let g := ((R.j : ℚ) - 1) * R.μ * (1 - HK)
  decide (0 ≤ a) && decide (a < 1) &&
    (decide (R.claim < (u + v) / 2 - g) ||
     decide (R.claim < max u v - (1 - R.μ) * (1 / 2 - (R.j : ℚ) * R.μ / (1 - R.μ)) - g) ||
     decide (R.claim < R.μ * (1 + HK + Jq)))

/-- A design is refuted if it is invalid (`a > 0` and `t` outside `(0, 1)`), or by `refCore` with `HT` an upper bound
on `H(t)` from `ht` (or `HT = 1`). -/
def Row.refOne (R : Row) (κ HK : ℚ) (d : ℚ × Circ × Circ) (ht : Option HbU) : Bool :=
  (decide (d.1 ≠ 0) && (decide (t5 d.1 d.2.1.s d.2.2.s κ ≤ 0) || decide (1 ≤ t5 d.1 d.2.1.s d.2.2.s κ))) ||
  match ht with
  | some e => e.ok (t5 d.1 d.2.1.s d.2.2.s κ) && R.refCore κ HK d e.hi
  | none => R.refCore κ HK d 1

def refL (R : Row) (κ HK : ℚ) : List (ℚ × Circ × Circ) → List (Option HbU) → Bool
  | [], [] => true
  | d :: ds, h :: hs => R.refOne κ HK d h && refL R κ HK ds hs
  | _, _ => false

/-- At `kappa` (with `HK ≤ H(kappa)` certified by `hk`), every design of the menu fails the claim. -/
def Row.refute (R : Row) (κ : ℚ) (hk : HbL) (hts : List (Option HbU)) : Bool :=
  decide (0 < R.μ) && decide (R.μ < 1) && decide (1 ≤ R.j) && hk.ok κ && refL R κ hk.lo R.designs hts

end SS5
