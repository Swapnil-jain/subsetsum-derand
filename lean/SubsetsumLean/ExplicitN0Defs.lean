import SubsetsumLean.ExplicitDefs
import SubsetsumLean.Stage2Defs

/-!
# Smaller n0 for the explicit Stage 2 (`PROOF/stage2b-explicit.md` Secs. 12-13; `cert/cert_explicit_b16.py`, `cert/cert_explicit_b17.py`)

Every rational quantity of the two certificates is defined here over `ℚ`, by the scripts' own formulas, so that
`decide +kernel` recomputes it: the three-piece structure and its per-pair gaps (Lemma E4'), the hull pair and
xi'' from the certified anchors (Sec. 13.4), the window and hole-fixing losses, S2 Lemma 6.1 with a general gamma
(Sec. 13.7), the ladder of base lengths (Lemma E4'', Sec. 13.6), and n0. Nothing is read from the scripts except
the inputs: the anchors (rounded up to the grid 10^-18), the window half-widths e and the base lengths N0. Every
choice made from them (J, the tail, the switch length, d1, the thresholds) is recomputed here.

The real side: `lg` is log base 2, and `tanBound` is Lemma V's concavity bound at a point x0 and a vertex v of K.
`lg_mem` encloses `lg` from the series of `Basic.lean`; `s2G_le` turns rational checks of the seven cost terms into
the real statement, with the real `log2 3`.
-/

open Real

namespace SS
namespace N0

/-! ## Integer helpers (kernel-evaluable) -/

/-- Floor of a rational, by integer floor division of numerator by denominator. -/
def qfloor (x : ℚ) : ℤ := Int.fdiv x.num x.den
def qceil (x : ℚ) : ℤ := -qfloor (-x)
/-- Floor of a nonnegative rational, as a natural number. -/
def qfloorN (x : ℚ) : ℕ := (qfloor x).toNat

def bitlenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n = 0 then 0 else bitlenAux f (n / 2) + 1
/-- Python's `int.bit_length` (exact for n < 2^1024): n < 2^(bitlen n), so it bounds log2 n from above. -/
def bitlen (n : ℕ) : ℕ := bitlenAux 1024 n
/-- The scripts' `lg_up`. -/
def lgUp (n : ℕ) : ℚ := (bitlen n : ℚ)

/-- Round up to the grid 10^-12 (the hull pair). -/
def up12 (x : ℚ) : ℚ := (qceil (x * 10 ^ 12) : ℚ) / 10 ^ 12
/-- Round down to the grid 2^-40 (the dyadic thresholds). -/
def dy40 (x : ℚ) : ℚ := (qfloor (x * 2 ^ 40) : ℚ) / 2 ^ 40

def lmax (l : List ℚ) : ℚ := l.foldl max (l.headD 0)
def lmin (l : List ℚ) : ℚ := l.foldl min (l.headD 0)

/-! ## The three-piece structure and its per-pair gaps (Lemma E4', Sec. 13.3) -/

/-- One (piece t, off point j) pair: the gap `d` = delta_{t,j} and the excess `r` = r_{t,j}. -/
structure Pair where
  t : ℕ
  j : ℕ
  d : ℚ
  r : ℚ

/-- Piece 2's volume exponent, the two-segment function through U0, Uh, U1. -/
def v3 (U0 Uh U1 t : ℚ) : ℚ := if t ≤ 1 / 2 then U0 + 2 * t * (Uh - U0) else Uh + 2 * (t - 1 / 2) * (U1 - Uh)

/-- The six pairs, for thresholds x1 (between pieces 1 and 2) and x2 (between 2 and 3). Piece 1 = (M,I) on
[0, t1], piece 2 = the window circuit on [t1, t2], piece 3 = (I,M) on [t2, 1]; c = (0, t1, (1-t2)/2, 0). -/
def pairsOf (U0 Uh U1 t1 t2 s1 s2 s3 x1 x2 : ℚ) : List Pair :=
  let c2 := (1 - t2) / 2
  [⟨1, 2, (t2 - t1) * (x1 - s2), t2 - c2⟩,
   ⟨1, 3, (t2 - t1) * (x1 - s2) + (1 - t2) * (x1 - s3), 1⟩,
   ⟨2, 0, t1 * (s1 - x1), v3 U0 Uh U1 0⟩,
   ⟨2, 3, (1 - t2) * (x2 - s3), v3 U0 Uh U1 1⟩,
   ⟨3, 0, t1 * (s1 - x2) + (t2 - t1) * (s2 - x2), 1 / 2⟩,
   ⟨3, 1, (t2 - t1) * (s2 - x2), (1 - t1) / 2 - t1⟩]

structure St where
  U0 : ℚ
  Uh : ℚ
  U1 : ℚ
  t1 : ℚ
  t2 : ℚ
  s1 : ℚ
  s2 : ℚ
  s3 : ℚ
  x1 : ℚ
  x2 : ℚ
  pairs : List Pair
  okS : Bool
  okSec : Bool
  dmin : ℚ
  d1 : ℕ
  S : ℚ
  Delta : ℚ
  rmax : ℚ
  dstar : ℕ
  LD : ℚ

/-- `structure(U, epsV, dL, dR)` of `cert_explicit_b17.py` (anchors A0, Ah, A1 before adding eps_V). -/
def mkSt (A0 Ah A1 epsV dL dR : ℚ) : St :=
  let U0 := A0 + epsV
  let Uh := Ah + epsV
  let U1 := A1 + epsV
  let t1 := U0 / (1 + 2 * U0 - 2 * Uh)
  let t2 := (1 / 2 - 2 * Uh + U1) / (1 / 2 + 2 * U1 - 2 * Uh)
  let c1 := t1
  let c2 := (1 - t2) / 2
  let s1 := c1 / t1
  let s2 := (c2 - c1) / (t2 - t1)
  let s3 := -c2 / (1 - t2)
  let x1 := dy40 ((s1 + s2) / 2)
  let x2 := dy40 ((s2 + s3) / 2)
  let ps := pairsOf U0 Uh U1 t1 t2 s1 s2 s3 x1 x2
  let line := fun t : ℚ => t * dL + (1 - t) * dR
  let okS := decide (0 < t1) && decide (t1 < 1 / 3) && decide (1 / 3 < t2) && decide (t2 < 1)
    && decide (2 * Uh ≤ U0 + U1) && decide (1 / 2 ≤ t2) && decide (s2 < s1) && decide (s3 < s2)
    && decide (|x1 - (s1 + s2) / 2| ≤ (s1 - s2) / 4) && decide (|x2 - (s2 + s3) / 2| ≤ (s2 - s3) / 4)
    && decide (v3 U0 Uh U1 t1 ≤ c1) && decide (v3 U0 Uh U1 t2 ≤ c2) && decide ((1 - t2) / 2 ≤ c2)
    && ps.all (fun p => decide (0 < p.d))
  let okSec := decide (0 ≤ line 0 + epsV) && decide (c1 ≤ line t1 + epsV) && decide (c2 ≤ line t2 + epsV)
    && decide (0 ≤ line 1 + epsV)
  let dmin := lmin (ps.map (·.d))
  let d1 := ((ps.filter (fun p => decide (0 < p.r))).map (fun p => qfloorN (p.r / p.d) + 1)).foldl max 0
  let S := ((List.range d1).map (fun i => max 0 (lmax (ps.map (fun p => p.r - ((i + 1 : ℕ) : ℚ) * p.d)))))
    |>.foldl (· + ·) 0
  let Delta := min t1 (min (t2 - t1) (1 - t2)) * min (s1 - s2) (s2 - s3) / 4
  let rAt := fun t c : ℚ => max (t - c) (max ((1 - t) / 2 - c) (v3 U0 Uh U1 t - c))
  let rmax := max (rAt 0 0) (max (rAt t1 c1) (max (rAt t2 c2) (rAt 1 0)))
  let dstar := qfloorN (rmax / Delta) + 1
  { U0 := U0, Uh := Uh, U1 := U1, t1 := t1, t2 := t2, s1 := s1, s2 := s2, s3 := s3, x1 := x1, x2 := x2,
    pairs := ps, okS := okS, okSec := okSec, dmin := dmin, d1 := d1, S := S, Delta := Delta, rmax := rmax,
    dstar := dstar, LD := (dstar : ℚ) * (rmax + 2) + 7 }

/-! ## The hull pair and xi'' from the anchors (Sec. 13.4) -/

structure Hull where
  dL : ℚ
  dR : ℚ
  xi : ℚ

/-- The line through Vbar's crossings with tau and (1-tau)/2, rounded up to 12 places; xi'' := (1/2 - dL - dR)/2,
rounded down to 15 places. -/
def hull (A0 Ah A1 : ℚ) : Hull :=
  let t1 := A0 / (1 + 2 * A0 - 2 * Ah)
  let t2 := (1 / 2 - 2 * Ah + A1) / (1 / 2 + 2 * A1 - 2 * Ah)
  let c1 := t1
  let c2 := (1 - t2) / 2
  let sl := (c2 - c1) / (t2 - t1)
  let dLp := up12 (c1 + sl * (1 - t1))
  let dRp := up12 (c1 - sl * t1)
  ⟨dLp, dRp, (qfloor ((1 / 2 - dLp - dRp) / 2 * 10 ^ 15) : ℚ) / 10 ^ 15⟩

/-! ## Window, hole fixing, Lemma E6 -/

/-- E3's flip count: the least J with J (2 e^2 N log2 e - 2) > 2.5 N, or none. -/
def jOf (e : ℚ) (N : ℕ) : Option ℕ :=
  let den := 2 * e * e * N * LOG2Elo - 2
  if den ≤ 0 then none else some (qfloorN (5 / 2 * N / den) + 1)

/-- `epsV_of`: eps_V = eps_win + eps_poly (+ J/N with E3 hole fixing), and J. -/
def epsVOf (N : ℕ) (e a : ℚ) (e3 : Bool) : Option (ℚ × ℕ) :=
  match jOf e N with
  | none => none
  | some J => if 1 / 20 < e then none else
      some (epsWin e a + (5 + 15 * lgUp (N + 1)) / N + (if e3 then (J : ℚ) / N else 0), J)

/-- Lemma E6's numeric hypotheses: 2^15 (N+1)^31 J <= 2^{0.49 N} and Vbar(0) + eps_V <= 1/2. -/
def e6ok (N J : ℕ) (U0 : ℚ) : Bool :=
  decide (15 + 31 * lgUp (N + 1) + lgUp J ≤ 49 / 100 * N) && decide (U0 ≤ 1 / 2)

/-! ## S2 Lemma 6.1 with a general gamma (Sec. 13.7) -/

/-- The seven distinct cost terms, with log2 3 <= 317/200. -/
def s2TermsQ (pi xi eps gam : ℚ) : List ℚ :=
  [pi, 2 * pi, 317 / 200 * pi, 1 / 4 + pi / 2, 1 / 4 + 3 / 4 * pi, 1 / 2 - gam * pi / 2,
   1 / 2 - (xi - gam) * pi + 2 * eps * pi]

structure S2G where
  pi : ℚ
  gam : ℚ
  E : ℚ

/-- gamma = 2(xi - 2 eps)/3, pi = 3/(12 + 2(xi - 2 eps)) rounded down to 13 places, E = the largest term. -/
def s2General (xi eps : ℚ) : Option S2G :=
  let gam := 2 / 3 * (xi - 2 * eps)
  if gam ≤ 0 then none else
  let pi := (qfloor (3 / (12 + 2 * (xi - 2 * eps)) * 10 ^ 13) : ℚ) / 10 ^ 13
  if 0 < pi ∧ pi ≤ 1 / 3 ∧ pi ≤ 2 / 5 then some ⟨pi, gam, lmax (s2TermsQ pi xi eps gam)⟩ else none

def s2OKq (pi xi eps gam E : ℚ) : Bool := decide (0 ≤ pi) && (s2TermsQ pi xi eps gam).all (fun t => decide (t ≤ E))

/-! ## n0 (Sec. 12) -/

/-- n0 := max(2 (c_b N0 + extra + 1)/(1 - g), 2 (log2 C + 1)/g), c_b = 4. -/
def n0Of (N0 : ℕ) (g log2C extra : ℚ) : ℚ := max (2 * (4 * N0 + extra + 1) / (1 - g)) (2 * (log2C + 1) / g)
def storageBits (N0 : ℕ) : ℚ := 4 + 2 * lgUp N0

/-! ## The ladder (Lemma E4'', Sec. 13.6) -/

/-- The tail N_j = q floor(N0 (3/4)^j / q), j = 1, 2, ..., while E6's hypotheses hold: (N_j, eps_V(N_j), J_j). -/
def tailList (N0 q : ℕ) (a A0 : ℚ) : ℕ → ℕ → List (ℕ × ℚ × ℕ)
  | 0, _ => []
  | f + 1, j =>
    let Nj := q * (N0 * 3 ^ j / (4 ^ j * q))
    if Nj < q then [] else
    let e : ℚ := 1 / 2 ^ ((bitlen Nj - 1) / 2)
    match epsVOf Nj e a false with
    | none => []
    | some (ev, J) =>
      if e6ok Nj J (A0 + ev) && decide (ev ≤ 1 / 100) then (Nj, ev, J) :: tailList N0 q a A0 f (j + 1) else []

/-- log2(1 + 2 * 2^Y) bound used per piece: 2^-60 below -62, 3 * 2^ceil(Y) up to -1, else Y^+ + 2. -/
def pieceExtra (Y : ℚ) : ℚ :=
  if Y ≤ -62 then 1 / 2 ^ 60 else if Y ≤ -1 then 3 / 2 ^ (-qceil Y).toNat else max Y 0 + 2

/-- The tail levels' factors phi_i (bottom-up, l = the length at and below the level) and their unions. -/
def tailBits (ps : List Pair) (epsV0 : ℚ) : List (ℕ × ℚ × ℕ) → ℕ → ℚ
  | [], _ => 0
  | (Nj, ev, J) :: rest, lrem =>
    let l := lrem + Nj
    let om := max 0 (ev - epsV0)
    let val := fun t : ℕ =>
      let A : ℚ := if t = 2 then (Nj : ℚ) * om else 0
      let ys := (ps.filter (fun p => p.t = t)).map
        (fun p => (Nj : ℚ) * (p.r + (if t = 2 then om else 0)) - (l : ℚ) * p.d)
      A + pieceExtra (lmax ys - A)
    max (val 1) (max (val 2) (val 3)) + lgUp J + tailBits ps epsV0 rest l

/-- The switch exponent K (least K >= 11 with E6 uniformly above 2^K), by search with fuel. -/
def findK (W A0 : ℚ) (N0 : ℕ) : ℕ → ℕ → ℕ
  | 0, K => K
  | f + 1, K =>
    if (W + 5 + 15 * ((K : ℚ) + 2)) / 2 ^ K + A0 ≤ 1 / 2 ∧ 15 + 31 * ((K : ℚ) + 2) + lgUp (3 * N0) ≤ 49 / 100 * 2 ^ K
    then K else findK W A0 N0 f (K + 1)

structure Lad where
  bits : ℚ
  T0 : ℚ
  ok : Bool
  ntail : ℕ
  Nmin : ℕ
  rebal : ℚ

/-- `ladder_bits`: the constant's bits (rebalancing + union + Delta level + main levels + chain + padding +
storage), T0 and the checks (Delta level, main levels, T0 >= 2 N0). -/
def ladder (N0 q : ℕ) (a A0 : ℚ) (st : St) (epsV0 : ℚ) : Lad :=
  let tail := tailList N0 q a A0 64 1
  let T0 : ℚ := ((tail.map (fun x => (x.1 : ℚ))).foldl (· + ·) 0)
  let bt := tailBits st.pairs epsV0 tail.reverse 0
  let Nmin := match tail.getLast? with | some x => x.1 | none => N0
  let W := 8 / (LN2lo * (99 / 100)) + 4 * a / ((1 / 4 - 1 / 20) * (1 / 4 - 1 / 20 - a) * LN2lo)
  let ombBig := W + 5 + 15 * lgUp (N0 + 1)
  let K := findK W A0 N0 200 11
  let Nsw : ℚ := 2 ^ K
  let omBits := max ombBig (Nsw * (1 - 3 * st.t1) / 2)
  let Yd := lmax (st.pairs.map (fun p => max ((N0 : ℚ) * (p.r - p.d)) 0 - T0 * p.d + max omBits (Nsw / 2)))
  let y0 := lmax (st.pairs.map (fun p => (N0 : ℚ) * p.r - T0 * p.d))
  let bits := bt + omBits + 3 + lgUp (3 * N0) + 4
  let chain := ((tail.length + 2 : ℕ) : ℚ) * lgUp (5 * N0)
  { bits := bits + chain + ((q : ℚ) + 1) / 2 + storageBits N0, T0 := T0,
    ok := decide (Yd ≤ -1) && decide (1600 ≤ Nsw) && decide (y0 ≤ -64) && decide (1 ≤ (N0 : ℚ) * st.dmin)
      && decide (2 * (N0 : ℚ) ≤ T0),
    ntail := tail.length, Nmin := Nmin, rebal := bits }

/-! ## The small-q rows (Sec. 13, table) -/

/-- A small-q design point: Ye-Li-type (a, b) with q = lcm(4, denominators) and certified anchors. -/
structure Tag where
  a : ℚ
  q : ℕ
  A0 : ℚ
  Ah : ℚ
  A1 : ℚ

structure Row where
  ok : Bool
  epsV : ℚ
  em : ℚ
  xi : ℚ
  pi : ℚ
  gam : ℚ
  E : ℚ
  log2C : ℚ
  n0 : ℚ
  T0 : ℚ
  rebal : ℚ
  Nmin : ℕ

def badRow : Row := ⟨false, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- `q_variant` at a fixed N0 and e: E3 or POS hole fixing, with or without the ladder. -/
def qRow (tg : Tag) (N0 : ℕ) (e : ℚ) (pos lad : Bool) : Row :=
  let h := hull tg.A0 tg.Ah tg.A1
  match epsVOf N0 e tg.a (!pos) with
  | none => badRow
  | some (epsV, J) =>
    let st := mkSt tg.A0 tg.Ah tg.A1 epsV h.dL h.dR
    let grp := (lgUp N0 + 9 / 4) / N0
    let uni := if pos then lgUp J / N0 else 0
    let em := max (epsV + grp + uni) (epsV + uni)
    match s2General h.xi em with
    | none => badRow
    | some s =>
      let g := 1 / 2 - s.E
      let base := st.okS && st.okSec && decide (1 ≤ (N0 : ℚ) * st.Delta) && decide (1 ≤ (N0 : ℚ) * st.dmin)
        && e6ok N0 J st.U0 && (pos || decide (8 * J ≤ N0)) && decide (0 < g) && decide (2 / 10 ^ 5 ≤ h.xi)
        && decide (h.dL + h.dR ≤ 1 / 2 - 2 * h.xi) && decide (N0 % tg.q = 0)
      if lad then
        let lb := ladder N0 tg.q tg.a tg.A0 st epsV
        ⟨base && lb.ok, epsV, em, h.xi, s.pi, s.gam, s.E, lb.bits,
          max (n0Of N0 g lb.bits 1) ((lb.T0 + tg.q) / s.pi), lb.T0, lb.rebal, lb.Nmin⟩
      else
        let log2C := st.S * N0 + 2 * st.d1 + 6 + ((N0 : ℚ) + 1) / 2 + storageBits N0
        ⟨base, epsV, em, h.xi, s.pi, s.gam, s.E, log2C, n0Of N0 g log2C 0, 0, 0, 0⟩

/-- The row's checks, its S2 terms below E, and the table's (E, n0) as upper bounds. -/
def Row.valid (r : Row) (Et n0t : ℚ) : Bool :=
  r.ok && s2OKq r.pi r.xi r.em r.gam r.E && decide (r.E ≤ Et) && decide (r.n0 ≤ n0t)

/-! ## The real side: log base 2, Lemma V's tangent bound, S2's terms -/

/-- log base 2. -/
noncomputable def lg (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- h(u, v) = u H(v/u) in bits, written as u lg u - v lg v - (u - v) lg (u - v). -/
noncomputable def hB (u v : ℝ) : ℝ := u * lg u - v * lg v - (u - v) * lg (u - v)
/-- Ye-Li's l and r (Sec. 3.5), and their partial derivatives in mu and theta. -/
noncomputable def fL (b μ θ : ℝ) : ℝ := hB (1 - b) μ + hB (2 * μ) θ - 4 * μ
noncomputable def fR (a μ θ : ℝ) : ℝ := hB a (μ - a) + hB μ (θ - μ)
noncomputable def gLm (b μ θ : ℝ) : ℝ := lg (1 - b - μ) - lg μ + 2 * (lg (2 * μ) - lg (2 * μ - θ)) - 4
noncomputable def gLt (μ θ : ℝ) : ℝ := lg (2 * μ - θ) - lg θ
noncomputable def gRm (a μ θ : ℝ) : ℝ :=
  lg (2 * a - μ) - lg (μ - a) + (lg μ - lg (2 * μ - θ)) - (lg (2 * μ - θ) - lg (θ - μ))
noncomputable def gRt (μ θ : ℝ) : ℝ := lg (2 * μ - θ) - lg (θ - μ)
/-- E1(1/4) = H(b) - (1/2) H(4a) - (1/2) H(2(1-b-2a)). -/
noncomputable def E1q (a b : ℝ) : ℝ := Hb b - Hb (4 * a) / 2 - Hb (2 * (1 - b - 2 * a)) / 2

/-- Lemma V's bound at tau, x0 = (mu0, theta0) and the vertex (vm, vt): tau E1(1/4) + (1 - tau)(b - 1/2 + 2a) +
f_tau(x0) + grad f_tau(x0) . (v - x0). Lemma V (paper) says V(tau) is at most the largest of these over the four
vertices of K. -/
noncomputable def tanBound (τ a b μ0 θ0 vm vt : ℝ) : ℝ :=
  τ * E1q a b + (1 - τ) * (b - 1 / 2 + 2 * a) + (τ * fL b μ0 θ0 + (1 - τ) * fR a μ0 θ0)
    + (τ * gLm b μ0 θ0 + (1 - τ) * gRm a μ0 θ0) * (vm - μ0) + (τ * gLt μ0 θ0 + (1 - τ) * gRt μ0 θ0) * (vt - θ0)

/-- The kernel-checked condition behind `lg_mem`: the log enclosure `[lo c, hi c']` of `logOK`, where c, c' are
the bounds on ln 2 that make `lo <= lg x <= hi` follow. -/
def lgOK (x : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ) : Bool :=
  logOK x k n (lo * (if 0 ≤ lo then L2hi else L2lo)) (hi * (if 0 ≤ hi then L2lo else L2hi))

theorem lg_mem (e : ℝ) (x lo hi : ℚ) (k : ℤ) (n : ℕ) (he : e = x) (h : lgOK x k n lo hi = true) :
    (lo : ℝ) ≤ lg e ∧ lg e ≤ hi := by
  obtain ⟨h1, h2⟩ := log_mem e x _ _ k n _ _ he rfl rfl h
  obtain ⟨l2a, l2b⟩ := log_two_mem
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  unfold lg
  constructor
  · rw [le_div_iff₀ hL]
    by_cases hlo : 0 ≤ lo
    · simp only [hlo, ↓reduceIte] at h1; push_cast at h1
      have : (lo : ℝ) * Real.log 2 ≤ (lo : ℝ) * (L2hi : ℝ) :=
        mul_le_mul_of_nonneg_left l2b (by exact_mod_cast hlo)
      linarith
    · simp only [hlo, ↓reduceIte] at h1; push_cast at h1
      have hlo' : (lo : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hlo)
      have : (lo : ℝ) * Real.log 2 ≤ (lo : ℝ) * (L2lo : ℝ) := mul_le_mul_of_nonpos_left l2a hlo'.le
      linarith
  · rw [div_le_iff₀ hL]
    by_cases hhi : 0 ≤ hi
    · simp only [hhi, ↓reduceIte] at h2; push_cast at h2
      have : (hi : ℝ) * (L2lo : ℝ) ≤ (hi : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left l2a (by exact_mod_cast hhi)
      linarith
    · simp only [hhi, ↓reduceIte] at h2; push_cast at h2
      have hhi' : (hi : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hhi)
      have : (hi : ℝ) * (L2hi : ℝ) ≤ (hi : ℝ) * Real.log 2 := mul_le_mul_of_nonpos_left l2b hhi'.le
      linarith

/-- S2 Lemma 6.1's seven distinct cost terms with a general gamma, with the real log2 3. -/
noncomputable def s2TermsG (pi xi eps gam : ℝ) : List ℝ :=
  [pi, 2 * pi, logb 2 3 * pi, 1 / 4 + pi / 2, 1 / 4 + 3 / 4 * pi, 1 / 2 - gam * pi / 2,
   1 / 2 - (xi - gam) * pi + 2 * eps * pi]

theorem s2G_le (pi xi eps gam E : ℚ) (h : s2OKq pi xi eps gam E = true) :
    ∀ t ∈ s2TermsG pi xi eps gam, t ≤ (E : ℝ) := by
  simp only [s2OKq, s2TermsQ, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨hp, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have c1 : ((pi : ℚ) : ℝ) ≤ E := by exact_mod_cast h1
  have c2 : ((2 * pi : ℚ) : ℝ) ≤ E := by exact_mod_cast h2
  have c3 : ((317 / 200 * pi : ℚ) : ℝ) ≤ E := by exact_mod_cast h3
  have c4 : ((1 / 4 + pi / 2 : ℚ) : ℝ) ≤ E := by exact_mod_cast h4
  have c5 : ((1 / 4 + 3 / 4 * pi : ℚ) : ℝ) ≤ E := by exact_mod_cast h5
  have c6 : ((1 / 2 - gam * pi / 2 : ℚ) : ℝ) ≤ E := by exact_mod_cast h6
  have c7 : ((1 / 2 - (xi - gam) * pi + 2 * eps * pi : ℚ) : ℝ) ≤ E := by exact_mod_cast h7
  have hp' : (0 : ℝ) ≤ pi := by exact_mod_cast hp
  have hl : logb 2 3 * (pi : ℝ) ≤ 317 / 200 * pi := mul_le_mul_of_nonneg_right log2_3_lt.le hp'
  push_cast at c1 c2 c3 c4 c5 c6 c7
  intro t ht
  simp only [s2TermsG, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> linarith

theorem Row.s2_real (r : Row) (Et n0t : ℚ) (h : r.valid Et n0t = true) :
    r.ok = true ∧ r.E ≤ Et ∧ r.n0 ≤ n0t ∧ ∀ t ∈ s2TermsG r.pi r.xi r.em r.gam, t ≤ (r.E : ℝ) := by
  simp only [Row.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h3, h4, s2G_le _ _ _ _ _ h2⟩

end N0
end SS
