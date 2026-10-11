import SubsetsumLean.Stage4Defs

/-!
# Stage 5b: Lemma 5b.1, the piecewise certificate for a family of three circuits

`proofs/stage5b.md` Lemma 5b.1 with J = 3. The pieces are `tau h(s)` on `[0, v0]`, the members `V_1, V_2, V_3` on
`[v0, v1]`, `[v1, v2]`, `[v2, v3]`, and `(1 - tau)(1 - s)` on `[v3, 1]`. Each piece minus the line is convex in `tau`
(for one colour `G4` is affine in `tau`; the trivial pieces are affine), so it is below the line on its interval when
it is at both ends. The two outer ends need only `r ≥ 0` (at `tau = 0`) and `l ≥ 0` (at `tau = 1`).
Unlike `line_single` and `line_family` of Stage 4, no slope condition is used: the line is given by its values
`r = line(0)` and `l = line(1)`, and the statement is for `tau` in `[0, 1]` only, which is all Lemma 3.4 needs.
-/

namespace SS4

/-- An affine function of `tau` that is `≥ 0` at both ends of `[a, b]` is `≥ 0` in between. -/
lemma aff_nonneg {A C a b τ : ℝ} (ha : 0 ≤ A * a + C) (hb : 0 ≤ A * b + C) (h1 : a ≤ τ) (h2 : τ ≤ b) :
    0 ≤ A * τ + C := by
  have := SS.lin_le (A := -A) (C := -C) (c := 0) (lo := a) (hi := b) (x := τ) (by linarith) (by linarith) h1 h2
  linarith

/-- Lemma 5b.1 for a family of three circuits (J = 3). -/
theorem line_fam3 (k ρ1 ρ2 ρ3 hs s v0 v1 v2 v3 l r : ℝ) (h01 : v0 ≤ v1) (h12 : v1 ≤ v2) (h23 : v2 ≤ v3)
    (hr : 0 ≤ r) (hl : 0 ≤ l)
    (h0 : v0 * hs ≤ r + (l - r) * v0) (h4 : (1 - v3) * (1 - s) ≤ r + (l - r) * v3)
    (c1a : ∀ m d, Poly4 k ρ1 m d → G4 k ρ1 v0 m d ≤ r + (l - r) * v0)
    (c1b : ∀ m d, Poly4 k ρ1 m d → G4 k ρ1 v1 m d ≤ r + (l - r) * v1)
    (c2a : ∀ m d, Poly4 k ρ2 m d → G4 k ρ2 v1 m d ≤ r + (l - r) * v1)
    (c2b : ∀ m d, Poly4 k ρ2 m d → G4 k ρ2 v2 m d ≤ r + (l - r) * v2)
    (c3a : ∀ m d, Poly4 k ρ3 m d → G4 k ρ3 v2 m d ≤ r + (l - r) * v2)
    (c3b : ∀ m d, Poly4 k ρ3 m d → G4 k ρ3 v3 m d ≤ r + (l - r) * v3) :
    ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      (∀ m d, Poly4 k ρ1 m d → G4 k ρ1 τ m d ≤ r + (l - r) * τ) ∨
      (∀ m d, Poly4 k ρ2 m d → G4 k ρ2 τ m d ≤ r + (l - r) * τ) ∨
      (∀ m d, Poly4 k ρ3 m d → G4 k ρ3 τ m d ≤ r + (l - r) * τ) ∨
      τ * hs ≤ r + (l - r) * τ ∨ (1 - τ) * (1 - s) ≤ r + (l - r) * τ := by
  intro τ ht0 ht1
  rcases le_or_gt τ v0 with h | h
  · right; right; right; left
    have := aff_nonneg (A := l - r - hs) (C := r) (a := 0) (b := v0) (by linarith) (by linarith) ht0 h
    linarith
  rcases le_or_gt v3 τ with h' | h'
  · right; right; right; right
    have := aff_nonneg (A := l - r + (1 - s)) (C := r - (1 - s)) (a := v3) (b := 1) (by linarith) (by linarith) h' ht1
    linarith
  rcases le_total τ v1 with g1 | g1
  · left
    intro m d hp
    exact G4_between (A := r) (σ := l - r) h.le g1 (by linarith [c1a m d hp]) (by linarith [c1b m d hp])
  rcases le_total τ v2 with g2 | g2
  · right; left
    intro m d hp
    exact G4_between (A := r) (σ := l - r) g1 g2 (by linarith [c2a m d hp]) (by linarith [c2b m d hp])
  · right; right; left
    intro m d hp
    exact G4_between (A := r) (σ := l - r) g2 h'.le (by linarith [c3a m d hp]) (by linarith [c3b m d hp])

end SS4
