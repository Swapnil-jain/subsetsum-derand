"""Generate SubsetsumLean/Stage2.lean, the kernel check of certificates/cert_eps.py.

Pure standard library. The constants (Ye-Li's table truncations, the rational pair, log2(3) < 317/200) are read
from cert_eps.py itself, and every claim and control is first re-checked here with cert_eps.check, so the Lean file
states exactly what the script certifies. Ye-Li's true constants are Lean variables, constrained only by the
hypotheses each theorem states.
Run:  python3 gen_stage2.py
"""
from fractions import Fraction as F
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "certificates"))
sys.path.insert(0, HERE)
import cert_eps as CE  # noqa: E402


def lit(x):
    x = F(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℝ)"
    for k in range(1, 61):
        if (x * 10 ** k).denominator == 1:
            return f"({x.numerator * 10 ** k // x.denominator}/{10 ** k} : ℝ)"
    return f"({x.numerator}/{x.denominator} : ℝ)"


def main():
    assert CE.LOG2_3_UP == F(317, 200)
    pi, eps, bound = F(2499, 10 ** 4), F(1, 10 ** 9), F("0.49999834")
    xiA, xiB = F("0.000020035"), F("0.00002")
    okA, EA = CE.check(pi, xiA, eps, bound)
    okB, EB = CE.check(pi, xiB, eps, bound)
    assert okA and okB
    sharp = F("0.499998332")          # gain > 1.668e-6
    nxt = F("0.4999983315")           # one unit lower in the 10th place: must fail
    assert EA < sharp and not EA < nxt
    E20 = CE.E20
    DLT, DRT, XIT, DLP, DRP = (lit(v) for v in (CE.DL_T, CE.DR_T, CE.XI_T, CE.DL_P, CE.DR_P))
    e20 = lit(E20)
    P, EPS, B = lit(pi), lit(eps), lit(bound)
    # controls, as cert_eps.py's
    ctl = {
        "C1": (pi, xiA, eps, F("0.49999833") + F(1, 10 ** 30), "the claim E <= 0.49999833 at [A]", "many"),
        "C2": (F(1, 4), xiA, eps, bound, "prefix pi = 1/4 (the covering costs 2^{n/2})", "cover"),
        "C3": (F(1, 3), xiA, eps, bound, "Ye-Li's prefix pi = 1/3 (the covering costs 2^{2n/3})", "cover"),
        "C4": (pi, xiA, F(1, 10 ** 6), bound, "slack eps_PM = 1e-6", "many"),
        "C5": (pi, F(0), eps, bound, "xi' = 0 (Prop. 4.2 false)", "few"),
    }
    for k, (p, x, e, b, _, _) in ctl.items():
        assert not CE.check(p, x, e, b)[0], k
    dl_down, dr_down = F("0.007275870559"), F("0.492684058988")
    assert not CE.admissible(dl_down, dr_down, xiA)
    assert dl_down < CE.DL_T + E20 / 2

    def pos(name, doc, xi, hx, b):
        X = lit(xi)
        return f"""/-- {doc} -/
theorem {name} (xiT dLT dRT : ℝ) {hx}
    (hl : dLT < {DLT} + {e20}) (hr : dRT < {DRT} + {e20}) :
    CertEps {P} {X} {EPS} {lit(b)} {DLP} {DRP} xiT dLT dRT := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num, ?_⟩
  · linarith [(by norm_num : {X} ≤ {XIT}), hx]
  · linarith [(by norm_num : {DLT} + {e20} ≤ {DLP})]
  · linarith [(by norm_num : {DRT} + {e20} ≤ {DRP})]
  · exact s2Terms_lt (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
"""

    out = [
        pos("stage2_A", "[A] cert_eps.py: pi = 0.2499, xi' = 2.0035e-5 (at most the table's xi), eps = 1e-9: every "
            "term < 0.49999834, so the time is O(2^{0.49999834 n}).", xiA, f"(hx : {XIT} ≤ xiT)", bound),
        pos("stage2_A_sharp", "[A] sharper: every term < 0.499998332, i.e. the gain 1/2 - E exceeds 1.668e-6.",
            xiA, f"(hx : {XIT} ≤ xiT)", sharp),
        pos("stage2_B", "[B] the same with xi' = 2e-5, below the stated xi > 0.00002 of Prop. 4.2, with the same table "
            "bounds on dL, dR as [A] (so [B] is no weaker in assumptions; it checks the xi bookkeeping).", xiB, "(hx : (2/100000 : ℝ) < xiT)", bound)
        .replace(f"linarith [(by norm_num : {lit(xiB)} ≤ {XIT}), hx]", "linarith [hx]"),
    ]
    which = {"many": "s2_many_mem", "cover": "s2_cover_mem", "few": "s2_few_mem"}
    out.append(f"""/-- Control: E < 0.4999983315 (one unit lower in the 10th place) at [A] is false. -/
theorem stage2_A_fails_next : ¬ ∀ t ∈ s2Terms {P} {lit(xiA)} {EPS}, t < {lit(nxt)} := by
  intro h; have := h _ (s2_many_mem _ _ _); norm_num at this
""")
    for k, (p, x, e, b, doc, w) in ctl.items():
        out.append(f"""/-- [{k}] must fail: {doc}. -/
theorem stage2_{k} : ¬ ∀ t ∈ s2Terms {lit(p)} {lit(x)} {lit(e)}, t < {lit(b)} := by
  intro h; have := h _ ({which[w]} _ _ _); norm_num at this
""")
    def bad_pair(name, doc, xi):
        return f"""/-- {doc} Some values of Ye-Li's pair allowed by the table (truncation <= true < truncation + 1e-20)
lie above the rounded-down pair, so `CertEps` fails there for every xi. -/
theorem {name} : ∃ dLT dRT : ℝ, {DLT} ≤ dLT ∧ dLT < {DLT} + {e20} ∧ {DRT} ≤ dRT ∧ dRT < {DRT} + {e20} ∧
    ∀ xiT : ℝ, ¬ CertEps {P} {lit(xi)} {EPS} {B} {lit(dl_down)} {lit(dr_down)} xiT dLT dRT :=
  ⟨{DLT} + {e20} / 2, {DRT} + {e20} / 2, by norm_num, by norm_num, by norm_num, by norm_num,
   fun _ h => by have := h.dl_ge; norm_num at this⟩
"""
    out.append(bad_pair("stage2_C6", "[C6] must fail: the pair rounded down below Ye-Li's table, at [A].", xiA))
    xi7 = F("0.000021")
    assert not CE.check(pi, xi7, eps, bound, xi_cap=F(1, 10 ** 4))[0] and DLP and CE.DL_P + CE.DR_P > F(1, 2) - 2 * xi7
    out.append(f"""/-- [C7] must fail: xi' = 2.1e-5, even with no cap from Ye-Li's xi, because the rational pair then breaks
`dl + dr <= 1/2 - 2 xi'`. (xi' = 2.0035e-5 is admissible for that pair, so [B]'s cap is bookkeeping.) -/
theorem stage2_C7 : ∀ xiT dLT dRT : ℝ, ¬ CertEps {P} {lit(xi7)} {EPS} {B} {DLP} {DRP} xiT dLT dRT :=
  fun _ _ _ h => by have := h.pair; norm_num at this
""")
    out.append(bad_pair("stage2_C8", "[C8] must fail: in [B], the pair rounded down below the upper bounds on dL, dR.",
                        F(2, 10 ** 5)))
    # [K] Cor. 3.2's block length
    import gen_stage1 as G
    km = 148444531984
    # N' = 22035779076245688040224: >= 2.2035e22, and NOT >= 2.2036e22 (PROOF.md rounds it up)
    assert km % 2 == 0 and 22035 * 10 ** 18 <= km * km + 2 * km < 22036 * 10 ** 18
    k1 = 8 * (max(CE.DL_P, CE.DR_P) + eps / 4) / eps
    assert k1 <= km
    logs = []
    for i, k in enumerate((km, km - 2)):
        x = F(k + 1); K = G.best_k(x); a, b = G.log_series(x, K, G.NTERMS)
        lo, hi = G.down(a), G.up(b)
        assert G.logOK(x, K, G.NTERMS, lo, hi)
        logs.append((x, K, lo, hi))
    q = eps / 4
    assert logs[0][3] / G.L2lo <= q * km and logs[1][2] / G.L2hi > q * (km - 2)
    (x0, K0, lo0, hi0), (x1, K1, lo1, hi1) = logs
    Q = lambda v: G.q(v)
    out.append(f"""/-- [K] Cor. 3.2's block length for the rational pair: kappa_0 = {km} meets both conditions, kappa_0 - 2
fails the second (so kappa_0 is the least even one, the second condition being monotone for kappa >= 1, a paper
fact), and N' = kappa_0^2 + 2 kappa_0 >= 2.2035e22 (exactly 22035779076245688040224, so the
rounded figure 2.2036e22 is not a lower bound; `stage2_K_fails_N`). -/
theorem stage2_K : kcond1 {DLP} {DRP} {EPS} ({km} : ℝ) ∧ kcond2 {EPS} ({km} : ℝ) ∧
    ¬ kcond2 {EPS} ({km - 2} : ℝ) ∧ {km} % 2 = 0 ∧ (22035 * 10 ^ 18 : ℝ) ≤ ({km} : ℝ) ^ 2 + 2 * {km} := by
  obtain ⟨a0l, a0h⟩ := log_mem (({km} : ℝ) + 1) {Q(x0)} {Q(lo0)} {Q(hi0)} ({K0}) {G.NTERMS} _ _ (by norm_num) rfl rfl
    (by decide +kernel)
  obtain ⟨a1l, a1h⟩ := log_mem (({km - 2} : ℝ) + 1) {Q(x1)} {Q(lo1)} {Q(hi1)} ({K1}) {G.NTERMS} _ _ (by norm_num) rfl rfl
    (by decide +kernel)
  obtain ⟨l2a, l2b⟩ := log_two_mem
  have hL : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  norm_num [L2lo, L2hi] at a0l a0h a1l a1h l2a l2b
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩
  · unfold kcond1; rw [max_eq_right (by norm_num)]; norm_num
  · unfold kcond2; rw [Real.logb, div_div, div_le_iff₀ (by positivity)]; nlinarith
  · unfold kcond2; rw [Real.logb, div_div, not_le, lt_div_iff₀ (by positivity)]; nlinarith
""")
    out.append(f"""/-- Control: N' >= 2.2036e22 (the rounded figure) is false. -/
theorem stage2_K_fails_N : ¬ ((22036 * 10 ^ 18 : ℝ) ≤ ({km} : ℝ) ^ 2 + 2 * {km}) := by norm_num
""")
    hdr = """import SubsetsumLean.Basic
import SubsetsumLean.Stage2Defs

/-!
# Kernel check of `certificates/stage2/cert_eps.py` (generated by `gen_stage2.py`; do not edit)

Positive theorems: `CertEps` at the script's points, for every value of Ye-Li's constants allowed by the stated
hypotheses. Controls (`stage2_C1` to `stage2_C8`, `stage2_A_fails_next`): the claims the script must reject,
proved false.
-/

open Real

namespace SS

"""
    path = os.path.join(HERE, "SubsetsumLean", "Stage2.lean")
    with open(path, "w") as f:
        f.write(hdr + "\n".join(out) + "\nend SS\n")
    print("wrote", path, "; E(A) =", float(EA), "E(B) =", float(EB))


if __name__ == "__main__":
    main()
