"""Generate the Stage 5b kernel check except the cell trees (gen_stage5b_cells.py): the family circuits, row R4b-min,
the must-fail controls, and the analysis modules Stage5bBase, Stage5bFam_*, Stage5bCtl_*, Stage5bE, Stage5b and
Stage5bAxioms.

Pure standard library. Every number comes from the Stage 5b certificate (CERT_DIR/cert_stage5b.py: FAM_DATA,
FAMILY_DENSITIES, the row and its controls) or from Stage 5's Lean data, and every claim is first re-checked here by
the exact mirrors of gen_stage5.py (`Row.pieceOK`, `Row.refOne` of Stage5ECheck.lean), so each `decide +kernel` is
known to succeed before Lean runs. Row R4b-min reuses Stage 5's checker unchanged: it reads only (s, H(s) bounds, l, r)
of each circuit, so a family enters the row exactly as a single circuit does (Lemma 5b.1 supplies its (l, r)).
Run:  python3 gen_stage5b.py   (after gen_stage5b_cells.py; writes stage5b_light_modules.txt)
"""
from fractions import Fraction as F
import contextlib
import io
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import gen_stage4_cells as G  # noqa: E402
import gen_stage4 as G4  # noqa: E402
import gen_stage5 as G5  # noqa: E402
import gen_stage5b_cells as GB  # noqa: E402

C5 = G5.C5
q, r, Qc = G4.q, G4.r, G4.Qc
LEAN = os.path.join(HERE, "SubsetsumLean")
MU = F(199, 1000)
ALPHAS = [F(m, 10) for m in range(10)] + [F(m, 100) for m in (93, 95, 96, 97, 98, 99)]
CLAIM = F(4986298176, 10 ** 10)       # Theorem 5b-F: E_det <= 0.4986298176 (row R4b-min)
K1_DELTA = F(2, 10 ** 6)              # K1 refutes claim - K1_DELTA (as Stage 5: the script's 1e-9 tests its own pieces)
F1_DROP = F(1, 10 ** 5)               # [F1]: the family's (l, r) lowered by this is refuted
F1_SLACK = F(4, 10 ** 6)              # witness targets at the [F1] breakpoints: line - F1_SLACK
CH_PIECES = G5.CH_PIECES
CH_DESIGNS = G5.CH_DESIGNS
HEAD = """set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Real

namespace SS5b

open SS SS4 SS5

"""
# Lean names of the H(s) enclosures already proved by Stage 4 / Stage 5, by density.
HS_THM = {F(2, 25): "hs_m80", F(19, 200): "hs_m95", F(13, 125): "hs_m104", F(111, 1000): "hs_m111", F(59, 500): "hs_m118", F(1, 8): "hs_s8",
          F(29, 200): "hs_m145", F(11, 100): "hs_s11"}


class FamC:
    """A family circuit as row data: density s, H(s) bounds as Stage 5 rounds them, and the family's line values."""

    def __init__(self, tag, s, l, r, rhos=None, bps=None):
        self.tag, self.s, self.l, self.r, self.rhos, self.bps = tag, F(s), F(l), F(r), rhos, bps
        lo, hi = G.hb_bounds(self.s)
        self.hlo30, self.hhi30 = lo, hi
        self.hsLo, self.hsHi = G5.dnq(lo, G5.HD), G5.upq(hi, G5.HD)
        self.xi = G5.dnq((lo - self.s) / 2 - (self.l + self.r) / 2, 10 ** 10)

    def tup(self):
        return (self.s, self.hsLo, self.hsHi, self.l, self.r)

    def lean(self):
        return f"⟨{Qc(self.s)}, {Qc(self.hsLo)}, {Qc(self.hsHi)}, {Qc(self.l)}, {Qc(self.r)}⟩"


def write(name, text):
    with open(os.path.join(LEAN, name + ".lean"), "w") as f:
        f.write(text)


def circuits():
    single, menu, fam, sfam = G5.circuits()
    singles = {c.s: c for c in menu + [single]}
    sname = {c.s: "C_" + c.tag for c in menu + [single]}          # Stage 5's Lean names (SS5.C_*)
    fams = {}
    for s, D in GB.fam_data().items():
        fams[s] = FamC(GB.fam_tag(s), s, D["l"], D["r"], D["rhos"], D["bps"])
    order = list(GB._literal("FAM_DATA"))                          # the certificate's circuit order
    assert set(order) == set(singles)
    rmin = [fams.get(s, singles[s]) for s in order]
    return singles, sname, fams, order, rmin


def main():
    G5.L3Q = G.up(G.up(G.log_bounds(F(3))[2]) / G.L2lo)
    assert G5.L3Q == F(39624062518029, 25 * 10 ** 12)
    singles, sname, fams, order, rmin = circuits()
    cname = {id(c): sname[c.s] for c in singles.values()}
    cname.update({id(c): "C_" + c.tag for c in fams.values()})
    with contextlib.redirect_stdout(io.StringIO()):
        assert C5.lam_max(C5.NB) <= float(G5.LAMQ)
    R = G5.Row("R4bmin", MU, 1, CLAIM, False, ALPHAS, rmin)
    assert G5.row_ok(R)
    k9 = [FamC("k9_" + (c.tag if isinstance(c, FamC) else c.tag), c.s, c.l + F(1, 100), c.r + F(1, 100)) for c in rmin]
    for c in k9:
        cname[id(c)] = "C_" + c.tag
    ctl = {"K1b": G5.Row("K1b", MU, 1, CLAIM - K1_DELTA, False, ALPHAS, rmin),
           "K2b": G5.Row("K2b", MU * F(101, 100), 1, CLAIM, False, ALPHAS, rmin),
           "K7pb": G5.Row("K7pb", MU, 1, CLAIM, False, ALPHAS, [singles[s] for s in order]),
           "K9b": G5.Row("K9b", MU, 1, CLAIM, False, ALPHAS, k9)}
    for s, c in fams.items():
        ctl[f"KFb_{c.tag}"] = G5.Row(f"KFb_{c.tag}", MU, 1, CLAIM, False, ALPHAS,
                                    [singles[x.s] if x is c else x for x in rmin])

    # ---------------- data module
    data = ["import SubsetsumLean.Stage5Data", "",
            "/-! Stage 5b data: the family circuits, row R4b-min of `cert_stage5b.py` and its controls (generated by "
            "`gen_stage5b.py`; do not edit). -/", "", "namespace SS5b", "", "open SS4 SS5", ""]
    for c in list(fams.values()) + k9:
        doc = (f"family rho = {', '.join(str(x) for x in c.rhos)}" if c.rhos else
               "control K9: the row circuit at this density with l and r raised by 1/100")
        data.append(f"/-- s = {c.s} ({doc}): hsLo <= H(s) <= hsHi, and (l, r). -/")
        data.append(f"def C_{c.tag} : Circ := {c.lean()}")
    data.append("")

    def lean_row(Rw):
        return G5.lean_row(Rw, cname)
    data.append(f"def R_R4bmin : Row := {lean_row(R)}")
    for name, Rc in ctl.items():
        data.append(f"def R_{name} : Row := {lean_row(Rc)}")
    data += ["theorem rowok_R4bmin : R_R4bmin.ok = true := by decide +kernel", "", "end SS5b", ""]
    write("Stage5bData", "\n".join(data))
    mods = ["Stage5bData"]

    # ---------------- the row
    ps = G5.pieces(R)
    assert G5.chk_mirror(R, F(0), F(1, 2), ps)
    print(f"R4bmin: {len(ps)} pieces ({sum(1 for p in ps if R.alphas[p[1]] != 0)} cored)", flush=True)
    parts, ka = [], F(0)
    for i in range(0, len(ps), CH_PIECES):
        sub = ps[i:i + CH_PIECES]
        parts.append((ka, sub[-1][0], sub))
        ka = sub[-1][0]
    for i, (a, b, sub) in enumerate(parts):
        mod = f"Stage5bRows_R4bmin_{i}"
        mods.append(mod)
        write(mod, f"""import SubsetsumLean.Stage5bData

/-! Stage 5b row R4b-min, pieces {i * CH_PIECES} to {i * CH_PIECES + len(sub) - 1} (generated by `gen_stage5b.py`; do not edit). -/

namespace SS5b

open SS4 SS5

def PS_R4bmin_{i} : List SS5.EP := [{", ".join(G5.lean_piece(p) for p in sub)}]

theorem ne_R4bmin_{i} : PS_R4bmin_{i} ≠ [] := by simp [PS_R4bmin_{i}]

theorem chk_R4bmin_{i} : R_R4bmin.chk {Qc(b)} {Qc(a)} PS_R4bmin_{i} = true := by decide +kernel

end SS5b
""")

    # ---------------- refutations
    refs = {}
    for name, Rc in ctl.items():
        kap, v = G5.best_kappa(Rc)
        print(f"{name}: kappa* = {kap} ({float(kap):.9f}), float min lower bound {v:.10f} vs target "
              f"{float(Rc.claim):.10f}", flush=True)
        assert v > float(Rc.claim), name
        subs = []
        for ia, a in enumerate(Rc.alphas):
            Rs = G5.Row(Rc.name, Rc.mu, Rc.j, Rc.claim, Rc.sym, [a], Rc.circs, Rc.osv, Rc.lam)
            hk, hts = G5.refutation(Rs, kap)
            subs.append((ia, a, hk, hts))
        refs[name] = (kap, subs)
        groups, cur, n = [], [], 0
        for sb in subs:
            if cur and n + len(sb[3]) > CH_DESIGNS:
                groups.append(cur)
                cur, n = [], 0
            cur.append(sb)
            n += len(sb[3])
        if cur:
            groups.append(cur)
        refs[name] = (kap, subs, len(groups))
        for gi, grp in enumerate(groups):
            mod = f"Stage5bRefs_{name}_{gi}"
            mods.append(mod)
            body = []
            for ia, a, hk, hts in grp:
                hl = ", ".join("none" if e is None else f"some {G4.lean_hbU(e)}" for e in hts)
                body.append(f"""/-- {name}, alpha = {a}: at kappa = {kap} every design fails the target. -/
theorem ref_{name}_{ia} : ({{ R_{name} with alphas := [{Qc(a)}] }} : Row).refute {Qc(kap)} {G4.lean_hbL(hk)} [{hl}] = true := by
  decide +kernel
""")
            write(mod, f"""import SubsetsumLean.Stage5bData

/-! Stage 5b must-fail control {name}, part {gi} (generated by `gen_stage5b.py`; do not edit). -/

namespace SS5b

open SS4 SS5

""" + "\n".join(body) + "\nend SS5b\n")
    with open(os.path.join(HERE, "stage5b_light_modules.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    print("light modules:", len(mods))
    return singles, sname, fams, order, rmin, R, ctl, parts, refs, cname, k9


# ------------------------------------------------------------------ heavy modules
def disj(k, rhos, s, L, Rv, tau):
    """Lean text of the family hypothesis at tau for the line R + (L - R) tau."""
    ln = f"{Rv} + ({L} - {Rv}) * {tau}"
    mem = [f"(∀ m d : ℝ, Poly4 {r(k)} {r(x)} m d → G4 {r(k)} {r(x)} {tau} m d ≤ {ln})" for x in rhos]
    return " ∨\n      ".join(mem + [f"{tau} * Hb {r(s)} ≤ {ln}", f"(1 - {tau}) * (1 - {r(s)}) ≤ {ln}"])


def colour_glo(c, rho, tau, need, name):
    """A witness colour (text, its rigorous lower bound) of member rho at tau, above `need`."""
    txt = G5.witness(name, c.s, rho, tau, need)
    # the bound is in the theorem statement `theorem w_<name> : <glo> ≤ G4 ...`
    head = txt.split(f"theorem w_{name} : ", 1)[1]
    lit = head.split(" ≤ G4", 1)[0]
    num, den = lit.strip("()").split(" : ")[0].split("/")
    return txt, F(int(num), int(den))


def write_heavy(singles, sname, fams, order, rmin, R, ctl, parts, refs, cname, k9):
    # Lean names by object identity, rebuilt here (ids do not survive the development cache)
    cname = {id(c): sname[c.s] for c in singles.values()}
    cname.update({id(c): "C_" + c.tag for c in list(fams.values()) + k9})
    # ---------------- Stage5bBase: the data facts hsLo <= H(s) <= hsHi of the new circuits
    out = ["import SubsetsumLean.Stage5Base", "import SubsetsumLean.Stage5bData", "",
           "/-!\n# Stage 5b kernel check, shared part (generated by `gen_stage5b.py`; do not edit)\n\n"
           "`hb_C_*`: `hsLo ≤ H(s) ≤ hsHi` for the six family circuits and the eight K9 circuits, from the H(s) "
           "enclosures of Stage 4 and Stage 5.\n-/", "", HEAD]
    for c in list(fams.values()) + k9:
        n = "C_" + c.tag
        out.append(f"""/-- The data of `{n}`: `hsLo ≤ H(s) ≤ hsHi`. -/
theorem hb_{n} : (({n}.hsLo : ℚ) : ℝ) ≤ Hb (({n}.s : ℚ) : ℝ) ∧ Hb (({n}.s : ℚ) : ℝ) ≤ (({n}.hsHi : ℚ) : ℝ) := by
  {G5.cfield(n, "s", c.s)}
  {G5.cfield(n, "hsLo", c.hsLo)}
  {G5.cfield(n, "hsHi", c.hsHi)}
  rw [e_s, e_hsLo, e_hsHi]
  have h := {HS_THM[c.s]}
  push_cast
  constructor <;> linarith [h.1, h.2]
""")
    out.append("end SS5b\n")
    write("Stage5bBase", "\n".join(out))

    # ---------------- Stage5bFam_*: Lemma 5b.1 for each family, from its six cell certificates
    for s, c in fams.items():
        k = c.s / 2
        names = [p for p in GB.problems() if p[0].startswith(c.tag + "_")]
        out = ["import SubsetsumLean.Stage5bBase", "import SubsetsumLean.Stage5bDefs"]
        out += [f"import SubsetsumLean.Stage5bCells_{p[0]}" for p in names]
        out += ["", f"/-!\n# Stage 5b: the family at s = {c.s} (generated by `gen_stage5b.py`; do not edit)\n\n"
                "`V_*`: the six member statements of Lemma 5b.1 over the whole colour polygon (cell trees, Stage 4's "
                "method);\n`fam_*`: Lemma 3.4's hypothesis for the family on [0, 1] (`line_fam3`); `xi_*`: xi and the "
                "row data.\n-/", "", HEAD]
        for nm, s_, rho, tau, T, doc in names:
            out.append(f"""/-- {doc} at s = {c.s}, rho = {rho}: on the whole colour polygon. -/
theorem V_{nm} : ∀ m d : ℝ, Poly4 {r(k)} {r(rho)} m d → G4 {r(k)} {r(rho)} {r(tau)} m d ≤ {r(T)} := by
  have h := G4_le_of_cells P_{nm} prob_{nm} T_{nm} _ _ _ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) cells_{nm}
  have e1 : P_{nm}.k = {q(k)} := by decide +kernel
  have e2 : P_{nm}.ρ = {q(rho)} := by decide +kernel
  have e3 : P_{nm}.τ = {q(tau)} := by decide +kernel
  have e4 : P_{nm}.T = {q(T)} := by decide +kernel
  rw [e1, e2, e3, e4] at h
  push_cast at h
  exact h
""")
        L, Rv = r(c.l), r(c.r)
        v = c.bps
        assert v[0] * c.hhi30 <= c.r + (c.l - c.r) * v[0] and (1 - v[3]) * (1 - c.s) <= c.r + (c.l - c.r) * v[3]
        vs = [f"(fun m d hp => (V_{c.tag}_{i + 1}{e} m d hp).trans (by norm_num))" for i in range(3) for e in "ab"]
        out.append(f"""/-- Lemma 3.4's hypothesis for the family at s = {c.s} (rho = {', '.join(str(x) for x in c.rhos)}): for every tau in
[0, 1] some member, or a trivial circuit, is below the line `r + (l - r) tau` (Lemma 5b.1). -/
theorem fam_{c.tag} : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      {disj(k, c.rhos, c.s, L, Rv, "τ")} := by
  have hs := {HS_THM[c.s]}
  exact line_fam3 {r(k)} {r(c.rhos[0])} {r(c.rhos[1])} {r(c.rhos[2])} (Hb {r(c.s)}) {r(c.s)} {r(v[0])} {r(v[1])} {r(v[2])}
    {r(v[3])} {L} {Rv} (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by have := hs.2; linarith) (by norm_num)
    {(chr(10) + "    ").join(vs)}

/-- xi = (h(s) - s)/2 - (l + r)/2 ≥ {c.xi} for the family's line, and the row data `C_{c.tag}` carries exactly (l, r). -/
theorem xi_{c.tag} : {r(c.xi)} ≤ (Hb {r(c.s)} - {r(c.s)}) / 2 - ({L} + {Rv}) / 2 ∧
    (({'C_' + c.tag}.l : ℚ) : ℝ) = {L} ∧ (({'C_' + c.tag}.r : ℚ) : ℝ) = {Rv} := by
  {G5.cfield('C_' + c.tag, "l", c.l)}
  {G5.cfield('C_' + c.tag, "r", c.r)}
  rw [e_l, e_r]
  have hs := {HS_THM[c.s]}.1
  refine ⟨?_, by norm_num, by norm_num⟩
  norm_num at hs ⊢
  linarith
""")
        out.append("end SS5b\n")
        write(f"Stage5bFam_{c.tag}", "\n".join(out))

    # ---------------- Stage5bCtl_*: [F1] and [NEED] per family, by explicit colours
    f1_info = {}
    for s, c in fams.items():
        k = c.s / 2
        bps, rhos = c.bps, c.rhos
        ln = lambda t: c.r + (c.l - c.r) * t  # noqa: E731
        # [F1]: two breakpoints on either side of 1/2; every piece is above line - F1_SLACK at both
        best = None
        for i in range(4):
            for j in range(4):
                if bps[i] < F(1, 2) < bps[j]:
                    lam = (bps[j] - F(1, 2)) / (bps[j] - bps[i])
                    best = best or (i, j, lam)
        cands = [(i, j) for i in range(4) for j in range(4) if bps[i] < F(1, 2) < bps[j]]
        txts, info = [], None
        for i, j in cands:
            try:
                parts_txt, gs = [], []
                for e, b in (("a", bps[i]), ("b", bps[j])):
                    g = [b * c.hlo30, (1 - b) * (1 - c.s)]
                    for mi, rho in enumerate(rhos):
                        t, glo = colour_glo(c, rho, b, ln(b) - F1_SLACK, f"{c.tag}_F1{e}{mi + 1}")
                        parts_txt.append(t)
                        g.append(glo)
                    gs.append(min(g))
                lam = (bps[j] - F(1, 2)) / (bps[j] - bps[i])
                chord = lam * gs[0] + (1 - lam) * gs[1]
                xiup = G5.upq((c.hhi30 - c.s) / 2 - chord, 10 ** 10)
                xib = (c.hlo30 - c.s) / 2 - (c.l + c.r - 2 * F1_DROP) / 2
                if xiup < xib:
                    info, txts = (i, j, gs, xiup), parts_txt
                    break
            except AssertionError:
                continue
        assert info is not None, ("[F1] failed", c.tag)
        f1_info[c.tag] = info
        i, j, gs, xiup = info
        print(f"[F1] {c.tag}: breakpoints {i}, {j}; any valid line has xi <= {float(xiup):.10f}; certified xi >= "
              f"{float(c.xi):.10f}", flush=True)
        hs = HS_THM[c.s]
        cases = []
        for e, b, g in (("a", bps[i], gs[0]), ("b", bps[j], gs[1])):
            alts = [f"    · have := h1 _ _ wp_{c.tag}_F1{e}{mi + 1}; linarith [w_{c.tag}_F1{e}{mi + 1}]" for mi in range(3)]
            alts += ["    · linarith [hs.1]", "    · norm_num at h1; linarith"]
            cases.append(f"""  have g{e} : {r(g)} ≤ R + (L - R) * {r(b)} := by
    rcases h {r(b)} (by norm_num) (by norm_num) with h1 | h1 | h1 | h1 | h1
""" + "\n".join(alts))
        body = "".join(txts) + f"""
/-- [F1] for the family at s = {c.s}: every line that satisfies Lemma 3.4's hypothesis with this family has
`xi ≤ {xiup}`. So the certified xi ≥ {c.xi} is within {float(xiup - c.xi):.1e} of the best this family allows. -/
theorem F1_{c.tag} : ∀ L R : ℝ, (∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      {disj(k, rhos, c.s, "L", "R", "τ")}) →
    (Hb {r(c.s)} - {r(c.s)}) / 2 - (L + R) / 2 ≤ {r(xiup)} := by
  intro L R h
  have hs := {hs}
{chr(10).join(cases)}
  linarith [hs.2]

/-- [F1], the control: the family's line with l and r lowered by {F1_DROP} fails Lemma 3.4's hypothesis. -/
theorem F1x_{c.tag} : ¬ ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      {disj(k, rhos, c.s, r(c.l - F1_DROP), r(c.r - F1_DROP), "τ")} := by
  intro h
  have := F1_{c.tag} _ _ h
  have hs := {hs}
  linarith [hs.1]
"""
        write(f"Stage5bCtl_{c.tag}_F1", "import SubsetsumLean.Stage5Base\n\n" +
              f"/-! Stage 5b control [F1] for the family at s = {c.s} (generated by `gen_stage5b.py`; do not edit). -/\n\n"
              + HEAD + body + "end SS5b\n")
        # [NEED]: member i is needed — at some tau inside its interval every other piece is above the line
        txts, thms = [], []
        for mi, rho in enumerate(rhos):
            a, b = bps[mi], bps[mi + 1]
            hit = None
            for frac in (F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4)):
                tau = a + (b - a) * frac
                tau = F(round(tau * 10 ** 6), 10 ** 6)
                if not (a < tau < b and tau * c.hlo30 > ln(tau) and (1 - tau) * (1 - c.s) > ln(tau)):
                    continue
                try:
                    ws = [colour_glo(c, x, tau, ln(tau), f"{c.tag}_N{mi + 1}o{oi + 1}")
                          for oi, x in enumerate(rhos) if x != rho]
                except AssertionError:
                    continue
                hit = (tau, ws)
                break
            assert hit is not None, ("[NEED] failed", c.tag, rho)
            tau, ws = hit
            others = [oi for oi, x in enumerate(rhos) if x != rho]
            txts += [w[0] for w in ws]
            negs = [f"(¬ ∀ m d : ℝ, Poly4 {r(k)} {r(rhos[oi])} m d → G4 {r(k)} {r(rhos[oi])} {r(tau)} m d ≤ {r(ln(tau))})"
                    for oi in others]
            pf = [f"  · intro h1; have := h1 _ _ wp_{c.tag}_N{mi + 1}o{oi + 1}; linarith [w_{c.tag}_N{mi + 1}o{oi + 1}]"
                  for oi in others]
            thms.append(f"""/-- [NEED] at s = {c.s}: member rho = {rho} is needed. At tau = {tau}, inside its interval, the other two members
and both trivial circuits are above the family's line, so only this member can satisfy Lemma 3.4's hypothesis there. -/
theorem NEED_{c.tag}_{mi + 1} : {" ∧ ".join(negs)} ∧
    ¬ ({r(tau)} * Hb {r(c.s)} ≤ {r(ln(tau))}) ∧ ¬ ((1 - {r(tau)}) * (1 - {r(c.s)}) ≤ {r(ln(tau))}) := by
  have hs := {hs}
  refine ⟨?_, ?_, ?_, ?_⟩
{chr(10).join(pf)}
  · intro h1; linarith [hs.1]
  · norm_num
""")
        write(f"Stage5bCtl_{c.tag}_NEED", "import SubsetsumLean.Stage5Base\n\n" +
              f"/-! Stage 5b control [NEED] for the family at s = {c.s} (generated by `gen_stage5b.py`; do not edit). -/\n\n"
              + HEAD + "".join(txts) + "\n" + "\n".join(thms) + "end SS5b\n")

    # ---------------- Stage5bE: the row, the integrality and window facts, the row controls
    out = ["import SubsetsumLean.Stage5bBase", "import SubsetsumLean.Stage5EDefs"]
    out += [f"import SubsetsumLean.Stage5bRows_R4bmin_{i}" for i in range(len(parts))]
    for name, (kap, subs, ng) in refs.items():
        out += [f"import SubsetsumLean.Stage5bRefs_{name}_{gi}" for gi in range(ng)]
    out += ["", "/-!\n# Stage 5b kernel check of row R4b-min and its controls (generated by `gen_stage5b.py`)\n\n"
            "`E_R4bmin`: every layer kappa in [0, 1] is served by a menu design whose P3, P4, P6 are at most the claim, "
            "and the\nconstant terms are too; `K*`: the must-fail controls of `cert_stage5b.py`, each proved false.\n-/",
            "", HEAD]
    nb = F(C5.NB)
    cs = ", ".join(cname[id(c)] for c in rmin)
    for a in ALPHAS:
        ab = nb * a / 2
        assert ab.denominator == 1 and all((ab * c.s).denominator == 1 for c in rmin)
    pairs = [(c.s, x) for c in fams.values() for x in c.rhos]
    assert all(p[0] * p[1] < F(1, 2) for p in pairs)
    out.append(f"""/-- Every alpha of R4b-min makes `a_b = alpha N_b/2` and `s a_b` integral for every circuit (Stage 5 Lemma 3.3). -/
theorem ab_integral5b : ∀ a ∈ [{", ".join(Qc(a) for a in ALPHAS)}], ((8000000000 : ℚ) * a / 2).den = 1 ∧
    ∀ c ∈ [{cs}], ((8000000000 : ℚ) * a / 2 * c.s).den = 1 := by decide +kernel

/-- Stage 4 Lemma 3.5''s window `s rho < 1/2` for every member of the six families. -/
theorem window5b : ∀ p ∈ [{", ".join(f"({Qc(a)}, {Qc(b)})" for a, b in pairs)}], p.1 * p.2 < 1 / 2 := by decide +kernel
""")
    hbname = {id(c): ("hb_" + cname[id(c)]) for c in list(rmin) + k9 + list(singles.values())}

    def circ_facts(nm, Rw, side):
        lst = [cname[id(c)] for c in Rw.circs]
        alts = " | ".join("rfl" for _ in lst)
        ex = ", ".join(f"{hbname[id(c)]}.{'1' if side == 'lo' else '2'}" for c in Rw.circs)
        st = (f"∀ c ∈ R_{nm}.circs, ((c.hsLo : ℚ) : ℝ) ≤ Hb ((c.s : ℚ) : ℝ)" if side == "lo" else
              f"∀ c ∈ R_{nm}.circs, Hb ((c.s : ℚ) : ℝ) ≤ ((c.hsHi : ℚ) : ℝ)")
        return f"""theorem hs{side}_{nm} : {st} := by
  intro c hc
  have e : R_{nm}.circs = [{", ".join(lst)}] := rfl
  rw [e] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with {alts}
  exacts [{ex}]
"""
    nm = "R4bmin"
    out.append(circ_facts(nm, R, "lo"))
    lines = [f"""/-- Row R4b-min: pieces of [0, 1/2]. -/
theorem half_{nm} : ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 / 2 → Covered R_{nm} κ := by
  intro κ h0 h1
  have hl3 : log 3 / log 2 ≤ ((R_{nm}.l3 : ℚ) : ℝ) := by
    have e : R_{nm}.l3 = (39624062518029/25000000000000 : ℚ) := by decide +kernel
    rw [e]; push_cast; exact log2_3_le5
  have e0 : ((Q 0 1 : ℚ) : ℝ) = 0 := by norm_num [Q]
  have e1 : ((Q 1 2 : ℚ) : ℝ) = 1 / 2 := by norm_num [Q]"""]
    for i, (a, b, sub) in enumerate(parts):
        lines.append(f"  have c{i} := chk_sound R_{nm} hslo_{nm} hl3 rowok_{nm} {Qc(b)} PS_{nm}_{i} {Qc(a)} chk_{nm}_{i} ne_{nm}_{i}")
    n = len(parts)
    prev = "(by rw [e0]; exact h0)"
    for i in range(n - 1):
        b = parts[i][1]
        lines.append(f"  rcases le_total κ (({Qc(b)} : ℚ) : ℝ) with hc{i} | hc{i}")
        lines.append(f"  · exact c{i} κ {prev} hc{i}")
        prev = f"hc{i}"
    lines.append(f"  exact c{n - 1} κ {prev} (by rw [e1]; exact h1)")
    out.append("\n".join(lines) + "\n")
    out.append(f"""/-- [E] row R4b-min, Theorem 5b-F (claim {CLAIM} = {float(CLAIM):.10f}): P1 = mu, P5 = Pscan = 2 mu,
Kenum = mu (2 + lambda) are at most the claim, and every layer kappa in [0, 1] has a menu design with P3, P4, P6 at
most the claim. The menu: the six families (`fam_*`) and Stage 5's circuits at 2/25 and 19/200. -/
theorem E_{nm} : ((R_{nm}.μ : ℚ) : ℝ) ≤ R_{nm}.claim ∧ 2 * ((R_{nm}.μ : ℚ) : ℝ) ≤ R_{nm}.claim ∧
    ((R_{nm}.μ : ℚ) : ℝ) * (2 + R_{nm}.lam) ≤ R_{nm}.claim ∧ ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → Covered R_{nm} κ := by
  have h := rowok_{nm}
  simp only [Row.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, c1⟩, c2⟩, c3⟩ := h
  refine ⟨by exact_mod_cast c1, by exact_mod_cast c2, by exact_mod_cast c3, ?_⟩
  exact row_covered R_{nm} (by decide +kernel) (by decide +kernel) half_{nm}
""")
    out.append("/-! ## The row controls: each is refuted (proved false) -/\n")
    same = ["R_K1b.alphas = R_R4bmin.alphas", "R_K1b.circs = R_R4bmin.circs", "R_K1b.μ = R_R4bmin.μ",
            "R_K2b.alphas = R_R4bmin.alphas", "R_K2b.circs = R_R4bmin.circs", "R_K2b.μ = R_R4bmin.μ * (101 / 100)",
            "R_K2b.claim = R_R4bmin.claim", "R_K7pb.alphas = R_R4bmin.alphas", "R_K7pb.μ = R_R4bmin.μ",
            "R_K7pb.claim = R_R4bmin.claim", "R_K9b.alphas = R_R4bmin.alphas", "R_K9b.μ = R_R4bmin.μ",
            "R_K9b.claim = R_R4bmin.claim"]
    for c in fams.values():
        same += [f"R_KFb_{c.tag}.alphas = R_R4bmin.alphas", f"R_KFb_{c.tag}.μ = R_R4bmin.μ",
                 f"R_KFb_{c.tag}.claim = R_R4bmin.claim"]
    out.append(f"""/-- Each control row is R4b-min with only the stated change (the circuit lists are in Stage5bData). -/
theorem same_ctl5b : {" ∧ ".join(same)} := by decide +kernel
""")
    docs = {"K1b": f"R4b-min's claim minus {K1_DELTA} fails", "K2b": "R4b-min with mu raised 1% fails the claim",
            "K7pb": "R4b-min with every family replaced by the single circuit at its density fails the claim",
            "K9b": "R4b-min with every circuit's (l, r) raised by 1/100 fails the claim"}
    for c in fams.values():
        docs[f"KFb_{c.tag}"] = f"R4b-min with the family at s = {c.s} alone replaced by its single circuit fails the claim"
    for name, Rc in ctl.items():
        out.append(circ_facts(name, Rc, "hi"))
        kap, subs, _ = refs[name]
        al = ", ".join(Qc(a) for a in Rc.alphas)
        alts = " | ".join("rfl" for _ in Rc.alphas)
        ex = ", ".join(f"⟨_, _, ref_{name}_{ia}⟩" for ia, *_ in subs)
        out.append(f"""/-- {name}: {docs[name]} (target {Rc.claim} = {float(Rc.claim):.10f}); at kappa = {kap} no design of the
menu meets it, for any w and any lambda ≥ 0. -/
theorem {name} : ∀ lam : ℝ, 0 ≤ lam → ¬ ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 → CoveredL R_{name} lam κ := by
  intro lam hlam h
  refine refute_alphas R_{name} hshi_{name} {Qc(kap)} ?_ lam hlam (h _ (by norm_num [Q]) (by norm_num [Q]))
  intro a ha
  have e : R_{name}.alphas = [{al}] := by decide +kernel
  rw [e] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with {alts}
  exacts [{ex}]
""")
    out.append("end SS5b\n")
    write("Stage5bE", "\n".join(out))
    tags = [c.tag for c in fams.values()]
    write("Stage5b", "\n".join([f"import SubsetsumLean.Stage5bFam_{t}" for t in tags] +
                               [f"import SubsetsumLean.Stage5bCtl_{t}_{x}" for t in tags for x in ("F1", "NEED")] +
                               ["import SubsetsumLean.Stage5bE", "",
                                "/-! Stage 5b: the kernel check of `cert_stage5b.py` (see LEAN_SCOPE.md). -/", ""]))
    thms = ["line_fam3"]
    for c in fams.values():
        thms += [f"V_{p[0]}" for p in GB.problems() if p[0].startswith(c.tag + "_")]
        thms += [f"fam_{c.tag}", f"xi_{c.tag}", f"hb_C_{c.tag}", f"F1_{c.tag}", f"F1x_{c.tag}"]
        thms += [f"NEED_{c.tag}_{i}" for i in (1, 2, 3)]
    thms += [f"hb_C_{c.tag}" for c in k9]
    thms += ["ab_integral5b", "window5b", "E_R4bmin", "same_ctl5b"] + list(ctl)
    write("Stage5bAxioms", "import SubsetsumLean.Stage5b\n\n/-! The axioms of every Stage 5b theorem (expect propext, "
          "Classical.choice, Quot.sound only). -/\n\nopen SS4 SS5b\n\n" +
          "\n".join(f"#print axioms {'SS4.' if t == 'line_fam3' else 'SS5b.'}{t}" for t in thms) + "\n")
    print("heavy modules written;", len(thms), "theorems in the axioms audit")


if __name__ == "__main__":
    cache = os.environ.get("GEN5B_CACHE")       # development only: reuse the light-module results from a pickle
    if cache and os.path.exists(cache):
        import pickle
        G5.L3Q = G.up(G.up(G.log_bounds(F(3))[2]) / G.L2lo)
        args = pickle.load(open(cache, "rb"))
    else:
        args = main()
        if cache:
            import pickle
            pickle.dump(args, open(cache, "wb"))
    write_heavy(*args)
