"""Gate-level end-to-end toy test of PROOF/stage2b-explicit.md Lemmas E1 + E2 + E3 + E4 at N = 8 (exact integers/rationals).

Toy parameters: N = 8, a = 1/8 (A = 1), b = 1/2 (B = 4), window half-width eps' = 1/8: rows of weight 3..5,
queries with z0 N = 1..3 zeros and z1 N = 4 - z0 N ones (4 stars). M = P_{8,1/2}: rows {0,1}^8, queries with 4
specified positions, M[x, y] = 1 iff x matches y on S(y).

Part 1, E1 + E2. For every window type (w, z0) the D-list and every Q-list are built by Lemma E1 (pessimistic
  estimator, with the ceil(2 t m_v) exponent): coverage constraints = the queries of the type (D level) or the
  u-subsets of comp(D) (Q level); sampling constraints = (row, u, theta) with the hypergeometric weight w_x(D)
  (D level) or (pattern on comp(D), theta) with indicator weights (Q level). T is the least integer with
  |U| e^-T + |V| 2^-T < 1. Checked: Phi_0 < 1 and Phi never rises; every constraint is covered; every sampling sum
  is < ceil(2 t m) + T; the Ye-Li gates (D, Q, sigma) from these lists give L R = M on the whole window X0 x Y0
  (all 182 x 980 pairs) and 0 off it; per colour the right degree is <= 2^{stars in D} C(A, u-A) C(u, theta-u)
  (Y2) and the left degree is <= 2 t_Q (2 t_D m_x + T_D + 1) + t_D (T_Q + 1) (E2(iii) with the ceil fix).
Part 2, E3 + (L). Greedy flips f in {0,1}^8 until the window translates cover all 256 x 1120 pairs; at every
  step the greedy flip covers at least (1 - delta) of what is left, where delta 2^N is the largest number of flips
  missing one pair (the E3 argument). Then the 2^J - 1 signed restricted copies are built gate by gate, L R is
  multiplied out over all 286,720 pairs and compared with M, and every copy's colour degrees are compared
  with those of the window circuit.
Part 3, E4. (a) Gate level: a depth-2 tree for M (x) M whose root uses C3 and whose children are chosen by the
  E4 threshold rule; L R checked on 4000 sampled pairs (half of them 1-entries), and the true max degrees
  satisfy deg_L + lambda deg_R <= G_2(lambda) (Y4). At N = 8 the circuit C3 lies above min(v1, v2) for every tau
  (Ye-Li's construction gains nothing at this size), so the rule itself only picks the trivial pieces.
  (b) The three-piece claim of E4 is therefore tested at degree level on a family in which C3 is on the hull
  (the YL-shaped family of PROOF/ye-li-audit/yl_rebalance.py): for d <= 14 and 41 values of lambda,
  G_d(lambda) <= D_d * sum_{tau in A} 2^{N d c(tau)} lambda^{1-tau}, with the induction's
  D_d = prod_{j <= d} (1 + 2^{1 + N(r_max - Delta j)}). This part uses floats for the irrational crossing
  points tau1, tau2 (relative tolerance 1e-9); G_d itself is exact.
Must-fail controls: [K1] drop every D-list member that fits one query (exactness fails); [K2] drop every
  Q-list member that contains one u-set U;
  [K3] the 2^J - 1 copies summed without signs (differs from M); [K4] the three-piece bound with D_d := 1 (no
  rebalancing constant), which is violated.
Exit 0 iff every check passes and every control fails. Pure standard library; about a minute, < 200 MB.
"""
import math
import random
import sys
from fractions import Fraction as F
from itertools import combinations
from math import comb

N, A, B = 8, 1, 4
FULL = (1 << N) - 1
WROWS = (3, 4, 5)
WZ0 = (1, 2, 3)
ok = True

def req(cond, msg):
    global ok
    if not cond:
        print("FAIL:", msg)
        ok = False

def popc(v):
    return bin(v).count("1")

def subsets(pos, k):
    for c in combinations(pos, k):
        m = 0
        for i in c:
            m |= 1 << i
        yield m

def bitsof(m):
    return [i for i in range(N) if m >> i & 1]

E_LO = F(2718, 1000)         # e >= 2.718, so e^-T <= (1000/2718)^T

def least_T(nu, nv):
    T = 1
    while nu * (1 / E_LO) ** T + nv * F(1, 2) ** T >= 1:
        T += 1
    return T

def ceil_frac(x):
    return -((-x.numerator) // x.denominator)

def e1_list(cands, U, covers, V, weight, T, p, t=None):
    """Lemma E1. covers[s] = set of u covered by s; weight(v, s) in [0,1] (Fraction).
    Returns the list and the check results."""
    if t is None:
        t = ceil_frac(F(T) / p)
    pu = {u: F(sum(1 for s in cands if u in covers[s]), len(cands)) for u in U}
    mv = {v: sum((weight(v, s) for s in cands), F(0)) / len(cands) for v in V}
    ev = {v: ceil_frac(2 * t * mv[v]) + T for v in V}          # ceil(2 t m_v) + T: exact rationals only
    W = {(v, s): weight(v, s) for v in V for s in cands}
    unc = set(U)
    prod = {v: F(1) for v in V}
    lst = []

    def phi(i, unc_, prod_):
        return (sum(((1 - pu[u]) ** (t - i) for u in unc_), F(0))
                + sum((prod_[v] * (1 + mv[v]) ** (t - i) / F(2) ** ev[v] for v in V), F(0)))
    prev = phi(0, unc, prod)
    phi0 = prev
    mono = True
    for i in range(1, t + 1):
        cu = {u: (1 - pu[u]) ** (t - i) for u in unc}
        cv = {v: prod[v] * (1 + mv[v]) ** (t - i) / F(2) ** ev[v] for v in V}
        best, bs = None, None
        base_u = sum(cu.values(), F(0))
        base_v = sum(cv.values(), F(0))
        for s in cands:
            val = base_u - sum((cu[u] for u in covers[s] if u in unc), F(0)) + base_v \
                + sum((cv[v] * W[v, s] for v in V if W[v, s]), F(0))
            if best is None or val < best:
                best, bs = val, s
        lst.append(bs)
        unc -= covers[bs]
        for v in V:
            prod[v] *= 1 + W[v, bs]
        mono &= best <= prev
        prev = best
    covered = not unc
    sampling = all(sum((W[v, s] for s in lst), F(0)) < ev[v] for v in V)
    return lst, dict(t=t, phi0=phi0, mono=mono, covered=covered, sampling=sampling, mv=mv)

# ---------------------------------------------------------------- Part 1: window circuit by E1 + E2
def queries_of(z0):
    out = []
    for z in subsets(range(N), z0):
        rest = [i for i in range(N) if not z >> i & 1]
        for o in subsets(rest, N // 2 - z0):
            out.append((z, o))
    return out

ALLQ = [q for z0 in range(0, N // 2 + 1) for q in queries_of(z0)]
ROWS = list(range(1 << N))
X0 = [x for x in ROWS if popc(x) in WROWS]
Y0 = [q for z0 in WZ0 for q in queries_of(z0)]
X0s, Y0s = set(X0), set(Y0)
USIZES = [u for u in range(A, 2 * A + 1) if 2 * u <= N - B]

def Dcovers(D, y):
    z, o = y
    out = FULL & ~D
    return popc(z & out) == A and popc(o & out) == A

Dcands = list(subsets(range(N), B))

def hyper(x, D, u, th):
    comp = FULL & ~D
    K = popc(x & comp)
    return F(comb(K, th) * comb(N - B - K, 2 * u - th), comb(N - B, 2 * u))

def build_type(w, z0):
    U = queries_of(z0)
    covers = {D: {y for y in U if Dcovers(D, y)} for D in Dcands}
    p = min(F(sum(1 for D in Dcands if y in covers[D]), len(Dcands)) for y in U)
    rows = [x for x in ROWS if popc(x) == w]
    V = [(x, u, th) for x in rows for u in USIZES for th in range(0, 2 * u + 1)]
    T = least_T(len(U), len(V))
    weight = lambda v, D: hyper(v[0], D, v[1], v[2])
    Dl, info = e1_list(Dcands, U, covers, V, weight, T, p)
    return Dl, info, T, U

def build_Q(D, u, TQ_cache):
    comp = [i for i in range(N) if not D >> i & 1]
    cands = list(subsets(comp, 2 * u))
    Us = list(subsets(comp, u))
    covers = {Q: {U_ for U_ in Us if U_ & Q == U_} for Q in cands}
    p = min(F(sum(1 for Q in cands if U_ in covers[Q]), len(cands)) for U_ in Us)
    V = [(pat, th) for k in range(len(comp) + 1) for pat in subsets(comp, k) for th in range(0, 2 * u + 1)]
    if u not in TQ_cache:            # one T and one length per u (Y3: every Q-list of a given u has one length)
        T = least_T(len(Us), len(V))
        TQ_cache[u] = (T, ceil_frac(F(T) / p))
    T, t = TQ_cache[u]
    weight = lambda v, Q: F(int(popc(v[0] & Q) == v[1]))
    Ql, info = e1_list(cands, Us, covers, V, weight, T, p, t=t)
    return Ql, info

def D_of(y, Dl):
    for D in Dl:
        if Dcovers(D, y):
            return D
    return None

def right_column(y, Dl, Ql, tag, drop=None):
    """Sparse column {gate: coef}, gate = (tag, D, Q, sigma); Ye-Li Sec. 3.5 (as derand/stage2/yl_circuit.py)."""
    z, o = y
    if drop is not None and drop[0] == "D":
        Dl = [d for d in Dl if not Dcovers(d, drop[1])]   # no member fits the query drop[1] any more
    D = D_of(y, Dl)
    col = {}
    if D is None:
        return col
    A1, A0 = o & ~D, z & ~D
    starsD = bitsof(D & ~(z | o))
    for k in range(A + 1):
        for W_ in subsets(bitsof(A0), k):
            U_ = A1 | W_
            u = popc(U_)
            sign = (-1) ** (u - A)
            lst = Ql[D, u]
            if drop is not None and drop[0] == "Q" and drop[1] == (D, u):
                lst = [q for q in lst if drop[2] & q != drop[2]]   # no member contains U = drop[2]
            Qs = [Q for Q in lst if U_ & Q == U_][:1]
            for Q in Qs:
                free = bitsof(Q & ~U_)
                for kk in range(len(free) + 1):
                    for Fm in subsets(free, kk):
                        for s in range(len(starsD) + 1):
                            for S in subsets(starsD, s):
                                sigma = o & D | S | U_ | Fm
                                g = (tag, D, Q, sigma)
                                col[g] = col.get(g, 0) + sign
    return {g: c for g, c in col.items() if c}

def matches(x, y):
    z, o = y
    return 1 if (x & o) == o and (x & z) == 0 else 0

print("Part 1 (E1 + E2): window circuit at N = 8, types (w, z0) in {3,4,5} x {1,2,3}")
TYPES = {}
TQ = {}
for w in WROWS:
    for z0 in WZ0:
        Dl, info, TD, U = build_type(w, z0)
        req(info["phi0"] < 1 and info["mono"] and info["covered"] and info["sampling"],
            "E1 D-level checks at type %s" % ((w, z0),))
        Ql, qinfo = {}, []
        for D in Dl:
            for u in USIZES:
                if (D, u) not in Ql:
                    Ql[D, u], qi = build_Q(D, u, TQ)
                    qinfo.append(qi)
                    req(qi["phi0"] < 1 and qi["mono"] and qi["covered"] and qi["sampling"], "E1 Q-level checks")
        TYPES[w, z0] = dict(Dl=Dl, Ql=Ql, tD=info["t"], TD=TD, mv=info["mv"])
        print("  type (w=%d, z0=%d): T_D=%d t_D=%d |L_D distinct|=%d; Phi_0=%.3g, Phi non-increasing, all covered, "
              "all sampling sums < ceil(2tm)+T" % (w, z0, TD, info["t"], len(set(Dl)), float(info["phi0"])))
print("  Q level: (T_Q, t_Q) per u =", {u: TQ[u] for u in sorted(TQ)})

def window_circuit(drop=None):
    """L as {x: {gate: 1}} only through sigma matching; R as {gate: {y: c}}."""
    R = {}
    for y in Y0:
        z, o = y
        z0 = popc(z)
        for w in WROWS:
            ty = TYPES[w, z0]
            for g, c in right_column(y, ty["Dl"], ty["Ql"], (w, z0), drop).items():
                R.setdefault(g, {})[y] = c
    return R

def L_of(x, R):
    """Gates incident to row x: (tag, D, Q, x|DuQ) with tag's row weight = |x|."""
    w = popc(x)
    out = []
    if w not in WROWS:
        return out
    for z0 in WZ0:
        ty = TYPES[w, z0]
        seen = set()
        for D in ty["Dl"]:
            if D in seen:
                continue
            seen.add(D)
            for u in USIZES:
                for Q in dict.fromkeys(ty["Ql"][D, u]):
                    g = ((w, z0), D, Q, x & (D | Q))
                    if g in R:
                        out.append(g)
    return out

R0 = window_circuit()
LX = {x: L_of(x, R0) for x in X0}
bad = 0
for x in X0:
    acc = {}
    for g in LX[x]:
        for y, c in R0[g].items():
            acc[y] = acc.get(y, 0) + c
    for y in ALLQ:
        want = matches(x, y) if y in Y0s else 0
        if acc.get(y, 0) != want:
            bad += 1
req(bad == 0, "E2 exactness on the window")
print("  L R = M on all %d x %d window pairs and 0 off the window: %s" % (len(X0), len(Y0), bad == 0))

def colour(g):
    tag, D, Q, sigma = g
    u = popc(Q) // 2
    return (tag, u, popc(sigma & Q))

# right degree (Y2) and left degree (E2(iii)) per colour
rdeg, worst_r = {}, 0.0
for g, col in R0.items():
    for y in col:
        rdeg[y, colour(g)] = rdeg.get((y, colour(g)), 0) + 1
for (y, (tag, u, th)), k in rdeg.items():
    z, o = y
    D = D_of(y, TYPES[tag]["Dl"])
    bound = 2 ** popc(D & ~(z | o)) * comb(A, u - A) * comb(u, th - u)
    req(k <= bound, "right degree (Y2)")
    worst_r = max(worst_r, k / bound)
ldeg = {}
for x in X0:
    for g in LX[x]:
        ldeg[x, colour(g)] = ldeg.get((x, colour(g)), 0) + 1
worst_l = 0.0
for (x, (tag, u, th)), k in ldeg.items():
    ty = TYPES[tag]
    TQu, tQ = TQ[u]
    mx = ty["mv"][x, u, th]
    bound = 2 * tQ * (2 * ty["tD"] * mx + ty["TD"] + 1) + ty["tD"] * (TQu + 1)
    req(k <= bound, "left degree (E2(iii))")
    worst_l = max(worst_l, float(k / bound))
print("  right degree <= (Y2) bound in every colour (max ratio %.3f); left degree <= E2(iii) bound (max ratio %.3f)"
      % (worst_r, worst_l))

# controls K1, K2: drop a needed list member
def needed_D():
    for (w, z0), ty in TYPES.items():
        for y in queries_of(z0):
            return ("D", y), (w, z0)
def needed_Q():
    for (w, z0), ty in TYPES.items():
        y = queries_of(z0)[0]
        D = D_of(y, ty["Dl"])
        return ("Q", (D, 1), y[1] & ~D), (w, z0)      # U = the A ones of y outside D(y), u = A = 1
for name, (drop, tag) in (("K1 drop D", needed_D()), ("K2 drop Q", needed_Q())):
    Rk = window_circuit(drop)
    badk = 0
    for x in X0:
        if popc(x) != tag[0]:
            continue
        acc = {}
        for g in L_of(x, Rk):
            for y, c in Rk[g].items():
                acc[y] = acc.get(y, 0) + c
        for y in queries_of(tag[1]):
            badk += acc.get(y, 0) != matches(x, y)
    req(badk > 0, "control %s must break exactness" % name)
    print("  control %s: %d mismatches (must be > 0)" % (name, badk))

# ---------------------------------------------------------------- Part 2: E3 greedy flips + (L) assembly
print("Part 2 (E3 + (L)): greedy flips, signed restricted copies, P_{8,1/2} on all 256 x %d pairs" % len(ALLQ))
QIDX = {y: i for i, y in enumerate(ALLQ)}

def flip_q(y, f):
    z, o = y
    S = z | o
    return ((z & ~f | o & f) & S, (o & ~f | z & f) & S)

Y0mask = 0
for y in Y0:
    Y0mask |= 1 << QIDX[y]
Xf = {f: [x for x in ROWS if (x ^ f) in X0s] for f in ROWS}
Yfm = {}
for f in ROWS:
    m = 0
    for y in ALLQ:
        if flip_q(y, f) in Y0s:
            m |= 1 << QIDX[y]
    Yfm[f] = m
# delta: the largest fraction of flips missing one pair (pairs (x, y): x ^ f in X0 and y ^ f in Y0)
cover_cnt = {}
for f in ROWS:
    ym = Yfm[f]
    for x in Xf[f]:
        cover_cnt[x] = cover_cnt.get(x, [])
        cover_cnt[x].append(ym)
miss_max = 0
for x in ROWS:
    cnt = [0] * len(ALLQ)
    for ym in cover_cnt.get(x, []):
        for j in range(len(ALLQ)):
            if ym >> j & 1:
                cnt[j] += 1
    miss_max = max(miss_max, max(256 - c for c in cnt))
delta = F(miss_max, 256)
unc = {x: (1 << len(ALLQ)) - 1 for x in ROWS}
flips = []
left = 256 * len(ALLQ)
greedy_ok = True
while left:
    bestf, bestc = None, -1
    for f in ROWS:
        ym = Yfm[f]
        c = sum(popc(unc[x] & ym) for x in Xf[f])
        if c > bestc:
            bestf, bestc = f, c
    greedy_ok &= bestc >= (1 - delta) * left
    flips.append(bestf)
    for x in Xf[bestf]:
        unc[x] &= ~Yfm[bestf]
    left -= bestc
J = len(flips)
req(greedy_ok, "greedy covers >= (1 - delta) of the rest at every step")
print("  delta = %s; greedy J = %d flips, each step covers >= (1 - delta) of the uncovered pairs: %s"
      % (delta, J, greedy_ok))

# gate lists of the window circuit: for gate g, its rows (L) and its queries (R)
GL = {}
for x in X0:
    for g in LX[x]:
        GL.setdefault(g, []).append(x)
C_ldeg = {}
for (x, col), k in ldeg.items():
    C_ldeg[col] = max(C_ldeg.get(col, 0), k)
C_rdeg = {}
for (y, col), k in rdeg.items():
    C_rdeg[col] = max(C_rdeg.get(col, 0), k)

def assemble(signed):
    tot = [[0] * len(ALLQ) for _ in ROWS]
    deg_ok = True
    colours = {}
    for k in range(1, J + 1):
        for I in combinations(range(J), k):
            f = flips[I[0]]
            XI = set.intersection(*[set(Xf[flips[i]]) for i in I])
            YI = Yfm[flips[I[0]]]
            for i in I[1:]:
                YI &= Yfm[flips[i]]
            sgn = (-1) ** (k + 1) if signed else 1
            ld, rd = {}, {}
            for g, xs in GL.items():
                rows = [x ^ f for x in xs if (x ^ f) in XI]
                if not rows:
                    continue
                cols = []
                for y, c in R0[g].items():
                    yy = flip_q(y, f)                 # y = yy ^ f, i.e. the copy's query is yy
                    j = QIDX[yy]
                    if YI >> j & 1:
                        cols.append((j, c))
                if not cols:
                    continue
                col = (I, colour(g))
                colours[col] = colour(g)
                for x in rows:
                    ld[x, col] = ld.get((x, col), 0) + 1
                    t = tot[x]
                    for j, c in cols:
                        t[j] += sgn * c
                for j, _ in cols:
                    rd[j, col] = rd.get((j, col), 0) + 1
            deg_ok &= all(v <= C_ldeg[col[1]] for (x, col), v in ld.items())
            deg_ok &= all(v <= C_rdeg[col[1]] for (j, col), v in rd.items())
    exact = all(tot[x][QIDX[y]] == matches(x, y) for x in ROWS for y in ALLQ)
    return exact, deg_ok, colours

exact, deg_ok, C3colours = assemble(True)
req(exact and deg_ok, "E3 + (L): signed copies give M, copy degrees <= window degrees")
print("  %d signed restricted copies: L R = M on all pairs: %s; every copy's colour degrees <= the window's: %s"
      % (2 ** J - 1, exact, deg_ok))
exact_u, _, _ = assemble(False)
req(not exact_u, "control K3 (no signs) must differ from M")
print("  control K3 unsigned sum equals M: %s (must be False)" % exact_u)

# ---------------------------------------------------------------- Part 3: E4
print("Part 3 (E4): rebalancing tree")
# colour degree lists (a, b) of the three circuits: (M, I), (I, M), C3 (copies tagged by I)
fam = {1: [(comb(N, N // 2), 1)], 2: [(1, 2 ** (N // 2))],
       3: [(C_ldeg[base], C_rdeg[base]) for col, base in C3colours.items()]}

def ups(lst, tau):
    return sum(a ** tau * b ** (1 - tau) for a, b in lst)

hull3 = min(math.log2(ups(fam[3], t / 100)) - min(math.log2(ups(fam[1], t / 100)), math.log2(ups(fam[2], t / 100)))
            for t in range(101))
print("  N = 8: min over tau of v3 - min(v1, v2) = %.3f > 0, so C3 is not on the hull at this size" % (hull3 / N))

def G(lst_of, d, lam, rule, memo):
    if d == 0:
        return 1 + lam
    key = (d, lam)
    if key in memo:
        return memo[key]
    t = rule(d, lam)
    val = sum((a * G(lst_of, d - 1, lam * F(b, a), rule, memo) for a, b in lst_of[t]), F(0))
    memo[key] = val
    return val

# (a) gate level: depth-2 tree for M (x) M, root C3, children by the two-piece threshold rule on (M,I), (I,M)
# Gates of the three circuits as functions: rows -> [(gate, colour)], gate -> {query: coef}
def gates_row(t, x):
    if t == 1:
        return [(("q", y), 0) for y in ALLQ if matches(x, y)]
    if t == 2:
        return [(("x", x), 0)]
    return C3_row[x]

def gates_col(t, g):
    if t == 1:
        return {g[1]: 1}
    if t == 2:
        return {y: 1 for y in ALLQ if matches(g[1], y)}
    return C3_col[g]

# C3 explicitly, gate by gate (the signed copies as in Part 2), keyed for lookup
C3_row, C3_col, C3_colid = {}, {}, {}
for k in range(1, J + 1):
    for I in combinations(range(J), k):
        f = flips[I[0]]
        XI = set.intersection(*[set(Xf[flips[i]]) for i in I])
        YI = Yfm[flips[I[0]]]
        for i in I[1:]:
            YI &= Yfm[flips[i]]
        sgn = (-1) ** (k + 1)
        for g, xs in GL.items():
            cols = {}
            for y, c in R0[g].items():
                yy = flip_q(y, f)
                if YI >> QIDX[yy] & 1:
                    cols[yy] = c
            rows = [x ^ f for x in xs if (x ^ f) in XI]
            if not cols or not rows:
                continue
            gg = (I, g)
            C3_col[gg] = cols
            C3_colid[gg] = (I, colour(g))
            for x in rows:
                C3_row.setdefault(x, []).append((gg, sgn))
colist = sorted(set(C3_colid.values()), key=repr)
ab3 = {cid: (C_ldeg[cid[1]], C_rdeg[cid[1]]) for cid in colist}
fam[3] = [ab3[cid] for cid in colist]

def rule2(d, lam):
    # two-piece threshold on ell = log2 lam / (N d): (M,I) when ell <= x1, else (I,M); x1 = mid slope
    s1, s2 = math.log2(comb(N, N // 2)) / N, -0.5
    return 1 if math.log2(lam) / (N * d) <= (s1 + s2) / 2 else 2

lam = F(2 ** 3)
rng = random.Random(1)
def entry(x1, x2, y1, y2):
    tot = 0
    for g1, c1 in C3_row.get(x1, []):
        r1 = C3_col[g1].get(y1, 0)
        if not r1:
            continue
        a, b = ab3[C3_colid[g1]]
        t2 = rule2(1, lam * F(b, a))
        s = 0
        for g2, _ in gates_row(t2, x2):
            s += gates_col(t2, g2).get(y2, 0)
        tot += c1 * r1 * s
    return tot
def completion(y):            # a random row matching y: y's ones, and random bits on its stars
    z, o = y
    return o | (rng.randrange(1 << N) & ~(z | o) & FULL)
pos = []
for _ in range(2000):
    y1, y2 = rng.choice(ALLQ), rng.choice(ALLQ)
    pos.append((completion(y1), completion(y2), y1, y2))
neg = [(rng.choice(ROWS), rng.choice(ROWS), rng.choice(ALLQ), rng.choice(ALLQ)) for _ in range(2000)]
bad = sum(entry(*p) != matches(p[0], p[2]) * matches(p[1], p[3]) for p in pos + neg)
req(bad == 0 and len(pos) == 2000, "E4 tree exactness on samples")
# true max degrees of the depth-2 tree: per row x1, counts of children of each type, times the child's row degree
deg_row = {1: comb(N, N // 2), 2: 1}
deg_col = {1: 1, 2: 2 ** (N // 2)}
def child(g1):
    a, b = ab3[C3_colid[g1]]
    return rule2(1, lam * F(b, a))
dl = max(sum(deg_row[child(g1)] for g1, _ in C3_row.get(x1, [])) for x1 in ROWS)
qcount = {}
for g1, col in C3_col.items():
    a, b = ab3[C3_colid[g1]]
    t2 = rule2(1, lam * F(b, a))
    for y1 in col:
        qcount[y1] = qcount.get(y1, 0) + deg_col[t2]
dr = max(qcount.values())
G2 = sum((a * G({1: fam[1], 2: fam[2]}, 1, lam * F(b, a), rule2, {}) for a, b in fam[3]), F(0))
req(dl + lam * dr <= G2, "(Y4) degree bound at depth 2")
print("  (a) depth-2 tree (root C3, children by rule): exact on %d sampled pairs (%d ones): %s; deg_L + lam deg_R = %d "
      "<= G_2(lam) = %d at lam = 8: %s" % (len(pos) + len(neg), len(pos), bad == 0, dl + lam * dr, G2, dl + lam * dr <= G2))

# (b) three-piece claim on the YL-shaped family (exponents per coordinate, N_ = 1)
famY = {1: [(2 ** 13, 1)], 2: [(1, 2 ** 8)], 3: [(1, 2 ** 5), (2, 2 ** 5)]}
v = {t: (lambda tau, t=t: math.log2(ups(famY[t], tau))) for t in famY}

def cross(f1, f2, lo, hi):
    for _ in range(200):
        mid = (lo + hi) / 2
        if (f1(lo) - f2(lo)) * (f1(mid) - f2(mid)) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2
t1 = cross(v[1], v[3], 1e-9, 8 / 21)
t2 = cross(v[3], v[2], 8 / 21, 1 - 1e-9)
Apts = [0.0, t1, t2, 1.0]
cval = [min(v[t](tau) for t in famY) for tau in Apts]
pieces_ok = abs(v[1](t1) - v[3](t1)) < 1e-9 and abs(v[3](t2) - v[2](t2)) < 1e-9 and v[3](t1) < v[2](t1) and \
    v[3](t2) < v[1](t2) and cval[0] == min(v[1](0), v[2](0), v[3](0))
sl = [(cval[i] - cval[i - 1]) / (Apts[i] - Apts[i - 1]) for i in (1, 2, 3)]
pieces_ok &= sl[0] > sl[1] > sl[2]
Delta = min(Apts[i] - Apts[i - 1] for i in (1, 2, 3)) * min(sl[0] - sl[1], sl[1] - sl[2]) / 4
rmax = max(v[t](tau) - c for t in famY for tau, c in zip(Apts, cval))
x1t, x2t = (sl[0] + sl[1]) / 2, (sl[1] + sl[2]) / 2

def rule3(d, lam):
    ell = math.log2(lam) / d
    if ell >= x1t:
        return 1
    if ell >= x2t:
        return 3
    return 2

def claim_ok(Dd_of, dmax=14):
    worst = -1e9
    for d in range(1, dmax + 1):
        memo = {}
        for j in range(-20, 21):
            lam = F(2) ** (j * d // 2)
            g = G(famY, d, lam, rule3, memo)
            rhs = Dd_of(d) * sum(2 ** (d * c) * float(lam) ** (1 - tau) for tau, c in zip(Apts, cval))
            worst = max(worst, math.log2(float(g)) - math.log2(rhs))
    return worst
Dd = lambda d: math.prod(1 + 2 ** (1 + (rmax - Delta * j)) for j in range(1, d + 1))
w3 = claim_ok(Dd)
req(pieces_ok and w3 <= 1e-9, "E4 three-piece claim")
print("  (b) YL-shaped family: pieces (M,I) | C3 | (I,M) with tau1 = %.4f, tau2 = %.4f, slopes %.3f > %.3f > %.3f: %s"
      % (t1, t2, sl[0], sl[1], sl[2], pieces_ok))
print("      G_d <= D_d sum_A 2^{d c} lam^{1-tau} for d <= 14, 41 lambdas: max log2 excess %.3f (must be <= 0)" % w3)
w0 = claim_ok(lambda d: 1.0)
req(w0 > 1e-6, "control K4 (D_d = 1) must be violated")
print("      control K4 with D_d := 1: max log2 excess %.3f (must be > 0)" % w0)
print("ALL PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
