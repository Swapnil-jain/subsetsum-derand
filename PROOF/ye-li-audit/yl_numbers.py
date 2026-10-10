"""Recompute Ye-Li (arXiv 2610.10446v1) Sec. 4 numbers from their formulas, independently.

High precision via decimal (60 digits) for the closed forms; a float grid over (mu, theta) cross-checks the
three anchors V(0), V(1/2), V(1) and the secant domination min{V, tau, (1-tau)/2} <= L(tau) with the TRUE V
(max over the colour grid), not only the two-segment bound. Exit 0 = every check passes.
"""
import sys, math
from decimal import Decimal as D, getcontext
getcontext().prec = 60

a = D("0.00037954865735953624129927")
b = D("0.99094548027616196930017929")
LN2 = D(2).ln()

def lg(x):
    return x.ln() / LN2 if x > 0 else D(0)

def hh(u, v):            # h(u,v) = u lg u - v lg v - (u-v) lg(u-v), 0 lg 0 = 0
    t = lambda x: x * lg(x) if x > 0 else D(0)
    return t(u) - t(v) - t(u - v)

def h(t): return hh(D(1), t)

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name)
    ok &= bool(cond)

one, half, quarter = D(1), D("0.5"), D("0.25")
# parameter constraints of Sec. 3.5 / Sec. 4
check("0 < a < 1/4", 0 < a < quarter)
check("4a <= 1-b < 1/2 + 2a", 4 * a <= one - b < half + 2 * a)
check("1-b > 10a", one - b > 10 * a)
E1 = h(b) - 2 * hh(quarter, a) - hh(half, one - b - 2 * a)      # |D| exponent
E0 = b - half + 2 * a                                            # stars inside D
check("dominance 1: E1 > 4a  (E1 = %.12f)" % E1, E1 > 4 * a)
check("dominance 2: h(1-b,2a) > 8a", hh(one - b, 2 * a) > 8 * a)

V0 = b - half + (2 + lg(D(6))) * a
V1 = E1 + hh(one - b, 2 * a) - 4 * a
c = one - b
disc = (27 * c - 10 * a) ** 2 + 7992 * a * c
mu = 108 * a * c / (disc.sqrt() + 27 * c - 10 * a)
check("mu root satisfies 37mu^2+(27(1-b)-10a)mu-54a(1-b)=0",
      abs(37 * mu * mu + (27 * c - 10 * a) * mu - 54 * a * c) < D(10) ** -50)
check("a < mu < 2a", a < mu < 2 * a)
th = D(4) / 3 * mu
Vh = (E1 + E0) / 2 + (hh(c, mu) + hh(2 * mu, th) - 4 * mu + hh(a, mu - a) + hh(mu, th - mu)) / 2
tm = V0 / (1 + 2 * V0 - 2 * Vh)
tp = 1 - V1 / (half - 2 * Vh + 2 * V1)
dL = (1 - tp) * (1 - 3 * tm) / (2 * (tp - tm))
dR = tm * (3 * tp - 1) / (2 * (tp - tm))
xi = quarter - (dL + dR) / 2
paper = {"V(0)": "0.49268569663735450584", "V(1/2)": "0.24997913372377961141", "V(1)": "0.00757766963945240565",
         "mu": "0.00069649211514613618", "theta*": "0.00092865615352818158", "tau-": "0.33168260605143320534",
         "tau+": "0.50137304583751125366", "dL": "0.00727587055962990941", "dR": "0.49268405898808998771",
         "xi": "0.00002003522614005143"}
ours = {"V(0)": V0, "V(1/2)": Vh, "V(1)": V1, "mu": mu, "theta*": th, "tau-": tm, "tau+": tp,
        "dL": dL, "dR": dR, "xi": xi}
for k, v in ours.items():
    # paper truncates after 20 places
    check("%-7s ours %s  paper %s" % (k, str(v)[:24], paper[k]), abs(v - D(paper[k])) < D(10) ** -19)
check("0 < tau- < 1/3 < 1/2 < tau+ < 1", 0 < tm < D(1) / 3 < half < tp < 1)
check("xi > 0.00002", xi > D("0.00002"))
check("1/2 - xi/9 + 1e-9 < 1/2 - 1/450000", half - xi / 9 + D("1e-9") < half - one / 450000)
check("dL,dR >= 0", dL >= 0 and dR >= 0)

# ---- float cross-checks with the true V (max over a colour grid) ----
af, bf = float(a), float(b)
def hf(u, v):
    t = lambda x: x * math.log2(x) if x > 0 else 0.0
    return t(u) - t(v) - t(u - v)
E1f, E0f = float(E1), float(E0)
G = 400
cols = []
for i in range(G + 1):
    m_ = af + af * i / G
    for j in range(G + 1):
        t_ = m_ + m_ * j / G
        cols.append((hf(1 - bf, m_) + hf(2 * m_, t_) - 4 * m_, hf(af, m_ - af) + hf(m_, t_ - m_)))
def Vtrue(tau):
    return tau * E1f + (1 - tau) * E0f + max(tau * l + (1 - tau) * r for l, r in cols)
for name, tau, ref in (("V(0)", 0.0, V0), ("V(1/2)", 0.5, Vh), ("V(1)", 1.0, V1)):
    g = Vtrue(tau)
    check("grid %s = %.12f <= closed form %.12f (+1e-9), gap < 1e-7" % (name, g, float(ref)),
          g <= float(ref) + 1e-9 and float(ref) - g < 1e-7)
L = lambda tau: tau * float(dL) + (1 - tau) * float(dR)
worst = max(min(Vtrue(t / 200), t / 200, (1 - t / 200) / 2) - L(t / 200) for t in range(201))
check("secant dominates min{V,tau,(1-tau)/2} on 201 taus (max excess %.3e <= 1e-12)" % worst, worst <= 1e-12)
# dominance of the third left-degree term over the first two, every colour on the grid
m_min = min(hf(1 - bf, af + af * i / G) - 4 * (af + af * i / G) for i in range(G + 1))
check("h(1-b,mu) - 4mu > 0 for all mu in [a,2a] (min %.3e)" % m_min, m_min > 0)
print("ALL PASS" if ok else "SOME CHECK FAILED")
sys.exit(0 if ok else 1)
