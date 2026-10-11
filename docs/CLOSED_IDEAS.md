# Closed ideas

These are routes to deterministic Subset Sum faster than meet-in-the-middle that we examined and found do not work.
Each row gives the reason. A closure holds only inside its stated model or route. None of them is a lower bound for
Subset Sum in general. An idea that breaks a stated hypothesis is not covered by its row.

**Status labels.**
- [proof]: a complete argument.
- [cert]: an exact or interval certificate.
- [exp]: a decisive toy experiment.
- [arg]: a short argument, not written as a full proof.

**Contributing.** If you find a mistake in a closure, or an idea that escapes one of the stated hypotheses, please
send the argument. Corrections will be credited.

## 1. Derandomising the 2^{0.489995 n} construction (openai/math #138)

| idea | why it fails | status |
|---|---|---|
| Listing aliases one by one, made deterministic | The number of aliases is about 2^n/P, and this must be <= 2^{tau n}, so the modulus has eta >= 1 - tau > 1/2. Any deterministic check per frequency or per residue mod P then costs >= 2^{eta n} > 2^{n/2} | [proof] |
| Exact counting modulo deterministically chosen moduli, then removing aliases and false hits | Subtracting aliases needs M >= 2^{(1-tau) n}. Exact counting of one residue class mod M costs >= min(nM, 2^{n/2}) by every known method (DP over residues, MITM counting, M Fourier frequencies). CRT does not help: the bin count mod M is not a function of the bin counts mod its factors | [arg] |
| The 3SUM greedy-chain trick (prime-at-a-time with an exact counting oracle) | It needs a polynomial-size query set and a counting oracle. Here the queries are the 2^{n/2} half-sums, and the oracle is the bin count itself, so the route is circular | [arg] |
| Deterministic isolation by a poly-size list of poly-bounded weightings | Isolating every family needs at least n / log2(n N0) weightings. Split [n] into that many blocks, and in each block pick A_j ≠ B_j of equal weight (pigeonhole). The family of all choices then defeats every weighting. Whether poly many suffice is open; the checksum would stay randomized anyway | [proof] (lower bound) |
| "P' has only about 0.057 n bits, so exact counts are cheap" | 0.057 n is the block size, and P' has about 0.028 n bits. Exact class counts by DP control the cost, but they do not show that the unknown alias hits the chosen class. That needs the universal covering, at 2^{0.085 n}. So P', the block and the filter can be derandomised, but the checksum walls above still stand | [arg], [exact] |

## 2. Covering choices inside the derandomisations

| idea | why it fails | status |
|---|---|---|
| Stage 2: one covering of the translates of the prefix-sum set, reused in every layer | The layer of a hit depends on the prefix c_pre, so the covering must range over pairs (c_pre, shift) | [exp] toy control `sigma` of `certificates/check_stage2.py`: 42 misses |
| Stage 1 / Stage 2: a single best residue, or a covering of one shift (y = 0) only | It misses solutions | [exp] controls `single` and `oneshift` of `certificates/check_stage1.py` and `certificates/check_stage2.py` |
| Stage 2: Ye–Li's own prefix n/3 with the deterministic covering | The covering costs 2^{2m} = 2^{2n/3} > 2^{n/2}. The prefix must stay below n/4 | [cert] control C3 of `cert_eps.py`, `stage2_C3` in Lean |
| Stage 2: prefix exactly n/4 | The covering then costs 2^{n/2}, so there is no saving | [cert] control C2, `stage2_C2` |
| Stage 1: CJRS's printed rounding (0.1579, 0.2427) | g < 0.0101 there, so the stated value needs the exact roots or a better rational point | [cert] C1, `stage1_C1` |

## 3. Templates that cannot give Stage 2

| idea | why it fails | status |
|---|---|---|
| Global-representation templates (the RW26 kind) | Their certificates need eps-sparse danger, which a worst-case instance need not have | [arg] |
| Derandomising CJRS Sec. 3 (Bit-Packing, n^{-1/2}) or Sec. 5 (n^{-0.5023}) with the same covering | The pseudolinear hash of their Lemma 1 has no deterministic replacement that we could certify below the meet-in-the-middle budget. This is not closed, only unsolved; we list it so it is not mistaken for part of Stage 1 | open, not closed |
