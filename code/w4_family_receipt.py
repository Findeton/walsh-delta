"""Paper XII receipt w4 -- the three-dip and j=3 families; Sections 5-6, 9.

Part A verifies, on genuinely low-entropy calibrated laws (the three-dip
family at n = 9, 10, 11 and the j=3 family at n = 9, 10, 11 -- the only
known laws with D <= 1/60), every inequality used in the paper's analytic part:
the coefficient/parameter floor (Lemma 5.1), the spectral-approximation
and floor and sign readout (Proposition 5.3), the dip-count bound (Lemma
5.2(i)), the
deep-dip count m >= 3 (Theorem 6.1), and the trichotomy conclusion
N*D >= 3*psi(e^-5) = 2.878716.

Part B prints the Section 9 table: N * D for the three-dip family at
n = 3..8, converging to 4*log(4) = 5.545177.

NUMERICAL NOTE (load-bearing): depths reach beta ~ N*log(N/4) (X ~ e^-5700
at n = 10), far below float64 underflow.  All depth-dependent quantities
are computed in log-domain: logX = log(N) + field - logsumexp(field).
Exponentiating X and taking logs silently corrupts every depth (clamps at
the underflow threshold) and produces false alarms.
"""
import numpy as np

def walsh(n):
    N = 1 << n
    pc = np.zeros((N, N), dtype=np.int64)
    for a in range(N):
        pc[a] = [bin(a & s).count("1") for s in range(N)]
    return np.where(pc % 2 == 0, 1.0, -1.0)

def solve(sigma, W, tol=1e-12, maxit=600):
    N = W.shape[0]; l = np.zeros(N - 1)
    def G(lv):
        f = W[1:].T @ lv; m = f.max()
        return m + np.log(np.mean(np.exp(f - m))) + np.exp(-sigma * lv).sum()
    for _ in range(maxit):
        f = W[1:].T @ l; f -= f.max(); w = np.exp(f); p = w / w.sum()
        x = W[1:] @ p; b = np.exp(-sigma * l); g = x - sigma * b
        if np.abs(g).max() < tol: break
        Wc = W[1:] * np.sqrt(p)[None, :]
        H = Wc @ Wc.T - np.outer(x, x) + np.diag(b)
        st = np.linalg.solve(H, g); g0 = G(l); t = 1.0
        while t > 1e-9 and G(l - t * st) > g0 + 1e-15: t /= 2
        l = l - t * st
    return l

def family_sigma(n, jbits):
    N = 1 << n
    mask = (1 << jbits) - 1
    return np.array([1.0 if (a & mask) == mask else -1.0 for a in range(1, N)])

def logdomain_law(sigma, W):
    N = W.shape[0]
    l = solve(sigma, W)
    field = W[1:].T @ l; m = field.max()
    lse = m + np.log(np.sum(np.exp(field - m)))
    logX = np.log(N) + field - lse
    p = np.exp(field - lse)
    D = float(np.sum(p * logX))
    return logX, D

def check(n, jbits, label):
    N = 1 << n; W = walsh(n)
    sigma = family_sigma(n, jbits)
    logX, D = logdomain_law(sigma, W)
    print(f"[{label}] n={n}  D={D:.6f}  N*D={N*D:.4f}  in-regime(D<=1/60)={D <= 1/60}")
    if D > 1 / 60:
        print("   out of regime; Theorem 7.1 case 1 applies -- nothing to check")
        return True
    dips = np.where(logX <= np.log(0.5))[0]
    beta = -logX[dips]
    ghat = (W[1:] @ logX) / N
    F = np.zeros(N - 1)
    for j, s in enumerate(dips):
        F += beta[j] * W[1:, s]
    epsG = 2.5 * np.sqrt(2 * D)
    hprime = 0.5 * np.log(1 / (2 * D)) - epsG
    x = (W[1:] @ np.exp(logX)) / N   # Walsh coefficients of X (bulk-scale; exp(logX)<=N safe)
    checks = [
        ("Lemma 5.1     u_max <= sqrt(2D)", float(np.abs(x).max()) <= np.sqrt(2 * D)),
        ("Lemma 5.1     h_min >= 0.5*log(1/2D)", float(np.abs(ghat).min()) >= 0.5 * np.log(1 / (2 * D)) - 1e-12),
        ("Lemma 5.2(i)  k <= D*N/psi(1/2)", len(dips) <= D * N / 0.1534264),
        ("Thm 6.1       deep count m >= 3", int((beta >= 5.0).sum()) >= 3),
        ("Prop 5.3(i)   |ghat + F/N| <= eps_G", float(np.abs(ghat + F / N).max()) <= epsG),
        ("Prop 5.3(ii)  min|F|/N >= h'", float(np.abs(F).min() / N) >= hprime),
        ("Prop 5.3(iii) sign readout eps=-sgnF", bool(np.all(sigma == -np.sign(F)))),
        ("Thm 6.1       N*D >= 2.878716", N * D >= 2.878716),
    ]
    ok = True
    for name, val in checks:
        ok &= bool(val)
        print(f"   {name}: {val}")
    return ok

if __name__ == "__main__":
    print("Part A: inequality verification on in-regime laws")
    allok = True
    for n in [9, 10, 11]:
        allok &= check(n, 2, "three-dip family")
    for n in [9, 10, 11]:
        allok &= check(n, 3, "j=3 family")
    print()
    print("Part B: Section 9 table -- three-dip family, N*D vs 4log4 =",
          f"{4*np.log(4):.6f}")
    for n in range(3, 9):
        N = 1 << n
        _, D = logdomain_law(family_sigma(n, 2), walsh(n))
        print(f"   n={n}  N*D = {N*D:.4f}")
    print()
    print("ALL CHECKS PASS" if allok else "FAILURES PRESENT")
