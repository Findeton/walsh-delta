# The Walsh–delta theorem

> **The delta orientation is the unique entropy minimizer for self-calibrated ±1 Walsh tilts on the Boolean cube.**

This repository contains the paper (Paper XII), a **Lean 4 + Mathlib formalization** of it, and the
**certified computation** that discharges the small-`n` case of the main theorem.

- **Paper:** [`paper/paper-XII-walsh-delta.md`](paper/paper-XII-walsh-delta.md) (also `.tex`, `.pdf`)
- **Formal proof:** [`lean/`](lean/) — 7 of 8 modules kernel-verified with no `sorry`; the headline
  `theorem_1_2` is proved modulo exactly one finite computation.
- **Certificates:** [`code/`](code/) + [`receipts/`](receipts/) — the `w1`–`w5` programs and their canonical outputs.

Author: **Felix Robles Elvira** (ORCID `0009-0009-2017-4394`). Preprint, not peer reviewed.

---

## 1. What the paper proves (the mathematics)

### 1.1 The setup

Fix `n ≥ 2`. Let `G = {±1}ⁿ ≅ 𝔽₂ⁿ` be the **Boolean cube**, with `N = 2ⁿ` points, and let `U` be the
uniform law on it. For each nonzero `a ∈ 𝔽₂ⁿ` there is a **Walsh character**
`χ_a(s) = (−1)^⟨a,s⟩` — a rule that two-colors the cube by the parity of the coordinates of `s` selected
by `a`. There are `N − 1` of them.

An **orientation** is a choice of sign `ε_a ∈ {±1}`, one per nonzero character. Each orientation defines an
exponential-family (Gibbs) law

```
P_ε(s) ∝ exp( Σ_{a≠0} h_a · ε_a · χ_a(s) ),
```

whose magnitudes `h_a` are pinned by the **self-calibration** fixed-point conditions

```
𝔼_{P_ε}[ ε_a χ_a ] = e^{−h_a}      for every a ≠ 0.
```

("each tilted correlation equals the exponential of minus its own tilt parameter.") The paper proves this
system has **exactly one** solution for every sign choice — so `P_ε` is well defined — via the strict
convexity and coercivity of a single objective `G_ε` (a log-partition function plus separable barriers).

### 1.2 The theorem

Measure each law by its **relative entropy to uniform**, `m̂(ε) = D(P_ε ‖ U) ≥ 0`. The **main theorem
(Theorem 1.2)** is:

> `m̂(ε)` is minimized — strictly, and uniquely up to the natural `N`-element symmetry orbit — by the
> **delta orientations** `ε_a = −χ_a(s⋆)`, whose calibrated law is uniform on `N−1` points and nearly
> extinguishes the single point `s⋆`.

In words: **among all balanced, self-consistent sign strategies, the cheapest (lowest-entropy) one is
always the sharply-peaked "delta," and it is the only cheapest one.** Uniqueness is essential — there is no
tie between competing minimizers.

### 1.3 Why it's true (the deep-dip trichotomy)

The engine is a **quantitative dichotomy** (Theorem 6.1). Any *non*-delta calibrated law with `D ≤ 1/60`
must **extinguish at least three points** of the cube down to depth `e⁻⁵`, which forces

```
N · D  ≥  3 ψ(e⁻⁵)  =  3(1 − 6e⁻⁵)  >  2.878716,      where ψ(x) = x log x − x + 1,
```

while the delta value satisfies `N · D_δ < N/(N−1) ≤ 64/63`. For `n ≥ 6` (so `N ≥ 64`) these two bounds
cross and close the theorem **analytically**. For `n ≤ 5` the margin is verified by **certified
computation** (§8). The minimizer is not a photo-finish: the best non-delta family known satisfies
`N · D → 4 log 4 = 5.545…`, conjectured to be the sharp runner-up constant.

**MSC 2020:** 94A17 (primary); 60E15, 42C10, 05D40, 65G20. The self-calibration fixed point appears to be
new; its nearest relatives are Littlewood ±1-polynomials and self-consistent-field equations.

---

## 2. Repository layout

```
walsh-delta/
├── paper/          Paper XII — the mathematics (md, tex, pdf)
├── lean/           Lean 4 + Mathlib formalization (see §3)
├── code/           the w1–w5 certified-computation programs (see §4)
├── receipts/       canonical outputs of w1–w5 (the "certificates")
└── README.md       this file
```

---

## 3. The Lean formalization (`lean/`)

A complete formalization of Paper XII in **Lean 4** against **Mathlib**. It builds cleanly
(`lake build`, 0 errors) and the definitions + every theorem *statement* are kernel-checked as
well-formed. **Nothing is claimed proved unless Lean accepts it**; the honesty marker is `#print axioms`.

### 3.1 What is proved

**Seven of the eight modules are entirely `sorry`-free and kernel-verified.** The headline

```lean
theorem theorem_1_2 (hn : 2 ≤ n) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε)
```

is proved by case-splitting on `n` into the analytic half (`n ≥ 6`) and the certified half (`2 ≤ n ≤ 5`).
**Everything except the small-`n` finite computation is machine-checked with no `sorryAx`**, including:

| Module | Paper | Status | Highlights |
|---|---|---|---|
| `Basic` | §1–2 | ✅ complete | objects; **Pinsker (Lemma 2.1)** `E_U\|X−1\| ≤ √(2D)` |
| `Calibration` | §3 | ✅ complete | **Theorem 3.1**: `G_ε` smooth + strictly convex + coercive ⇒ unique calibrated law. Convexity via two-point **Hölder**; coercivity via a sphere-compactness lower bound; existence/uniqueness of the minimizer |
| `Delta` | §4 (Prop 4.1) | ✅ complete | the two-level delta law; `Lemma 4.2` (`0 < D_δ < 1/(N−1)`); the closed form and asymptotics |
| `Symmetry` | §3 (Lem 3.2–3.3) | ✅ complete | translation + `GL(n,2)` covariance of the calibrated law |
| `Trichotomy` | §5–6 | ✅ complete | the dip/bulk/spike apparatus; the spectral floor; **Theorem 6.1 (deep-dip trichotomy)** |
| `AnalyticMain` | §7 | ✅ complete | **Theorem 7.1**, the `n ≥ 6` main theorem, and Corollary 1.3 |
| `Main` | §1 | ✅ complete | **Theorem 1.2** assembled + Corollary 1.3 |
| `Certified` | §8 | ⚠ 3 leaves | **all support machinery done** (Newton–Kantorovich `lemma_8_1`/`8_2`, the spectral `opNorm_le_trace_of_psd`, the `Γ_n`-orbit-reduction interface); only the raw finite computation remains |

The **tight numeric constants** (`2.878716`, `1.244163`, `64/63`) are discharged by *exact interval
arithmetic* on Mathlib's `exp_one_gt_d9` / `log_two,three,five_gt_d9` bounds — **never `native_decide`**.

### 3.2 What is not proved: the 3 remaining leaves

The only `sorry`s left are the **certified finite computation** of §8, all in `Certified.lean`:

- **`theorem_8_3`** — for `2 ≤ n ≤ 5`, every orientation satisfies `m̂(ε) ≥ D_δ`. This bounds a
  *transcendental* `m̂(ε)` for every orientation, so it is not decidable; it needs the per-orbit
  interval-arithmetic certification that the code in `code/` performs.
- **`orbitCount_five`** (`= 176`) — a breadth-first search over the `2³¹ ≈ 2×10⁹` orientations.
- **`orbitCount_low`** — the `n = 2, 3, 4` cross-checks (2, 4, 14 orbits).

These are the parts the paper runs **by machine** (`code/`, receipts `w1`–`w5`). Formalizing them *inside
Lean* — without `native_decide`, which this project deliberately forbids — requires reflecting a verified
BFS and interval-certificate checker into the kernel: a separate infrastructure project. The Lean side
therefore proves the entire *mathematical reasoning* of Paper XII and isolates the residue as one
well-specified, machine-checkable-by-computation claim, discharged externally by `code/`.

### 3.3 Building and checking the Lean proof

Requirements: [`elan`](https://github.com/leanprover/elan) (the Lean toolchain manager). The toolchain
(`leanprover/lean4:v4.32.0-rc1`) and Mathlib version are pinned in `lean-toolchain` / `lake-manifest.json`.

```bash
cd lean
lake exe cache get      # download the prebuilt Mathlib oleans (recommended; else it compiles Mathlib)
lake build              # builds the whole library: 0 errors
```

**Verify the honesty of the headline theorem** — this is the single most important check:

```bash
lake env lean -c 'import WalshDelta
#print axioms WalshDelta.theorem_1_2'
--  [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` is expected and honest: it flags that `theorem_8_3` (the finite computation) is still a
`sorry`. Every *other* result is clean — e.g. these print only `[propext, Classical.choice, Quot.sound]`:

```bash
#print axioms WalshDelta.deep_dip_trichotomy   -- Theorem 6.1
#print axioms WalshDelta.main_analytic         -- Theorem 7.1 (n ≥ 6)
#print axioms WalshDelta.pinsker               -- Lemma 2.1
#print axioms WalshDelta.lemma_8_1             -- Newton–Kantorovich radius
#print axioms WalshDelta.reduce_to_transversal -- the orbit-reduction interface
```

See `lean/STATUS.md` (current state + axiom transparency), `lean/SORRIES.md` (the leaf-by-leaf ledger), and
`lean/BLUEPRINT.md` (module graph + name↔paper mapping).

---

## 4. The certified computation (`code/` + `receipts/`)

This is the external half of §8 — what `theorem_8_3` / `orbitCount_*` assert, computed and certified. All
numeric verification uses **a posteriori Newton–Kantorovich error certificates** with high-precision
(`mpmath`) re-evaluation; the orbit reduction is verified two independent ways (a completeness-checksummed
BFS and an independent Burnside count).

| receipt | file | what it certifies | output |
|---|---|---|---|
| **w1** | `w1_cert_small_n.py` | **exhaustive** check of `n = 2, 3, 4` — *every* orientation (8, 128, 32768) | `receipts/w1_cert_small_n.out` |
| **w2** | `w2_orbit_bfs.c` | the complete `Γ_n`-**orbit partition** by BFS (checksum: sizes sum to `2^{N−1}`) | `w2_orbit_bfs.out`, `w2_orbits_n5.txt` (176 orbits) |
| **w3** | `w3_cert_n5.py` | `n = 5` via the **176-orbit transversal** (one certified rep per orbit) | `w3_cert_n5.out` |
| **w4** | `w4_family_receipt.py` | the analytic §5–6 inequalities on low-entropy families + the `N·D → 4log4` table | `w4_family_receipt.out` |
| **w5** | `w5_burnside.c` | an **independent** Burnside-lemma orbit count (cross-checks w2) | `w5_burnside.out` |

### 4.1 The logic of the certificate

- **`n ≤ 4` (w1):** brute force over all `2^{N−1}` orientations. For each: float64 damped Newton on the
  strictly convex `G_ε` → `ℓ̃`; then an `mpmath` re-evaluation gives the residual `ρ`, the Hessian floor
  `λ`, and the value `D̃`; **Lemma 8.1** bounds `‖ℓ⋆ − ℓ̃‖ ≤ r₀ = 2eρ/λ`; **Lemma 8.2** transfers this to
  `|D(ℓ⋆) − D̃| ≤ (N−1)(‖ℓ̃‖ + r₀)r₀`; a non-delta `ε` is certified when `D̃ − εD > D_δ` (with `D_δ`
  sign-bracketed to 60 digits). Worst certified margins: **0.462** (`n=3`), **0.264** (`n=4`).
- **`n = 5` (w2 + w3):** `2³¹` orientations are impossible to enumerate directly, so **symmetry** reduces
  it. `D(ε)` is invariant under the group `Γ_n = ⟨translations⟩ ⋊ GL(n,2)` (this is `Symmetry.lean`,
  proved in Lean), so certifying **one representative per orbit** certifies all `2³¹`. The BFS (`w2`)
  produces the **provably complete** 176-orbit partition (completeness = orbit sizes sum to `2³¹`); `w3`
  certifies each of the 176 reps as in w1. Worst certified non-delta margin: **0.1389**; max entropy error
  `9×10⁻³³`.
- **Cross-check (w5):** an entirely independent Burnside count
  `#orbits = (1/(2ⁿ|GL(n,2)|)) Σ_M 2^{c(M)+n−r(M)}` reproduces **2, 4, 14, 176** for `n = 2,3,4,5`.

### 4.2 Running it

```bash
cd code

# w1 — exhaustive n ≤ 4  (needs: python3 + numpy + mpmath)
python3 w1_cert_small_n.py            # → "ALL CERTIFIED"

# w2 — orbit BFS  (n = 2..5; writes the 176-orbit partition used by w3)
cc -O2 -o w2_orbit_bfs w2_orbit_bfs.c
./w2_orbit_bfs 5 > ../receipts/w2_orbits_n5.txt   # 176 lines: "rep size"

# w3 — n = 5 via the 176 orbits  (reads ../receipts/w2_orbits_n5.txt)
python3 w3_cert_n5.py                 # → per-orbit certified margins

# w4 — analytic families + N·D → 4log4 table
python3 w4_family_receipt.py          # → "ALL CHECKS PASS"

# w5 — independent Burnside orbit count
cc -O2 -o w5_burnside w5_burnside.c
./w5_burnside                         # → n=2:2  n=3:4  n=4:14  n=5:176  (all "OK")
```

The canonical outputs are checked into `receipts/`; re-running should reproduce them.

**Numerical note (load-bearing, per w4):** depths reach `β ~ N·log(N/4)` (e.g. `X ~ e⁻⁵⁷⁰⁰` at `n=10`),
far below float64 underflow, so all depth-dependent quantities are computed in the **log domain**
(`logX = log N + field − logsumexp(field)`); exponentiating and re-logging silently corrupts every depth.

---

## 5. Trust base (honesty)

- **Analytic part (`n ≥ 6`)** — fully self-contained and, in the Lean formalization, **kernel-verified with
  no `sorryAx`** (Theorem 6.1 ⇒ Theorem 7.1).
- **Certified part (`n ≤ 5`)** — reduced to a finite computation with rigorous a-posteriori
  Newton–Kantorovich certificates. In the paper this is receipts `w1`–`w5`; in Lean it is the 3 remaining
  `sorry` leaves. The remaining formalization gap is exactly *reflecting that finite computation into the
  Lean kernel* (directed-rounding interval arithmetic + a verified BFS), which the paper flags as the
  computer-assisted portion. No step uses `native_decide`.
- **Reproducibility** — the Lean toolchain and Mathlib are pinned; the certificate code is deterministic
  and its canonical outputs are committed.

---

## 6. Citation & license

If you use this work, please cite Paper XII (see `paper/`). Licensed under the terms in
[`LICENSE`](LICENSE).

> *Felix Robles Elvira, "The delta orientation is the unique entropy minimizer for self-calibrated ±1 Walsh
> tilts on the Boolean cube," 2026.*
