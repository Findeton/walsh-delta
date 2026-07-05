# Walsh–delta formalization — blueprint & status

**Project:** a Lean 4 + Mathlib formalization of paper XII, *"The delta orientation is the unique entropy minimizer for self-calibrated ±1 Walsh tilts on the Boolean cube"* (`/Users/felixrobles/workspace/shard/papers/paper-XII-walsh-delta.md`).
**Lean code root:** `/Users/felixrobles/workspace/shard/lean/` (`WalshDelta.lean` + `WalshDelta/{Basic,Calibration,Symmetry,Delta,Trichotomy,AnalyticMain,Certified,Main}.lean`).
**Toolchain declared:** `leanprover/lean4:v4.21.0`, Mathlib pinned by git rev (the `rev` field in `lakefile.toml` is a `<pin-me>` placeholder — not yet fixed).
**Document date:** 2026-07-03.

## 1. What is being formalized, and a strict honesty disclaimer

The goal is a machine-checked proof of **Theorem 1.2** of paper XII: over the Boolean cube `G = {±1}ⁿ` (`N = 2ⁿ`), among all `2^{N−1}` sign choices ("orientations") for the nonzero Walsh characters, the self-calibrated exponential-family law `P_ε` has relative entropy `m̂(ε) = D(P_ε ‖ U)` minimized exactly (and only) on the `N` delta orientations `ε⋆_a = −χ_a(s⋆)`. The formalization encodes the objects (calibrated law, entropy integrand `ψ`, the convex objective `G_ε`), the existence/uniqueness theorem (3.1), the two symmetry covariances (3.2/3.3), the closed-form delta law (4.1) and its bound (4.2), the deep-dip trichotomy (6.1), the analytic closure for `n ≥ 6` (7.1, Cor 1.3), and the certified `2 ≤ n ≤ 5` leg (Lemmas 8.1/8.2, Thm 8.3 via the 176-orbit `Γ₅` transversal), assembled in Thm 1.2.

**STRICT HONESTY DISCLAIMER.** What exists today is an **uncompiled skeleton**. Every mathematically substantive proof is a `sorry` leaf (currently **97 `sorry`s** across the modules: Basic 8, Calibration 14, Symmetry 9, Delta 21, Trichotomy 16, AnalyticMain 8, Certified 21, Main 0). It has **never been built against Mathlib** in the authoring environment (no Lean toolchain was present; the Mathlib revision is not even pinned). Beyond the `sorry`s, the skeleton does **not currently elaborate as an assembled whole**: each module was written to be independently readable, so several modules *re-declare* their upstream dependencies (`mhat`, `IsDelta`, `Ddelta`, `calLaw`/`Pcal`, `calibrated_exists_unique`, `deep_dip_trichotomy`, `transOrient`/`tau`, …) as local `sorry`-ed statements inside the *same* `namespace WalshDelta`. `mhat`, `IsDelta`, and `Ddelta` alone are each defined in **six** files. Consequently:
- The root `WalshDelta.lean`, which `import`s all eight modules, would fail with duplicate-declaration errors.
- `Main.lean` imports `Delta`, `AnalyticMain`, `Certified` (mutually colliding definitions) **and** references names that do not exist under those spellings in the imported files — e.g. `theorem_7_1` and `mhat_floor` (AnalyticMain actually exports `main_analytic` and `corollary_1_3`) and `Ddelta_lt_inv` (Delta/AnalyticMain export `Ddelta_lt`). So `Main.lean` would not even type-check against the current imports.

Therefore: **"bug-free" / "verified" is a status this project has NOT reached.** It is reached only when `lake build` succeeds with **zero `sorry`** and **zero `axiom`** (checked, e.g., with `#print axioms theorem_1_2` showing only the standard `propext, Classical.choice, Quot.sound`). *Until then, the only content that has real force is the mathematical faithfulness of the `theorem`/`def` **statements** — and even those must be audited, because a `sorry`-ed statement can be trivially true or subtly wrong.* When (and only when) it compiles cleanly, the trust base becomes exactly:

> **Lean 4 kernel  +  Mathlib (as an axiom base)  +  the faithfulness of the top-level *statements*** (that `Calibrated`, `mhat`, `deltaOrientation`, `Dkl`, `IsDelta`, and Thm 1.2's phrasing actually mean what paper XII means).

No compilation ⇒ no verification. This document is a map of the work, not a certificate.

## 2. Module dependency graph

Two graphs matter, and they currently disagree.

**(a) Intended logical DAG** (what the mathematics requires; the target once the re-declared interfaces are deduplicated into real cross-module `import`s):

```
                         Basic
        (Point, chi, Orientation, deltaOrientation,
         ProbLaw, EU/EP/dens/xhat, psi, Dkl, pinsker,
         tilt, Calibrated)
          |        |         |            |
          v        v         v            v
     Calibration  Symmetry  Delta      Trichotomy
      (Thm 3.1)  (Lem 3.2/  (Prop 4.1, (Sec 5 apparatus,
          |       3.3)       Lem 4.2)    Thm 6.1)
          |        |          |            |
          +--------+----+-----+------------+
                        |          |
                        v          v
                    AnalyticMain   Certified
                     (Thm 7.1,      (Lem 8.1/8.2,
                      Cor 1.3)       Thm 8.3, Γ₅ orbits)
                        |          |
                        +----+-----+
                             v
                            Main
                    (Thm 1.2, Cor 1.3 assembled)
```
Logical edges: `Calibration` ← Basic; `Symmetry` ← Basic (+Thm 3.1's uniqueness, carried abstractly via `IsCalAssignment`); `Delta` ← Basic + Thm 3.1 + Lem 3.2; `Trichotomy` ← Basic + Thm 3.1 (+ Lem 5.1 uses `pinsker`); `AnalyticMain` ← Delta (Lem 4.2) + Trichotomy (Thm 6.1) + Symmetry (Lem 3.2); `Certified` ← Basic + Thm 3.1 + Symmetry; `Main` ← AnalyticMain + Certified + Delta.

**(b) Actual current `import` graph** (what the files literally declare):

```
Basic        : import Mathlib
Calibration  : import Mathlib, WalshDelta.Basic
Symmetry     : import Mathlib, WalshDelta.Basic
Delta        : import Mathlib, WalshDelta.Basic
Trichotomy   : import Mathlib, WalshDelta.Basic
AnalyticMain : import Mathlib, WalshDelta.Basic          (NOT Delta/Trichotomy/Symmetry)
Certified    : import Mathlib, WalshDelta.Basic
Main         : import Mathlib, Basic, Delta, AnalyticMain, Certified
WalshDelta   : imports all eight
```
Every module pulls the whole of `Mathlib` (no fine-grained imports) and depends only on `Basic`, re-proving its upstream lemmas locally as `sorry`. The middle layer (`Calibration`, `Symmetry`, `Delta`, `Trichotomy`) never imports one another. **Reconciling (b) into (a) — deleting the duplicated interface stubs, wiring real imports, and fixing the dangling `Main` references — is itself a required (and non-trivial) task on the completion plan (§6, Phase 0).**

## 3. Paper-statement ↔ Lean-name mapping

Names below are the identifiers currently present (namespace `WalshDelta`). Where a statement is (re)declared in several modules, the **canonical** home is listed first; duplicates are flagged.

| Paper statement | Lean declaration(s) | File | Status |
|---|---|---|---|
| Def 1.1 (calibrated law) | `Calibrated` (Prop); `tilt`; `CalibratedWith` (named params) | Basic; Basic; Trichotomy | stated |
| Lemma 2.1 (Pinsker) | `pinsker` | Basic | `sorry` |
| Lemma 2.2 (integrand `ψ`) | `psi`, `psi_one`, `psi_hasDerivAt`, `psi_nonneg`, `psi_strictAntiOn`, `psi_strictMonoOn`, `Dkl`, `Dkl_eq_EU_psi` | Basic | mix (`psi_hasDerivAt` proved; rest `sorry`) |
| Def of `m̂(ε)` | `mhat` | Calibration (dup: Symmetry, Delta, AnalyticMain, Certified) | stated |
| Thm 3.1 (existence/uniqueness) | `theorem_3_1` (+ `Gfun`, `Gfun_strictConvexOn`, `Gfun_coercive`, `critical_iff_calibrationEqs`, `calibrated_exists_unique`, `calLaw`) | Calibration | `sorry` leaves |
| ” restated interface | `exists_unique_calibrated`; `calibrated_exists_unique`; `exists_unique_minimizer` | Delta; AnalyticMain; Certified | `sorry` (to merge) |
| Lemma 3.2 (translation covariance) | `translation_covariance_law`, `translation_covariance_mhat`, `delta_translation`, `delta_single_translation_orbit` | Symmetry | `delta_translation` proved; rest `sorry` |
| ” restated | `calLaw_tauOrient`,`mhat_tauOrient`; `translation_covariance`,`tau_deltaOrientation`; `mhat_transOrient` | Delta; AnalyticMain; Certified | `sorry` |
| Lemma 3.3 (GL(n,2) covariance) | `glAction_covariance_law`, `glAction_covariance_mhat`, `delta_glAction`, `GLn`, `glOrient` | Symmetry | `sorry` (`glOrient` etc. defined) |
| ” restated | `mhat_glOrient`, `glOrient`, `maskMap` | Certified | `sorry` |
| Γₙ corollary (one orbit) | `gammaAct`, `mhat_gamma_invariant`, `delta_gamma_transitive`, `delta_gamma_closed` | Symmetry | `mhat_gamma_invariant`/transitive/closed proved from `sorry` lemmas |
| Prop 4.1 (delta law) | `deltaPoly`, `uStar_exists_unique`, `uStar`, `deltaLaw`, `dens_deltaLaw`, `calibrated_deltaLaw`, `calLaw_deltaOrientation`, `Ddelta_closedForm` | Delta | `sorry` leaves (`deltaPoly_zero`, `dens_deltaLaw` proved) |
| Lemma 4.2 (delta bound) | `Lemma_4_2` (= `Ddelta_pos` ∧ `Ddelta_lt`); `N_Ddelta_tendsto_one` | Delta | `sorry` |
| ” restated | `Ddelta_lt` | AnalyticMain | `sorry` |
| §5 apparatus | `dipSet/bulkSet/spikeSet`, `depth`, `dipTransform`, `logXhat`, `epsG`, `hPrime`, `hMin`, `parameter_floor` (Lem 5.1), `bookkeeping` (Lem 5.2), `spectral_floor` (Prop 5.3), `dominance_criterion` (Prop 5.4) | Trichotomy | `sorry` (defs + `psi_half`, `psi_exp_neg5` proved) |
| Thm 6.1 (deep-dip trichotomy) | `deep_dip_trichotomy` (+ `deepDipCount_ne_zero/one/two`, `deepDipCount_ge_three`, `shallowDepthSum_lt`) | Trichotomy | `deepDipCount_ge_three` proved from `sorry` cases |
| ” restated | `deep_dip_trichotomy` | AnalyticMain | `sorry` |
| Thm 7.1 (`n ≥ 6`) | `main_analytic` | AnalyticMain | **proof body complete** modulo the interface `sorry`s + numeric lemmas it calls |
| Cor 1.3 (quantitative floor) | `corollary_1_3` | AnalyticMain **and** Main | proof bodies present; rest on `sorry` upstream |
| Lemma 8.1 (a-posteriori radius / NK) | `lemma_8_1` | Certified | `sorry` |
| Lemma 8.2 (entropy transfer) | `lemma_8_2_transfer` (+ `lemma_8_2_grad`, `lemma_8_2_opNorm`, `opNorm_le_trace_of_psd`, `covMatrix_le_secondMoment`, `trace_secondMomentMatrix_eq`) | Certified | `lemma_8_2_opNorm` assembled from `sorry`s; `trace` proved |
| Thm 8.3 (`2 ≤ n ≤ 5`, certified) | `theorem_8_3` (+ `reduce_to_transversal`, `CompleteTransversal`, `orbitCount_five = 176`, `theorem_8_3_n5_via_176_orbits`) | Certified | `reduce_to_transversal` proved; `theorem_8_3`, orbit counts `sorry` |
| Cor 1.3 (as in §1.2) | `corollary_1_3` | Main | proof body present |
| **Thm 1.2 (main theorem)** | `theorem_1_2` (+ `mhat_ge_Ddelta`, `mhat_delta_lt_of_not_isDelta`) | Main | **proof body complete**, resting entirely on the (renamed/`sorry`) upstream API |

Reading note: several *high-level assembly proofs are already written and would compile* the moment their inputs are real — `main_analytic`, `theorem_1_2`, `corollary_1_3`, `reduce_to_transversal`, `deepDipCount_ge_three`, `mhat_gamma_invariant`. The `sorry`s are concentrated at (i) the analytic leaves and (ii) the certified-computation leaf.

## 4. The two hard formalization frontiers

### (a) The analytic `n ≥ 6` quantitative inequalities

The `n ≥ 6` closure (`main_analytic`) reduces cleanly to a handful of **transcendental numeric facts** and the **convex-analysis backbone**. The numeric facts are the genuine obstruction, because Lean must reason about `e^{−5}`, `log 30`, `√(1/30)`, `√(2D)` *rigorously*, not by floating-point evaluation. The load-bearing statements:

- `hPrime_gt : (1.244163 : ℝ) < (1/2)·log 30 − (5/2)·√(1/30)` (Prop 5.3(ii));
- `three_psi_exp_neg5_gt : (2.878716 : ℝ) < 3(1 − 6·e^{−5})` (Thm 6.1);
- `psi_nonneg`, `psi_strictAntiOn`, `psi_strictMonoOn` — sign/monotonicity of `ψ(x)=x log x − x + 1` via `ψ' = log`;
- `parameter_floor` and `spectral_floor` — Pinsker `|x_a| ≤ √(2D)` ⇒ `h_a ≥ ½log(1/2D) ≥ ½log 30 > 1.70059`, and the `¾√(2D)`-vs-floor comparison whose worst case is pinned at `D = 1/60`.

The intended discipline (stated in the source comments): discharge each constant by a **certified rational enclosure** of the transcendental — e.g. bound `e^{−5}` between explicit rationals using Mathlib's `Real.add_one_le_exp` / `Real.exp_bound` / truncated-series bounds, bound `log 30` and `√(1/30)` via `Real.log`/`Real.sqrt` monotonicity and `Real.log_le_sub_one_of_pos`-type inequalities, then close with `nlinarith`/`polyrith` on rationals. This is exactly where "safe rounding" in the paper (lower bounds rounded down, upper bounds up) becomes a Lean obligation: the margins (`2.878716` vs `64/63 ≈ 1.01587`, a `2.8×` gap) are comfortable, so *tight* enclosures are not needed — but *sound* directed enclosures are mandatory. Real risk items here: (1) the convexity/coercivity of `G_ε` (Thm 3.1) needs `∇²F = Cov_{P_ℓ}(χ) ⪰ 0` and the compactness/ray argument for coercivity, then Fermat's interior-minimum theorem — none of which Mathlib packages as a single lemma for a log-partition function; (2) Pinsker itself (see §5); (3) the covariance/Hessian identities are real multivariable-calculus proofs, not one-liners.

### (b) The certified `2 ≤ n ≤ 5` computation

`theorem_8_3` is the paper's computer-assisted leg, and formalizing it is the single largest and highest-risk piece. Two independent hard requirements:

**Exact / interval arithmetic (not floats).** Paper §8.5 is explicit that the shipped computation uses *round-to-nearest* multiple-precision floats (mpmath, 30–60 digits), and that a fully formal proof "would substitute outward-rounded interval arithmetic throughout — a mechanical upgrade that we have not performed." In Lean this means the Newton–Kantorovich certificate must be carried in exact `ℚ` (or a verified interval type). The two certificate lemmas are already stated: `lemma_8_1` (a-posteriori radius `‖ℓ⋆ − ℓ̃‖₂ ≤ r₀ = 2eρ/λ` from gradient residual `ρ` and curvature floor `λ`; proved in the paper by a convexity monotonicity argument on `g(t) = ⟨∇G_ε(ℓ̃+tv), v⟩`, an alternative to a literal Banach/contraction framing) and `lemma_8_2_transfer` (entropy transfer `|𝒟(ℓ⋆) − 𝒟(ℓ̃)| ≤ (N−1)(‖ℓ̃‖₂ + r₀)r₀`, needing `‖∇²F‖_op ≤ N−1` via `Cov ⪯ 𝔼[χχᵀ]` and op-norm ≤ trace). To *use* these one must evaluate `∇G_ε(ℓ̃)`, `λ`, and the delta bracket at rational witnesses for every representative and check the certified enclosure beats `D_δ` — i.e. embed a small verified linear-algebra + interval kernel and run it reflectively. The `Γ₅` reduction (`reduce_to_transversal`, `CompleteTransversal`) means the check is over **176 representatives**, not `2^{31}` orientations — but each of the 176 carries a full `N−1 = 31`-dimensional certified solve, and `n ≤ 4` is a genuinely exhaustive `8 / 128 / 32768`-orientation sweep. The transversal's **completeness** is a second proof obligation: `CompleteTransversal.checksum` (`∑ orbit sizes = 2^{N−1}`) plus `orbitCount_five = 176`, cross-checked by the Burnside count. Note the current `CompleteTransversal` is stated but *no witnessing 176-element `Finset` is constructed* — building it and proving `covers`/`checksum` is open.

**Why `native_decide` is deliberately avoided.** Both `Trichotomy` and `Certified` state, in their headers and per-lemma comments, that the finite/numeric facts "are to be discharged by exact rational interval arithmetic, **never by `native_decide`**." The reasons are trust-base and soundness: `native_decide` compiles the decision procedure to native code and trusts the compiler's output via the `Lean.ofReduceBool` axiom, **adding the Lean compiler + the `Decidable` instance's runtime to the trusted base and bypassing the kernel** — precisely the enlargement of the trust base that §1's disclaimer promises not to make. It has also historically been a source of unsoundness incidents (miscompiled `Decidable` instances, `#eval`/kernel disagreements). Since the whole point of the formal upgrade is to *shrink* the trust base to "kernel + Mathlib + statements," the computation must be either (i) kernel-reducible `Decidable`/`decide` over `ℚ` (feasible only for the tiny `n ≤ 3` cases), or (ii) a reflective proof whose steps the kernel re-checks (a verified interval-arithmetic evaluator proven correct in Lean, à la `Mathlib`'s `norm_num` extensions / `Polyrith` / the `interval` line of work), with the 176-representative data supplied as verified rational literals. Even `decide` at `n = 4, 5` will be performance-prohibitive without a purpose-built verified kernel; this is the crux engineering problem of the whole project.

## 5. Mathlib pieces this leans on

- **Convex analysis:** `ConvexOn`, `StrictConvexOn`, `IsMinOn`, uniqueness of minimizer of a strictly convex coercive function, Fermat interior-critical-point (`IsLocalMin.deriv_eq_zero` / `HasDerivAt` at a minimizer). Convexity of the log-partition (cumulant) function is *not* a ready Mathlib lemma and must be built from `∇²F = Cov ⪰ 0` (`InnerProductSpace`, `Matrix.PosSemidef`).
- **`Real.log` / `Real.exp` calculus and bounds:** `Real.hasDerivAt_log`, `Real.log_exp`, `Real.exp_log`, `Real.log_le_sub_one_of_pos` (drives `log(1+x) ≤ x` and `|log x| ≤ 2|x−1|` on `[½,2]`), `Real.add_one_le_exp`, `Real.exp_bound`/series tails for certified enclosures of `e^{−5}`, `Real.sqrt` monotonicity for `√(1/30)`. The entropy integrand connects to `Real.negMulLog` (`= −x log x`) and Mathlib's `Real.negMulLog`-based entropy API.
- **Pinsker / KL divergence:** Mathlib's information-theory / `ProbabilityTheory` measure-theoretic KL (`klDiv`) and, in recent revisions, a Pinsker-type bound. Whether the *finite, uniform-reference* form `E_U|X−1| ≤ √(2D)` is directly citable or must be reproved from convexity of `x ↦ x log x` is an open API question — flagged in `Basic.pinsker`'s own `TODO`. The safe assumption is: **reprove Pinsker for the finite cube** from `negMulLog` convexity rather than depend on the measure-theoretic library matching this normalization.
- **Newton–Kantorovich core:** the paper's `lemma_8_1` proof is a monotonicity argument (`g(t)` nondecreasing) leaning on the strict-convexity Hessian floor, needing `Cauchy–Schwarz` (`inner_mul_le_norm_mul_norm`) and the segment-convexity API. An alternative framing uses Mathlib's inverse-function theorem (`HasStrictFDerivAt.localInverse`, `ContDiffAt` inverse) or `ContractingWith`/`Banach` fixed point — available but heavier; the convexity route in the source is likely the shorter path.
- **Op-norm ≤ trace (Lemma 8.2):** the Hermitian spectral theorem `Matrix.IsHermitian.spectral_theorem`, eigenvalue nonnegativity for PSD (`Matrix.PosSemidef.eigenvalue_nonneg`), and `Matrix.trace = ∑ eigenvalues`. Explicitly called out in `opNorm_le_trace_of_psd` as "not short in Lean."
- **Finite group actions & orbit counting (Γ₅ transversal):** `Matrix.GeneralLinearGroup (Fin n) (ZMod 2)`, `Matrix.mulVec`/`vecMul`/`transpose` adjunction, `ZMod 2`/`CharTwo` (`CharTwo.add_self_eq_zero`), `LinearEquiv` for the mask relabeling, `EqvGen`/`Quot` for orbit equivalence, `Nat.card`, `Fintype.card_pi`/`card_subtype_compl` for `|NonzeroMask| = N−1` and `|Orientation| = 2^{N−1}`, and (for the Burnside cross-check) `MulAction`/`Finset` orbit-stabilizer / Burnside-lemma API.
- **Entropy / `negMulLog`:** `Real.negMulLog`, its convexity and continuity lemmas, for both `ψ` and the KL functional.

## 6. Completion plan, effort estimate, and how to contribute

**Phase 0 — make it a single compiling `sorry`-project (foundational, do first).** Pin Mathlib `rev` + matching `lean-toolchain`; `lake exe cache get && lake build`. Deduplicate the re-declared interfaces (choose canonical homes: Thm 3.1 in `Calibration`, Lem 3.2/3.3 in `Symmetry`, Prop 4.1/Lem 4.2 in `Delta`, Thm 6.1 in `Trichotomy`), replace the local stubs with real `import`s, and fix `Main`'s dangling references (`theorem_7_1`→`main_analytic`, `mhat_floor`→the Cor-1.3 floor, `Ddelta_lt_inv`→`Ddelta_lt`). Target: `lake build` green with `sorry`s only (no elaboration errors, no name clashes). *Estimate: ~1–2 weeks.* This is a prerequisite for everything else and is currently blocking.

**Phase 1 — Basic + `ψ` + Pinsker.** Discharge `card_point`, `chi_add`, `xhat_dens_eq_EP`, `Dkl_eq_EU_psi`, `psi_nonneg`/mono, and `pinsker`. Pinsker is the schedule risk. *~3–5 weeks.*

**Phase 2 — Thm 3.1 (convex backbone).** `logPartition_convexOn`, `Gfun_strictConvexOn`, `Gfun_coercive`, gradient identities, `calibrated_exists_unique`. Heaviest analysis chunk. *~1.5–3 months.*

**Phase 3 — Symmetry (Lem 3.2/3.3) + Delta (Prop 4.1/Lem 4.2).** Mostly algebra + one IVT/monotonicity root argument; the `GL(n,2)` covariances need the matrix-adjunction lemmas. *~1–2 months.*

**Phase 4 — Trichotomy (§5–6) + analytic numeric constants.** `parameter_floor`, `bookkeeping`, `spectral_floor`, `dominance_criterion`, the three trichotomy cases, and the certified-constant lemmas (`hPrime_gt`, `three_psi_exp_neg5_gt`). With Phases 1–3 done, `main_analytic`/`corollary_1_3`/`theorem_1_2` fall out. *~2–3 months.* **`n ≥ 6` is fully closed at the end of this phase.**

**Phase 5 — Certified `n ≤ 5` (the crux).** Build/verify an exact-`ℚ`/interval evaluator; prove `lemma_8_1`, `lemma_8_2_*` (incl. spectral op-norm≤trace); construct the 176-element `Γ₅` transversal `Finset` with `covers` + `checksum`; prove `orbitCount_five = 176` and the Burnside cross-check; run the reflective certification for `n ≤ 4` exhaustively and `n = 5` over the transversal, all without `native_decide`. Highest risk (both proof-engineering and kernel-performance). *~4–9 months*, and the dominant cost/uncertainty of the whole project.

**Overall:** a realistic, sober estimate for one experienced Lean/Mathlib contributor is **~12–24 months of focused work**, back-loaded onto Phase 5. `n ≥ 6` alone (Phases 0–4) is a self-contained, lower-risk milestone (~6–9 months) worth landing first, since it is the analytically complete half and yields a genuine partial theorem.

**How to contribute (blueprint-driven, PFR-style).** Adopt the Polynomial Freiman–Ruzsa (`leanprover-community/pfr`) workflow: a `leanblueprint`-generated dependency web mirroring §2's DAG, with each node a `\lean{...}` declaration tracked green/`sorry`/blocked, so contributors can claim leaf nodes independently. Coordinate on the Lean **Zulip** (`#new members`, `#maths`, `#Is there code for X?` — especially for the Pinsker API question in §5 and the interval-arithmetic/reflection strategy for Phase 5). Concrete on-ramps, in rising difficulty: the finished-assembly consistency audit (Phase 0); the algebraic `Basic`/`Symmetry` leaves; the certified-constant enclosures (Phase 4, `norm_num`-extension-friendly); then the Phase 2 convex analysis and Phase 5 computation for veterans. Every merged leaf should be gated by CI running `lake build` and an axiom check (`#print axioms theorem_1_2`) so that "no new `sorry`, no `native_decide`, no stray axioms" is enforced mechanically — that gate is what eventually converts this skeleton's claims into verified ones.
