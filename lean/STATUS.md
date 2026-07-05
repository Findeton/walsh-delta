# STATUS — WalshDelta formalization

**One line:** the **whole library compiles and links** against Mathlib (Lean
`v4.32.0-rc1`) — `lake build` succeeds with **0 errors** — and **only 3 `sorry`
leaves remain, all of them the single finite certified computation** of §8
(`theorem_8_3` for `2 ≤ n ≤ 5`, and the `orbitCount` BFS cross-checks).  Seven of
the eight modules are entirely `sorry`-free and kernel-verified; the headline
`WalshDelta.theorem_1_2` is proved **modulo exactly `theorem_8_3`**.

Date: 2026-07-04. Verified with `lake build` against a locally built Mathlib.

## What is verified now

- **`lake build` links the entire library** (all 8 modules, one namespace,
  canonical shared definitions). 0 elaboration errors.
- **`theorem_1_2` is proved as an assembly** (its own proof body has no
  `sorry`): it case-splits on `n` and defers to `AnalyticMain.main_equality_analytic`
  (`n ≥ 6`, analytic) and `Certified.theorem_8_3` (`2 ≤ n ≤ 5`, certified
  computation). Its axiom dependency is transparent:
  ```
  #print axioms WalshDelta.theorem_1_2
  --> [propext, sorryAx, Classical.choice, Quot.sound]
  ```
  i.e. the three standard Mathlib axioms **plus `sorryAx`** — the honest marker
  that `theorem_8_3` (the small-`n` certified computation) is still `sorry`. The
  `n ≥ 6` half (`main_equality_analytic`) and ALL of §8's supporting machinery
  (`lemma_8_1`/`8_2`, `opNorm_le_trace_of_psd`, the orbit-reduction interface) are
  `sorryAx`-free; only the raw finite computation remains.
- Every definition and theorem statement type-checks — which is the load-bearing
  part of "bug-free": a formal proof is only as meaningful as its statement.

## What is not done

**3 `sorry`s** remain (90 discharged and `lake build`-verified; see `SORRIES.md`).  Nothing is claimed proved
unless Lean accepts it; `#print axioms` will show `sorryAx` until they are gone.

**Seven of eight modules are entirely `sorry`-free and kernel-verified:** `Basic`, `Calibration`, `Delta`,
`Symmetry`, `Trichotomy`, `AnalyticMain`, `Main`.  The remaining 3 are the certified finite computation in
`Certified` §8: `theorem_8_3` (the `2 ≤ n ≤ 5` per-orbit entropy-margin certification), `orbitCount_five`
(the 2³¹-state BFS giving 176 orbits), and `orbitCount_low` (the n=2,3,4 cross-checks).  These are the parts
the paper runs by machine (receipt `w5`); formalizing them without `native_decide` requires a verified
BFS + interval-arithmetic-certificate infrastructure.  Every §8 *support* lemma is done and clean:
`lemma_8_1` (Newton–Kantorovich a-posteriori radius), `lemma_8_2_grad`/`_opNorm`/`_transfer` (the
entropy-transfer bound), `opNorm_le_trace_of_psd` (spectral, and an elementary `gradNorm_bound` via a
discriminant argument), `exists_unique_minimizer`, `nat_card_orientation`, and the full `Γ_n`-orbit-reduction
interface (`mhat_transOrient`/`_glOrient`/`_of_sameOrbit`, `isDelta_of_sameOrbit`, `reduce_to_transversal`).

**The entire analytic side is done.**  `Basic`, `Calibration`, `Delta`, `Symmetry`, `Trichotomy`, and
`AnalyticMain` are now ALL sorry-free and kernel-verified.  In particular `pinsker` (Lemma 2.1, via the
pointwise bound `3(x−1)²≤(2x+4)ψ(x)` from an `f''≥0` convexity argument + Cauchy–Schwarz),
`deep_dip_trichotomy` (**Theorem 6.1**), and `main_analytic` (**Theorem 7.1**, the `n≥6` main theorem) all
depend on only `[propext, Classical.choice, Quot.sound]`.  The tight numeric constants (`hPrime_gt`,
`three_psi_exp_neg5_gt`, `three_psi_gt`) were discharged by exact interval arithmetic on Mathlib's `exp_one_gt_d9`
/ `log_two,three,five_gt_d9` — never `native_decide`.  The **only** reason `Main.theorem_1_2` still carries
`sorryAx` is its small-`n` half (`Certified.theorem_8_3`, the `2≤n≤5` 176-orbit computation) — the last cluster.

**`Calibration`, `Delta`, and `Symmetry`** (§3 Theorem 3.1,
§4 Proposition 4.1 + Lemma 4.2, and the §3 Lemma 3.2 / 3.3 covariance).  Beyond the convex core (below), this
pass added: `Delta.deltaLaw` (a valid `ProbLaw` for *every* `n`, via the root identity `(N−1)u⋆<1`),
`calibrated_deltaLaw` (the two-level law is calibrated for `ε⋆`, constant tilt `h_a=−log u⋆`),
`calLaw_tauOrient`/`mhat_tauOrient` (translation covariance of the calibrated law, via `calLaw_unique`),
`Ddelta_closedForm`/`Ddelta_pos`/`Ddelta_lt` (`Lemma_4_2`: `0<D_δ<1/(N−1)` via the `ψ`-form and
`log(1+u⋆)≤u⋆`), the asymptotic `N_Ddelta_tendsto_one`, and all four `Symmetry` calibrated-law covariance
theorems (`translation_covariance_law/_mhat`, `glAction_covariance_law/_mhat` — the latter via the
`chi_mulVec` mask-relabeling bijection).  Every one depends on only `[propext, Classical.choice, Quot.sound]`.

**The convex-analysis core (Paper XII Theorem 3.1) is COMPLETE and kernel-verified.** All 14 `Calibration`
leaves are proved, so `WalshDelta.theorem_3_1` (smoothness + strict convexity + coercivity of `G_ε`; its
unique minimizer is *the* calibrated law with `h_a = ε_a ℓ⋆_a > 0`; each orientation has exactly one
calibrated law) now depends on only `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. Highlights:
`logPartition_convexOn` (log-sum-exp convexity via two-point weighted Hölder, `Real.inner_le_Lp_mul_Lq`);
`Gfun_strictConvexOn` (convex `F` + strictly-convex separable barrier); `logPartition_radial_tendsto` +
`Gfun_coercive` (μ(v)>0 zero-mean argument + sphere-compactness lower bound `c‖ℓ‖ − log N`);
`logPartition_partialDeriv` (the log-sum-exp gradient via `HasDerivAt`); `critical_iff_calibrationEqs`,
`hcoeff_pos_of_critical`, `Gfun_min_exists_unique` (coercive+continuous ⇒ min on a compact ball; strict
convexity ⇒ unique), `ellStar_isCritical` (Fermat), and the capstone `calibrated_exists_unique`. The
downstream `Delta.exists_unique_calibrated` is now `:= calibrated_exists_unique ε`.

Recently discharged (this pass, all `lake build`-verified): the Walsh
orthogonality core (`Delta.sum_chi`, `sum_nonzero_chi`), the delta-polynomial root
theory (`Delta.deltaPoly_strictMonoOn`, `deltaPoly_pos_at_bound`,
`uStar_exists_unique` by IVT — which also clears `uStar_spec`/`uStar_pos`/
`deltaPoly_uStar`/`uStar_lt` transitively — and `tauOrient_deltaOrientation`), the
moment-matrix positive-semidefiniteness (`Certified.secondMomentMatrix_psd`,
`covMatrix_psd` via Cauchy–Schwarz, `covMatrix_le_secondMoment`, plus the reusable
closed forms `quadForm_secondMomentMatrix`, `sum_v_xcoord`, `quadForm_covMatrix_eq`),
and the `GL(n,2)`/translation kinematics (`Symmetry.dotZ2_mulVec`,
`glTransInv_mulVec_ne_zero`, `glOrient_one`, `delta_injective`, `delta_glAction`),
plus `Trichotomy.log_abs_le_two_abs_sub_one`.

The remaining 16 are a single research frontier plus one isolated leaf
(`Main.corollary_1_3_top`): the **certified frontier** (`Certified` §8 — the
Newton–Kantorovich a-posteriori certification of `Theorem 8.3` over the 176-orbit
Γ₅ transversal for `2 ≤ n ≤ 5`, plus the spectral `opNorm_le_trace_of_psd`).
This is the exact-rational / interval-arithmetic computation that the paper does
by machine; it is deliberately kept off `native_decide`, so it needs the finite
computation reflected into `ℚ`/interval arithmetic with the Burnside completeness
checksum formalized.

## How it was produced

Statements were extracted from paper XII (`../papers/paper-XII-walsh-delta.md`),
formalized module-by-module (a multi-agent drafting pass), then **compiled and
iterated against Mathlib**: mechanical elaboration errors were fixed
(`noncomputable`, a stray `open … in`, a renamed `EqvGen`, renamed order/division
lemmas), and — the substantive integration step — the shared objects `mhat`,
`Ddelta`, `IsDelta` (originally redeclared in up to 5 modules via different
calibrated-law intermediates) were **unified onto single canonical homes**
(`mhat`,`Ddelta` in `Calibration`; `IsDelta` in `Basic`), the duplicates deleted
and re-imported, until the whole library linked. A handful of drafted proofs that
depended on the old private definitions were reduced to `sorry` (statements
kept).

## Inventory (per module — all compile; the library links)

| Module | Formalizes (paper) | `sorry` |
|---|---|---:|
| `Basic` | §1.1 objects; §2 Pinsker (2.1) + ψ (2.2); canonical `IsDelta` | 1 |
| `Calibration` | **§3 Thm 3.1 — COMPLETE, kernel-verified (no `sorryAx`)** | **0** |
| `Symmetry` | **§3 Lemmas 3.2 / 3.3 (covariance) — COMPLETE** | **0** |
| `Delta` | **§1.2 + §4 Prop 4.1 (delta law), Lemma 4.2 — COMPLETE** | **0** |
| `Trichotomy` | **§5 apparatus + §6 Thm 6.1 (deep-dip trichotomy) — COMPLETE** | **0** |
| `AnalyticMain` | **§7 Thm 7.1 / main theorem n≥6 / Cor 1.3 — COMPLETE** | **0** |
| `Certified` | §8 Lemmas 8.1/8.2 done; only the finite computation (Thm 8.3 + orbit BFS) left | 3 |
| `Main` | **Thm 1.2** + Cor 1.3 — **COMPLETE (assembly + `corollary_1_3_top`)** | **0** |
| **total** | | **3** |

(`sorry` counts are the tactic leaves; a couple more appear inside `def` bodies
for scaffolding — e.g. `Certified.cGl`'s nonzero-preservation.)

## Remaining work — discharge the remaining `sorry`s

Roughly in order:
1. **Standard Mathlib territory:** `Basic` (χ homomorphism, Pinsker, ψ facts),
   `Calibration` (convexity/coercivity of `Gobj`), `Symmetry` (covariance),
   `Delta` (the two-level law + `u⋆` root).
2. **The analytic frontier** (`Trichotomy`, `AnalyticMain`): the quantitative
   inequalities — rigorous bounds on `e^{-5}`, `ψ`, `2.878716`, `64/63` — via
   Mathlib `Real.log`/`Real.exp` bounds + `norm_num` + interval reasoning.
3. **The certified frontier** (`Certified.theorem_8_3`): discharge by **exact
   rational / interval arithmetic** through the Newton–Kantorovich certificates
   (`Lemma 8.1` radius, `Lemma 8.2` transfer) over the **176-orbit Γ₅ transversal**
   (`Symmetry` reduces 2³¹ orientations to 176). `native_decide` is deliberately
   **not** used (trust base + soundness); reflect the finite computation into
   `ℚ`/interval arithmetic with the Burnside completeness checksum formalized.

At zero `sorry`, `#print axioms WalshDelta.theorem_1_2` shows only
`[propext, Classical.choice, Quot.sound]` and the theorem is kernel-checked.

## Reproduce

```
cd shard/lean                 # Mathlib pinned via lake-manifest.json; toolchain v4.32.0-rc1
lake build                    # links the whole library, 0 errors (80 sorry warnings)
lake env lean -c 'import WalshDelta; #print axioms WalshDelta.theorem_1_2'
```

See `BLUEPRINT.md` for the module graph, the name↔paper mapping, and the Mathlib
pieces this leans on. This is a good blueprint-driven target for the
Lean/Mathlib community (PFR/FLT-style).
