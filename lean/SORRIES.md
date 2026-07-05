# SORRIES — the map of open proof leaves, easiest → hardest

Every `sorry` in the development, triaged by difficulty. `theorem_1_2` depends on
`sorryAx` until Tier D's two halves (`main_equality_analytic`, `theorem_8_3`) and
everything they transitively use are discharged. Work top-down: Tier A/B are
self-contained Mathlib exercises; Tier C are real but standard; Tier D are the
two research frontiers (the analytic quantitative bounds and the certified
finite computation).

Status legend: ☐ open · ✅ done (`lake build` clean).

## Tier A — trivial (Mathlib one-liner / `ring` / `ext`)

- ✅ `Basic.card_point` — `Fintype.card (Fin n → ZMod 2) = 2^n`.
- ✅ `Basic.chi_add` — `χ_{a+b} = χ_a·χ_b` (sign homomorphism of the `𝔽₂` pairing).
- ✅ `Delta.chi_right_add` — `χ_a(s+t) = χ_a(s)·χ_a(t)` (same, in the point arg).
- ✅ `Basic.Dkl_eq_EU_psi` — `E_U[ψ(X)] = D` (algebra + `EU_dens_eq_one`).
- ✅ `Basic.xhat_dens_eq_EP` — `E_U[X χ_a] = E_P[χ_a]` (unfold `dens`, cancel `N`).
- ✅ `Delta.deltaPoly_root_iff` — expand `u^N(1+u)` and `ring`.
- ✅ `Delta.deltaA_pos` / ✅ `Delta.deltaA_lt_one` — `linarith` from `uStar_lt`/`uStar_pos`.
- ✅ `Certified.secondMomentMatrix_isSymm` — `mul_comm` inside the sum.
- ✅ `Trichotomy.isDelta_iff` — `Orientation.ext` (equality ⟺ signs agree).

## Tier B — easy (one real Mathlib lemma, a few lines)

- ✅ `Basic.psi_nonneg`, `psi_strictAntiOn`, `psi_strictMonoOn` — monotonicity of
  `ψ` from `ψ' = log` (`StrictMonoOn`/`StrictAntiOn` of-deriv; `psi_hasDerivAt`).
- ☐ `Basic.pinsker` — Mathlib information-theory Pinsker (`… .tv_le … `) + `E_U|X-1| = 2·TV`.
- ✅ `Delta.sum_chi`, `sum_nonzero_chi` — Walsh/character orthogonality on `𝔽₂ⁿ`
  (sign-flip involution `s ↦ s + eⱼ`; full-sum-minus-`a=0` via pairing symmetry).
- ☐ `Delta.deltaLaw` (pos, sum_one) — `A,B > 0`; `A + (N-1)B = N`. (Blocked: `pos`
  needs the `n<2` junk-root edge; skip until `uStar_exists_unique` extends.)
- ✅ `Delta.uStar_lt` — strict monotone `p` with `p(u⋆)=0 < p(1/(N-1))`.  ☐ `Ddelta_pos`.
- ✅ `Certified.secondMomentMatrix_psd`, `covMatrix_psd` — `vᵀMv = E[(∑vχ)²] ≥ 0`
  (closed forms `quadForm_secondMomentMatrix`, `sum_v_xcoord`; `covMatrix_psd` = Cauchy–Schwarz).
- ✅ `Certified.covMatrix_le_secondMoment` (rank-one `quadForm_covMatrix_eq`).
  ☐ `opNorm_le_trace_of_psd` — spectral theorem (really Tier D).
- ✅ `Trichotomy.log_abs_le_two_abs_sub_one` — `Real.log_le_sub_one_of_pos` on `[½,2]`.
- ✅ `Symmetry.glOrient_one`, `delta_injective` — identity action; characters separate points.
- ✅ `Symmetry.dotZ2_mulVec`, `glTransInv_mulVec_ne_zero`, `delta_glAction` — matrix
  adjunction (`dotProduct_mulVec`/`mulVec_transpose`); `(M⁻¹)ᵀ` invertible; `chi_mulVec`.

## Tier C — medium (multi-step, standard mathematics)

- ✅ `Calibration.*` convex-analysis core — **ALL 14 DONE, kernel-verified** (`theorem_3_1`
  has no `sorryAx`): `logPartition_contDiff`/`Gfun_contDiff` (ContDiff.log ∘ exp ∘ linear),
  `logPartition_convexOn` (log-sum-exp convexity via two-point weighted Hölder,
  `Real.inner_le_Lp_mul_Lq`), `Gfun_strictConvexOn` (convex `F` + strictly-convex separable
  barrier), `logPartition_radial_tendsto` + `Gfun_coercive` (μ(v)>0 zero-mean + sphere
  compactness ⇒ `c‖ℓ‖−log N`), `logPartition_partialDeriv`/`Gfun_partialDeriv` (log-sum-exp
  gradient via `HasDerivAt`), `critical_iff_calibrationEqs`, `calibrated_of_critical`,
  `hcoeff_pos_of_critical` (|E_P χ_a|<1), `Gfun_min_exists_unique` (compact-ball min + strict
  convexity), `ellStar_isCritical` (Fermat), `calibrated_exists_unique`.  Also `Delta.exists_unique_calibrated := calibrated_exists_unique`.
- ✅ `Symmetry.*` covariance cluster — ALL DONE (see below).
- ✅ `Delta`: `deltaPoly_strictMonoOn` (monotone sum), `deltaPoly_pos_at_bound`
  (`(N-1)·1/(N-1)=1` cancels), `uStar_exists_unique` (IVT + strict mono),
  `tauOrient_deltaOrientation` (`chi_right_add`).  [These also clear `uStar_spec`,
  `uStar_pos`, `deltaPoly_uStar`, `uStar_lt` transitively.]
- ✅ `Delta` delta-law/covariance cluster — **ALL DONE** (kernel-verified): `deltaLaw`
  (valid `ProbLaw` ∀`n` via `(N−1)u⋆<1`), `calibrated_deltaLaw` (constant tilt `−log u⋆`;
  `chi_right_add`+`sum_nonzero_chi`+`deltaPoly_root_iff`), `calLaw_tauOrient`+`mhat_tauOrient`
  (translation covariance via `calLaw_unique`+reindex), `Ddelta_closedForm`, `Ddelta_pos`
  (`ψ`-form, `psi`>0 for `A<1`), `Ddelta_lt`/`Lemma_4_2` (`log(1+u⋆)≤u⋆`), `N_Ddelta_tendsto_one`
  (asymptotic), `exists_unique_calibrated`.
- ✅ `Symmetry` calibrated-law covariance — **ALL DONE**: `translation_covariance_law/_mhat`,
  `glAction_covariance_law/_mhat` (build the translate/pushforward `ProbLaw`, show it's calibrated
  for the acted orientation, conclude by `IsCalAssignment` uniqueness; `glAction` via `chi_mulVec`).
- ☐ `Certified`: `exists_unique_minimizer`, `lemma_8_1`, `lemma_8_2_grad/_transfer`,
  `Ddelta_eq`, `mhat_transOrient/_glOrient/_of_sameOrbit`, `isDelta_of_sameOrbit`,
  `nat_card_orientation`.

## Tier D — hard (the frontiers + the numeric constants)

- ✅ **Analytic frontier — ALL DONE, kernel-verified** (`Trichotomy` §5–6 + `AnalyticMain` §7):
  `parameter_floor`, `bookkeeping`, `spectral_floor` (the `|Φ(a)|≥1.24416N` floor + sign readout),
  `hMin_sub_epsG_ge_hPrime`, `dipTransform_ne_zero`, `dominance_criterion`, `shallowDepthSum_lt`,
  `deepDipCount_ne_zero/_one/_two`, `deep_dip_trichotomy` (**Thm 6.1**); `main_analytic` (**Thm 7.1**),
  `corollary_1_3`, `main_equality_analytic`, `translation_covariance`, `tau_deltaOrientation`,
  `N_Ddelta_tendsto_one`.  Also **`Basic.pinsker`** (Lemma 2.1, pointwise `3(x−1)²≤(2x+4)ψ(x)` via `f''≥0`
  + Cauchy–Schwarz).  [`Main.corollary_1_3_top` still open — see below.]
- ✅ **Numeric constants — ALL DONE** (exact interval arithmetic on Mathlib `exp_one_gt_d9` /
  `log_two,three,five_gt_d9`, NOT `native_decide`): `three_psi_gt`, `hPrime_gt`, `three_psi_exp_neg5_gt`.
- ✅ **Certified §8 SUPPORT — ALL DONE, kernel-verified**: `exists_unique_minimizer` (=`Gfun_min_exists_unique`),
  `Ddelta_eq`, `lemma_8_1` (Newton–Kantorovich a-posteriori radius, via `xhigh`), `lemma_8_2_grad`/`_opNorm`/
  `_transfer`, `opNorm_le_trace_of_psd` (spectral) + the elementary `gradNorm_bound` (discriminant), the
  differentiability + ℓ²-geometry helpers, `nat_card_orientation`, and the full `Γ_n`-orbit interface
  (`mhat_transOrient`/`_glOrient`/`_of_sameOrbit`, `isDelta_of_sameOrbit`, `reduce_to_transversal`, `cGl`).
  Also `Main.corollary_1_3_top` (=`corollary_1_3.1`).
- ☐ **Certified §8 COMPUTATION — the only 3 leaves left** (the genuine wall; the paper runs these by machine,
  receipt `w5`; `native_decide` forbidden): `theorem_8_3` (the `2≤n≤5` per-orbit entropy-margin certification
  via exact `ℚ`/interval arithmetic through Lemmas 8.1–8.2), `orbitCount_five` (`=176`, a 2³¹-state BFS), and
  `orbitCount_low` (n=2,3,4).  These need a verified BFS + interval-certificate checker — a distinct
  formalization project, not a fan-out target.

---


