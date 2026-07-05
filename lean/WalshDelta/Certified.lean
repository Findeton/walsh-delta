import Mathlib
import WalshDelta.Basic
import WalshDelta.Symmetry
import WalshDelta.Calibration
import WalshDelta.Delta

/-!
# Walsh–delta: the certified computation for `2 ≤ n ≤ 5` (Paper XII, Section 8)

Formalization of Section 8 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

This module states the two a-posteriori certification lemmas (Lemma 8.1, the
error radius; Lemma 8.2, the entropy-transfer bound), the finite main theorem
(Theorem 8.3, `2 ≤ n ≤ 5`), and the `Γ_n`-orbit reduction interface used for
`n = 5` (Section 8.3).

## Note on module boundaries

The Section-3/4/5 objects that Section 8 rests on — the log-partition `F`, the
Gibbs mean `x(ℓ)`, the convex objective `G_ε` (Theorem 3.1), the minimizer
`ℓ⋆`, the entropy value `m̂(ε)`, the relative-entropy functional `𝒟(ℓ)`, and the
delta reference `D_δ` — would in a full development live in dedicated modules
(`WalshDelta.Convex`, `WalshDelta.Delta`, `WalshDelta.Symmetry`).  Those modules
do not yet exist, so to keep this file self-contained and its statements
faithful we introduce those objects here, each with a docstring citing the
paper.  None of them redefine an object exported by `WalshDelta.Basic`; they
reuse `Basic`'s `Point`, `chi`, `EU`, `NonzeroMask`, `Orientation`,
`deltaOrientation`, etc. verbatim.
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## Section-3 substrate: `F`, `x(ℓ)`, `G_ε`, the minimizer `ℓ⋆`, and `m̂` -/

/-- Paper XII, Section 3.  The linear tilt `∑_{a≠0} ℓ_a χ_a(s)` (the Section-3
parametrization by `ℓ` directly, related to Basic's `tilt` by `ℓ_a = h_a ε_a`). -/
def linComb (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  ∑ a : NonzeroMask n, ℓ a * chi a.1 s

/-- Paper XII, Section 3.  The Gibbs weight `exp(∑_a ℓ_a χ_a(s))` (unnormalized
density of `P_ℓ` w.r.t. uniform). -/
noncomputable def gibbsWeight (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  Real.exp (linComb ℓ s)

/-- Paper XII, Section 3.  The partition sum `Z(ℓ) = ∑_s exp(∑_a ℓ_a χ_a(s))`. -/
noncomputable def Zpart (ℓ : NonzeroMask n → ℝ) : ℝ := ∑ s, gibbsWeight ℓ s

/-- `Z(ℓ) > 0` (a sum of exponentials over the nonempty cube). -/
lemma Zpart_pos (ℓ : NonzeroMask n → ℝ) : 0 < Zpart ℓ := by
  have : Nonempty (Point n) := inferInstance
  apply Finset.sum_pos
  · intro s _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Paper XII, Section 3.  The log-partition function
`F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`. -/
noncomputable def Fpart (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Real.log (EU (fun s => Real.exp (linComb ℓ s)))

/-- Paper XII, Section 3.  The Gibbs mean of a character,
`x_a(ℓ) = 𝔼_{P_ℓ}[χ_a] = ∂F/∂ℓ_a`. -/
noncomputable def xcoord (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  (∑ s, gibbsWeight ℓ s * chi a.1 s) / Zpart ℓ

/-- Paper XII, Section 3, Theorem 3.1.  The strictly convex objective
`G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`. -/
noncomputable def Gobj (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Fpart ℓ + ∑ a : NonzeroMask n, Real.exp (- ε.sign a * ℓ a)

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  For every orientation
`ε`, the objective `G_ε` has a unique global minimizer on `ℝ^{N-1}`.  (Proved in
Section 3 via smoothness + strict convexity + coercivity; the analytic proof
belongs to the convexity module.) -/
theorem exists_unique_minimizer (ε : Orientation n) :
    ∃! ℓ : NonzeroMask n → ℝ, ∀ m, Gobj ε ℓ ≤ Gobj ε m := by
  have hGG : Gobj ε = Gfun ε := by
    funext ℓ
    unfold Gobj Gfun Fpart logPartition
    congr 1
    exact Finset.sum_congr rfl (fun a _ => by rw [neg_mul])
  obtain ⟨ℓ0, h0, hu⟩ := Gfun_min_exists_unique ε
  rw [isMinOn_univ_iff] at h0
  refine ⟨ℓ0, ?_, ?_⟩
  · intro m
    rw [hGG]; exact h0 m
  · intro y hy
    apply hu
    rw [isMinOn_univ_iff]
    intro m
    have := hy m
    rw [hGG] at this
    exact this
/-- Paper XII, Theorem 3.1.  The unique minimizer `ℓ⋆(ε)` of `G_ε`. -/
noncomputable def lstar (ε : Orientation n) : NonzeroMask n → ℝ :=
  (exists_unique_minimizer ε).exists.choose

/-- `ℓ⋆(ε)` is a global minimizer of `G_ε` (Theorem 3.1). -/
theorem lstar_isMinimizer (ε : Orientation n) :
    ∀ m, Gobj ε (lstar ε) ≤ Gobj ε m :=
  (exists_unique_minimizer ε).exists.choose_spec

/-- Paper XII, Section 8.2.  The relative-entropy functional
`𝒟(ℓ) := D(P_ℓ ‖ U) = ⟨ℓ, x(ℓ)⟩ - F(ℓ)`. -/
noncomputable def Dcal (ℓ : NonzeroMask n → ℝ) : ℝ :=
  (∑ a : NonzeroMask n, ℓ a * xcoord ℓ a) - Fpart ℓ

-- (removed redundant `mhat`; canonical in an imported module)
-- (removed redundant `Ddelta`; canonical in an imported module)
/-- Paper XII, Lemma 3.2.  All `N` delta orientations share the value `D_δ`. -/
theorem Ddelta_eq (sstar : Point n) : mhat (deltaOrientation sstar) = Ddelta n := by
  exact mhat_deltaOrientation_const sstar
/-- The distinguished `deltaOrientation` at `s⋆` satisfies `IsDelta`. -/
lemma isDelta_deltaOrientation (sstar : Point n) :
    IsDelta (deltaOrientation sstar) :=
  ⟨sstar, rfl⟩

/-! ## The `ℓ²`-geometry on `ℝ^{N-1}` -/

/-- Paper XII, Section 8.  The Euclidean (`ℓ²`) norm on `ℝ^{N-1}`, indexed by
nonzero masks: `‖v‖₂ = √(∑_a v_a²)`. -/
noncomputable def l2norm (v : NonzeroMask n → ℝ) : ℝ := Real.sqrt (∑ a, (v a) ^ 2)

/-! ## The gradient of `G_ε`, and the Hessian of `F` -/

/-- Paper XII, Section 3 / Section 8.1.  The gradient of `G_ε`, componentwise:
`(∇G_ε)_a = x_a(ℓ) - ε_a e^{-ε_a ℓ_a}`. -/
noncomputable def gradG (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  xcoord ℓ a - ε.sign a * Real.exp (- ε.sign a * ℓ a)

/-- Paper XII, Section 3.  The second moment `𝔼_{P_ℓ}[χ_a χ_b]`. -/
noncomputable def secondMoment (ℓ : NonzeroMask n → ℝ) (a b : NonzeroMask n) : ℝ :=
  (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) / Zpart ℓ

/-- Paper XII, Section 3.  The Hessian `∇²F(ℓ) = Cov_{P_ℓ}(χ)`, with entries
`𝔼_{P_ℓ}[χ_a χ_b] - x_a x_b`. -/
noncomputable def covMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix (NonzeroMask n) (NonzeroMask n) ℝ :=
  fun a b => secondMoment ℓ a b - xcoord ℓ a * xcoord ℓ b

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  The uncentered second-moment
matrix `𝔼_{P_ℓ}[χ χᵀ]`. -/
noncomputable def secondMomentMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix (NonzeroMask n) (NonzeroMask n) ℝ :=
  fun a b => secondMoment ℓ a b

/-- The quadratic form `vᵀ H v = ∑_{a,b} v_a H_{ab} v_b` associated to a matrix
`H`; used to express operator-norm bounds without invoking the operator-norm
API directly. -/
def quadForm (H : Matrix (NonzeroMask n) (NonzeroMask n) ℝ)
    (v : NonzeroMask n → ℝ) : ℝ :=
  ∑ a, ∑ b, v a * H a b * v b

/-! ### Elementary character algebra used below -/

/-- `χ_a(s)² = 1` since every Walsh character is `±1`-valued. -/
lemma chi_mul_self (a s : Point n) : chi a s * chi a s = 1 := by
  rcases chi_mem a s with h | h <;> rw [h] <;> norm_num

/-- Paper XII, Section 8.1.  The diagonal second moment is `𝔼_{P_ℓ}[χ_a²] = 1`. -/
lemma secondMoment_diag (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    secondMoment ℓ a a = 1 := by
  have hchi : ∀ s, gibbsWeight ℓ s * chi a.1 s * chi a.1 s = gibbsWeight ℓ s := by
    intro s; rw [mul_assoc, chi_mul_self]; ring
  unfold secondMoment
  simp only [hchi]
  exact div_self (Zpart_pos ℓ).ne'

/-- Paper XII, Section 1.1.  There are exactly `N - 1` nonzero masks. -/
lemma card_nonzeroMask (n : ℕ) : Fintype.card (NonzeroMask n) = N n - 1 := by
  show Fintype.card {a : Point n // a ≠ 0} = N n - 1
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_point]
  -- TODO(api): confirm `Fintype.card_subtype_compl` and `Fintype.card_subtype_eq`.

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  `tr 𝔼[χχᵀ] = ∑_{a≠0} 1
= |{a≠0}|`. -/
lemma trace_secondMomentMatrix (ℓ : NonzeroMask n → ℝ) :
    Matrix.trace (secondMomentMatrix ℓ) = (Fintype.card (NonzeroMask n) : ℝ) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, secondMomentMatrix, secondMoment_diag]
  simp [Finset.card_univ]
  -- TODO(api): confirm `Matrix.trace` unfolds to `∑ i, diag i` and `Matrix.diag_apply`.

/-- Paper XII, Section 8.1 (proof of Lemma 8.2).  `tr 𝔼[χχᵀ] = N - 1`. -/
lemma trace_secondMomentMatrix_eq (ℓ : NonzeroMask n → ℝ) :
    Matrix.trace (secondMomentMatrix ℓ) = (N n : ℝ) - 1 := by
  rw [trace_secondMomentMatrix, card_nonzeroMask, Nat.cast_sub (N_pos n), Nat.cast_one]

/-! ### Positive semidefiniteness and symmetry of the moment matrices -/

/-- Paper XII, Section 3.  The weighted mean `∑_a v_a x_a(ℓ)` in closed form:
`= (∑_s w_ℓ(s)(∑_a v_a χ_a(s)))/Z(ℓ)`. -/
lemma sum_v_xcoord (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    (∑ a : NonzeroMask n, v a * xcoord ℓ a)
      = (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) / Zpart ℓ := by
  have numX : (∑ a : NonzeroMask n, v a * (∑ s, gibbsWeight ℓ s * chi a.1 s))
      = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ => by ring))
  have Xdist : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) / Zpart ℓ
      = ∑ a : NonzeroMask n, (v a * (∑ s, gibbsWeight ℓ s * chi a.1 s)) / Zpart ℓ := by
    rw [← numX]; simp only [Finset.sum_div]
  unfold xcoord
  rw [Xdist]
  refine Finset.sum_congr rfl (fun a _ => by rw [mul_div_assoc])

/-- Paper XII, Section 8.1 (the rank-one subtraction, quadratic-form identity).
`vᵀ 𝔼[χχᵀ] v - vᵀ Cov v = (∑_a v_a x_a)²`. -/
lemma quadForm_covMatrix_eq (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (secondMomentMatrix ℓ) v - quadForm (covMatrix ℓ) v
      = (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2 := by
  unfold quadForm secondMomentMatrix covMatrix
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => by ring)

/-- Paper XII, Section 8.1.  The quadratic form of `𝔼[χχᵀ]` in closed form:
`vᵀ 𝔼[χχᵀ] v = (∑_s w_ℓ(s)(∑_a v_a χ_a(s))²)/Z(ℓ)`. -/
lemma quadForm_secondMomentMatrix (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (secondMomentMatrix ℓ) v
      = (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) / Zpart ℓ := by
  have e1 : ∀ s : Point n,
      gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2
        = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
            v a * (gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b := by
    intro s
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  have numkey : (∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
        v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b)
      = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2 := by
    have L : (∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
          v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b)
        = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n, ∑ s,
            v a * (gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [L, Finset.sum_congr rfl (fun s _ => e1 s)]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
  have Rdist : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) / Zpart ℓ
      = ∑ a : NonzeroMask n, ∑ b : NonzeroMask n,
          (v a * (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * v b) / Zpart ℓ := by
    rw [← numkey]
    simp only [Finset.sum_div]
  rw [Rdist]
  unfold quadForm secondMomentMatrix secondMoment
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- Paper XII, Section 8.1.  `𝔼[χχᵀ] ⪰ 0` (a nonnegative mixture of rank-one
outer products `χ(s)χ(s)ᵀ`). -/
theorem secondMomentMatrix_psd (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    0 ≤ quadForm (secondMomentMatrix ℓ) v := by
  rw [quadForm_secondMomentMatrix]
  refine div_nonneg (Finset.sum_nonneg (fun s _ => ?_)) (Zpart_pos ℓ).le
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Paper XII, Section 3.  `∇²F = Cov_{P_ℓ}(χ) ⪰ 0` (a covariance matrix):
`vᵀ Cov v = Var_{P_ℓ}(∑_a v_a χ_a) ≥ 0`, by Cauchy–Schwarz. -/
theorem covMatrix_psd (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    0 ≤ quadForm (covMatrix ℓ) v := by
  have hZ := Zpart_pos ℓ
  have hsq : ∀ s, (0:ℝ) ≤ gibbsWeight ℓ s := fun s => (Real.exp_pos _).le
  have hCS : (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s)) ^ 2
      ≤ Zpart ℓ * (∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2) := by
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun s => Real.sqrt (gibbsWeight ℓ s))
      (fun s => Real.sqrt (gibbsWeight ℓ s) * (∑ a : NonzeroMask n, v a * chi a.1 s))
    have e_fg : (∑ s, Real.sqrt (gibbsWeight ℓ s)
          * (Real.sqrt (gibbsWeight ℓ s) * (∑ a : NonzeroMask n, v a * chi a.1 s)))
        = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) :=
      Finset.sum_congr rfl (fun s _ => by rw [← mul_assoc, Real.mul_self_sqrt (hsq s)])
    have e_f2 : (∑ s, Real.sqrt (gibbsWeight ℓ s) ^ 2) = Zpart ℓ := by
      unfold Zpart
      exact Finset.sum_congr rfl (fun s _ => Real.sq_sqrt (hsq s))
    have e_g2 : (∑ s, (Real.sqrt (gibbsWeight ℓ s)
          * (∑ a : NonzeroMask n, v a * chi a.1 s)) ^ 2)
        = ∑ s, gibbsWeight ℓ s * (∑ a : NonzeroMask n, v a * chi a.1 s) ^ 2 :=
      Finset.sum_congr rfl (fun s _ => by rw [mul_pow, Real.sq_sqrt (hsq s)])
    rw [e_fg, e_f2, e_g2] at cs
    exact cs
  have goal2 : (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2
      ≤ quadForm (secondMomentMatrix ℓ) v := by
    rw [quadForm_secondMomentMatrix, sum_v_xcoord, div_pow,
        div_le_div_iff₀ (pow_pos hZ 2) hZ]
    nlinarith [mul_le_mul_of_nonneg_right hCS hZ.le]
  linarith [quadForm_covMatrix_eq ℓ v, goal2]

/-- `𝔼[χχᵀ]` is symmetric (`χ_a χ_b = χ_b χ_a`). -/
theorem secondMomentMatrix_isSymm (ℓ : NonzeroMask n → ℝ) :
    (secondMomentMatrix ℓ).IsSymm := by
  unfold Matrix.IsSymm
  ext a b
  simp only [Matrix.transpose_apply, secondMomentMatrix, secondMoment]
  congr 1
  exact Finset.sum_congr rfl (fun s _ => by ring)

/-- Paper XII, Section 8.1 (the rank-one subtraction).  `Cov ⪯ 𝔼[χχᵀ]` in the
PSD order: `vᵀ Cov v = vᵀ𝔼[χχᵀ]v - (∑_a v_a x_a)² ≤ vᵀ𝔼[χχᵀ]v`. -/
theorem covMatrix_le_secondMoment (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (covMatrix ℓ) v ≤ quadForm (secondMomentMatrix ℓ) v := by
  have hsplit : quadForm (secondMomentMatrix ℓ) v - quadForm (covMatrix ℓ) v
      = (∑ a : NonzeroMask n, v a * xcoord ℓ a) ^ 2 := by
    unfold quadForm secondMomentMatrix covMatrix
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  nlinarith [sq_nonneg (∑ a : NonzeroMask n, v a * xcoord ℓ a), hsplit]

/-- **The operator-norm-≤-trace step of Lemma 8.2** (stated generally).  For a
symmetric positive-semidefinite matrix `H`, `⟨v, Hv⟩ ≤ (tr H) ‖v‖₂²`; i.e. the
operator norm of a PSD matrix is at most its trace.

Left as `sorry`: this is the spectral-theorem step (op-norm `= λ_max ≤ ∑ λ_i
= tr H`) and is *not* a short proof in Lean — it needs the Hermitian spectral
decomposition (`Matrix.IsHermitian.spectral_theorem` and eigenvalue
nonnegativity).  Cf. Lemma 8.2. -/
theorem opNorm_le_trace_of_psd
    (H : Matrix (NonzeroMask n) (NonzeroMask n) ℝ)
    (_hsymm : H.IsSymm)
    (_hpsd : ∀ v, 0 ≤ quadForm H v)
    (v : NonzeroMask n → ℝ) :
    quadForm H v ≤ Matrix.trace H * ∑ a, (v a) ^ 2 := by
  -- pointwise symmetry
  have hsymm : ∀ i j, H i j = H j i := by
    intro i j
    have h := congrFun (congrFun _hsymm j) i
    rwa [Matrix.transpose_apply] at h
  -- trace as diagonal sum
  have htrace : Matrix.trace H = ∑ a, H a a := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply]
  -- single-vector sum helpers (indicator test vectors)
  have inner_single : ∀ (i c : NonzeroMask n) (x : ℝ),
      (∑ j, H i j * (if j = c then x else (0:ℝ))) = H i c * x := by
    intro i c x
    rw [Finset.sum_eq_single c]
    · rw [if_pos rfl]
    · intro j _ hj; rw [if_neg hj, mul_zero]
    · intro h; exact absurd (Finset.mem_univ c) h
  have outer_single : ∀ (c : NonzeroMask n) (x : ℝ) (g : NonzeroMask n → ℝ),
      (∑ i, (if i = c then x else (0:ℝ)) * g i) = x * g c := by
    intro c x g
    rw [Finset.sum_eq_single c]
    · rw [if_pos rfl]
    · intro i _ hi; rw [if_neg hi, zero_mul]
    · intro h; exact absurd (Finset.mem_univ c) h
  -- quadratic form on a two-atom test vector
  have hquad_form : ∀ (a b : NonzeroMask n) (x : ℝ),
      quadForm H (fun i => (if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0))
        = H a a * x ^ 2 + (2 * H a b) * x + H b b := by
    intro a b x
    have inner : ∀ i : NonzeroMask n,
        (∑ j, ((if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0)) * H i j
              * ((if j = a then x else (0:ℝ)) + (if j = b then (1:ℝ) else 0)))
          = ((if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0))
              * (H i a * x + H i b * 1) := by
      intro i
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, inner_single i a x, inner_single i b 1]
    calc quadForm H (fun i => (if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0))
        = ∑ i, ((if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0))
              * (H i a * x + H i b * 1) := by
            unfold quadForm
            exact Finset.sum_congr rfl (fun i _ => inner i)
      _ = (∑ i, (if i = a then x else (0:ℝ)) * (H i a * x + H i b * 1))
            + (∑ i, (if i = b then (1:ℝ) else 0) * (H i a * x + H i b * 1)) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = x * (H a a * x + H a b * 1) + 1 * (H b a * x + H b b * 1) := by
            rw [outer_single a x (fun i => H i a * x + H i b * 1),
                outer_single b 1 (fun i => H i a * x + H i b * 1)]
      _ = H a a * x ^ 2 + (2 * H a b) * x + H b b := by
            rw [hsymm b a]; ring
  -- diagonal nonnegativity
  have hdiag : ∀ a, 0 ≤ H a a := by
    intro a
    have h := _hpsd (fun i => (if i = a then (0:ℝ) else 0) + (if i = a then (1:ℝ) else 0))
    rw [hquad_form a a 0] at h
    simpa using h
  -- entrywise Cauchy–Schwarz from PSD (discriminant)
  have hentry : ∀ a b, (H a b) ^ 2 ≤ H a a * H b b := by
    intro a b
    have hnn : ∀ x : ℝ, 0 ≤ H a a * (x * x) + (2 * H a b) * x + H b b := by
      intro x
      have hp := _hpsd (fun i => (if i = a then x else (0:ℝ)) + (if i = b then (1:ℝ) else 0))
      rw [hquad_form a b x] at hp
      nlinarith [hp]
    have hd := discrim_le_zero hnn
    simp only [discrim] at hd
    nlinarith [hd]
  -- main chain
  calc quadForm H v
      ≤ (∑ a, |v a| * Real.sqrt (H a a)) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum]
        unfold quadForm
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        have habs : |H a b| ≤ Real.sqrt (H a a) * Real.sqrt (H b b) := by
          rw [← Real.sqrt_mul (hdiag a) (H b b), ← Real.sqrt_sq_eq_abs]
          exact Real.sqrt_le_sqrt (hentry a b)
        calc v a * H a b * v b
            ≤ |v a * H a b * v b| := le_abs_self _
          _ = |v a| * |H a b| * |v b| := by rw [abs_mul, abs_mul]
          _ ≤ |v a| * (Real.sqrt (H a a) * Real.sqrt (H b b)) * |v b| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
          _ = |v a| * Real.sqrt (H a a) * (|v b| * Real.sqrt (H b b)) := by ring
    _ ≤ (∑ a, (v a) ^ 2) * (∑ a, H a a) := by
        have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun a => |v a|) (fun a => Real.sqrt (H a a))
        have e1 : (∑ a, |v a| ^ 2) = ∑ a, (v a) ^ 2 :=
          Finset.sum_congr rfl (fun a _ => sq_abs (v a))
        have e2 : (∑ a, (Real.sqrt (H a a)) ^ 2) = ∑ a, H a a :=
          Finset.sum_congr rfl (fun a _ => Real.sq_sqrt (hdiag a))
        rw [e1, e2] at cs
        exact cs
    _ = Matrix.trace H * ∑ a, (v a) ^ 2 := by rw [htrace]; ring
/-! ## Lemma 8.1 — the a posteriori error radius -/

/-- Paper XII, Lemma 8.1 (a posteriori radius).  Fix an orientation `ε` and any
`ℓ̃ ∈ ℝ^{N-1}`.  Let `ρ = ‖∇G_ε(ℓ̃)‖₂` and let `λ = min_a e^{-ε_a ℓ̃_a}` (encoded
as `IsLeast` of the range of the barrier weights).  If `r₀ := 2eρ/λ ≤ 1`, then
the true minimizer satisfies `‖ℓ⋆ - ℓ̃‖₂ ≤ r₀`. -/
theorem lemma_8_1
    (ε : Orientation n) (ℓt : NonzeroMask n → ℝ)
    (ρ lam r₀ : ℝ)
    (hρ : ρ = l2norm (gradG ε ℓt))
    (hlam : IsLeast (Set.range fun a => Real.exp (- ε.sign a * ℓt a)) lam)
    (hr₀ : r₀ = 2 * Real.exp 1 * ρ / lam)
    (hle : r₀ ≤ 1) :
    l2norm (lstar ε - ℓt) ≤ r₀ := by
  -- ===== small ℓ² helpers (inlined; the file's copies come after this lemma) =====
  have l2norm_nonneg : ∀ v : NonzeroMask n → ℝ, 0 ≤ l2norm v := fun v => Real.sqrt_nonneg _
  have l2norm_smul : ∀ (c : ℝ) (v : NonzeroMask n → ℝ), l2norm (c • v) = |c| * l2norm v := by
    intro c v
    unfold l2norm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul]; ring
  have l2_inner_le : ∀ (u w : NonzeroMask n → ℝ), |∑ a, u a * w a| ≤ l2norm u * l2norm w := by
    intro u w
    have hcs : (∑ a, u a * w a) ^ 2 ≤ (∑ a, (u a) ^ 2) * (∑ a, (w a) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
    rw [← Real.sqrt_sq_eq_abs, l2norm, l2norm,
        ← Real.sqrt_mul (Finset.sum_nonneg (fun a _ => sq_nonneg _))]
    exact Real.sqrt_le_sqrt hcs
  -- ===== directional-derivative machinery (∀ direction d) =====
  have dlin : ∀ (d : NonzeroMask n → ℝ) (s : Point n) (t : ℝ),
      HasDerivAt (fun τ : ℝ => linComb (ℓt + τ • d) s) (∑ a, d a * chi a.1 s) t := by
    intro d s t
    have hfun : (fun τ : ℝ => linComb (ℓt + τ • d) s)
        = (fun τ : ℝ => linComb ℓt s + τ * (∑ a, d a * chi a.1 s)) := by
      funext τ
      unfold linComb
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hfun]
    simpa using ((hasDerivAt_id t).mul_const (∑ a, d a * chi a.1 s)).const_add (linComb ℓt s)
  have dmu : ∀ (d : NonzeroMask n → ℝ) (s : Point n) (t : ℝ),
      HasDerivAt (fun τ : ℝ => Real.exp (linComb (ℓt + τ • d) s))
        (Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)) t :=
    fun d s t => (dlin d s t).exp
  have dPfun : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ∑ s, Real.exp (linComb (ℓt + τ • d) s))
        (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)) t := by
    intro d t
    have h := HasDerivAt.sum (fun s (_ : s ∈ (Finset.univ : Finset (Point n))) => dmu d s t)
    have hfe : (fun τ : ℝ => ∑ s, Real.exp (linComb (ℓt + τ • d) s))
        = ∑ s : Point n, (fun τ : ℝ => Real.exp (linComb (ℓt + τ • d) s)) := by
      funext τ; rw [Finset.sum_apply]
    rw [hfe]; exact h
  have dP1 : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ∑ s, Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s))
        (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s)) t := by
    intro d t
    have hterm : ∀ s : Point n,
        HasDerivAt (fun τ : ℝ => Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s))
          (Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s)) t :=
      fun s => (dmu d s t).mul_const (∑ a, d a * chi a.1 s)
    have h := HasDerivAt.sum (fun s (_ : s ∈ (Finset.univ : Finset (Point n))) => hterm s)
    have hfe : (fun τ : ℝ => ∑ s, Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s))
        = ∑ s : Point n, (fun τ : ℝ => Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s)) := by
      funext τ; rw [Finset.sum_apply]
    rw [hfe]; exact h
  have dFpart : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => Fpart (ℓt + τ • d))
        ((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
          / (∑ s, Real.exp (linComb (ℓt + t • d) s))) t := by
    intro d t
    have hEUeq : (fun τ : ℝ => Fpart (ℓt + τ • d))
        = fun τ : ℝ => Real.log ((∑ s, Real.exp (linComb (ℓt + τ • d) s)) / (N n : ℝ)) := by
      funext τ; simp only [Fpart, EU]
    rw [hEUeq]
    have hden : (∑ s, Real.exp (linComb (ℓt + t • d) s)) / (N n : ℝ) ≠ 0 :=
      div_ne_zero (Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty).ne' (N_ne_zero n)
    have hd := ((dPfun d t).div_const (N n : ℝ)).log hden
    have hval : ((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)) / (N n : ℝ))
          / ((∑ s, Real.exp (linComb (ℓt + t • d) s)) / (N n : ℝ))
        = (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
          / (∑ s, Real.exp (linComb (ℓt + t • d) s)) := by
      rw [div_div_div_cancel_right₀ (N_ne_zero n)]
    rw [hval] at hd; exact hd
  have dBval : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)))
        (∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a))) t := by
    intro d t
    have hterm : ∀ a : NonzeroMask n,
        HasDerivAt (fun τ : ℝ => Real.exp (-(ε.sign a) * (ℓt a + τ * d a)))
          (Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a))) t := by
      intro a
      have hu : HasDerivAt (fun τ : ℝ => ℓt a + τ * d a) (d a) t := by
        simpa using ((hasDerivAt_id t).mul_const (d a)).const_add (ℓt a)
      have h := (hu.const_mul (-(ε.sign a))).exp
      have he : (-(ε.sign a)) * d a = -(ε.sign a * d a) := by ring
      rw [he] at h; exact h
    have h := HasDerivAt.sum (fun a (_ : a ∈ (Finset.univ : Finset (NonzeroMask n))) => hterm a)
    have hfe : (fun τ : ℝ => ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)))
        = ∑ a : NonzeroMask n, (fun τ : ℝ => Real.exp (-(ε.sign a) * (ℓt a + τ * d a))) := by
      funext τ; rw [Finset.sum_apply]
    rw [hfe]; exact h
  have dBd : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a)))
        (∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a))) t := by
    intro d t
    have hterm : ∀ a : NonzeroMask n,
        HasDerivAt (fun τ : ℝ => Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a)))
          (Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a))) t := by
      intro a
      have hu : HasDerivAt (fun τ : ℝ => ℓt a + τ * d a) (d a) t := by
        simpa using ((hasDerivAt_id t).mul_const (d a)).const_add (ℓt a)
      have h := (hu.const_mul (-(ε.sign a))).exp
      have he : (-(ε.sign a)) * d a = -(ε.sign a * d a) := by ring
      rw [he] at h
      exact h.mul_const (-(ε.sign a * d a))
    have h := HasDerivAt.sum (fun a (_ : a ∈ (Finset.univ : Finset (NonzeroMask n))) => hterm a)
    have hfe : (fun τ : ℝ => ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a)))
        = ∑ a : NonzeroMask n,
            (fun τ : ℝ => Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a))) := by
      funext τ; rw [Finset.sum_apply]
    rw [hfe]; exact h
  -- first derivative of Gobj∘γ
  have G1 : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt (fun τ : ℝ => Gobj ε (ℓt + τ • d))
        ((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
          / (∑ s, Real.exp (linComb (ℓt + t • d) s))
        + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a))) t := by
    intro d t
    have hGeq : (fun τ : ℝ => Gobj ε (ℓt + τ • d))
        = fun τ : ℝ => Fpart (ℓt + τ • d) + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) := by
      funext τ; unfold Gobj; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hGeq]
    exact (dFpart d t).add (dBval d t)
  -- second derivative (derivative of the gradient function)
  have G2 : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      HasDerivAt
        (fun τ : ℝ => (∑ s, Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s))
            / (∑ s, Real.exp (linComb (ℓt + τ • d) s))
          + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a)))
        (((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s))
            * (∑ s, Real.exp (linComb (ℓt + t • d) s))
            - (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
              * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)))
            / (∑ s, Real.exp (linComb (ℓt + t • d) s)) ^ 2
          + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a))) t := by
    intro d t
    have hPne : (∑ s, Real.exp (linComb (ℓt + t • d) s)) ≠ 0 :=
      (Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty).ne'
    exact ((dP1 d t).div (dPfun d t) hPne).add (dBd d t)
  -- nonnegativity of the variance (quotient) part
  have G3quot : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      0 ≤ (((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s))
            * (∑ s, Real.exp (linComb (ℓt + t • d) s))
            - (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
              * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)))
            / (∑ s, Real.exp (linComb (ℓt + t • d) s)) ^ 2) := by
    intro d t
    have hCS : (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
          * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
        ≤ (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s))
          * (∑ s, Real.exp (linComb (ℓt + t • d) s)) := by
      have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun s => Real.sqrt (Real.exp (linComb (ℓt + t • d) s)))
        (fun s => Real.sqrt (Real.exp (linComb (ℓt + t • d) s)) * (∑ a, d a * chi a.1 s))
      have e_fg : (∑ s, Real.sqrt (Real.exp (linComb (ℓt + t • d) s))
            * (Real.sqrt (Real.exp (linComb (ℓt + t • d) s)) * (∑ a, d a * chi a.1 s)))
          = ∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) :=
        Finset.sum_congr rfl (fun s _ => by rw [← mul_assoc, Real.mul_self_sqrt (Real.exp_pos _).le])
      have e_f2 : (∑ s, Real.sqrt (Real.exp (linComb (ℓt + t • d) s)) ^ 2)
          = ∑ s, Real.exp (linComb (ℓt + t • d) s) :=
        Finset.sum_congr rfl (fun s _ => Real.sq_sqrt (Real.exp_pos _).le)
      have e_g2 : (∑ s, (Real.sqrt (Real.exp (linComb (ℓt + t • d) s)) * (∑ a, d a * chi a.1 s)) ^ 2)
          = ∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s) :=
        Finset.sum_congr rfl (fun s _ => by rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le, sq]; ring)
      rw [e_fg, e_f2, e_g2] at cs
      calc (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
            * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
          = (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)) ^ 2 := by rw [sq]
        _ ≤ (∑ s, Real.exp (linComb (ℓt + t • d) s))
              * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s)) := cs
        _ = (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s))
              * (∑ s, Real.exp (linComb (ℓt + t • d) s)) := by ring
    apply div_nonneg _ (sq_nonneg _)
    linarith [hCS]
  -- nonnegativity of the full second derivative
  have G3 : ∀ (d : NonzeroMask n → ℝ) (t : ℝ),
      0 ≤ (((∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s) * (∑ a, d a * chi a.1 s))
            * (∑ s, Real.exp (linComb (ℓt + t • d) s))
            - (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s))
              * (∑ s, Real.exp (linComb (ℓt + t • d) s) * (∑ a, d a * chi a.1 s)))
            / (∑ s, Real.exp (linComb (ℓt + t • d) s)) ^ 2
          + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a))) := by
    intro d t
    have hbar : 0 ≤ ∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a)) := by
      refine Finset.sum_nonneg (fun a _ => ?_)
      have h : Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a))
          = Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (ε.sign a * d a) ^ 2 := by ring
      rw [h]; exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    linarith [G3quot d t, hbar]
  -- value of the gradient function at t = 0
  have G4 : ∀ (d : NonzeroMask n → ℝ),
      ((∑ s, Real.exp (linComb (ℓt + (0:ℝ) • d) s) * (∑ a, d a * chi a.1 s))
          / (∑ s, Real.exp (linComb (ℓt + (0:ℝ) • d) s))
        + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + (0:ℝ) * d a)) * (-(ε.sign a * d a)))
        = ∑ a, d a * gradG ε ℓt a := by
    intro d
    simp only [zero_smul, add_zero, zero_mul]
    have hx : (∑ s, Real.exp (linComb ℓt s) * (∑ a, d a * chi a.1 s)) / (∑ s, Real.exp (linComb ℓt s))
        = ∑ a, d a * xcoord ℓt a := by
      rw [sum_v_xcoord ℓt d]; rfl
    rw [hx, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold gradG
    ring
  -- barrier lower bound on the segment
  have Bd2_lower : ∀ (d : NonzeroMask n → ℝ) (t : ℝ) (lm : ℝ),
      0 ≤ lm → (∀ a, lm ≤ Real.exp (-ε.sign a * ℓt a)) →
      (∀ a, |d a| ≤ 1) → |t| ≤ 1 →
      (lm / Real.exp 1) * (∑ a, (d a) ^ 2)
        ≤ ∑ a, Real.exp (-(ε.sign a) * (ℓt a + t * d a)) * (-(ε.sign a * d a)) * (-(ε.sign a * d a)) := by
    intro d t lm hlampos hlb hd1 ht
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hsign_sq : (ε.sign a) * (ε.sign a) = 1 := by
      rcases ε.is_sign a with h | h <;> rw [h] <;> norm_num
    have hprodsq : (-(ε.sign a * d a)) * (-(ε.sign a * d a)) = (d a) ^ 2 := by
      have h : (-(ε.sign a * d a)) * (-(ε.sign a * d a)) = (ε.sign a * ε.sign a) * (d a * d a) := by ring
      rw [h, hsign_sq]; ring
    rw [mul_assoc, hprodsq]
    have hexp_lb : lm / Real.exp 1 ≤ Real.exp (-(ε.sign a) * (ℓt a + t * d a)) := by
      have hsplit : -(ε.sign a) * (ℓt a + t * d a)
          = (-ε.sign a * ℓt a) + (-(ε.sign a) * (t * d a)) := by ring
      rw [hsplit, Real.exp_add]
      have h1 : lm ≤ Real.exp (-ε.sign a * ℓt a) := hlb a
      have h2 : Real.exp (-1 : ℝ) ≤ Real.exp (-(ε.sign a) * (t * d a)) := by
        apply Real.exp_le_exp.mpr
        have hX : |(ε.sign a) * (t * d a)| ≤ 1 := by
          rw [abs_mul]
          have hs : |ε.sign a| = 1 := by rcases ε.is_sign a with h | h <;> rw [h] <;> norm_num
          rw [hs, one_mul, abs_mul]
          calc |t| * |d a| ≤ 1 * 1 := mul_le_mul ht (hd1 a) (abs_nonneg _) zero_le_one
            _ = 1 := by norm_num
        have hle1 := (abs_le.mp hX).2
        nlinarith [hle1]
      have he1 : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      have hmul : lm * Real.exp (-1 : ℝ)
          ≤ Real.exp (-ε.sign a * ℓt a) * Real.exp (-(ε.sign a) * (t * d a)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (le_trans hlampos h1)
      have heq : lm / Real.exp 1 = lm * Real.exp (-1 : ℝ) := by rw [he1]; ring
      rw [heq]; exact hmul
    exact mul_le_mul_of_nonneg_right hexp_lb (sq_nonneg _)
  -- ===== preliminaries =====
  obtain ⟨a₀, ha₀⟩ := hlam.1
  have hlam_pos : 0 < lam := ha₀ ▸ Real.exp_pos _
  have hlam_lb : ∀ a, lam ≤ Real.exp (-ε.sign a * ℓt a) := fun a => hlam.2 ⟨a, rfl⟩
  have he_pos : (0:ℝ) < Real.exp 1 := Real.exp_pos _
  have hρ_nonneg : 0 ≤ ρ := hρ ▸ l2norm_nonneg _
  have hr0_nonneg : 0 ≤ r₀ := by
    rw [hr₀]; apply div_nonneg _ hlam_pos.le
    have : (0:ℝ) ≤ 2 * Real.exp 1 := by positivity
    exact mul_nonneg this hρ_nonneg
  rcases eq_or_lt_of_le hρ_nonneg with hρ0 | hρpos
  · -- BRANCH A: ρ = 0
    have hgradzero : ∀ a, gradG ε ℓt a = 0 := by
      have hsum_le : (∑ a, (gradG ε ℓt a) ^ 2) ≤ 0 := by
        have h : l2norm (gradG ε ℓt) = 0 := by rw [← hρ, ← hρ0]
        rw [l2norm] at h
        exact Real.sqrt_eq_zero'.mp h
      have hsum0 : ∑ a, (gradG ε ℓt a) ^ 2 = 0 :=
        le_antisymm hsum_le (Finset.sum_nonneg (fun a _ => sq_nonneg _))
      intro a
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg (gradG ε ℓt a))).mp hsum0 a
        (Finset.mem_univ a)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have hmin : ∀ m, Gobj ε ℓt ≤ Gobj ε m := by
      intro m
      set d : NonzeroMask n → ℝ := m - ℓt with hddef
      have hGmono : Monotone (fun τ : ℝ =>
          (∑ s, Real.exp (linComb (ℓt + τ • d) s) * (∑ a, d a * chi a.1 s))
            / (∑ s, Real.exp (linComb (ℓt + τ • d) s))
          + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * d a)) * (-(ε.sign a * d a))) :=
        monotone_of_deriv_nonneg (fun x => (G2 d x).differentiableAt)
          (fun x => by rw [(G2 d x).deriv]; exact G3 d x)
      have hG0 : ((∑ s, Real.exp (linComb (ℓt + (0:ℝ) • d) s) * (∑ a, d a * chi a.1 s))
            / (∑ s, Real.exp (linComb (ℓt + (0:ℝ) • d) s))
          + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + (0:ℝ) * d a)) * (-(ε.sign a * d a))) = 0 := by
        rw [G4 d]
        exact Finset.sum_eq_zero (fun a _ => by rw [hgradzero a, mul_zero])
      have hdiff : Differentiable ℝ (fun τ : ℝ => Gobj ε (ℓt + τ • d)) :=
        fun x => (G1 d x).differentiableAt
      have hmonoOn : MonotoneOn (fun τ : ℝ => Gobj ε (ℓt + τ • d)) (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hdiff.continuous.continuousOn
          hdiff.differentiableOn
        intro x hx
        rw [interior_Icc] at hx
        rw [(G1 d x).deriv]
        calc (0:ℝ) = _ := hG0.symm
          _ ≤ _ := hGmono (le_of_lt hx.1)
      have hψ01 := hmonoOn (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
        zero_le_one
      simp only [zero_smul, add_zero, one_smul] at hψ01
      have hm : ℓt + d = m := by rw [hddef]; abel
      rw [hm] at hψ01
      exact hψ01
    have heq : ℓt = lstar ε := (exists_unique_minimizer ε).unique hmin (lstar_isMinimizer ε)
    rw [← heq, sub_self]
    have : l2norm (0 : NonzeroMask n → ℝ) = 0 := by simp [l2norm]
    rw [this]; exact hr0_nonneg
  · -- BRANCH B: ρ > 0
    have hr0pos : 0 < r₀ := by
      rw [hr₀]; exact div_pos (mul_pos (mul_pos (by norm_num) he_pos) hρpos) hlam_pos
    set Δ : NonzeroMask n → ℝ := lstar ε - ℓt with hΔdef
    rcases eq_or_lt_of_le (l2norm_nonneg Δ) with hT0 | hTpos
    · rw [← hT0]; exact hr0_nonneg
    · set T : ℝ := l2norm Δ with hTdef
      set v : NonzeroMask n → ℝ := T⁻¹ • Δ with hvdef
      have hv_norm : l2norm v = 1 := by
        rw [hvdef, l2norm_smul, abs_of_pos (inv_pos.2 hTpos), ← hTdef,
          inv_mul_cancel₀ (ne_of_gt hTpos)]
      have hv_sumsq : ∑ a, (v a) ^ 2 = 1 := by
        have h := hv_norm
        rw [l2norm] at h
        have hsq := Real.sq_sqrt (Finset.sum_nonneg
          (fun a (_ : a ∈ (Finset.univ : Finset (NonzeroMask n))) => sq_nonneg (v a)))
        rw [h, one_pow] at hsq
        exact hsq.symm
      have hva_abs : ∀ a, |v a| ≤ 1 := by
        intro a
        have hle1 : (v a) ^ 2 ≤ 1 := by
          rw [← hv_sumsq]
          exact Finset.single_le_sum (fun b _ => sq_nonneg (v b)) (Finset.mem_univ a)
        nlinarith [sq_abs (v a), abs_nonneg (v a), hle1]
      have hpoint : ℓt + T • v = lstar ε := by
        rw [hvdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hTpos), one_smul, hΔdef]; abel
      set G : ℝ → ℝ := fun τ : ℝ =>
        (∑ s, Real.exp (linComb (ℓt + τ • v) s) * (∑ a, v a * chi a.1 s))
          / (∑ s, Real.exp (linComb (ℓt + τ • v) s))
        + ∑ a, Real.exp (-(ε.sign a) * (ℓt a + τ * v a)) * (-(ε.sign a * v a)) with hGdef
      have hdiffG : Differentiable ℝ G := by
        rw [hGdef]; exact fun x => (G2 v x).differentiableAt
      have hGmono : Monotone G := by
        rw [hGdef]
        exact monotone_of_deriv_nonneg (fun x => (G2 v x).differentiableAt)
          (fun x => by rw [(G2 v x).deriv]; exact G3 v x)
      have hG0val : G 0 = ∑ a, v a * gradG ε ℓt a := G4 v
      have hmin_glob : ∀ τ : ℝ, Gobj ε (ℓt + T • v) ≤ Gobj ε (ℓt + τ • v) := by
        intro τ; rw [hpoint]; exact lstar_isMinimizer ε _
      have hlocmin : IsLocalMin (fun τ : ℝ => Gobj ε (ℓt + τ • v)) T :=
        Filter.Eventually.of_forall hmin_glob
      have hGTval : G T = 0 := hlocmin.hasDerivAt_eq_zero (G1 v T)
      have hg0_ge : -ρ ≤ G 0 := by
        rw [hG0val]
        have hcs := l2_inner_le v (gradG ε ℓt)
        rw [hv_norm, ← hρ, one_mul] at hcs
        exact (abs_le.mp hcs).1
      have hcontG : ContinuousOn G (Set.Icc 0 r₀) := hdiffG.continuous.continuousOn
      have hderivMVT : ∀ x ∈ Set.Ioo (0:ℝ) r₀, HasDerivAt G (deriv G x) x :=
        fun x _ => (hdiffG x).hasDerivAt
      obtain ⟨c, hc_mem, hc_eq⟩ :=
        exists_hasDerivAt_eq_slope G (deriv G) hr0pos hcontG hderivMVT
      have hc1 : |c| ≤ 1 := by
        rw [abs_of_pos hc_mem.1]; exact le_trans (le_of_lt hc_mem.2) hle
      have hderivc_lb : lam / Real.exp 1 ≤ deriv G c := by
        rw [hGdef, (G2 v c).deriv]
        have hq := G3quot v c
        have hb : lam / Real.exp 1
            ≤ ∑ a, Real.exp (-(ε.sign a) * (ℓt a + c * v a)) * (-(ε.sign a * v a)) * (-(ε.sign a * v a)) := by
          have hbl := Bd2_lower v c lam hlam_pos.le hlam_lb hva_abs hc1
          rwa [hv_sumsq, mul_one] at hbl
        linarith [hq, hb]
      have hdiff_ge : (lam / Real.exp 1) * r₀ ≤ G r₀ - G 0 := by
        have h1 : lam / Real.exp 1 ≤ (G r₀ - G 0) / (r₀ - 0) := by rw [← hc_eq]; exact hderivc_lb
        rw [sub_zero, le_div_iff₀ hr0pos] at h1
        exact h1
      have hkey : (lam / Real.exp 1) * r₀ = 2 * ρ := by
        have hlamne : lam ≠ 0 := hlam_pos.ne'
        have hene : Real.exp 1 ≠ 0 := he_pos.ne'
        rw [hr₀]; field_simp
      have hBr0_ge : ρ ≤ G r₀ := by
        rw [hkey] at hdiff_ge; linarith [hg0_ge, hdiff_ge]
      by_contra hcon
      have hcon2 : r₀ < T := not_le.mp hcon
      have hmono_le : G r₀ ≤ G T := hGmono (le_of_lt hcon2)
      rw [hGTval] at hmono_le
      linarith [hBr0_ge, hmono_le, hρpos]
/-! ## Lemma 8.2 — the entropy-transfer bound -/

/-- Paper XII, Section 8.  Coordinate (directional) partial derivative of a
function `f : ℝ^{N-1} → ℝ` in the `a`-th coordinate direction. -/
noncomputable def partialAt (f : (NonzeroMask n → ℝ) → ℝ)
    (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) : ℝ :=
  deriv (fun t : ℝ => f (ℓ + t • Pi.single a (1 : ℝ))) 0

/-- Paper XII, Lemma 8.2 (gradient identity).  `∇𝒟(ℓ) = ∇²F(ℓ) ℓ`, componentwise:
the `a`-th partial derivative of `𝒟` equals `(∇²F(ℓ) · ℓ)_a`. -/
theorem lemma_8_2_grad (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    partialAt Dcal ℓ a = Matrix.mulVec (covMatrix ℓ) ℓ a := by
  set e : NonzeroMask n → ℝ := Pi.single a (1:ℝ) with he
  have hc0 : (ℓ + (0:ℝ) • e) = ℓ := by simp
  have hZpos : Zpart ℓ ≠ 0 := (Zpart_pos ℓ).ne'
  have hea : e a = 1 := by rw [he, Pi.single_eq_same]
  have hene : ∀ b : NonzeroMask n, b ≠ a → e b = 0 := by
    intro b hb; rw [he, Pi.single_eq_of_ne hb]
  -- (A) derivative of the linear form
  have hlin : ∀ s : Point n,
      HasDerivAt (fun t : ℝ => linComb (ℓ + t • e) s) (chi a.1 s) 0 := by
    intro s
    have hfun : (fun t : ℝ => linComb (ℓ + t • e) s)
        = (fun t : ℝ => linComb ℓ s + t * chi a.1 s) := by
      funext t
      unfold linComb
      have hstep : ∀ b : NonzeroMask n,
          (ℓ + t • e) b * chi b.1 s
            = ℓ b * chi b.1 s + t * (e b * chi b.1 s) := by
        intro b
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hpick : (∑ b : NonzeroMask n, e b * chi b.1 s) = chi a.1 s := by
        rw [Finset.sum_eq_single a (fun b _ hb => by rw [hene b hb, zero_mul])
          (fun h => absurd (Finset.mem_univ a) h), hea, one_mul]
      rw [Finset.sum_congr rfl (fun b _ => hstep b), Finset.sum_add_distrib,
        ← Finset.mul_sum, hpick]
    rw [hfun]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (chi a.1 s)).const_add (linComb ℓ s)
  -- (B) derivative of the Gibbs weight
  have hexp : ∀ s : Point n,
      HasDerivAt (fun t : ℝ => gibbsWeight (ℓ + t • e) s)
        (gibbsWeight ℓ s * chi a.1 s) 0 := by
    intro s
    have h := (hlin s).exp
    simp only [zero_smul, add_zero] at h
    exact h
  -- (C) derivative of the partition sum
  have hZ : HasDerivAt (fun t : ℝ => Zpart (ℓ + t • e))
      (∑ s, gibbsWeight ℓ s * chi a.1 s) 0 := by
    have h := HasDerivAt.sum (fun s (_ : s ∈ (Finset.univ : Finset (Point n))) => hexp s)
    have hfe : (fun t : ℝ => Zpart (ℓ + t • e))
        = ∑ s : Point n, (fun t : ℝ => gibbsWeight (ℓ + t • e) s) := by
      funext t; rw [Finset.sum_apply]; rfl
    rw [hfe]; exact h
  -- (D) derivative of the numerators
  have hNb : ∀ b : NonzeroMask n,
      HasDerivAt (fun t : ℝ => ∑ s, gibbsWeight (ℓ + t • e) s * chi b.1 s)
        (∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) 0 := by
    intro b
    have h := HasDerivAt.sum
      (fun s (_ : s ∈ (Finset.univ : Finset (Point n))) => (hexp s).mul_const (chi b.1 s))
    have hfe : (fun t : ℝ => ∑ s, gibbsWeight (ℓ + t • e) s * chi b.1 s)
        = ∑ s : Point n, (fun t : ℝ => gibbsWeight (ℓ + t • e) s * chi b.1 s) := by
      funext t; rw [Finset.sum_apply]
    rw [hfe]; exact h
  -- (E) derivative of xcoord
  have hxb : ∀ b : NonzeroMask n,
      HasDerivAt (fun t : ℝ => xcoord (ℓ + t • e) b) (covMatrix ℓ a b) 0 := by
    intro b
    have hg0 : Zpart (ℓ + (0:ℝ) • e) ≠ 0 := by rw [hc0]; exact hZpos
    have hdiv := (hNb b).div hZ hg0
    simp only [zero_smul, add_zero] at hdiv
    have hcov : covMatrix ℓ a b
        = ((∑ s, gibbsWeight ℓ s * chi a.1 s * chi b.1 s) * Zpart ℓ
            - (∑ s, gibbsWeight ℓ s * chi b.1 s) * (∑ s, gibbsWeight ℓ s * chi a.1 s))
            / Zpart ℓ ^ 2 := by
      unfold covMatrix secondMoment xcoord
      field_simp
    rw [hcov]
    exact hdiv
  -- helper: hval and hFeq for Fpart
  have hval : ((∑ s, gibbsWeight ℓ s * chi a.1 s) / (N n:ℝ)) / (Zpart ℓ / (N n:ℝ))
      = xcoord ℓ a := by
    have hN : (N n:ℝ) ≠ 0 := N_ne_zero n
    unfold xcoord
    field_simp
  have hFeq : (fun t : ℝ => Fpart (ℓ + t • e))
      = (fun t : ℝ => Real.log (Zpart (ℓ + t • e) / (N n:ℝ))) := rfl
  -- (F) derivative of Fpart
  have hFpart : HasDerivAt (fun t : ℝ => Fpart (ℓ + t • e)) (xcoord ℓ a) 0 := by
    have hZN := hZ.div_const (N n : ℝ)
    have hne : (Zpart (ℓ + (0:ℝ) • e) / (N n : ℝ)) ≠ 0 := by
      rw [hc0]; exact div_ne_zero hZpos (N_ne_zero n)
    have hlog := hZN.log hne
    simp only [zero_smul, add_zero] at hlog
    rw [hval] at hlog
    rw [hFeq]
    exact hlog
  -- (G) derivative of each coordinate curve
  have hcb : ∀ b : NonzeroMask n,
      HasDerivAt (fun t : ℝ => (ℓ + t • e) b) (e b) 0 := by
    intro b
    have hfun : (fun t : ℝ => (ℓ + t • e) b)
        = (fun t : ℝ => ℓ b + t * e b) := by
      funext t; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (e b)).const_add (ℓ b)
  -- product terms
  have hterm : ∀ b : NonzeroMask n,
      HasDerivAt (fun t : ℝ => (ℓ + t • e) b * xcoord (ℓ + t • e) b)
        (e b * xcoord ℓ b + ℓ b * covMatrix ℓ a b) 0 := by
    intro b
    have h := (hcb b).mul (hxb b)
    simp only [zero_smul, add_zero] at h
    exact h
  have hprod : HasDerivAt (fun t : ℝ => ∑ b : NonzeroMask n, (ℓ + t • e) b * xcoord (ℓ + t • e) b)
      (∑ b : NonzeroMask n, (e b * xcoord ℓ b + ℓ b * covMatrix ℓ a b)) 0 := by
    have h := HasDerivAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (NonzeroMask n))) => hterm b)
    have hfe : (fun t : ℝ => ∑ b : NonzeroMask n, (ℓ + t • e) b * xcoord (ℓ + t • e) b)
        = ∑ b : NonzeroMask n, (fun t : ℝ => (ℓ + t • e) b * xcoord (ℓ + t • e) b) := by
      funext t; rw [Finset.sum_apply]
    rw [hfe]; exact h
  -- (H) combine into Dcal
  have hDcal : HasDerivAt (fun t : ℝ => Dcal (ℓ + t • e))
      ((∑ b : NonzeroMask n, (e b * xcoord ℓ b + ℓ b * covMatrix ℓ a b)) - xcoord ℓ a) 0 :=
    hprod.sub hFpart
  -- finish
  have hsingle : (∑ b : NonzeroMask n, e b * xcoord ℓ b) = xcoord ℓ a := by
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [hene b hb, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h), hea, one_mul]
  have hmv : Matrix.mulVec (covMatrix ℓ) ℓ a = ∑ b : NonzeroMask n, covMatrix ℓ a b * ℓ b := rfl
  unfold partialAt
  rw [← he, hDcal.deriv, hmv, Finset.sum_add_distrib, hsingle, add_sub_cancel_left]
  exact Finset.sum_congr rfl (fun b _ => mul_comm (ℓ b) (covMatrix ℓ a b))
/-- Paper XII, Lemma 8.2 (operator-norm bound).  `‖∇²F(ℓ)‖_op ≤ N - 1`, expressed
via the quadratic form: `vᵀ ∇²F(ℓ) v ≤ (N-1) ‖v‖₂²`.

Proof structure: `Cov ⪯ 𝔼[χχᵀ]` (rank-one subtraction), then op-norm `≤` trace
for the PSD `𝔼[χχᵀ]`, whose trace is `∑_{a≠0} 𝔼[χ_a²] = N - 1`.  Only the middle
(spectral) step is `sorry`. -/
theorem lemma_8_2_opNorm (ℓ : NonzeroMask n → ℝ) (v : NonzeroMask n → ℝ) :
    quadForm (covMatrix ℓ) v ≤ ((N n : ℝ) - 1) * ∑ a, (v a) ^ 2 := by
  calc quadForm (covMatrix ℓ) v
      ≤ quadForm (secondMomentMatrix ℓ) v := covMatrix_le_secondMoment ℓ v
    _ ≤ Matrix.trace (secondMomentMatrix ℓ) * ∑ a, (v a) ^ 2 :=
          opNorm_le_trace_of_psd _ (secondMomentMatrix_isSymm ℓ)
            (secondMomentMatrix_psd ℓ) v
    _ = ((N n : ℝ) - 1) * ∑ a, (v a) ^ 2 := by
          rw [trace_secondMomentMatrix_eq]

/-! ## The gradient operator-norm bound (fully honest helper). -/

/-- `‖(∇²F ℓ) ℓ‖₂ = ‖(Cov ℓ) ℓ‖₂ ≤ (N-1) ‖ℓ‖₂`, from `lemma_8_2_opNorm` +
`covMatrix_psd` via a Cauchy–Schwarz / discriminant argument (no spectral theorem). -/
lemma gradNorm_bound (ℓ : NonzeroMask n → ℝ) :
    l2norm (Matrix.mulVec (covMatrix ℓ) ℓ) ≤ ((N n : ℝ) - 1) * l2norm ℓ := by
  set L : ℝ := (N n : ℝ) - 1 with hLdef
  have hLnn : 0 ≤ L := by
    have h1 : (1 : ℝ) ≤ (N n : ℝ) := by exact_mod_cast N_pos n
    simpa [hLdef] using sub_nonneg.mpr h1
  set M : Matrix (NonzeroMask n) (NonzeroMask n) ℝ := covMatrix ℓ with hMdef
  set g : NonzeroMask n → ℝ := Matrix.mulVec M ℓ with hgdef
  have hga : ∀ a, g a = ∑ b, M a b * ℓ b := fun a => Matrix.mulVec_apply_eq_sum M ℓ a
  have hMsymm : ∀ a b, M a b = M b a := by
    intro a b
    show secondMoment ℓ a b - xcoord ℓ a * xcoord ℓ b
        = secondMoment ℓ b a - xcoord ℓ b * xcoord ℓ a
    rw [mul_comm (xcoord ℓ b)]
    have : secondMoment ℓ a b = secondMoment ℓ b a := by
      unfold secondMoment
      congr 1
      exact Finset.sum_congr rfl (fun s _ => by ring)
    rw [this]
  set P : ℝ := ∑ a, (g a) ^ 2 with hPdef
  have hP1 : P = ∑ a, ∑ b, g a * M a b * ℓ b := by
    rw [hPdef]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sq, hga a, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have hP2 : P = ∑ a, ∑ b, ℓ a * M a b * g b := by
    rw [hP1]
    have step1 : (∑ a, ∑ b, g a * M a b * ℓ b) = ∑ a, ∑ b, ℓ b * M b a * g a := by
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hMsymm a b]; ring
    rw [step1, Finset.sum_comm]
  set Qℓ : ℝ := quadForm M ℓ with hQℓdef
  set Qg : ℝ := quadForm M g with hQgdef
  have poly : ∀ t : ℝ, quadForm M (fun a => t * ℓ a - g a)
      = Qℓ * (t * t) + (-2 * P) * t + Qg := by
    intro t
    have hterm : ∀ a b, (t * ℓ a - g a) * M a b * (t * ℓ b - g b)
        = (t * t) * (ℓ a * M a b * ℓ b) - t * (ℓ a * M a b * g b)
          - t * (g a * M a b * ℓ b) + (g a * M a b * g b) := fun a b => by ring
    have hexp : quadForm M (fun a => t * ℓ a - g a)
        = (t * t) * (∑ a, ∑ b, ℓ a * M a b * ℓ b)
          - t * (∑ a, ∑ b, ℓ a * M a b * g b)
          - t * (∑ a, ∑ b, g a * M a b * ℓ b)
          + (∑ a, ∑ b, g a * M a b * g b) := by
      simp only [quadForm, hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
    rw [hexp, ← hP2, ← hP1, hQℓdef, hQgdef]
    unfold quadForm
    ring
  have hquadnn : ∀ t : ℝ, 0 ≤ Qℓ * (t * t) + (-2 * P) * t + Qg := by
    intro t
    rw [← poly t]
    exact covMatrix_psd ℓ _
  have hdisc : discrim Qℓ (-2 * P) Qg ≤ 0 := discrim_le_zero hquadnn
  have hP2le : P ^ 2 ≤ Qℓ * Qg := by
    have hd : (-2 * P) ^ 2 - 4 * Qℓ * Qg ≤ 0 := by
      have := hdisc; simpa [discrim] using this
    nlinarith [hd]
  have hQg_le : Qg ≤ L * P := by
    have := lemma_8_2_opNorm ℓ g
    rw [← hMdef] at this
    calc Qg = quadForm M g := hQgdef
      _ ≤ ((N n : ℝ) - 1) * ∑ a, (g a) ^ 2 := this
      _ = L * P := by rw [hLdef, hPdef]
  set T : ℝ := ∑ a, (ℓ a) ^ 2 with hTsdef
  have hQℓ_le : Qℓ ≤ L * T := by
    have := lemma_8_2_opNorm ℓ ℓ
    rw [← hMdef] at this
    calc Qℓ = quadForm M ℓ := hQℓdef
      _ ≤ ((N n : ℝ) - 1) * ∑ a, (ℓ a) ^ 2 := this
      _ = L * T := by rw [hLdef, hTsdef]
  have hQgnn : 0 ≤ Qg := hQgdef ▸ covMatrix_psd ℓ g
  have hPnn : 0 ≤ P := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hTnn : 0 ≤ T := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have key : P ^ 2 ≤ L ^ 2 * T * P := by
    calc P ^ 2 ≤ Qℓ * Qg := hP2le
      _ ≤ (L * T) * (L * P) := by
            apply mul_le_mul hQℓ_le hQg_le hQgnn
            exact mul_nonneg hLnn hTnn
      _ = L ^ 2 * T * P := by ring
  have hP_le : P ≤ L ^ 2 * T := by
    rcases eq_or_lt_of_le hPnn with hP0 | hPpos
    · rw [← hP0]; exact mul_nonneg (sq_nonneg L) hTnn
    · have hmul : P * P ≤ (L ^ 2 * T) * P := by nlinarith [key]
      exact le_of_mul_le_mul_right hmul hPpos
  have hgoal : l2norm g ≤ L * l2norm ℓ := by
    rw [l2norm]
    have hg_sq : (∑ a, (g a) ^ 2) = P := hPdef.symm
    rw [hg_sq]
    calc Real.sqrt P ≤ Real.sqrt (L ^ 2 * T) := Real.sqrt_le_sqrt hP_le
      _ = L * Real.sqrt T := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hLnn]
      _ = L * l2norm ℓ := by rw [l2norm]
  simpa [hgdef, hLdef] using hgoal

/-! ## Differentiability of `𝒟` (fully honest; no black boxes). -/

lemma diff_sum' {ι : Type*} (u : Finset ι) (A : ι → (NonzeroMask n → ℝ) → ℝ)
    (h : ∀ i ∈ u, Differentiable ℝ (A i)) :
    Differentiable ℝ (fun ℓ => ∑ i ∈ u, A i ℓ) := by
  have e : (fun ℓ : NonzeroMask n → ℝ => ∑ i ∈ u, A i ℓ) = ∑ i ∈ u, A i :=
    (Finset.sum_fn u A).symm
  rw [e]; exact Differentiable.sum h

lemma diff_linComb (s : Point n) :
    Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ => linComb ℓ s) := by
  show Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ => ∑ a : NonzeroMask n, ℓ a * chi a.1 s)
  exact diff_sum' (Finset.univ : Finset (NonzeroMask n))
    (fun (a : NonzeroMask n) (ℓ : NonzeroMask n → ℝ) => ℓ a * chi a.1 s)
    (fun a _ => (differentiable_pi.1 differentiable_id a).mul_const (chi a.1 s))

lemma diff_Zpart : Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ => Zpart ℓ) := by
  show Differentiable ℝ (fun ℓ => ∑ s, Real.exp (linComb ℓ s))
  exact diff_sum' (Finset.univ : Finset (Point n)) (fun s ℓ => Real.exp (linComb ℓ s))
    (fun s _ => (diff_linComb s).exp)

lemma diff_Fpart : Differentiable ℝ (Fpart : (NonzeroMask n → ℝ) → ℝ) := by
  show Differentiable ℝ (fun ℓ => Real.log (EU (fun s => Real.exp (linComb ℓ s))))
  have hf : Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ =>
      EU (fun s => Real.exp (linComb ℓ s))) := by
    have e : (fun ℓ : NonzeroMask n → ℝ => EU (fun s => Real.exp (linComb ℓ s)))
        = fun ℓ => (∑ s, Real.exp (linComb ℓ s)) * (N n : ℝ)⁻¹ := by
      funext ℓ; simp only [EU, div_eq_mul_inv]
    rw [e]
    exact (diff_sum' (Finset.univ : Finset (Point n)) (fun s ℓ => Real.exp (linComb ℓ s))
      (fun s _ => (diff_linComb s).exp)).mul_const ((N n : ℝ)⁻¹)
  refine Differentiable.log hf ?_
  intro ℓ
  show EU (fun s => Real.exp (linComb ℓ s)) ≠ 0
  have hz : (0:ℝ) < EU (fun s => Real.exp (linComb ℓ s)) := by
    show (0:ℝ) < (∑ s, Real.exp (linComb ℓ s)) / (N n : ℝ)
    apply div_pos
    · exact Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
    · exact_mod_cast N_pos n
  exact hz.ne'

lemma diff_xcoord (a : NonzeroMask n) :
    Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ => xcoord ℓ a) := by
  have e : (fun ℓ : NonzeroMask n → ℝ => xcoord ℓ a)
      = fun ℓ => (∑ s, Real.exp (linComb ℓ s) * chi a.1 s) * (Zpart ℓ)⁻¹ := by
    funext ℓ; simp only [xcoord, gibbsWeight, div_eq_mul_inv]
  rw [e]
  exact Differentiable.mul
    (diff_sum' (Finset.univ : Finset (Point n))
      (fun s ℓ => Real.exp (linComb ℓ s) * chi a.1 s)
      (fun s _ => (diff_linComb s).exp.mul_const (chi a.1 s)))
    (Differentiable.inv diff_Zpart (fun ℓ => (Zpart_pos ℓ).ne'))

lemma diff_Dcal : Differentiable ℝ (Dcal : (NonzeroMask n → ℝ) → ℝ) := by
  show Differentiable ℝ (fun ℓ : NonzeroMask n → ℝ => (∑ a, ℓ a * xcoord ℓ a) - Fpart ℓ)
  apply Differentiable.sub
  · exact diff_sum' (Finset.univ : Finset (NonzeroMask n))
      (fun (a : NonzeroMask n) (ℓ : NonzeroMask n → ℝ) => ℓ a * xcoord ℓ a)
      (fun a _ => (differentiable_pi.1 differentiable_id a).mul (diff_xcoord a))
  · exact diff_Fpart

/-! ## `ℓ²` geometry: nonnegativity, homogeneity, Cauchy–Schwarz, triangle. -/

lemma l2norm_nonneg (v : NonzeroMask n → ℝ) : 0 ≤ l2norm v := Real.sqrt_nonneg _

lemma l2norm_smul (c : ℝ) (v : NonzeroMask n → ℝ) :
    l2norm (c • v) = |c| * l2norm v := by
  unfold l2norm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]; ring

lemma l2_inner_le (u w : NonzeroMask n → ℝ) :
    |∑ a, u a * w a| ≤ l2norm u * l2norm w := by
  have hcs : (∑ a, u a * w a) ^ 2 ≤ (∑ a, (u a) ^ 2) * (∑ a, (w a) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  rw [← Real.sqrt_sq_eq_abs, l2norm, l2norm,
      ← Real.sqrt_mul (Finset.sum_nonneg (fun a _ => sq_nonneg _))]
  exact Real.sqrt_le_sqrt hcs

lemma l2norm_add_le (u w : NonzeroMask n → ℝ) :
    l2norm (u + w) ≤ l2norm u + l2norm w := by
  have huw : ∑ a, u a * w a ≤ l2norm u * l2norm w :=
    (le_abs_self _).trans (l2_inner_le u w)
  have hLnn : 0 ≤ l2norm u + l2norm w := add_nonneg (l2norm_nonneg u) (l2norm_nonneg w)
  have e1 : ∑ a, ((u + w) a) ^ 2
      = ∑ a, (u a) ^ 2 + 2 * (∑ a, u a * w a) + ∑ a, (w a) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Pi.add_apply]; ring
  have hu2 : l2norm u ^ 2 = ∑ a, (u a) ^ 2 := by
    unfold l2norm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))]
  have hw2 : l2norm w ^ 2 = ∑ a, (w a) ^ 2 := by
    unfold l2norm; rw [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))]
  have hsum_le : ∑ a, ((u + w) a) ^ 2 ≤ (l2norm u + l2norm w) ^ 2 := by
    rw [e1, add_sq, hu2, hw2]; nlinarith [huw]
  calc l2norm (u + w) = Real.sqrt (∑ a, ((u + w) a) ^ 2) := by rw [l2norm]
    _ ≤ Real.sqrt ((l2norm u + l2norm w) ^ 2) := Real.sqrt_le_sqrt hsum_le
    _ = l2norm u + l2norm w := by rw [Real.sqrt_sq hLnn]

/-! ## From coordinate partials to the Fréchet derivative of `𝒟`. -/

/-- The coordinate partial equals the Fréchet derivative applied to the basis vector. -/
lemma partialAt_eq_fderiv (L : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    partialAt Dcal L a = fderiv ℝ Dcal L (Pi.single a (1:ℝ)) := by
  set e : NonzeroMask n → ℝ := Pi.single a (1:ℝ) with hedef
  have hγ : HasDerivAt (fun t : ℝ => L + t • e) e 0 := by
    have h0 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const e
    simpa using h0.const_add L
  have hcomp : HasDerivAt (fun t : ℝ => Dcal (L + t • e)) (fderiv ℝ Dcal L e) 0 := by
    have h2 := ((diff_Dcal ((fun t : ℝ => L + t • e) 0)).hasFDerivAt.comp (0:ℝ)
      hγ.hasFDerivAt).hasDerivAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, Function.comp_def, zero_smul, add_zero] at h2
    exact h2
  unfold partialAt
  exact hcomp.deriv

/-- Directional derivative of `𝒟` decomposes over coordinates:
`∇𝒟(L)·Δ = ∑_a Δ_a ∂_a 𝒟(L)`. -/
lemma fderiv_Dcal_apply (L Δ : NonzeroMask n → ℝ) :
    fderiv ℝ Dcal L Δ = ∑ a, Δ a * partialAt Dcal L a := by
  have hΔ : Δ = ∑ a, Pi.single a (Δ a) := (Finset.univ_sum_single Δ).symm
  conv_lhs => rw [hΔ]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hs : Pi.single a (Δ a) = Δ a • Pi.single a (1:ℝ) := by
    ext b; simp [Pi.single_apply]
  rw [hs, map_smul, smul_eq_mul, partialAt_eq_fderiv]

/-- Paper XII, Lemma 8.2 (entropy transfer).  In the setting of Lemma 8.1
(same `ε`, `ℓ̃ = ℓt`, `ρ`, `λ`, `r₀`), the entropy values at the numeric point
and the true minimizer differ by at most
`(N-1)(‖ℓ̃‖₂ + r₀) r₀`. -/
theorem lemma_8_2_transfer
    (ε : Orientation n) (ℓt : NonzeroMask n → ℝ)
    (ρ lam r₀ : ℝ)
    (hρ : ρ = l2norm (gradG ε ℓt))
    (hlam : IsLeast (Set.range fun a => Real.exp (- ε.sign a * ℓt a)) lam)
    (hr₀ : r₀ = 2 * Real.exp 1 * ρ / lam)
    (hle : r₀ ≤ 1) :
    |Dcal (lstar ε) - Dcal ℓt| ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ := by
  set Δ : NonzeroMask n → ℝ := lstar ε - ℓt with hΔdef
  have hΔnorm : l2norm Δ ≤ r₀ := by
    rw [hΔdef]; exact lemma_8_1 ε ℓt ρ lam r₀ hρ hlam hr₀ hle
  have hr0nn : 0 ≤ r₀ := le_trans (l2norm_nonneg Δ) hΔnorm
  have hLnn : 0 ≤ (N n : ℝ) - 1 := by
    have h1 : (1:ℝ) ≤ (N n:ℝ) := by exact_mod_cast N_pos n
    linarith
  set φ : ℝ → ℝ := fun t => Dcal (ℓt + t • Δ) with hφdef
  have hφ1 : φ 1 = Dcal (lstar ε) := by
    simp only [hφdef, one_smul]
    congr 1
    rw [hΔdef]; abel
  have hφ0 : φ 0 = Dcal ℓt := by simp only [hφdef, zero_smul, add_zero]
  have hderiv : ∀ x ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt φ (∑ a, Δ a * partialAt Dcal (ℓt + x • Δ) a) (Set.Icc 0 1) x := by
    intro x _
    have hγ : HasDerivAt (fun t : ℝ => ℓt + t • Δ) Δ x := by
      have h0 : HasDerivAt (fun t : ℝ => t • Δ) Δ x := by
        simpa using (hasDerivAt_id x).smul_const Δ
      simpa using h0.const_add ℓt
    have hcomp : HasDerivAt (fun t : ℝ => Dcal (ℓt + t • Δ))
        (fderiv ℝ Dcal (ℓt + x • Δ) Δ) x := by
      have h2 := ((diff_Dcal (ℓt + x • Δ)).hasFDerivAt.comp x hγ.hasFDerivAt).hasDerivAt
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        one_smul, Function.comp_def] at h2
      exact h2
    rw [fderiv_Dcal_apply] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0:ℝ) 1,
      ‖∑ a, Δ a * partialAt Dcal (ℓt + x • Δ) a‖
        ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x ≤ 1 := hx.2.le
    have hg : (∑ a, Δ a * partialAt Dcal (ℓt + x • Δ) a)
        = ∑ a, Δ a * (Matrix.mulVec (covMatrix (ℓt + x • Δ)) (ℓt + x • Δ) a) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [lemma_8_2_grad]
    rw [hg]
    set Lx : NonzeroMask n → ℝ := ℓt + x • Δ with hLxdef
    set g : NonzeroMask n → ℝ := Matrix.mulVec (covMatrix Lx) Lx with hgdef
    have hcs : ‖∑ a, Δ a * g a‖ ≤ l2norm Δ * l2norm g := by
      rw [Real.norm_eq_abs]; exact l2_inner_le Δ g
    have hgn : l2norm g ≤ ((N n : ℝ) - 1) * l2norm Lx := gradNorm_bound Lx
    have hLxn : l2norm Lx ≤ l2norm ℓt + r₀ := by
      have hsm : l2norm (x • Δ) = |x| * l2norm Δ := l2norm_smul x Δ
      calc l2norm Lx = l2norm (ℓt + x • Δ) := by rw [hLxdef]
        _ ≤ l2norm ℓt + l2norm (x • Δ) := l2norm_add_le _ _
        _ = l2norm ℓt + |x| * l2norm Δ := by rw [hsm]
        _ ≤ l2norm ℓt + r₀ := by
              have hxle : |x| * l2norm Δ ≤ r₀ := by
                rw [abs_of_nonneg hx0]
                calc x * l2norm Δ ≤ 1 * l2norm Δ :=
                        mul_le_mul_of_nonneg_right hx1 (l2norm_nonneg Δ)
                  _ = l2norm Δ := one_mul _
                  _ ≤ r₀ := hΔnorm
              linarith
    have hA : l2norm g ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) :=
      hgn.trans (mul_le_mul_of_nonneg_left hLxn hLnn)
    have hAnn : 0 ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) :=
      mul_nonneg hLnn (add_nonneg (l2norm_nonneg ℓt) hr0nn)
    have hfin : l2norm Δ * l2norm g ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ := by
      calc l2norm Δ * l2norm g
          ≤ r₀ * (((N n : ℝ) - 1) * (l2norm ℓt + r₀)) :=
            mul_le_mul hΔnorm hA (l2norm_nonneg g) hr0nn
        _ = ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ := by ring
    exact hcs.trans hfin
  have hC : ‖φ 1 - φ 0‖ ≤ ((N n : ℝ) - 1) * (l2norm ℓt + r₀) * r₀ :=
    norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  rw [hφ1, hφ0, Real.norm_eq_abs] at hC
  exact hC
/-! ## Theorem 8.3 — the finite main theorem (`2 ≤ n ≤ 5`) -/

/-- Paper XII, Theorem 8.3.  For `2 ≤ n ≤ 5`, every orientation satisfies
`m̂(ε) ≥ D_δ`, with equality iff `ε` is one of the `N` delta orientations
(certified margin at least `0.138`).

`sorry` — discharged by certified computation — exhaustive over the `2^{N-1}`
orientations for `n ≤ 4` and via the provably-complete 176-orbit `Γ_5`-transversal
for `n = 5` (Section 8.3), each orientation's entropy gap enclosed by exact
rational interval arithmetic through Lemmas 8.1–8.2; to be formalized with exact
`ℚ`/interval arithmetic, NOT native_decide. -/
theorem theorem_8_3 (hn : 2 ≤ n ∧ n ≤ 5) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  sorry
  -- discharged by certified computation — exhaustive over the 2^{N-1}
  -- orientations for n≤4 and via the provably-complete 176-orbit Γ_5-transversal
  -- for n=5 (Section 8.3), each orientation's entropy gap enclosed by exact
  -- rational interval arithmetic through Lemmas 8.1–8.2; to be formalized with
  -- exact ℚ/interval arithmetic, NOT native_decide.

/-! ## Section 8.3 — the symmetry group `Γ_n` and the orbit-reduction interface -/

/-- Certified-local translation action on orientations (Certified's own orbit
model; named `cTrans` to avoid clashing with `Symmetry.transOrient`). -/
def cTrans (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := fun a => by
    rcases ε.is_sign a with h | h <;> rcases chi_mem a.1 t with g | g <;> simp [h, g]

/-- Certified-local `GL(n,2)` action on orientations via a linear equivalence of
masks (`cGl φ ε` reindexes the signs by `φ⁻¹`); named `cGl` to avoid clashing
with `Symmetry.glOrient`.  The nonzero-preservation of `φ.symm` is left `sorry`. -/
noncomputable def cGl (φ : Point n ≃ₗ[ZMod 2] Point n) (ε : Orientation n) :
    Orientation n where
  sign := fun a => ε.sign ⟨φ.symm a.1, fun h => a.2 ((LinearEquiv.map_eq_zero_iff φ.symm).mp h)⟩
  is_sign := fun a => ε.is_sign _
/-- Paper XII, Lemma 3.3.  A `GL(n,2)` element is an `𝔽₂`-linear automorphism of
the mask space; it relabels a nonzero mask to another nonzero mask.  (`φ`
represents `M⁻ᵀ` in the paper's notation; as `M` ranges over `GL(n,2)`, so does
`φ` over all automorphisms of `𝔽₂ⁿ`.) -/
def maskMap (φ : Point n ≃ₗ[ZMod 2] Point n) (a : NonzeroMask n) : NonzeroMask n :=
  ⟨φ a.1, by
    intro h
    exact a.2 ((LinearEquiv.map_eq_zero_iff φ).1 h)⟩
    -- TODO(api): `LinearEquiv.map_eq_zero_iff : φ x = 0 ↔ x = 0`.

/-- Paper XII, Section 8.3.  One `Γ_n`-generator step: `ε'` is obtained from `ε`
by a translation or a `GL(n,2)` relabeling. -/
def gammaStep (ε ε' : Orientation n) : Prop :=
  (∃ t : Point n, ε' = cTrans t ε) ∨
  (∃ φ : Point n ≃ₗ[ZMod 2] Point n, ε' = cGl φ ε)

/-- Paper XII, Section 8.3.  `ε` and `ε'` lie in the same `Γ_n`-orbit iff they are
connected by generator steps (the equivalence closure of `gammaStep`). -/
def SameOrbit (ε ε' : Orientation n) : Prop := Relation.EqvGen gammaStep ε ε'
  -- TODO(api): `EqvGen r` is the equivalence-relation closure of `r`.

/-- Paper XII, Lemma 3.2 (Symmetry).  `m̂` is invariant under translations. -/
theorem mhat_transOrient (t : Point n) (ε : Orientation n) :
    mhat (cTrans t ε) = mhat ε := by
  have h : cTrans t ε = tauOrient t ε := Orientation.ext (fun a => rfl)
  rw [h]
  exact mhat_tauOrient t ε
/-- Paper XII, Lemma 3.3 (Symmetry).  `m̂` is invariant under `GL(n,2)`. -/
theorem mhat_glOrient (φ : Point n ≃ₗ[ZMod 2] Point n) (ε : Orientation n) :
    mhat (cGl φ ε) = mhat ε := by
  -- Bridge: realise `cGl φ` as `Symmetry.glOrient M` for a suitable `M ∈ GL(n,2)`.
  obtain ⟨M, hM⟩ :
      ∃ M : GLn n, ∀ b : NonzeroMask n,
        Matrix.mulVec (glTransInv M) b.1 = φ.symm b.1 := by
    set A : Matrix (Fin n) (Fin n) (ZMod 2) :=
      LinearMap.toMatrix' (φ.symm : Point n →ₗ[ZMod 2] Point n) with hA
    set B : Matrix (Fin n) (Fin n) (ZMod 2) :=
      LinearMap.toMatrix' (φ : Point n →ₗ[ZMod 2] Point n) with hB
    have hAB : A * B = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hcomp : (φ.symm : Point n →ₗ[ZMod 2] Point n) ∘ₗ (φ : Point n →ₗ[ZMod 2] Point n)
          = LinearMap.id := by ext x; simp
      rw [hcomp, LinearMap.toMatrix'_id]
    have hBA : B * A = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hcomp : (φ : Point n →ₗ[ZMod 2] Point n) ∘ₗ (φ.symm : Point n →ₗ[ZMod 2] Point n)
          = LinearMap.id := by ext x; simp
      rw [hcomp, LinearMap.toMatrix'_id]
    let uAt : (Matrix (Fin n) (Fin n) (ZMod 2))ˣ :=
      ⟨Matrix.transpose A, Matrix.transpose B,
        by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one],
        by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]⟩
    refine ⟨uAt⁻¹, fun b => ?_⟩
    have hcoe : (↑((uAt⁻¹ : GLn n)⁻¹) : Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transpose A := by
      rw [inv_inv]
    unfold glTransInv
    rw [hcoe, Matrix.transpose_transpose, hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  -- `cGl φ ε = glOrient M ε`.
  have hEq : cGl φ ε = glOrient M ε := by
    apply Orientation.ext
    intro b
    change ε.sign _ = ε.sign (glMaskInvT M b)
    congr 1
    apply Subtype.ext
    show φ.symm b.1 = Matrix.mulVec (glTransInv M) b.1
    exact (hM b).symm
  -- `calLaw` is THE calibrated-law assignment (Theorem 3.1).
  have hCal : IsCalAssignment (calLaw : Orientation n → ProbLaw n) :=
    ⟨calLaw_calibrated,
      fun ε' Q hQ => (calibrated_exists_unique ε').unique hQ (calLaw_calibrated ε')⟩
  -- Invariance of `m̂` under the `GL(n,2)` relabeling (Lemma 3.3).
  rw [hEq]
  show mhatFam calLaw (glOrient M ε) = mhatFam calLaw ε
  exact glAction_covariance_mhat calLaw hCal M ε
/-- Paper XII, Lemmas 3.2–3.3 (Symmetry).  `m̂` is constant on `Γ_n`-orbits. -/
theorem mhat_of_sameOrbit {ε ε' : Orientation n} (h : SameOrbit ε ε') :
    mhat ε = mhat ε' := by
  induction h with
  | rel x y hxy =>
      rcases hxy with ⟨t, rfl⟩ | ⟨φ, rfl⟩
      · exact (mhat_transOrient t x).symm
      · exact (mhat_glOrient φ x).symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
/-- Paper XII, Lemmas 3.2–3.3.  The delta family is a single `Γ_n`-orbit, so
`IsDelta` is `Γ_n`-invariant. -/
theorem isDelta_of_sameOrbit {ε ε' : Orientation n} (h : SameOrbit ε ε') :
    IsDelta ε ↔ IsDelta ε' := by
  -- cTrans is the same as tauOrient (same sign function).
  have cTrans_eq : ∀ (t : Point n) (δ : Orientation n), cTrans t δ = tauOrient t δ := by
    intro t δ; ext a; rfl
  -- forward preservation of IsDelta along one generator step
  have key : ∀ x y : Orientation n, gammaStep x y → IsDelta x → IsDelta y := by
    intro x y hstep hx
    obtain ⟨sstar, rfl⟩ := hx
    rcases hstep with ⟨t, rfl⟩ | ⟨φ, rfl⟩
    · -- translation: cTrans t (deltaOrientation sstar) = deltaOrientation (sstar + t)
      exact ⟨sstar + t, by rw [cTrans_eq, tauOrient_deltaOrientation]⟩
    · -- GL relabeling: build the transported base point s'
      set s' : Point n := fun i => dotZ2 (φ.symm (Pi.single i (1 : ZMod 2))) sstar with hs'
      have hdecomp : ∀ c : Point n, c = ∑ i, Pi.single i (c i) := by
        intro c; funext j; simp [Finset.sum_pi_single]
      have hbrep : ∀ b : Point n,
          (φ.symm b : Point n) = ∑ i, b i • φ.symm (Pi.single i (1 : ZMod 2)) := by
        intro b
        conv_lhs => rw [hdecomp b, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← LinearEquiv.map_smul]
        congr 1
        ext k
        by_cases hk : k = i <;> simp [smul_eq_mul, Pi.single_eq_same, Pi.single_eq_of_ne, hk]
      have hs'_eq : ∀ i, s' i = dotZ2 (φ.symm (Pi.single i (1 : ZMod 2))) sstar := fun i => rfl
      have hdot : ∀ b : Point n, dotZ2 (φ.symm b) sstar = dotZ2 b s' := by
        intro b
        rw [hbrep b]
        simp only [dotZ2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hs'_eq i]
        simp only [dotZ2]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring
      have hchi : ∀ b : Point n, chi (φ.symm b) sstar = chi b s' := by
        intro b; unfold chi; rw [hdot b]
      refine ⟨s', ?_⟩
      ext a
      show (deltaOrientation sstar).sign _ = (deltaOrientation s').sign a
      show - chi (φ.symm a.1) sstar = - chi a.1 s'
      rw [hchi a.1]
  -- one generator step is symmetric
  have gsymm : ∀ x y : Orientation n, gammaStep x y → gammaStep y x := by
    intro x y hstep
    rcases hstep with ⟨t, rfl⟩ | ⟨φ, rfl⟩
    · refine Or.inl ⟨t, ?_⟩
      ext a
      show x.sign a = (cTrans t (cTrans t x)).sign a
      show x.sign a = x.sign a * chi a.1 t * chi a.1 t
      rw [mul_assoc, chi_mul_self, mul_one]
    · refine Or.inr ⟨φ.symm, ?_⟩
      ext a
      show x.sign a = (cGl φ.symm (cGl φ x)).sign a
      show x.sign a = x.sign ⟨φ.symm (φ.symm.symm a.1), _⟩
      congr 1
      apply Subtype.ext
      show a.1 = φ.symm (φ a.1)
      rw [LinearEquiv.symm_apply_apply]
  have keyIff : ∀ x y : Orientation n, gammaStep x y → (IsDelta x ↔ IsDelta y) :=
    fun x y hr => ⟨key x y hr, key y x (gsymm x y hr)⟩
  -- induct on the equivalence closure
  unfold SameOrbit at h
  induction h with
  | rel x y hr => exact keyIff x y hr
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
/-- Paper XII, Section 8.3.  The `Γ_n`-orbit of a representative `r`. -/
def orbitOf (r : Orientation n) : Set (Orientation n) := {ε | SameOrbit r ε}

/-- Paper XII, Section 8.3.  A **complete transversal** for the `Γ_n`-action on
orientations: a finite set of orbit representatives whose orbits cover every
orientation, together with the checksum that the orbit sizes sum to the total
number of orientations `2^{N-1}` (for `n = 5`, `2^{31}`).  The checksum is the
"provably complete by construction" certificate of Section 8.3 (cross-checked
against the Burnside count, receipt `w5`). -/
structure CompleteTransversal (reps : Finset (Orientation n)) : Prop where
  /-- Every orientation lies in the orbit of some representative. -/
  covers : ∀ ε : Orientation n, ∃ r ∈ reps, SameOrbit r ε
  /-- Orbit sizes sum to `2^{N-1}` (the `∑ orbit sizes = 2^{31}` checksum at
  `n = 5`). -/
  checksum : ∑ r ∈ reps, Nat.card (orbitOf r) = 2 ^ (N n - 1)

/-- Paper XII, Section 8.3 (orbit-reduction interface).  If `reps` is a complete
transversal and Theorem 8.3's two conclusions hold on every representative, then
they hold for **every** orientation.  This is exactly how `m̂` being
`Γ_n`-invariant (Symmetry) reduces the check to the representatives — for `n = 5`,
to the 176 orbits. -/
theorem reduce_to_transversal
    (reps : Finset (Orientation n)) (hCT : CompleteTransversal reps)
    (hreps : ∀ r ∈ reps, Ddelta n ≤ mhat r ∧ (mhat r = Ddelta n ↔ IsDelta r)) :
    ∀ ε : Orientation n, Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  intro ε
  obtain ⟨r, hr, horb⟩ := hCT.covers ε
  have hm : mhat r = mhat ε := mhat_of_sameOrbit horb
  have hd : IsDelta r ↔ IsDelta ε := isDelta_of_sameOrbit horb
  obtain ⟨hge, hiff⟩ := hreps r hr
  refine ⟨hm ▸ hge, ?_⟩
  calc mhat ε = Ddelta n ↔ mhat r = Ddelta n := by rw [hm]
    _ ↔ IsDelta r := hiff
    _ ↔ IsDelta ε := hd

/-- Paper XII, Section 8.3.  The number of `Γ_n`-orbits of orientations. -/
noncomputable def orbitCount (n : ℕ) : ℕ :=
  Nat.card (Quot (gammaStep : Orientation n → Orientation n → Prop))

/-- Paper XII, Section 8.3.  The BFS over `{±1}^{31}` (with the `∑ orbit sizes =
2^{31}` checksum and the independent Burnside cross-check, receipt `w5`) yields
**176 orbits** at `n = 5`. -/
theorem orbitCount_five : orbitCount 5 = 176 := by
  sorry
  -- Certified: BFS over the 2^{31} states partitions them into 176 orbits; the
  -- orbit sizes sum to 2^{31} exactly, and an independent Burnside computation
  -- (averaging 2^{c(M)+n-r(M)} over GL(5,2)) reproduces 176.  Cf. Section 8.3.

/-- Paper XII, Section 8.2/8.3.  Cross-check: the same BFS/Burnside count gives
`2, 4, 14` orbits at `n = 2, 3, 4`, matching the exhaustive enumerations. -/
theorem orbitCount_low : orbitCount 2 = 2 ∧ orbitCount 3 = 4 ∧ orbitCount 4 = 14 := by
  sorry
  -- Cross-check of Section 8.2 exhaustive scans (8, 128, 32768 orientations) with
  -- the orbit BFS.  Cf. Section 8.3.

/-- Paper XII, Section 8.3.  Total number of orientations `= 2^{N-1}` (each is a
free `±1` choice per nonzero mask); underlies the `2^{31}` checksum at `n = 5`. -/
theorem nat_card_orientation (n : ℕ) : Nat.card (Orientation n) = 2 ^ (N n - 1) := by
  classical
  let e : Orientation n ≃ (NonzeroMask n → Bool) :=
  { toFun := fun ε a => if ε.sign a = 1 then true else false
    invFun := fun f => ⟨fun a => if f a then (1:ℝ) else -1, by
      intro a; by_cases h : f a = true
      · rw [if_pos h]; left; rfl
      · rw [if_neg h]; right; rfl⟩
    left_inv := by
      intro ε; ext a
      dsimp only
      have h1 : (-1:ℝ) ≠ 1 := by norm_num
      rcases ε.is_sign a with h | h
      · simp [h]
      · simp [h, h1]
    right_inv := by
      intro f; funext a
      dsimp only
      have h1 : (-1:ℝ) ≠ 1 := by norm_num
      by_cases hfa : f a = true
      · simp [hfa]
      · simp [hfa, h1] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
      card_nonzeroMask]
/-- Paper XII, Theorem 8.3 for `n = 5`, via the 176-orbit transversal.  Given the
provably-complete 176-representative `Γ_5`-transversal (with the `2^{31}`
checksum) and the per-representative certification of Lemmas 8.1–8.2, the main
inequality and equality set follow for **every** orientation on the `n = 5`
cube. -/
theorem theorem_8_3_n5_via_176_orbits
    (reps : Finset (Orientation 5)) (hCT : CompleteTransversal reps)
    (hcard : reps.card = 176)
    (hreps : ∀ r ∈ reps, Ddelta 5 ≤ mhat r ∧ (mhat r = Ddelta 5 ↔ IsDelta r)) :
    ∀ ε : Orientation 5, Ddelta 5 ≤ mhat ε ∧ (mhat ε = Ddelta 5 ↔ IsDelta ε) :=
  reduce_to_transversal reps hCT hreps

end WalshDelta
