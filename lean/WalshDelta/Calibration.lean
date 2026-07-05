import Mathlib
import WalshDelta.Basic

/-!
# Walsh–delta: existence, uniqueness and the entropy gap (Paper XII, Section 3)

Formalization of Section 3 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

For a parameter vector `ℓ ∈ ℝ^{N-1}` (indexed by the nonzero Walsh masks) this
file introduces:

* the log-partition function
  `F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`  (`logPartition`);
* the associated Gibbs law `P_ℓ ∝ exp(∑_{a≠0} ℓ_a χ_a)`  (`gibbs`), a
  `ProbLaw`;
* the character means `x_a(ℓ) = 𝔼_{P_ℓ}[χ_a] = ∂F/∂ℓ_a`  (`xa`);
* the calibration objective
  `G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`  (`Gfun`);
* the entropy gap of interest `m̂(ε) = D(P_ε ‖ U)`  (`mhat`).

The headline is **Theorem 3.1** (`theorem_3_1`): `G_ε` is smooth, strictly
convex and coercive; its unique minimizer `ℓ⋆` is the calibrated law of `ε`
with `h_a = ε_a ℓ⋆_a > 0`, and conversely every calibrated law arises this way,
so each orientation has exactly one calibrated law `P_ε`.

The section is decomposed into a convexity lemma (`Gfun_strictConvexOn`), a
coercivity lemma (`Gfun_coercive`), a critical-point = calibration lemma
(`critical_iff_calibrationEqs`, `calibrated_of_critical`, `hcoeff_pos_of_critical`)
and an existence/uniqueness statement (`Gfun_min_exists_unique`,
`calibrated_exists_unique`).
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## The unsigned tilt, log-partition and Gibbs law -/

/-- Paper XII, Section 3.  The (unsigned) linear tilt attached to a parameter
vector `ℓ ∈ ℝ^{N-1}`: `L_ℓ(s) = ∑_{a≠0} ℓ_a χ_a(s)`.  Unlike `tilt` (which
carries the orientation signs), here the reals `ℓ_a` absorb the signs, so that
`ℓ_a = h_a ε_a` recovers `tilt ε h`. -/
def linForm (ℓ : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  ∑ a : NonzeroMask n, ℓ a * chi a.1 s

/-- Paper XII, Section 3.  The unnormalized partition sum
`Z(ℓ) = ∑_{r} exp(L_ℓ(r))`. -/
noncomputable def gibbsZ (ℓ : NonzeroMask n → ℝ) : ℝ :=
  ∑ r, Real.exp (linForm ℓ r)

/-- The partition sum is strictly positive (sum of exponentials over the
nonempty cube). -/
lemma gibbsZ_pos (ℓ : NonzeroMask n → ℝ) : 0 < gibbsZ ℓ := by
  apply Finset.sum_pos
  · intro r _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

/-- Paper XII, Section 3.  The log-partition function
`F(ℓ) = log 𝔼_U exp(∑_{a≠0} ℓ_a χ_a)`.  Its gradient is the character-mean
vector and its Hessian is `Cov_{P_ℓ}(χ) ⪰ 0` (used in `logPartition_convexOn`). -/
noncomputable def logPartition (ℓ : NonzeroMask n → ℝ) : ℝ :=
  Real.log (EU (fun s => Real.exp (linForm ℓ s)))

/-- Paper XII, Section 3.  The Gibbs law `P_ℓ(s) ∝ exp(∑_{a≠0} ℓ_a χ_a(s))`,
packaged as a full-support `ProbLaw`. -/
noncomputable def gibbs (ℓ : NonzeroMask n → ℝ) : ProbLaw n where
  P := fun s => Real.exp (linForm ℓ s) / gibbsZ ℓ
  pos := fun s => div_pos (Real.exp_pos _) (gibbsZ_pos ℓ)
  sum_one := by
    have hZ : gibbsZ ℓ ≠ 0 := (gibbsZ_pos ℓ).ne'
    rw [← Finset.sum_div]
    show gibbsZ ℓ / gibbsZ ℓ = 1
    exact div_self hZ

/-- Paper XII, Section 3.  The character means of the Gibbs law,
`x_a(ℓ) = 𝔼_{P_ℓ}[χ_a]`.  Theorem 3.1's gradient identity reads
`∂F/∂ℓ_a = x_a(ℓ)`. -/
noncomputable def xa (ℓ : NonzeroMask n → ℝ) (a : Point n) : ℝ :=
  EP (gibbs ℓ) (fun s => chi a s)

/-! ## The calibration objective `G_ε` -/

/-- Paper XII, Theorem 3.1.  The calibration objective
`G_ε(ℓ) = F(ℓ) + ∑_{a≠0} e^{-ε_a ℓ_a}`. -/
noncomputable def Gfun (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : ℝ :=
  logPartition ℓ + ∑ a : NonzeroMask n, Real.exp (-(ε.sign a * ℓ a))

/-! ## Coercivity predicate -/

/-- Coercivity on the finite-dimensional space `ℝ^{N-1}`: `g(ℓ) → ∞` as
`‖ℓ‖ → ∞`.  (Equivalently `Tendsto g (cocompact _) atTop`.) -/
def Coercive (g : (NonzeroMask n → ℝ) → ℝ) : Prop :=
  ∀ C : ℝ, ∃ R : ℝ, ∀ ℓ : NonzeroMask n → ℝ, R ≤ ‖ℓ‖ → C ≤ g ℓ

/-! ## Smoothness -/

/-- Paper XII, Theorem 3.1 (smoothness).  `F` is smooth: `𝔼_U exp(L_ℓ) > 0` for
every `ℓ`, and `log` of a strictly positive smooth function is smooth. -/
lemma logPartition_contDiff : ContDiff ℝ ⊤ (logPartition (n := n)) := by
  have hlin : ∀ s : Point n, ContDiff ℝ ⊤ (fun ℓ : NonzeroMask n → ℝ => linForm ℓ s) := by
    intro s
    unfold linForm
    apply ContDiff.sum
    intro a _
    exact (contDiff_apply ℝ ℝ a).mul contDiff_const
  have hexp : ∀ s : Point n, ContDiff ℝ ⊤ (fun ℓ : NonzeroMask n → ℝ => Real.exp (linForm ℓ s)) := by
    intro s
    exact Real.contDiff_exp.comp (hlin s)
  have hg : ContDiff ℝ ⊤ (fun ℓ : NonzeroMask n → ℝ => EU (fun s => Real.exp (linForm ℓ s))) := by
    unfold EU
    apply ContDiff.div_const
    apply ContDiff.sum
    intro s _
    exact hexp s
  have hpos : ∀ ℓ : NonzeroMask n → ℝ, EU (fun s => Real.exp (linForm ℓ s)) ≠ 0 := by
    intro ℓ
    have : 0 < EU (fun s => Real.exp (linForm ℓ s)) := by
      unfold EU
      apply div_pos
      · apply Finset.sum_pos
        · intro r _; exact Real.exp_pos _
        · exact Finset.univ_nonempty
      · exact_mod_cast N_pos n
    exact this.ne'
  unfold logPartition
  exact hg.log hpos
/-- Paper XII, Theorem 3.1 (smoothness).  Each barrier `ℓ ↦ e^{-ε_a ℓ_a}` and
hence the whole objective `G_ε` is smooth. -/
lemma Gfun_contDiff (ε : Orientation n) : ContDiff ℝ ⊤ (Gfun ε) := by
  unfold Gfun
  refine logPartition_contDiff.add ?_
  refine ContDiff.sum (fun a _ => ?_)
  refine Real.contDiff_exp.comp ?_
  have h1 : ContDiff ℝ ⊤ (fun ℓ : NonzeroMask n → ℝ => ℓ a) := contDiff_apply ℝ ℝ a
  exact (h1.const_smul (ε.sign a)).neg
/-! ## Convexity lemma -/

/-- Paper XII, Theorem 3.1 (convexity of `F`).  `∇²F = Cov_{P_ℓ}(χ) ⪰ 0`, so
`F` is convex on `ℝ^{N-1}`. -/
lemma logPartition_convexOn :
    ConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (logPartition (n := n)) := by
  have hLP : ∀ ℓ : NonzeroMask n → ℝ,
      logPartition ℓ = Real.log (∑ s, Real.exp (linForm ℓ s)) - Real.log (N n) := by
    intro ℓ
    have hsum : (0:ℝ) < ∑ s, Real.exp (linForm ℓ s) :=
      Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
    simp only [logPartition, EU]
    rw [Real.log_div hsum.ne' (Nat.cast_ne_zero.mpr (N_pos n).ne')]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hFpos : (0:ℝ) < ∑ s, Real.exp (linForm x s) :=
    Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  have hGpos : (0:ℝ) < ∑ s, Real.exp (linForm y s) :=
    Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · -- a = 0
    have ha0' : a = 0 := ha0.symm
    subst ha0'
    have hb1 : b = 1 := by linarith
    subst hb1
    simp only [zero_smul, zero_add, one_smul, zero_mul, one_mul, le_refl]
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · -- b = 0
      have hb0' : b = 0 := hb0.symm
      subst hb0'
      have ha1 : a = 1 := by linarith
      subst ha1
      simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, le_refl]
    · -- 0 < a, 0 < b
      rw [hLP (a • x + b • y), hLP x, hLP y]
      have hlin : ∀ s, linForm (a • x + b • y) s
          = a * linForm x s + b * linForm y s := by
        intro s
        simp only [linForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun c _ => by ring)
      have hexp : ∀ s, Real.exp (linForm (a • x + b • y) s)
          = Real.exp (linForm x s) ^ a * Real.exp (linForm y s) ^ b := by
        intro s
        rw [hlin s, Real.exp_add, mul_comm a (linForm x s), mul_comm b (linForm y s),
            Real.exp_mul, Real.exp_mul]
      have hpq : (a⁻¹).HolderConjugate (b⁻¹) :=
        Real.HolderConjugate.inv_inv ha0 hb0 hab
      have hia : (1:ℝ) / a⁻¹ = a := by rw [one_div, inv_inv]
      have hib : (1:ℝ) / b⁻¹ = b := by rw [one_div, inv_inv]
      have hsumF : (∑ s, |Real.exp (linForm x s) ^ a| ^ a⁻¹)
          = ∑ s, Real.exp (linForm x s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le a),
            ← Real.rpow_mul (Real.exp_pos _).le, mul_inv_cancel₀ ha0.ne', Real.rpow_one]
      have hsumG : (∑ s, |Real.exp (linForm y s) ^ b| ^ b⁻¹)
          = ∑ s, Real.exp (linForm y s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le b),
            ← Real.rpow_mul (Real.exp_pos _).le, mul_inv_cancel₀ hb0.ne', Real.rpow_one]
      have hZbound : (∑ s, Real.exp (linForm (a • x + b • y) s))
          ≤ (∑ s, Real.exp (linForm x s)) ^ a * (∑ s, Real.exp (linForm y s)) ^ b := by
        calc (∑ s, Real.exp (linForm (a • x + b • y) s))
            = ∑ s, Real.exp (linForm x s) ^ a * Real.exp (linForm y s) ^ b :=
              Finset.sum_congr rfl (fun s _ => hexp s)
          _ ≤ (∑ s, |Real.exp (linForm x s) ^ a| ^ a⁻¹) ^ (1 / a⁻¹)
                * (∑ s, |Real.exp (linForm y s) ^ b| ^ b⁻¹) ^ (1 / b⁻¹) :=
              Real.inner_le_Lp_mul_Lq (Finset.univ : Finset (Point n))
                (fun s => Real.exp (linForm x s) ^ a)
                (fun s => Real.exp (linForm y s) ^ b) hpq
          _ = (∑ s, Real.exp (linForm x s)) ^ a * (∑ s, Real.exp (linForm y s)) ^ b := by
              rw [hsumF, hsumG, hia, hib]
      have hZpos : (0:ℝ) < ∑ s, Real.exp (linForm (a • x + b • y) s) :=
        Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
      have hlog : Real.log (∑ s, Real.exp (linForm (a • x + b • y) s))
          ≤ a * Real.log (∑ s, Real.exp (linForm x s))
            + b * Real.log (∑ s, Real.exp (linForm y s)) := by
        have hle := Real.log_le_log hZpos hZbound
        rwa [Real.log_mul (by positivity) (by positivity),
            Real.log_rpow hFpos, Real.log_rpow hGpos] at hle
      have hN : a * Real.log (N n) + b * Real.log (N n) = Real.log (N n) := by
        rw [← add_mul, hab, one_mul]
      linarith [hlog, hN]
/-- Paper XII, Theorem 3.1 (strict convexity).  Each barrier
`e^{-ε_a ℓ_a}` is smooth and convex with strictly positive second derivative in
the coordinate `ℓ_a`, so `∇²G_ε ⪰ diag(e^{-ε_a ℓ_a}) ≻ 0` and `G_ε` is
strictly convex. -/
lemma Gfun_strictConvexOn (ε : Orientation n) :
    StrictConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (Gfun ε) := by
  have hbar : StrictConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ))
      (fun ℓ : NonzeroMask n → ℝ => ∑ a : NonzeroMask n, Real.exp (-(ε.sign a * ℓ a))) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ hxy a b ha hb hab
    have e : ∀ i : NonzeroMask n,
        -(ε.sign i * ((a • x + b • y) i))
          = a * (-(ε.sign i * x i)) + b * (-(ε.sign i * y i)) := by
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hle : ∀ i ∈ (Finset.univ : Finset (NonzeroMask n)),
        Real.exp (-(ε.sign i * ((a • x + b • y) i)))
          ≤ a * Real.exp (-(ε.sign i * x i)) + b * Real.exp (-(ε.sign i * y i)) := by
      intro i _
      rw [e i]
      have h := convexOn_exp.2 (Set.mem_univ (-(ε.sign i * x i)))
        (Set.mem_univ (-(ε.sign i * y i))) ha.le hb.le hab
      simp only [smul_eq_mul] at h
      exact h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    have hs : ε.sign i ≠ 0 := by rcases ε.is_sign i with h | h <;> simp [h]
    have huv : -(ε.sign i * x i) ≠ -(ε.sign i * y i) := by
      intro h
      exact hi (mul_left_cancel₀ hs (neg_injective h))
    have hlt : ∃ i ∈ (Finset.univ : Finset (NonzeroMask n)),
        Real.exp (-(ε.sign i * ((a • x + b • y) i)))
          < a * Real.exp (-(ε.sign i * x i)) + b * Real.exp (-(ε.sign i * y i)) := by
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [e i]
      have h := strictConvexOn_exp.2 (Set.mem_univ (-(ε.sign i * x i)))
        (Set.mem_univ (-(ε.sign i * y i))) huv ha hb hab
      simp only [smul_eq_mul] at h
      exact h
    have hsum := Finset.sum_lt_sum hle hlt
    have rhs :
        (∑ i : NonzeroMask n,
          (a * Real.exp (-(ε.sign i * x i)) + b * Real.exp (-(ε.sign i * y i))))
        = a • (∑ i : NonzeroMask n, Real.exp (-(ε.sign i * x i)))
          + b • (∑ i : NonzeroMask n, Real.exp (-(ε.sign i * y i))) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      simp [smul_eq_mul]
    calc
      (∑ i : NonzeroMask n, Real.exp (-(ε.sign i * ((a • x + b • y) i))))
          < ∑ i : NonzeroMask n,
              (a * Real.exp (-(ε.sign i * x i)) + b * Real.exp (-(ε.sign i * y i))) := hsum
      _ = a • (∑ i : NonzeroMask n, Real.exp (-(ε.sign i * x i)))
            + b • (∑ i : NonzeroMask n, Real.exp (-(ε.sign i * y i))) := rhs
  have hconv := (logPartition_convexOn (n := n)).add_strictConvexOn hbar
  exact hconv
/-! ## Coercivity lemma -/

/-- Paper XII, Theorem 3.1 (coercivity, radial step).  For every unit direction
`v ≠ 0`, `μ(v) := max_s ⟨v, χ(s)⟩ > 0` (the characters are linearly independent
and `⟨v, χ(·)⟩` has zero mean), whence `F(tv) ≥ t μ(v) − log N → ∞`. -/
lemma logPartition_radial_tendsto (v : NonzeroMask n → ℝ) (hv : v ≠ 0) :
    Filter.Tendsto (fun t : ℝ => logPartition (fun a => t * v a)) Filter.atTop
      Filter.atTop := by
  -- char-2 helpers
  have hself : ∀ p : Point n, p + p = 0 := by
    intro p; funext i; simp only [Pi.add_apply, Pi.zero_apply]
    have h : ∀ z : ZMod 2, z + z = 0 := by decide
    exact h (p i)
  have habeq : ∀ p q : Point n, p + q = 0 → p = q := by
    intro p q h
    have h2 : p + q + q = q := by rw [h, zero_add]
    rw [add_assoc, hself q, add_zero] at h2
    exact h2
  -- character sum (Walsh orthogonality, single character)
  have hchisum : ∀ c : Point n, (∑ s, chi c s) = if c = 0 then (N n : ℝ) else 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc
      rw [if_pos rfl]
      simp only [chi_zero, Finset.sum_const, Finset.card_univ, card_point, nsmul_eq_mul, mul_one]
    · rw [if_neg hc]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
      simp only [Pi.zero_apply] at hj
      set ej : Point n := Pi.single j (1 : ZMod 2) with hej
      have hdot : dotZ2 c ej = c j := by
        unfold dotZ2
        rw [Finset.sum_eq_single j]
        · rw [hej, Pi.single_eq_same, mul_one]
        · intro i _ hij; rw [hej, Pi.single_eq_of_ne hij, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hchi_ej : chi c ej = -1 := by unfold chi; rw [hdot, if_neg hj]
      have hpt : ∀ s : Point n, chi c (s + ej) = chi c s * chi c ej := by
        intro s
        have hadd : dotZ2 c (s + ej) = dotZ2 c s + dotZ2 c ej := by
          simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        have hvz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        have key2 : ∀ x y : ZMod 2, (if x + y = 0 then (1:ℝ) else -1)
            = (if x = 0 then (1:ℝ) else -1) * (if y = 0 then (1:ℝ) else -1) := by
          intro x y; rcases hvz x with hx | hx <;> rcases hvz y with hy | hy <;>
            subst hx <;> subst hy <;> simp [show (1:ZMod 2) + 1 = 0 from by decide]
        simp only [chi, hadd]; exact key2 _ _
      have hbij : (∑ s, chi c (s + ej)) = ∑ s, chi c s :=
        Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi c (s + ej)) (chi c) (fun x => rfl)
      have hflip : (∑ s, chi c (s + ej)) = ∑ s, (- chi c s) :=
        Finset.sum_congr rfl (fun s _ => by rw [hpt, hchi_ej, mul_neg_one])
      rw [hflip, Finset.sum_neg_distrib] at hbij
      linarith [hbij]
  -- orthogonality of two characters
  have horth : ∀ p q : Point n, (∑ s, chi p s * chi q s) = if p + q = 0 then (N n : ℝ) else 0 := by
    intro p q
    have hrw : (∑ s, chi p s * chi q s) = ∑ s, chi (p + q) s := by
      apply Finset.sum_congr rfl; intro s _; rw [chi_add]
    rw [hrw, hchisum (p + q)]
  -- linForm is homogeneous
  have hlin : ∀ (t : ℝ) (s : Point n), linForm (fun a => t * v a) s = t * linForm v s := by
    intro t s
    unfold linForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    dsimp only
    ring
  -- zero mean of s ↦ linForm v s
  have hmean0 : (∑ s, linForm v s) = 0 := by
    unfold linForm
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    rw [← Finset.mul_sum, hchisum a.1, if_neg a.2, mul_zero]
  -- not identically zero
  have hnz : ∃ s, linForm v s ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv
    funext b
    rw [Pi.zero_apply]
    -- compute the b-th Walsh coefficient two ways
    have hS : (∑ s, linForm v s * chi b.1 s) = v b * (N n : ℝ) := by
      have e1 : (∑ s, linForm v s * chi b.1 s)
          = ∑ a : NonzeroMask n, v a * (∑ s, chi a.1 s * chi b.1 s) := by
        unfold linForm
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have e2 : (∑ a : NonzeroMask n, v a * (∑ s, chi a.1 s * chi b.1 s))
          = ∑ a : NonzeroMask n, v a * (if a.1 + b.1 = 0 then (N n : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [horth a.1 b.1]
      have hsingle2 : (∑ a : NonzeroMask n, v a * (if a.1 + b.1 = 0 then (N n : ℝ) else 0))
          = v b * (if b.1 + b.1 = 0 then (N n : ℝ) else 0) := by
        apply Finset.sum_eq_single
        · intro a _ hab
          rw [if_neg (fun h => hab (Subtype.ext (habeq a.1 b.1 h))), mul_zero]
        · intro h; exact absurd (Finset.mem_univ b) h
      rw [e1, e2, hsingle2, if_pos (hself b.1)]
    have hzero : (∑ s, linForm v s * chi b.1 s) = 0 := by
      apply Finset.sum_eq_zero; intro s _; rw [hcon s, zero_mul]
    rw [hS] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (N_ne_zero n)
  -- argmax
  haveI : Nonempty (Point n) := ⟨0⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_max (fun s => linForm v s)
  -- the max is strictly positive
  have hμpos : 0 < linForm v s0 := by
    by_contra hle
    push_neg at hle
    have hnonpos : ∀ s ∈ (Finset.univ : Finset (Point n)), linForm v s ≤ 0 :=
      fun s _ => le_trans (hs0 s) hle
    have hall0 : ∀ s ∈ (Finset.univ : Finset (Point n)), linForm v s = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hmean0
    obtain ⟨s1, hs1⟩ := hnz
    exact hs1 (hall0 s1 (Finset.mem_univ s1))
  -- affine lower bound on the ray
  have hNpos : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have key : ∀ t : ℝ,
      linForm v s0 * t + -Real.log (N n : ℝ) ≤ logPartition (fun a => t * v a) := by
    intro t
    have hfun : (fun s => Real.exp (linForm (fun a => t * v a) s))
        = (fun s => Real.exp (t * linForm v s)) := by
      funext s; rw [hlin t s]
    have hsum_pos : (0 : ℝ) < ∑ s, Real.exp (t * linForm v s) :=
      Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
    have hsingle : Real.exp (t * linForm v s0) ≤ ∑ s, Real.exp (t * linForm v s) :=
      Finset.single_le_sum (f := fun s => Real.exp (t * linForm v s))
        (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ s0)
    have hlogsum : linForm v s0 * t ≤ Real.log (∑ s, Real.exp (t * linForm v s)) := by
      have h1 : Real.log (Real.exp (t * linForm v s0))
          ≤ Real.log (∑ s, Real.exp (t * linForm v s)) :=
        Real.log_le_log (Real.exp_pos _) hsingle
      rwa [Real.log_exp, mul_comm] at h1
    unfold logPartition
    rw [hfun]
    unfold EU
    rw [Real.log_div hsum_pos.ne' hNpos.ne']
    linarith [hlogsum]
  -- assemble the tendsto
  have hmul : Filter.Tendsto (fun t : ℝ => linForm v s0 * t) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hμpos Filter.tendsto_id
  have hmin : Filter.Tendsto (fun t : ℝ => linForm v s0 * t + -Real.log (N n : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (-Real.log (N n : ℝ)) hmul
  exact Filter.tendsto_atTop_mono key hmin
/-- Paper XII, Theorem 3.1 (coercivity).  `G_ε` is coercive on `ℝ^{N-1}`. -/
lemma Gfun_coercive (ε : Orientation n) : Coercive (Gfun ε) := by
  intro C
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0 : the index set is empty, ‖ℓ‖ = 0, so the condition is vacuous.
    refine ⟨1, fun ℓ hR => ?_⟩
    exfalso
    have hIE : IsEmpty (NonzeroMask n) := by
      subst hn0
      constructor
      rintro ⟨a, ha⟩
      exact ha (Subsingleton.elim a 0)
    have hz : ℓ = 0 := funext (fun a => hIE.elim a)
    rw [hz, norm_zero] at hR
    linarith
  · -- n ≥ 1 : the genuine coercivity argument.
    -- Character orthogonality: ∑_s χ_c(s) = 0 for c ≠ 0.
    have sum_chi_zero : ∀ (c : Point n), c ≠ 0 → (∑ s, chi c s) = 0 := by
      intro c hc
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
      simp only [Pi.zero_apply] at hj
      set ej : Point n := Pi.single j (1 : ZMod 2) with hej
      have hdot : dotZ2 c ej = c j := by
        unfold dotZ2
        rw [Finset.sum_eq_single j]
        · rw [hej, Pi.single_eq_same, mul_one]
        · intro i _ hij; rw [hej, Pi.single_eq_of_ne hij, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hcj : c j = 1 := by
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (c j) with h | h
        · exact absurd h hj
        · exact h
      have hadddot : ∀ s, dotZ2 c (s + ej) = dotZ2 c s + c j := by
        intro s
        have h1 : dotZ2 c (s + ej) = dotZ2 c s + dotZ2 c ej := by
          simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [h1, hdot]
      have hflip : ∀ s, chi c (s + ej) = - chi c s := by
        intro s
        unfold chi
        rw [hadddot s, hcj]
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (dotZ2 c s) with h | h <;>
          rw [h] <;> simp [show ((1:ZMod 2) + 1) = 0 from by decide]
      have hbij : (∑ s, chi c (s + ej)) = ∑ s, chi c s :=
        Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi c (s + ej)) (chi c) (fun x => rfl)
      have hneg : (∑ s, chi c (s + ej)) = ∑ s, (- chi c s) :=
        Finset.sum_congr rfl (fun s _ => hflip s)
      rw [hneg, Finset.sum_neg_distrib] at hbij
      linarith [hbij]
    -- Orthogonality of a pair of characters summed over s.
    have orth : ∀ (a b : NonzeroMask n),
        (∑ s, chi a.1 s * chi b.1 s) = if a = b then (N n : ℝ) else 0 := by
      intro a b
      have hmul : ∀ s, chi a.1 s * chi b.1 s = chi (a.1 + b.1) s :=
        fun s => (chi_add a.1 b.1 s).symm
      simp_rw [hmul]
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        have hself : a.1 + a.1 = 0 := by
          funext i
          have hz : ∀ z : ZMod 2, z + z = 0 := by decide
          simp only [Pi.add_apply, Pi.zero_apply]
          exact hz (a.1 i)
        rw [hself]
        simp only [chi_zero, Finset.sum_const, Finset.card_univ, card_point, nsmul_eq_mul,
          mul_one]
      · rw [if_neg hab]
        apply sum_chi_zero
        intro h
        apply hab
        have heq : a.1 = b.1 := by
          funext i
          have hi := congrFun h i
          simp only [Pi.add_apply, Pi.zero_apply] at hi
          have hz : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
          exact hz _ _ hi
        exact Subtype.ext heq
    -- Zero mean of L_ℓ.
    have sumx0 : ∀ (ℓ : NonzeroMask n → ℝ), (∑ s, linForm ℓ s) = 0 := by
      intro ℓ
      unfold linForm
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro a _
      rw [← Finset.mul_sum, sum_chi_zero a.1 a.2, mul_zero]
    -- Second moment of L_ℓ.
    have sumx2 : ∀ (ℓ : NonzeroMask n → ℝ),
        (∑ s, (linForm ℓ s)^2) = (N n : ℝ) * ∑ a, (ℓ a)^2 := by
      intro ℓ
      have step1 : (∑ s, (linForm ℓ s)^2)
          = ∑ a, ∑ b, (ℓ a * ℓ b) * (∑ s, chi a.1 s * chi b.1 s) := by
        unfold linForm
        simp_rw [sq, Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        ring
      rw [step1]
      simp_rw [orth]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl]; ring
      · intro b _ hba; rw [if_neg (Ne.symm hba)]; ring
      · intro h; exact absurd (Finset.mem_univ a) h
    -- Nonemptiness of the index set and N ≥ 2.
    have hne : Nonempty (NonzeroMask n) := by
      obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      refine ⟨⟨Pi.single i (1 : ZMod 2), ?_⟩⟩
      intro h
      have hh := congrFun h i
      simp only [Pi.single_eq_same, Pi.zero_apply] at hh
      exact one_ne_zero hh
    have hN2 : 2 ≤ N n := by
      rw [N_eq]
      calc (2:ℕ) = 2^1 := (pow_one 2).symm
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hnpos
    have hN2R : (2:ℝ) ≤ (N n : ℝ) := by exact_mod_cast hN2
    have hNm1_pos : (0:ℝ) < (N n : ℝ) - 1 := by linarith
    have hNpos : (0:ℝ) < (N n : ℝ) := by linarith
    -- Provide the threshold.
    refine ⟨((N n : ℝ) - 1) * (C + Real.log (N n : ℝ)), fun ℓ hR => ?_⟩
    -- ‖ℓ‖² ≤ ∑ (ℓ a)²  (sup-norm ≤ ℓ²-norm).
    have hTge : ‖ℓ‖^2 ≤ ∑ a, (ℓ a)^2 := by
      have hnorm_le : ‖ℓ‖ ≤ Real.sqrt (∑ a, (ℓ a)^2) := by
        rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
        intro a
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        apply Real.sqrt_le_sqrt
        exact Finset.single_le_sum (fun b _ => sq_nonneg (ℓ b)) (Finset.mem_univ a)
      calc ‖ℓ‖^2 ≤ (Real.sqrt (∑ a, (ℓ a)^2))^2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
        _ = ∑ a, (ℓ a)^2 := Real.sq_sqrt (Finset.sum_nonneg (fun b _ => sq_nonneg _))
    -- ∃ s₀, ∑ (ℓ a)² ≤ (L_ℓ s₀)²  (a term at least the average).
    have hexists : ∃ s₀, (∑ a, (ℓ a)^2) ≤ (linForm ℓ s₀)^2 := by
      have heq : ∑ _s : Point n, (∑ a, (ℓ a)^2) = ∑ s : Point n, (linForm ℓ s)^2 := by
        rw [Finset.sum_const, Finset.card_univ, card_point, nsmul_eq_mul, sumx2]
      obtain ⟨s₀, _, hs₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty heq.le
      exact ⟨s₀, hs₀⟩
    obtain ⟨s₀, hs₀⟩ := hexists
    have hnorm_sq_le : ‖ℓ‖^2 ≤ (linForm ℓ s₀)^2 := le_trans hTge hs₀
    -- ∃ s', ‖ℓ‖/(N-1) ≤ L_ℓ s'.
    have hstar : ∃ s', ‖ℓ‖ / ((N n : ℝ) - 1) ≤ linForm ℓ s' := by
      rcases lt_or_ge (linForm ℓ s₀) 0 with hneg | hpos
      · have hge : ‖ℓ‖ ≤ - linForm ℓ s₀ := by
          have h1 : |‖ℓ‖| ≤ - linForm ℓ s₀ := by
            apply abs_le_of_sq_le_sq
            · rw [neg_sq]; exact hnorm_sq_le
            · linarith
          rwa [abs_of_nonneg (norm_nonneg ℓ)] at h1
        have hsum_erase : ∑ s ∈ Finset.univ.erase s₀, linForm ℓ s = - linForm ℓ s₀ := by
          rw [Finset.sum_erase_eq_sub (Finset.mem_univ s₀), sumx0]
          ring
        have hcard : (Finset.univ.erase s₀).card = N n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ s₀), Finset.card_univ, card_point]
        have hnef : (Finset.univ.erase s₀).Nonempty := by
          rw [← Finset.card_pos, hcard]; omega
        have hne0 : ((N n : ℝ) - 1) ≠ 0 := ne_of_gt hNm1_pos
        have hconst_le : ∑ _s ∈ Finset.univ.erase s₀, (‖ℓ‖ / ((N n : ℝ) - 1))
            ≤ ∑ s ∈ Finset.univ.erase s₀, linForm ℓ s := by
          rw [Finset.sum_const, hcard, hsum_erase, nsmul_eq_mul,
            Nat.cast_sub (by omega : 1 ≤ N n), Nat.cast_one]
          have hmd : ((N n : ℝ) - 1) * (‖ℓ‖ / ((N n : ℝ) - 1)) = ‖ℓ‖ := by
            rw [mul_comm]; exact div_mul_cancel₀ ‖ℓ‖ hne0
          rw [hmd]; exact hge
        obtain ⟨s', _, hs'⟩ := Finset.exists_le_of_sum_le hnef hconst_le
        exact ⟨s', hs'⟩
      · refine ⟨s₀, ?_⟩
        have hge : ‖ℓ‖ ≤ linForm ℓ s₀ := by
          have h1 : |‖ℓ‖| ≤ linForm ℓ s₀ := abs_le_of_sq_le_sq hnorm_sq_le hpos
          rwa [abs_of_nonneg (norm_nonneg ℓ)] at h1
        calc ‖ℓ‖ / ((N n : ℝ) - 1) ≤ ‖ℓ‖ :=
              div_le_self (norm_nonneg _) (by linarith)
          _ ≤ linForm ℓ s₀ := hge
    obtain ⟨s', hs'⟩ := hstar
    -- Lower bound of the log-partition by a single term.
    have hlp : linForm ℓ s' - Real.log (N n : ℝ) ≤ logPartition ℓ := by
      have hA : (0:ℝ) < EU (fun s => Real.exp (linForm ℓ s)) := by
        unfold EU
        exact div_pos (Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty) hNpos
      have hsum_ge : Real.exp (linForm ℓ s') ≤ ∑ r, Real.exp (linForm ℓ r) :=
        Finset.single_le_sum (fun r _ => (Real.exp_pos _).le) (Finset.mem_univ s')
      unfold logPartition
      rw [Real.le_log_iff_exp_le hA, Real.exp_sub, Real.exp_log hNpos]
      unfold EU
      exact div_le_div_of_nonneg_right hsum_ge (le_of_lt hNpos)
    -- Barrier terms are nonnegative.
    have hbar : (0:ℝ) ≤ ∑ a : NonzeroMask n, Real.exp (-(ε.sign a * ℓ a)) :=
      Finset.sum_nonneg (fun a _ => (Real.exp_pos _).le)
    have hGge : logPartition ℓ ≤ Gfun ε ℓ := by unfold Gfun; linarith
    -- Assemble.
    have hstep : linForm ℓ s' - Real.log (N n : ℝ) ≤ Gfun ε ℓ := le_trans hlp hGge
    have hfin : (C + Real.log (N n : ℝ)) ≤ linForm ℓ s' := by
      have hdiv : (C + Real.log (N n : ℝ)) ≤ ‖ℓ‖ / ((N n : ℝ) - 1) := by
        rw [le_div_iff₀ hNm1_pos, mul_comm]; exact hR
      exact le_trans hdiv hs'
    linarith [hstep, hfin]
/-! ## Gradient and the critical-point = calibration lemma -/

/-- Paper XII, Section 3.  Partial derivative of the log-partition:
`∂F/∂ℓ_a = 𝔼_{P_ℓ}[χ_a] = x_a(ℓ)`. -/
lemma logPartition_partialDeriv (ℓ : NonzeroMask n → ℝ) (a : NonzeroMask n) :
    deriv (fun t : ℝ => logPartition (Function.update ℓ a t)) (ℓ a)
      = xa ℓ a.1 := by
  -- Step 1: derivative of the linear form in the coordinate `ℓ_a`.
  have hlin : ∀ s : Point n,
      HasDerivAt (fun t : ℝ => linForm (Function.update ℓ a t) s) (chi a.1 s) (ℓ a) := by
    intro s
    have hterm : ∀ b : NonzeroMask n, HasDerivAt
        (fun t : ℝ => Function.update ℓ a t b * chi b.1 s)
        ((if b = a then (1:ℝ) else 0) * chi b.1 s) (ℓ a) := by
      intro b
      by_cases hb : b = a
      · have hfun : (fun t : ℝ => Function.update ℓ a t b * chi b.1 s)
                  = (fun t : ℝ => t * chi b.1 s) := by
          funext t; simp [hb]
        rw [hfun, if_pos hb]
        simpa using (hasDerivAt_id (ℓ a)).mul_const (chi b.1 s)
      · have hfun : (fun t : ℝ => Function.update ℓ a t b * chi b.1 s)
                  = (fun _ : ℝ => ℓ b * chi b.1 s) := by
          funext t; rw [Function.update_of_ne hb]
        rw [hfun, if_neg hb, zero_mul]
        exact hasDerivAt_const (ℓ a) (ℓ b * chi b.1 s)
    have hsum := HasDerivAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (NonzeroMask n))) => hterm b)
    have hcoef : (∑ b : NonzeroMask n, (if b = a then (1:ℝ) else 0) * chi b.1 s) = chi a.1 s := by
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl, one_mul]
      · intro b _ hb; rw [if_neg hb, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [hcoef] at hsum
    have hfe : (fun t : ℝ => linForm (Function.update ℓ a t) s)
        = ∑ b : NonzeroMask n, (fun t : ℝ => Function.update ℓ a t b * chi b.1 s) := by
      funext t
      simp only [Finset.sum_apply, linForm]
    rw [hfe]
    exact hsum
  -- Step 2: derivative of `exp ∘ linForm`.
  have hexp : ∀ s : Point n,
      HasDerivAt (fun t : ℝ => Real.exp (linForm (Function.update ℓ a t) s))
        (Real.exp (linForm ℓ s) * chi a.1 s) (ℓ a) := by
    intro s
    have h := (hlin s).exp
    rw [Function.update_eq_self] at h
    exact h
  -- Step 3: derivative of the partition sum.
  have hZsum : HasDerivAt (fun t : ℝ => ∑ s, Real.exp (linForm (Function.update ℓ a t) s))
      (∑ s, Real.exp (linForm ℓ s) * chi a.1 s) (ℓ a) := by
    have h := HasDerivAt.sum
      (fun s (_ : s ∈ (Finset.univ : Finset (Point n))) => hexp s)
    have hfe : (fun t : ℝ => ∑ s, Real.exp (linForm (Function.update ℓ a t) s))
        = ∑ s : Point n, (fun t : ℝ => Real.exp (linForm (Function.update ℓ a t) s)) := by
      funext t; rw [Finset.sum_apply]
    rw [hfe]; exact h
  -- Step 4: divide by `N` to get `EU`.
  have hEU := hZsum.div_const (N n : ℝ)
  -- Step 5: apply `log`.
  have hne : (∑ s, Real.exp (linForm (Function.update ℓ a (ℓ a)) s)) / (N n : ℝ) ≠ 0 := by
    rw [Function.update_eq_self]
    exact div_ne_zero (gibbsZ_pos ℓ).ne' (N_ne_zero n)
  -- helper equality for `xa`
  have hxa : xa ℓ a.1 = (∑ s, Real.exp (linForm ℓ s) * chi a.1 s) / gibbsZ ℓ := by
    simp only [xa, EP]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    rw [show (gibbs ℓ).P s = Real.exp (linForm ℓ s) / gibbsZ ℓ from rfl]
    ring
  have hN : (N n : ℝ) ≠ 0 := N_ne_zero n
  have hZ : gibbsZ ℓ ≠ 0 := (gibbsZ_pos ℓ).ne'
  -- Assemble via `HasDerivAt.log` and evaluate the derivative.
  have key : deriv (fun t : ℝ => logPartition (Function.update ℓ a t)) (ℓ a)
      = ((∑ s, Real.exp (linForm ℓ s) * chi a.1 s) / (N n : ℝ))
        / ((∑ s, Real.exp (linForm (Function.update ℓ a (ℓ a)) s)) / (N n : ℝ)) :=
    (hEU.log hne).deriv
  rw [key, Function.update_eq_self, hxa,
      show (∑ s, Real.exp (linForm ℓ s)) = gibbsZ ℓ from rfl]
  field_simp
/-- Paper XII, Theorem 3.1 (critical equation).  Partial derivative of the
objective: `∂G_ε/∂ℓ_a = x_a(ℓ) − ε_a e^{-ε_a ℓ_a}`. -/
lemma Gfun_partialDeriv (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (a : NonzeroMask n) :
    deriv (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a)
      = xa ℓ a.1 - ε.sign a * Real.exp (-(ε.sign a * ℓ a)) := by
  -- smoothness of `t ↦ update ℓ a t`
  have hupd : ContDiff ℝ ⊤ (fun t : ℝ => Function.update ℓ a t) := by
    rw [contDiff_pi]
    intro b
    by_cases hba : b = a
    · have h : (fun t : ℝ => Function.update ℓ a t b) = fun t => t := by
        funext t; rw [hba]; exact Function.update_self a t ℓ
      rw [h]; exact contDiff_id
    · have h : (fun t : ℝ => Function.update ℓ a t b) = fun _ => ℓ b := by
        funext t; exact Function.update_of_ne hba t ℓ
      rw [h]; exact contDiff_const
  -- logPartition part
  have hL_diff : DifferentiableAt ℝ
      (fun t : ℝ => logPartition (Function.update ℓ a t)) (ℓ a) :=
    ((logPartition_contDiff.comp hupd).differentiable (by simp)).differentiableAt
  have hL : HasDerivAt (fun t : ℝ => logPartition (Function.update ℓ a t))
      (xa ℓ a.1) (ℓ a) := by
    have h := hL_diff.hasDerivAt
    rwa [logPartition_partialDeriv] at h
  -- barrier part, term by term
  have key : ∀ b : NonzeroMask n,
      HasDerivAt (fun t : ℝ => Real.exp (-(ε.sign b * Function.update ℓ a t b)))
        (Real.exp (-(ε.sign b * ℓ b))
          * -(ε.sign b * (if b = a then (1 : ℝ) else 0))) (ℓ a) := by
    intro b
    have hb : HasDerivAt (fun t : ℝ => Function.update ℓ a t b)
        (if b = a then (1 : ℝ) else 0) (ℓ a) := by
      by_cases hba : b = a
      · have h : (fun t : ℝ => Function.update ℓ a t b) = fun t => t := by
          funext t; rw [hba]; exact Function.update_self a t ℓ
        rw [h, if_pos hba]; exact hasDerivAt_id (ℓ a)
      · have h : (fun t : ℝ => Function.update ℓ a t b) = fun _ => ℓ b := by
          funext t; exact Function.update_of_ne hba t ℓ
        rw [h, if_neg hba]; exact hasDerivAt_const (ℓ a) (ℓ b)
    have hg : HasDerivAt (fun t : ℝ => -(ε.sign b * Function.update ℓ a t b))
        (-(ε.sign b * (if b = a then (1 : ℝ) else 0))) (ℓ a) :=
      (hb.const_mul (ε.sign b)).neg
    have he := hg.exp
    have hupd_eq : Function.update ℓ a (ℓ a) = ℓ := by
      funext c; by_cases hc : c = a
      · rw [hc]; exact Function.update_self a (ℓ a) ℓ
      · exact Function.update_of_ne hc (ℓ a) ℓ
    rwa [hupd_eq] at he
  have hbar : HasDerivAt
      (fun t : ℝ => ∑ b : NonzeroMask n,
          Real.exp (-(ε.sign b * Function.update ℓ a t b)))
      (∑ b : NonzeroMask n, Real.exp (-(ε.sign b * ℓ b))
          * -(ε.sign b * (if b = a then (1 : ℝ) else 0))) (ℓ a) := by
    have heq : (fun t : ℝ => ∑ b : NonzeroMask n,
          Real.exp (-(ε.sign b * Function.update ℓ a t b)))
        = (∑ b : NonzeroMask n,
            fun t : ℝ => Real.exp (-(ε.sign b * Function.update ℓ a t b))) := by
      funext t; rw [Finset.sum_apply]
    rw [heq]
    exact HasDerivAt.sum (fun b (_ : b ∈ Finset.univ) => key b)
  have hsum_eq : (∑ b : NonzeroMask n, Real.exp (-(ε.sign b * ℓ b))
      * -(ε.sign b * (if b = a then (1 : ℝ) else 0)))
      = -(ε.sign a) * Real.exp (-(ε.sign a * ℓ a)) := by
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]; ring
    · intro b _ hba; rw [if_neg hba]; ring
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hsum_eq] at hbar
  have hd : HasDerivAt (fun t : ℝ => Gfun ε (Function.update ℓ a t))
      (xa ℓ a.1 + -ε.sign a * Real.exp (-(ε.sign a * ℓ a))) (ℓ a) := by
    have heq2 : (fun t : ℝ => Gfun ε (Function.update ℓ a t))
        = (fun t : ℝ => logPartition (Function.update ℓ a t))
          + (fun t : ℝ => ∑ b : NonzeroMask n,
              Real.exp (-(ε.sign b * Function.update ℓ a t b))) := by
      funext t; rfl
    rw [heq2]
    exact hL.add hbar
  rw [hd.deriv]
  ring
/-- Paper XII, Theorem 3.1.  `ℓ` is a critical point of `G_ε` when every partial
derivative vanishes. -/
def IsCritical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) : Prop :=
  ∀ a : NonzeroMask n,
    deriv (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a) = 0

/-- Paper XII, Theorem 3.1 (critical point = calibration equations).  `ℓ` is a
critical point of `G_ε` iff the self-calibration fixed point holds for `P_ℓ`
with `h_a = ε_a ℓ_a`, i.e. `𝔼_{P_ℓ}[ε_a χ_a] = e^{-ε_a ℓ_a}` for every
`a ≠ 0`. -/
lemma critical_iff_calibrationEqs (ε : Orientation n) (ℓ : NonzeroMask n → ℝ) :
    IsCritical ε ℓ ↔
      ∀ a : NonzeroMask n,
        EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s)
          = Real.exp (-(ε.sign a * ℓ a)) := by
  have hsq : ∀ a : NonzeroMask n, ε.sign a * ε.sign a = 1 := by
    intro a; rcases ε.is_sign a with h | h <;> rw [h] <;> ring
  have hEP : ∀ a : NonzeroMask n,
      EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s) = ε.sign a * xa ℓ a.1 := by
    intro a
    simp only [xa, EP]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _; ring
  constructor
  · intro hcrit a
    have h0 := hcrit a
    rw [Gfun_partialDeriv ε ℓ a] at h0
    have hx : xa ℓ a.1 = ε.sign a * Real.exp (-(ε.sign a * ℓ a)) := sub_eq_zero.1 h0
    rw [hEP a, hx, ← mul_assoc, hsq a, one_mul]
  · intro hcal a
    have hcala := hcal a
    rw [hEP a] at hcala
    have hx : xa ℓ a.1 = ε.sign a * Real.exp (-(ε.sign a * ℓ a)) := by
      rw [← hcala, ← mul_assoc, hsq a, one_mul]
    show deriv (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a) = 0
    rw [Gfun_partialDeriv ε ℓ a, hx]; ring
/-- Paper XII, Theorem 3.1 (critical point ⇒ calibrated law).  A critical point
`ℓ` yields a calibrated law `P_ℓ` for `ε` with parameters `h_a = ε_a ℓ_a`. -/
lemma calibrated_of_critical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (hcrit : IsCritical ε ℓ) : Calibrated (gibbs ℓ) ε := by
  refine ⟨fun a => ε.sign a * ℓ a, ?_, ?_⟩
  · have htilt : ∀ s, tilt ε (fun a => ε.sign a * ℓ a) s = linForm ℓ s := by
      intro s
      unfold tilt linForm
      apply Finset.sum_congr rfl
      intro a _
      have hsq : ε.sign a * ε.sign a = 1 := by
        rcases ε.is_sign a with h | h <;> rw [h] <;> ring
      calc (ε.sign a * ℓ a) * ε.sign a * chi a.1 s
          = ℓ a * (ε.sign a * ε.sign a) * chi a.1 s := by ring
        _ = ℓ a * 1 * chi a.1 s := by rw [hsq]
        _ = ℓ a * chi a.1 s := by ring
    intro s
    show Real.exp (linForm ℓ s) / gibbsZ ℓ
        = Real.exp (tilt ε (fun a => ε.sign a * ℓ a) s)
          / (∑ r, Real.exp (tilt ε (fun a => ε.sign a * ℓ a) r))
    rw [htilt s]
    congr 1
    unfold gibbsZ
    apply Finset.sum_congr rfl
    intro r _
    rw [htilt r]
  · intro a
    have := (critical_iff_calibrationEqs ε ℓ).1 hcrit a
    simpa using this
/-- Paper XII, Theorem 3.1 (positivity of the parameters).  At a critical point
`h_a = ε_a ℓ_a > 0` for every nonzero mask, because
`e^{-h_a} = |𝔼_P[χ_a]| < 1` for any full-support law with the nonconstant
`±1`-valued `χ_a`. -/
lemma hcoeff_pos_of_critical (ε : Orientation n) (ℓ : NonzeroMask n → ℝ)
    (hcrit : IsCritical ε ℓ) (a : NonzeroMask n) : 0 < ε.sign a * ℓ a := by
  -- calibration equation at `a`
  have hE : EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s)
      = Real.exp (-(ε.sign a * ℓ a)) := (critical_iff_calibrationEqs ε ℓ).1 hcrit a
  -- χ_a(0) = 1
  have h0 : chi a.1 (0 : Point n) = 1 := by
    unfold chi dotZ2
    simp
  -- a ≠ 0 ⇒ some coordinate is nonzero
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp a.2
  have hi₀' : a.1 i₀ ≠ 0 := by simpa using hi₀
  -- indicator point giving χ_a = -1
  set s_ind : Point n := fun i => if i = i₀ then (1 : ZMod 2) else 0 with hs_ind
  have hdot : dotZ2 a.1 s_ind = a.1 i₀ := by
    simp only [dotZ2, hs_ind]
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  have hchi_ind : chi a.1 s_ind = -1 := by
    unfold chi; rw [hdot, if_neg hi₀']
  -- there is a point where ε_a χ_a = -1
  obtain ⟨s0, hs0⟩ : ∃ s0, ε.sign a * chi a.1 s0 = -1 := by
    rcases ε.is_sign a with hsg | hsg
    · exact ⟨s_ind, by rw [hsg, one_mul]; exact hchi_ind⟩
    · exact ⟨(0 : Point n), by rw [hsg, h0]; norm_num⟩
  -- ε_a χ_a ≤ 1 everywhere
  have hle : ∀ s, ε.sign a * chi a.1 s ≤ 1 := by
    intro s
    rcases ε.is_sign a with hsg | hsg <;> rcases chi_mem a.1 s with hc | hc <;>
      rw [hsg, hc] <;> norm_num
  -- E < 1
  have hEP : EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s) < 1 := by
    have h1 : (∑ s, (gibbs ℓ).P s * (ε.sign a * chi a.1 s)) < ∑ s, (gibbs ℓ).P s := by
      apply Finset.sum_lt_sum
      · intro s _
        have hp := (gibbs ℓ).pos s
        nlinarith [hle s, hp]
      · exact ⟨s0, Finset.mem_univ s0, by rw [hs0]; nlinarith [(gibbs ℓ).pos s0]⟩
    calc EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s)
        = ∑ s, (gibbs ℓ).P s * (ε.sign a * chi a.1 s) := rfl
      _ < ∑ s, (gibbs ℓ).P s := h1
      _ = 1 := (gibbs ℓ).sum_one
  -- conclude
  rw [hE] at hEP
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm] at hEP
  have hneg := Real.exp_lt_exp.mp hEP
  linarith
/-! ## Existence, uniqueness, and the calibrated law `P_ε` -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness of the minimizer).  The
smooth, strictly convex, coercive `G_ε` attains a unique global minimum. -/
lemma Gfun_min_exists_unique (ε : Orientation n) :
    ∃! ℓstar : NonzeroMask n → ℝ,
      IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) ℓstar := by
  -- Existence: coercivity + continuity.
  obtain ⟨R, hR⟩ := Gfun_coercive ε (Gfun ε 0)
  set Rball : ℝ := max R 0 with hRball
  have hRball_nonneg : 0 ≤ Rball := le_max_right _ _
  set K : Set (NonzeroMask n → ℝ) := Metric.closedBall 0 Rball with hK
  have hKcompact : IsCompact K := isCompact_closedBall 0 Rball
  have h0K : (0 : NonzeroMask n → ℝ) ∈ K := by
    simp [hK, Metric.mem_closedBall, hRball_nonneg]
  have hKne : K.Nonempty := ⟨0, h0K⟩
  have hcont : ContinuousOn (Gfun ε) K := (Gfun_contDiff ε).continuous.continuousOn
  obtain ⟨ℓ0, hℓ0K, hℓ0min⟩ := hKcompact.exists_isMinOn hKne hcont
  -- `ℓ0` minimises on `K`; in particular `Gfun ℓ0 ≤ Gfun 0`.
  have hle0 : Gfun ε ℓ0 ≤ Gfun ε 0 := hℓ0min h0K
  -- `ℓ0` is a global minimiser.
  have hglobal : IsMinOn (Gfun ε) Set.univ ℓ0 := by
    rw [isMinOn_iff]
    intro ℓ _
    by_cases hnorm : ‖ℓ‖ ≤ Rball
    · exact hℓ0min (by simp [hK, Metric.mem_closedBall, dist_eq_norm, hnorm])
    · rw [not_le] at hnorm
      have hRle : R ≤ ‖ℓ‖ := le_of_lt (lt_of_le_of_lt (le_max_left R 0) hnorm)
      exact le_trans hle0 (hR ℓ hRle)
  -- Uniqueness: strict convexity.
  refine ⟨ℓ0, hglobal, ?_⟩
  intro y hy
  exact (Gfun_strictConvexOn ε).eq_of_isMinOn hy hglobal (Set.mem_univ _) (Set.mem_univ _)
/-- Paper XII, Theorem 3.1.  The unique minimizer `ℓ⋆(ε)` of `G_ε`. -/
noncomputable def ellStar (ε : Orientation n) : NonzeroMask n → ℝ :=
  Classical.choose (Gfun_min_exists_unique ε)

/-- `ℓ⋆(ε)` is indeed a global minimizer of `G_ε`. -/
lemma ellStar_isMinOn (ε : Orientation n) :
    IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) (ellStar ε) :=
  (Classical.choose_spec (Gfun_min_exists_unique ε)).1

/-- Paper XII, Theorem 3.1.  The (unique) calibrated law of `ε`,
`P_ε := P_{ℓ⋆(ε)}`. -/
noncomputable def calLaw (ε : Orientation n) : ProbLaw n :=
  gibbs (ellStar ε)

/-- Paper XII, Theorem 3.1.  The minimizer `ℓ⋆` is a critical point of `G_ε`. -/
lemma ellStar_isCritical (ε : Orientation n) : IsCritical ε (ellStar ε) := by
  intro a
  set ℓ := ellStar ε with hℓ
  have hmin := ellStar_isMinOn ε
  -- φ has a global (hence local) minimum at ℓ a
  have hloc : IsLocalMin (fun t : ℝ => Gfun ε (Function.update ℓ a t)) (ℓ a) := by
    have hminOn : IsMinOn (fun t : ℝ => Gfun ε (Function.update ℓ a t))
        (Set.univ : Set ℝ) (ℓ a) := by
      intro t _
      have hle : Gfun ε ℓ ≤ Gfun ε (Function.update ℓ a t) := hmin (Set.mem_univ _)
      simpa [Function.update_eq_self] using hle
    exact hminOn.isLocalMin (Filter.univ_mem)
  exact hloc.deriv_eq_zero
/-- Paper XII, Theorem 3.1.  The calibrated law `P_ε` is calibrated for `ε`. -/
lemma calLaw_calibrated (ε : Orientation n) : Calibrated (calLaw ε) ε :=
  calibrated_of_critical ε (ellStar ε) (ellStar_isCritical ε)

/-- Paper XII, Theorem 3.1 ("exactly one calibrated law").  Every orientation
has a unique calibrated law. -/
theorem calibrated_exists_unique (ε : Orientation n) :
    ∃! P : ProbLaw n, Calibrated P ε := by
  -- A convex differentiable function whose coordinate partials all vanish is a
  -- global minimizer.
  have critical_imp_min : ∀ m : NonzeroMask n → ℝ, IsCritical ε m →
      IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) m := by
    intro m hm
    have hdiff : Differentiable ℝ (Gfun ε) := (Gfun_contDiff ε).differentiable (by simp)
    set D := fderiv ℝ (Gfun ε) m with hD
    have hfd : HasFDerivAt (Gfun ε) D m := (hdiff m).hasFDerivAt
    -- Each coordinate partial derivative of `Gfun ε` at `m` is `D (Pi.single a 1) = 0`.
    have hpart : ∀ a : NonzeroMask n, D (Pi.single a (1 : ℝ)) = 0 := by
      intro a
      have hcurve : HasDerivAt (Function.update m a) (Pi.single a (1 : ℝ)) (m a) :=
        hasDerivAt_update m a (m a)
      have hfd' : HasFDerivAt (Gfun ε) D (Function.update m a (m a)) := by
        rw [Function.update_eq_self]; exact hfd
      have hcomp : HasDerivAt (fun t : ℝ => Gfun ε (Function.update m a t))
          (D (Pi.single a (1 : ℝ))) (m a) := hfd'.comp_hasDerivAt (m a) hcurve
      have := hm a
      rw [hcomp.deriv] at this
      exact this
    -- Hence the full derivative is zero.
    have hD0 : D = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.zero_apply, zero_apply]
      conv_lhs => rw [pi_eq_sum_univ' v]
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro a _
      rw [map_smul, hpart a, smul_zero]
    have hfd0 : HasFDerivAt (Gfun ε) 0 m := hD0 ▸ hfd
    -- Restrict to the segment through `m` and any `x`, use the 1-D convex criterion.
    have hconvG : ConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (Gfun ε) :=
      (Gfun_strictConvexOn ε).convexOn
    rw [isMinOn_iff]
    intro x _
    have hg_conv : ConvexOn ℝ (Set.univ : Set ℝ)
        (fun t : ℝ => Gfun ε (AffineMap.lineMap (k := ℝ) m x t)) := by
      have h := hconvG.comp_affineMap (AffineMap.lineMap (k := ℝ) m x)
      rw [Set.preimage_univ] at h
      exact h
    have hline : HasDerivAt (AffineMap.lineMap (k := ℝ) m x) (x - m) 0 :=
      AffineMap.hasDerivAt_lineMap
    have hgderiv : HasDerivAt (fun t : ℝ => Gfun ε (AffineMap.lineMap (k := ℝ) m x t))
        ((0 : (NonzeroMask n → ℝ) →L[ℝ] ℝ) (x - m)) 0 := by
      have hfdb : HasFDerivAt (Gfun ε) (0 : (NonzeroMask n → ℝ) →L[ℝ] ℝ)
          ((AffineMap.lineMap (k := ℝ) m x) (0 : ℝ)) := by
        rw [AffineMap.lineMap_apply_zero]; exact hfd0
      exact hfdb.comp_hasDerivAt (0 : ℝ) hline
    rw [ContinuousLinearMap.zero_apply] at hgderiv
    have hrd : derivWithin (fun t : ℝ => Gfun ε (AffineMap.lineMap (k := ℝ) m x t)) (Set.Ioi 0) 0 = 0 :=
      hgderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0)
    have hmin1 : IsMinOn (fun t : ℝ => Gfun ε (AffineMap.lineMap (k := ℝ) m x t))
        (Set.univ : Set ℝ) 0 :=
      hg_conv.isMinOn_of_rightDeriv_eq_zero (by rw [interior_univ]; exact Set.mem_univ 0) hrd
    have hle := (isMinOn_iff.mp hmin1) 1 (Set.mem_univ 1)
    simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hle
    exact hle
  -- Now the existence/uniqueness statement.
  refine ⟨calLaw ε, calLaw_calibrated ε, ?_⟩
  intro Q hQ
  obtain ⟨h, hgibbs, hcalib⟩ := hQ
  set ℓ : NonzeroMask n → ℝ := fun a => ε.sign a * h a with hℓ
  have htilt : ∀ s, tilt ε h s = linForm ℓ s := by
    intro s
    unfold tilt linForm
    apply Finset.sum_congr rfl
    intro a _
    simp only [hℓ]; ring
  have hZ : (∑ r, Real.exp (tilt ε h r)) = gibbsZ ℓ := by
    unfold gibbsZ
    apply Finset.sum_congr rfl
    intro r _
    rw [htilt r]
  -- `Q = gibbs ℓ`.
  have hQeq : Q = gibbs ℓ := by
    have hPeq : Q.P = (gibbs ℓ).P := by
      funext s
      rw [hgibbs s]
      show Real.exp (tilt ε h s) / (∑ r, Real.exp (tilt ε h r))
        = Real.exp (linForm ℓ s) / gibbsZ ℓ
      rw [htilt s, hZ]
    cases Q with
    | mk QP Qpos Qsum =>
      cases hg : gibbs ℓ with
      | mk GP Gpos Gsum =>
        simp only at hPeq
        rw [hg] at hPeq
        simp only at hPeq
        subst hPeq
        rfl
  -- `ℓ` is critical.
  have hcrit : IsCritical ε ℓ := by
    rw [critical_iff_calibrationEqs]
    intro a
    have hEP : EP (gibbs ℓ) (fun s => ε.sign a * chi a.1 s)
        = EP Q (fun s => ε.sign a * chi a.1 s) := by rw [hQeq]
    rw [hEP, hcalib a]
    congr 1
    have hsq : ε.sign a * ℓ a = h a := by
      simp only [hℓ]
      rcases ε.is_sign a with hs | hs <;> rw [hs] <;> ring
    rw [hsq]
  -- Critical points of the strictly convex `Gfun ε` coincide with the unique minimizer.
  have hmin : IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) ℓ :=
    critical_imp_min ℓ hcrit
  have hℓstar : ℓ = ellStar ε :=
    (Gfun_min_exists_unique ε).unique hmin (ellStar_isMinOn ε)
  rw [hQeq, hℓstar]
  rfl
/-! ## The entropy gap of interest -/

/-- Paper XII, Section 1.1 / Section 3.  The entropy gap of the orientation,
`m̂(ε) = D(P_ε ‖ U) = 𝔼_U[X log X] ≥ 0` — the quantity minimized by the main
theorem. -/
noncomputable def mhat (ε : Orientation n) : ℝ := Dkl (calLaw ε)

/-- Paper XII, §1.2.  The delta entropy value `D_δ = m̂(ε⋆)` (canonical home). -/
noncomputable def Ddelta (n : ℕ) : ℝ := mhat (deltaOrientation (0 : Point n))

/-! ## Theorem 3.1 (headline) -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  For every orientation
`ε`, the objective `G_ε` is smooth, strictly convex and coercive on
`ℝ^{N-1}`; its unique global minimizer `ℓ⋆` gives the calibrated law of `ε`
with `h_a = ε_a ℓ⋆_a > 0`, and conversely every calibrated law arises this
way.  In particular each orientation has exactly one calibrated law `P_ε`. -/
theorem theorem_3_1 (ε : Orientation n) :
    ContDiff ℝ ⊤ (Gfun ε)
    ∧ StrictConvexOn ℝ (Set.univ : Set (NonzeroMask n → ℝ)) (Gfun ε)
    ∧ Coercive (Gfun ε)
    ∧ IsMinOn (Gfun ε) (Set.univ : Set (NonzeroMask n → ℝ)) (ellStar ε)
    ∧ Calibrated (calLaw ε) ε
    ∧ (∀ a : NonzeroMask n, 0 < ε.sign a * ellStar ε a)
    ∧ (∃! P : ProbLaw n, Calibrated P ε) := by
  refine ⟨Gfun_contDiff ε, Gfun_strictConvexOn ε, Gfun_coercive ε,
    ellStar_isMinOn ε, calLaw_calibrated ε, ?_, calibrated_exists_unique ε⟩
  intro a
  exact hcoeff_pos_of_critical ε (ellStar ε) (ellStar_isCritical ε) a

end WalshDelta
