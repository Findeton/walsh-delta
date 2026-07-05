import Mathlib
import WalshDelta.Basic
import WalshDelta.Calibration

/-!
# Walsh–delta: the symmetry group (Paper XII, Section 3, Lemmas 3.2–3.3)

This file records the exact symmetry group of the calibration problem: the
translation action `τ_t` and the `GL(n,2)` relabeling action on orientations,
together with the two covariance lemmas (Paper XII, Lemmas 3.2 and 3.3) and
their corollary that the entropy functional `m̂` is constant on the orbits of
`Γ_n = ⟨translations, GL(n,2)⟩` while the `N` delta orientations form exactly
one `Γ_n`-orbit.

## Forward references

The calibrated law `P_ε` of an orientation and its entropy value
`m̂(ε) = D(P_ε ‖ U)` are produced by the existence/uniqueness theorem
(Paper XII, Theorem 3.1), formalized in the existence module.  Here we do NOT
re-derive that theorem; instead the covariance statements are phrased against
an abstract assignment `Pcal : Orientation n → ProbLaw n` that is *THE* unique
calibrated law of each orientation (`IsCalAssignment Pcal` below), which is
precisely the content Theorem 3.1 supplies.  The delta orientation itself is
`WalshDelta.deltaOrientation` from `Basic`.

## Public names exported by this file

  Orientation.ext, sign_mul_sign,
  dotZ2_comm, chi_comm, chi_add_right,
  transOrient,
  GLn, glAct, glTransInv, glMaskInvT, glOrient, glOrient_one,
  dotZ2_mulVec, chi_mulVec,
  delta_translation, delta_injective, delta_single_translation_orbit,
  delta_glAction,
  IsCalAssignment, mhatFam,
  translation_covariance_law, translation_covariance_mhat,
  glAction_covariance_law, glAction_covariance_mhat,
  gammaAct, mhat_gamma_invariant,
  delta_gamma_transitive, delta_gamma_closed
-/

namespace WalshDelta

open scoped BigOperators
open scoped Matrix

variable {n : ℕ}

/-! ## Extensionality and a sign-arithmetic helper -/

-- `Orientation.ext` is canonical in `Basic` (imported).

/-- A product of two `±1` reals is again `±1`.  Used to show the translation
and `GL` actions preserve the `Orientation` sign condition. -/
lemma sign_mul_sign {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;> norm_num

/-! ## Additivity of the Walsh character in the point argument

`Basic` records additivity of `χ` in the *mask* argument (`chi_add`).  The
pairing `⟨a,s⟩` is symmetric, so `χ` is additive in the *point* argument too;
this is what the translation covariance needs. -/

/-- Paper XII, Section 1.1.  The `𝔽₂`-pairing is symmetric: `⟨a,s⟩ = ⟨s,a⟩`. -/
lemma dotZ2_comm (a s : Point n) : dotZ2 a s = dotZ2 s a := by
  unfold dotZ2
  exact Finset.sum_congr rfl (fun i _ => mul_comm (a i) (s i))

/-- Paper XII, Section 1.1.  Walsh characters are symmetric in their two
`𝔽₂ⁿ` arguments: `χ_a(s) = χ_s(a)`. -/
lemma chi_comm (a s : Point n) : chi a s = chi s a := by
  unfold chi
  rw [dotZ2_comm]

/-- Paper XII, Section 1.1: `χ_a(s + t) = χ_a(s) · χ_a(t)` (additivity in the
point argument; the mask-argument version is `chi_add`). -/
lemma chi_add_right (a s t : Point n) : chi a (s + t) = chi a s * chi a t := by
  rw [chi_comm a (s + t), chi_add s t a, chi_comm s a, chi_comm t a]

/-! ## The translation action `τ_t` on orientations (Lemma 3.2) -/

/-- Paper XII, Lemma 3.2 (translation action).  For `t ∈ G`,
`(τ_t ε)_a = ε_a · χ_a(t)`.  Since `ε_a` and `χ_a(t)` are both `±1`, the
result is again an orientation. -/
def transOrient (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := fun a => sign_mul_sign (ε.is_sign a) (chi_mem a.1 t)

/-! ## The `GL(n,2)` relabeling action (Lemma 3.3) -/

/-- `GL(n,2)`, the general linear group of invertible `n × n` matrices over
`𝔽₂ = ZMod 2`; the matrices `M` of Paper XII, Lemma 3.3. -/
abbrev GLn (n : ℕ) : Type := Matrix.GeneralLinearGroup (Fin n) (ZMod 2)

/-- Paper XII, Lemma 3.3.  The point action of `M ∈ GL(n,2)` on the cube,
`s ↦ M s` (matrix–vector product over `𝔽₂`). -/
def glAct (M : GLn n) (s : Point n) : Point n :=
  (M : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ s

/-- Paper XII, Section 1.1 / Lemma 3.3.  The `𝔽₂`-pairing intertwines the
point action `s ↦ Ms` with the transpose mask action: `⟨a, Ms⟩ = ⟨Mᵀa, s⟩`. -/
lemma dotZ2_mulVec (M : Matrix (Fin n) (Fin n) (ZMod 2)) (a s : Point n) :
    dotZ2 a (M *ᵥ s) = dotZ2 (Mᵀ *ᵥ a) s := by
  show a ⬝ᵥ (M *ᵥ s) = (Mᵀ *ᵥ a) ⬝ᵥ s
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- Paper XII, Lemma 3.3: `χ_a(M s) = χ_{Mᵀ a}(s)`. -/
lemma chi_mulVec (M : Matrix (Fin n) (Fin n) (ZMod 2)) (a s : Point n) :
    chi a (M *ᵥ s) = chi (Mᵀ *ᵥ a) s := by
  unfold chi
  rw [dotZ2_mulVec]

/-- Paper XII, Lemma 3.3.  The transpose-inverse matrix `M^{-ᵀ} = (M⁻¹)ᵀ` of
`M ∈ GL(n,2)`, which relabels masks under the `GL` action. -/
def glTransInv (M : GLn n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  ((M⁻¹ : GLn n) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ

/-- The relabeling `b ↦ M^{-ᵀ} b` maps nonzero masks to nonzero masks
(`M^{-ᵀ}` is invertible over the field `𝔽₂`). -/
lemma glTransInv_mulVec_ne_zero (M : GLn n) {b : Point n} (hb : b ≠ 0) :
    glTransInv M *ᵥ b ≠ 0 := by
  intro hzero
  apply hb
  have hinv : ((M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) * glTransInv M = 1 := by
    unfold glTransInv
    rw [← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one]
  calc b = 1 *ᵥ b := (Matrix.one_mulVec b).symm
    _ = ((M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * glTransInv M) *ᵥ b := by rw [hinv]
    _ = (M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ (glTransInv M *ᵥ b) := by
          rw [← Matrix.mulVec_mulVec]
    _ = (M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ 0 := by rw [hzero]
    _ = 0 := Matrix.mulVec_zero _

/-- Paper XII, Lemma 3.3.  The action on the mask index set,
`b ↦ M^{-ᵀ} b`, as a self-map of nonzero masks. -/
def glMaskInvT (M : GLn n) (b : NonzeroMask n) : NonzeroMask n :=
  ⟨glTransInv M *ᵥ b.1, glTransInv_mulVec_ne_zero M b.2⟩

/-- Paper XII, Lemma 3.3 (relabeled orientation).  `(M · ε)_b = ε_{M^{-ᵀ} b}`,
equivalently `(M · ε)_{Mᵀ a} = ε_a`.  The sign condition is inherited since the
value is literally a value of `ε`. -/
def glOrient (M : GLn n) (ε : Orientation n) : Orientation n where
  sign := fun b => ε.sign (glMaskInvT M b)
  is_sign := fun b => ε.is_sign (glMaskInvT M b)

/-- The identity of `GL(n,2)` acts trivially on orientations. -/
lemma glOrient_one (ε : Orientation n) : glOrient 1 ε = ε := by
  apply Orientation.ext
  intro b
  show ε.sign (glMaskInvT 1 b) = ε.sign b
  congr 1
  apply Subtype.ext
  show glTransInv 1 *ᵥ b.1 = b.1
  simp [glTransInv, inv_one, Matrix.transpose_one, Matrix.one_mulVec]

/-! ## Lemma 3.2 : translation covariance -/

/-- Paper XII, Lemma 3.2 (delta orbit under translation).
`τ_t(ε⋆ at s⋆) = ε⋆ at (s⋆ + t)`: translation carries a delta orientation to a
delta orientation, shifting its center. -/
theorem delta_translation (t sstar : Point n) :
    transOrient t (deltaOrientation sstar) = deltaOrientation (sstar + t) := by
  ext a
  show (- chi a.1 sstar) * chi a.1 t = - chi a.1 (sstar + t)
  rw [chi_add_right a.1 sstar t]
  ring

/-- Paper XII, Lemma 3.2 (the `N` delta orientations are distinct).  The map
`s⋆ ↦ (ε⋆ at s⋆)` is injective: characters separate points of `G`. -/
theorem delta_injective :
    Function.Injective (deltaOrientation : Point n → Orientation n) := by
  have hif : ∀ x y : ZMod 2,
      (if x = 0 then (1:ℝ) else -1) = (if y = 0 then (1:ℝ) else -1) → x = y := by
    have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    intro x y hxy
    rcases hv x with hx | hx <;> rcases hv y with hy | hy <;> subst hx <;> subst hy <;>
      first | rfl | (norm_num at hxy)
  intro s s' h
  funext j
  have hj : (Pi.single j (1 : ZMod 2)) ≠ (0 : Point n) := by
    intro hcontra
    have := congrFun hcontra j
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  have hchi : chi (Pi.single j (1 : ZMod 2)) s = chi (Pi.single j (1 : ZMod 2)) s' := by
    have hs := congrArg (fun o : Orientation n => o.sign ⟨Pi.single j (1 : ZMod 2), hj⟩) h
    simp only [deltaOrientation] at hs
    exact neg_injective hs
  have hdot : ∀ w : Point n, dotZ2 (Pi.single j (1 : ZMod 2)) w = w j := by
    intro w
    unfold dotZ2
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_mul]
    · intro i _ hij; rw [Pi.single_eq_of_ne hij, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  unfold chi at hchi
  rw [hdot s, hdot s'] at hchi
  exact hif (s j) (s' j) hchi

/-- Paper XII, Lemma 3.2 (single translation orbit).  Translations act
transitively on the `N` delta orientations: for any centers `s⋆, s'` there is a
`t` with `τ_t(ε⋆ at s⋆) = ε⋆ at s'` (namely `t = s⋆ + s'`, using char 2). -/
theorem delta_single_translation_orbit (sstar sstar' : Point n) :
    ∃ t : Point n, transOrient t (deltaOrientation sstar) = deltaOrientation sstar' := by
  refine ⟨sstar + sstar', ?_⟩
  rw [delta_translation]
  congr 1
  funext i
  show sstar i + (sstar i + sstar' i) = sstar' i
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  -- TODO(api): `CharTwo.add_self_eq_zero : a + a = 0` in `ZMod 2` (char two).

/-- **Paper XII, Lemma 3.3 (delta family under `GL(n,2)`).**
`M · (ε⋆ at s⋆) = ε⋆ at (M⁻¹ s⋆)`: the `GL(n,2)` action permutes the delta
orientations among themselves. -/
theorem delta_glAction (M : GLn n) (sstar : Point n) :
    glOrient M (deltaOrientation sstar) = deltaOrientation (glAct M⁻¹ sstar) := by
  apply Orientation.ext
  intro b
  show - chi (glTransInv M *ᵥ b.1) sstar = - chi b.1 (glAct M⁻¹ sstar)
  congr 1
  unfold glTransInv glAct
  rw [chi_mulVec]

/-! ## The calibrated-law assignment and the entropy functional `m̂`

Both are supplied by Paper XII, Theorem 3.1 (existence/uniqueness module); we
carry them as an abstract assignment satisfying `IsCalAssignment`. -/

/-- Paper XII, Theorem 3.1.  `Pcal` assigns to each orientation *THE* unique
calibrated law of Definition 1.1: each `Pcal ε` is calibrated for `ε`, and any
law calibrated for `ε` equals `Pcal ε`. -/
def IsCalAssignment (Pcal : Orientation n → ProbLaw n) : Prop :=
  (∀ ε, Calibrated (Pcal ε) ε) ∧ (∀ ε (Q : ProbLaw n), Calibrated Q ε → Q = Pcal ε)

/-- Paper XII, eq. (1.2).  The entropy value of an orientation,
`m̂(ε) = D(P_ε ‖ U)`, where `P_ε = Pcal ε` is its calibrated law
(Theorem 3.1). -/
noncomputable def mhatFam (Pcal : Orientation n → ProbLaw n) (ε : Orientation n) : ℝ :=
  Dkl (Pcal ε)

/-- **Paper XII, Lemma 3.2 (translation covariance, law).**  Under the unique
calibrated-law assignment `Pcal` (Theorem 3.1),
`P_{τ_t ε}(s) = P_ε(s + t)`. -/
theorem translation_covariance_law
    (Pcal : Orientation n → ProbLaw n) (hP : IsCalAssignment Pcal)
    (t : Point n) (ε : Orientation n) (s : Point n) :
    (Pcal (transOrient t ε)).P s = (Pcal ε).P (s + t) := by
  let Q : ProbLaw n :=
    { P := fun u => (Pcal ε).P (u + t)
      pos := fun u => (Pcal ε).pos (u + t)
      sum_one := by
        rw [← (Pcal ε).sum_one]
        exact Fintype.sum_equiv (Equiv.addRight t)
          (fun u => (Pcal ε).P (u + t)) (fun u => (Pcal ε).P u) (fun u => rfl) }
  obtain ⟨h, hexp, hcalib⟩ := hP.1 ε
  have hchi : ∀ (a x y : Point n), chi a (x + y) = chi a x * chi a y := by
    intro a x y
    have hadd : dotZ2 a (x + y) = dotZ2 a x + dotZ2 a y := by
      simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have key : ∀ p q : ZMod 2,
        (if p + q = 0 then (1:ℝ) else -1)
          = (if p = 0 then (1:ℝ) else -1) * (if q = 0 then (1:ℝ) else -1) := by
      intro p q
      rcases hv p with hp | hp <;> rcases hv q with hq | hq <;>
        subst hp <;> subst hq <;> simp [show (1:ZMod 2) + 1 = 0 from by decide]
    simp only [chi, hadd]; exact key _ _
  have hsign : ∀ a : NonzeroMask n, (transOrient t ε).sign a = ε.sign a * chi a.1 t :=
    fun a => rfl
  have hQP : ∀ u, Q.P u = (Pcal ε).P (u + t) := fun u => rfl
  have htilt : ∀ u, tilt (transOrient t ε) h u = tilt ε h (u + t) := by
    intro u
    simp only [tilt]
    apply Finset.sum_congr rfl
    intro a _
    rw [hsign a, hchi]
    ring
  have hZ : (∑ r, Real.exp (tilt (transOrient t ε) h r))
      = ∑ r, Real.exp (tilt ε h r) := by
    apply Fintype.sum_equiv (Equiv.addRight t)
    intro r
    simp only [Equiv.coe_addRight]
    rw [htilt r]
  have hQcal : Calibrated Q (transOrient t ε) := by
    refine ⟨h, ?_, ?_⟩
    · intro u
      rw [hQP u, hexp (u + t), htilt u, hZ]
    · intro a
      have key : EP Q (fun u => (transOrient t ε).sign a * chi a.1 u)
          = EP (Pcal ε) (fun u => ε.sign a * chi a.1 u) := by
        simp only [EP]
        apply Fintype.sum_equiv (Equiv.addRight t)
        intro u
        simp only [Equiv.coe_addRight, hQP, hsign a]
        rw [hchi]
        ring
      rw [key]
      exact hcalib a
  have hEq := hP.2 (transOrient t ε) Q hQcal
  rw [← hEq, hQP s]
/-- **Paper XII, Lemma 3.2 (translation covariance, entropy).**
`m̂(τ_t ε) = m̂(ε)`. -/
theorem translation_covariance_mhat
    (Pcal : Orientation n → ProbLaw n) (hP : IsCalAssignment Pcal)
    (t : Point n) (ε : Orientation n) :
    mhatFam Pcal (transOrient t ε) = mhatFam Pcal ε := by
  unfold mhatFam Dkl EU
  have key : ∀ s, dens (Pcal (transOrient t ε)) s = dens (Pcal ε) (s + t) := by
    intro s
    unfold dens
    rw [translation_covariance_law Pcal hP t ε s]
  congr 1
  rw [← Equiv.sum_comp (Equiv.addRight t)
      (fun u => dens (Pcal ε) u * Real.log (dens (Pcal ε) u))]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Equiv.coe_addRight]
  rw [key s]
/-- **Paper XII, Lemma 3.3 (`GL(n,2)` covariance, law).**  `P_{M·ε}` is the
pushforward of `P_ε` under the `U`-preserving bijection `s ↦ M⁻¹ s`; concretely
`P_{M·ε}(s) = P_ε(M s)`. -/
theorem glAction_covariance_law
    (Pcal : Orientation n → ProbLaw n) (hP : IsCalAssignment Pcal)
    (M : GLn n) (ε : Orientation n) (s : Point n) :
    (Pcal (glOrient M ε)).P s = (Pcal ε).P (glAct M s) := by
  -- matrix inverse facts
  have hMMinv : (M : Matrix (Fin n) (Fin n) (ZMod 2))
      * (↑(M⁻¹ : GLn n) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hMinvM : (↑(M⁻¹ : GLn n) : Matrix (Fin n) (Fin n) (ZMod 2))
      * (M : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  -- point action is bijective
  have hpt : Function.Bijective (glAct M) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨glAct (M⁻¹), fun s => ?_, fun t => ?_⟩
    · show glAct (M⁻¹) (glAct M s) = s
      unfold glAct
      rw [Matrix.mulVec_mulVec, hMinvM, Matrix.one_mulVec]
    · show glAct M (glAct (M⁻¹) t) = t
      unfold glAct
      rw [Matrix.mulVec_mulVec, hMMinv, Matrix.one_mulVec]
  -- mask-relabeling algebra
  have hMt_prod : (M : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * glTransInv M = 1 := by
    unfold glTransInv
    rw [← Matrix.transpose_mul, hMinvM, Matrix.transpose_one]
  have hchi_id : ∀ (s : Point n) (b : NonzeroMask n),
      chi (glMaskInvT M b).1 (glAct M s) = chi b.1 s := by
    intro s b
    show chi (glTransInv M *ᵥ b.1) (glAct M s) = chi b.1 s
    unfold glAct
    rw [chi_mulVec, Matrix.mulVec_mulVec, hMt_prod, Matrix.one_mulVec]
  -- mask action is bijective
  have htrans_prod : glTransInv M * glTransInv (M⁻¹ : GLn n) = 1 := by
    unfold glTransInv
    rw [inv_inv, ← Matrix.transpose_mul, hMMinv, Matrix.transpose_one]
  have htrans_prod' : glTransInv (M⁻¹ : GLn n) * glTransInv M = 1 := by
    unfold glTransInv
    rw [inv_inv, ← Matrix.transpose_mul, hMinvM, Matrix.transpose_one]
  have hmaskinv : ∀ b : NonzeroMask n, glMaskInvT M (glMaskInvT (M⁻¹ : GLn n) b) = b := by
    intro b
    apply Subtype.ext
    show glTransInv M *ᵥ (glTransInv (M⁻¹ : GLn n) *ᵥ b.1) = b.1
    rw [Matrix.mulVec_mulVec, htrans_prod, Matrix.one_mulVec]
  have hmaskinv' : ∀ b : NonzeroMask n, glMaskInvT (M⁻¹ : GLn n) (glMaskInvT M b) = b := by
    intro b
    apply Subtype.ext
    show glTransInv (M⁻¹ : GLn n) *ᵥ (glTransInv M *ᵥ b.1) = b.1
    rw [Matrix.mulVec_mulVec, htrans_prod', Matrix.one_mulVec]
  have hmaskbij : Function.Bijective (glMaskInvT M) :=
    Function.bijective_iff_has_inverse.mpr ⟨glMaskInvT (M⁻¹ : GLn n), hmaskinv', hmaskinv⟩
  have hsign : ∀ b : NonzeroMask n, (glOrient M ε).sign b = ε.sign (glMaskInvT M b) :=
    fun b => rfl
  -- calibration data for `Pcal ε`
  obtain ⟨h₀, hA, hB⟩ := hP.1 ε
  -- tilt intertwining identity
  have htilt : ∀ s : Point n,
      tilt (glOrient M ε) (fun b => h₀ (glMaskInvT M b)) s = tilt ε h₀ (glAct M s) := by
    intro s
    unfold tilt
    refine Fintype.sum_bijective (glMaskInvT M) hmaskbij _ _ ?_
    intro b
    show h₀ (glMaskInvT M b) * (glOrient M ε).sign b * chi b.1 s
       = h₀ (glMaskInvT M b) * ε.sign (glMaskInvT M b) * chi (glMaskInvT M b).1 (glAct M s)
    rw [hsign b, hchi_id s b]
  -- normalizer equality
  have hZ : (∑ r, Real.exp (tilt ε h₀ r))
      = ∑ r, Real.exp (tilt (glOrient M ε) (fun b => h₀ (glMaskInvT M b)) r) := by
    symm
    have hstep : (∑ r, Real.exp (tilt (glOrient M ε) (fun b => h₀ (glMaskInvT M b)) r))
        = ∑ r, Real.exp (tilt ε h₀ (glAct M r)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [htilt r]
    rw [hstep]
    exact Fintype.sum_bijective (glAct M) hpt
      (fun r => Real.exp (tilt ε h₀ (glAct M r))) (fun t => Real.exp (tilt ε h₀ t)) (fun r => rfl)
  -- the pushforward law
  let Q : ProbLaw n :=
    { P := fun s => (Pcal ε).P (glAct M s)
      pos := fun s => (Pcal ε).pos (glAct M s)
      sum_one := by
        rw [← (Pcal ε).sum_one]
        exact Fintype.sum_bijective (glAct M) hpt
          (fun s => (Pcal ε).P (glAct M s)) (fun t => (Pcal ε).P t) (fun s => rfl) }
  -- Q is calibrated for `glOrient M ε`
  have hcalQ : Calibrated Q (glOrient M ε) := by
    refine ⟨fun b => h₀ (glMaskInvT M b), ?_, ?_⟩
    · intro s
      show (Pcal ε).P (glAct M s)
          = Real.exp (tilt (glOrient M ε) (fun b => h₀ (glMaskInvT M b)) s)
            / (∑ r, Real.exp (tilt (glOrient M ε) (fun b => h₀ (glMaskInvT M b)) r))
      rw [hA (glAct M s), ← htilt s, hZ]
    · intro b
      show EP Q (fun s => (glOrient M ε).sign b * chi b.1 s)
          = Real.exp (- h₀ (glMaskInvT M b))
      rw [← hB (glMaskInvT M b)]
      unfold EP
      refine Fintype.sum_bijective (glAct M) hpt _ _ ?_
      intro s
      show (Pcal ε).P (glAct M s) * ((glOrient M ε).sign b * chi b.1 s)
          = (Pcal ε).P (glAct M s)
            * (ε.sign (glMaskInvT M b) * chi (glMaskInvT M b).1 (glAct M s))
      rw [hsign b, hchi_id s b]
  -- identify Q with the calibrated law of `glOrient M ε`
  have hfin : Q = Pcal (glOrient M ε) := hP.2 (glOrient M ε) Q hcalQ
  calc (Pcal (glOrient M ε)).P s = Q.P s := by rw [hfin]
    _ = (Pcal ε).P (glAct M s) := rfl
/-- **Paper XII, Lemma 3.3 (`GL(n,2)` covariance, entropy).**
`m̂(M·ε) = m̂(ε)`. -/
theorem glAction_covariance_mhat
    (Pcal : Orientation n → ProbLaw n) (hP : IsCalAssignment Pcal)
    (M : GLn n) (ε : Orientation n) :
    mhatFam Pcal (glOrient M ε) = mhatFam Pcal ε := by
  have hleft : ∀ s, glAct M⁻¹ (glAct M s) = s := by
    intro s
    unfold glAct
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hright : ∀ s, glAct M (glAct M⁻¹ s) = s := by
    intro s
    unfold glAct
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have hbij : Function.Bijective (glAct M) :=
    Function.bijective_iff_has_inverse.mpr ⟨glAct M⁻¹, hleft, hright⟩
  unfold mhatFam Dkl EU
  congr 1
  apply Fintype.sum_bijective (glAct M) hbij
  intro s
  have hd : dens (Pcal (glOrient M ε)) s = dens (Pcal ε) (glAct M s) := by
    unfold dens
    rw [glAction_covariance_law Pcal hP M ε s]
  rw [hd]
/-! ## Corollary: the group `Γ_n` and its orbits

`Γ_n = ⟨translations, GL(n,2)⟩ = AGL(n,2)`, the affine group of `𝔽₂ⁿ`; every
element is `τ_t ∘ (M · —)` for some `M ∈ GL(n,2)`, `t ∈ G`.  Lemmas 3.2 and 3.3
say `m̂` is constant on `Γ_n`-orbits, and the `N` delta orientations form
exactly one `Γ_n`-orbit (translations already act transitively on them, and
`GL(n,2)` maps the delta family to itself). -/

/-- Paper XII, Section 3 corollary.  The combined `Γ_n = AGL(n,2)` action on
orientations, `(M, t) · ε = τ_t (M · ε)`. -/
def gammaAct (M : GLn n) (t : Point n) (ε : Orientation n) : Orientation n :=
  transOrient t (glOrient M ε)

/-- **Paper XII, corollary to Lemmas 3.2–3.3.**  `m̂` is constant on
`Γ_n`-orbits: `m̂((M,t) · ε) = m̂(ε)`. -/
theorem mhat_gamma_invariant
    (Pcal : Orientation n → ProbLaw n) (hP : IsCalAssignment Pcal)
    (M : GLn n) (t : Point n) (ε : Orientation n) :
    mhatFam Pcal (gammaAct M t ε) = mhatFam Pcal ε := by
  unfold gammaAct
  rw [translation_covariance_mhat Pcal hP t (glOrient M ε),
      glAction_covariance_mhat Pcal hP M ε]

/-- **Paper XII, corollary to Lemmas 3.2–3.3 (one orbit, transitivity).**  Any
two delta orientations lie in the same `Γ_n`-orbit; translations alone suffice
(take `M = 1`). -/
theorem delta_gamma_transitive (sstar sstar' : Point n) :
    ∃ (M : GLn n) (t : Point n),
      gammaAct M t (deltaOrientation sstar) = deltaOrientation sstar' := by
  obtain ⟨t, ht⟩ := delta_single_translation_orbit sstar sstar'
  refine ⟨1, t, ?_⟩
  unfold gammaAct
  rw [glOrient_one]
  exact ht

/-- **Paper XII, corollary to Lemmas 3.2–3.3 (one orbit, closure).**  The
`Γ_n`-orbit of a delta orientation consists only of delta orientations:
`(M,t) · (ε⋆ at s⋆) = ε⋆ at (M⁻¹ s⋆ + t)`.  With `delta_gamma_transitive`, the
`N` deltas form exactly one `Γ_n`-orbit. -/
theorem delta_gamma_closed (M : GLn n) (t : Point n) (sstar : Point n) :
    ∃ sstar' : Point n, gammaAct M t (deltaOrientation sstar) = deltaOrientation sstar' := by
  refine ⟨glAct M⁻¹ sstar + t, ?_⟩
  unfold gammaAct
  rw [delta_glAction, delta_translation]

end WalshDelta
