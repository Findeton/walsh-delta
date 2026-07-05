import Mathlib

/-!
# Walsh–delta: foundations (Paper XII, Sections 1.1 and 2)

Formalization of the core objects of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

This file fixes the representations that every downstream module imports.

## Representation choices (documented)

* **Boolean cube.**  We identify `G = {±1}^n` with `𝔽₂ⁿ` exactly as in the
  paper (Section 1.1, `+1 ↔ 0`, `-1 ↔ 1`, group law = coordinatewise sum in
  `𝔽₂` = coordinatewise product in the `±1` picture).  We take
  `Point n := Fin n → ZMod 2`.  This is a `Fintype` with `DecidableEq`, an
  `AddCommGroup` under pointwise `+`, has a canonical `0` (the all-`+1`
  point / zero mask), and its cardinality is `2 ^ n = N`.  Masks `a` and
  points `s` live in the SAME type (the group is self-dual), matching the
  paper's use of `a ∈ 𝔽₂ⁿ` for both.

* **Walsh character.**  `chi a s = (-1)^{⟨a,s⟩}` with `⟨a,s⟩ = ∑ᵢ aᵢ sᵢ ∈ 𝔽₂`.
  Encoded as `if ⟨a,s⟩ = 0 then (1:ℝ) else -1`, hence literally `±1`-valued.

* **Orientation.**  A sign per NONZERO mask, valued in `{±1}` (Section 1.1).
  Represented as a `structure` bundling `sign : NonzeroMask n → ℝ` with a proof
  that each value is `1` or `-1`.  (A `Bool`-valued field would also work; we
  keep real values so downstream Gibbs formulas `∑ hₐ εₐ χₐ` are direct.)

* **Probability law.**  A `structure ProbLaw` with a real density `P`, full
  support (`0 < P s`, required by Definition 1.1), and `∑ P s = 1`.  The
  density w.r.t. uniform is `X := N • P` (`dens`), so `E_U[X] = 1`.

## Public names exported by this file

  Point, N, N_pos, N_ne_zero, card_point,
  dotZ2, chi, chi_zero, chi_mem, chi_add,
  NonzeroMask, Orientation, deltaOrientation,
  ProbLaw, EU, EP, dens, EU_dens_eq_one, xhat, xhat_dens_eq_EP,
  psi, psi_one, psi_hasDerivAt, psi_nonneg, psi_strictAntiOn, psi_strictMonoOn,
  Dkl, Dkl_eq_EU_psi, pinsker,
  tilt, Calibrated
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## The Boolean cube `G = {±1}ⁿ ≅ 𝔽₂ⁿ` -/

/-- Paper XII, Section 1.1.  A point of the Boolean cube (equivalently a Walsh
mask), identified with `𝔽₂ⁿ`.  `+1 ↔ 0`, `-1 ↔ 1`; the group law `s + t` is
coordinatewise addition in `𝔽₂` (= coordinatewise product in the `±1`
picture). -/
abbrev Point (n : ℕ) : Type := Fin n → ZMod 2

/-- Paper XII, Section 1.1.  `N = 2ⁿ = |G|`, the number of points of the cube. -/
def N (n : ℕ) : ℕ := 2 ^ n

@[simp] lemma N_eq (n : ℕ) : N n = 2 ^ n := rfl

/-- `N n > 0`. -/
lemma N_pos (n : ℕ) : 0 < N n := by
  unfold N; exact pow_pos (by norm_num) n

/-- `(N n : ℝ) ≠ 0`, used to divide by `N` in expectations. -/
lemma N_ne_zero (n : ℕ) : (N n : ℝ) ≠ 0 := by
  have h : 0 < N n := N_pos n
  exact_mod_cast h.ne'

/-- Paper XII, Section 1.1.  `|G| = N = 2ⁿ`. -/
lemma card_point (n : ℕ) : Fintype.card (Point n) = N n := by
  simp only [Point, N]
  rw [Fintype.card_pi]
  simp [ZMod.card]

/-! ## Walsh characters -/

/-- Paper XII, Section 1.1.  The `𝔽₂`-pairing `⟨a,s⟩ = ∑ᵢ aᵢ sᵢ ∈ 𝔽₂` of a
mask `a` and a point `s`. -/
def dotZ2 (a s : Point n) : ZMod 2 := ∑ i, a i * s i

/-- Paper XII, Section 1.1.  The Walsh character
`χ_a(s) = (-1)^{⟨a,s⟩} = ∏_{i : aᵢ=1} sᵢ`, a `±1`-valued real function. -/
def chi (a s : Point n) : ℝ := if dotZ2 a s = 0 then 1 else -1

/-- Paper XII, Section 1.1: `χ₀ ≡ 1`. -/
@[simp] lemma chi_zero (s : Point n) : chi (0 : Point n) s = 1 := by
  unfold chi dotZ2
  simp

/-- Paper XII, Section 1.1: every Walsh character is `±1`-valued. -/
lemma chi_mem (a s : Point n) : chi a s = 1 ∨ chi a s = -1 := by
  unfold chi
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Paper XII, Section 1.1: `χ_{a+b} = χ_a · χ_b` (pointwise). -/
lemma chi_add (a b s : Point n) : chi (a + b) s = chi a s * chi b s := by
  have hadd : dotZ2 (a + b) s = dotZ2 a s + dotZ2 b s := by
    simp only [dotZ2, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have key : ∀ x y : ZMod 2,
      (if x + y = 0 then (1:ℝ) else -1)
        = (if x = 0 then (1:ℝ) else -1) * (if y = 0 then (1:ℝ) else -1) := by
    intro x y
    rcases hv x with hx | hx <;> rcases hv y with hy | hy <;>
      subst hx <;> subst hy <;> simp [show (1:ZMod 2) + 1 = 0 from by decide]
  simp only [chi, hadd]; exact key _ _

/-! ## Orientations and the delta orientation -/

/-- Paper XII, Section 1.1.  The nonzero masks, index set of an orientation
(there are `N - 1` of them). -/
abbrev NonzeroMask (n : ℕ) : Type := {a : Point n // a ≠ 0}

/-- Paper XII, Section 1.1 (orientation).  A sign vector
`ε = (εₐ)_{a≠0} ∈ {±1}^{N-1}`, one sign per nonzero Walsh mask. -/
structure Orientation (n : ℕ) where
  /-- The sign `εₐ ∈ {±1}` attached to each nonzero mask `a`. -/
  sign : NonzeroMask n → ℝ
  /-- Each sign is `±1`. -/
  is_sign : ∀ a, sign a = 1 ∨ sign a = -1

/-- Extensionality for `Orientation`: two orientations are equal iff their sign
functions agree (the `is_sign` proofs are irrelevant). -/
@[ext] theorem Orientation.ext {ε₁ ε₂ : Orientation n}
    (h : ∀ a, ε₁.sign a = ε₂.sign a) : ε₁ = ε₂ := by
  cases ε₁ with
  | mk s1 p1 => cases ε₂ with
    | mk s2 p2 => have hs : s1 = s2 := funext (fun a => h a); subst hs; rfl

/-- Paper XII, Section 1.2 (delta orientation at `s⋆`).  `ε⋆_a = -χ_a(s⋆)`:
every sign is chosen to disagree with the point `s⋆`.  There are exactly `N`
of these, one per point of the cube. -/
def deltaOrientation (sstar : Point n) : Orientation n where
  sign := fun a => - chi a.1 sstar
  is_sign := by
    intro a
    rcases chi_mem a.1 sstar with h | h
    · rw [h]; exact Or.inr (by norm_num)
    · rw [h]; exact Or.inl (by norm_num)

/-- Paper XII, §1.2.  `ε` **is a delta orientation** iff `ε = ε⋆` at some base
point `s⋆` (the canonical predicate; other modules import this). -/
def IsDelta (ε : Orientation n) : Prop := ∃ sstar : Point n, ε = deltaOrientation sstar

/-! ## Probability laws, expectations and the density `X = N·P` -/

/-- Paper XII, Sections 1.1 and 2.  A probability law `P` on `G` with full
support (required by Definition 1.1). -/
structure ProbLaw (n : ℕ) where
  /-- The point masses `P(s)`. -/
  P : Point n → ℝ
  /-- Full support: `P(s) > 0` for every point. -/
  pos : ∀ s, 0 < P s
  /-- Total mass one. -/
  sum_one : ∑ s, P s = 1

/-- Paper XII, Section 1.1.  Expectation under the UNIFORM law `U`:
`E_U[f] = (1/N) ∑_s f(s)`. -/
noncomputable def EU (f : Point n → ℝ) : ℝ := (∑ s, f s) / (N n : ℝ)

/-- Paper XII, Section 1.1.  Expectation under `P`:
`E_P[f] = ∑_s P(s) f(s)`. -/
noncomputable def EP (P : ProbLaw n) (f : Point n → ℝ) : ℝ := ∑ s, P.P s * f s

/-- Paper XII, Section 2.  The density of `P` with respect to uniform,
`X = N·P` (so that `E_U[X] = 1`). -/
noncomputable def dens (P : ProbLaw n) (s : Point n) : ℝ := (N n : ℝ) * P.P s

/-- Paper XII, Section 2: `E_U[X] = 1` for `X = N·P`. -/
lemma EU_dens_eq_one (P : ProbLaw n) : EU (dens P) = 1 := by
  unfold EU dens
  rw [← Finset.mul_sum, P.sum_one, mul_one, div_self (N_ne_zero n)]

/-- Paper XII, Section 1.1.  Walsh–Fourier coefficient of `f`:
`f̂(a) = E_U[f · χ_a]`. -/
noncomputable def xhat (f : Point n → ℝ) (a : Point n) : ℝ := EU (fun s => f s * chi a s)

/-- Paper XII, Section 1.1: `X̂(a) = E_U[X χ_a] = E_P[χ_a] = xₐ`. -/
lemma xhat_dens_eq_EP (P : ProbLaw n) (a : Point n) :
    xhat (dens P) a = EP P (fun s => chi a s) := by
  simp only [xhat, EU, dens, EP]
  rw [div_eq_iff (N_ne_zero n), Finset.sum_mul]
  exact Finset.sum_congr rfl (fun s _ => by ring)

/-! ## The entropy integrand `ψ` and relative entropy `D(P‖U)` -/

/-- Paper XII, Lemma 2.2.  `ψ(x) = x log x - x + 1`.  Note `ψ(0) = 1`
automatically, since `Real.log 0 = 0`. -/
noncomputable def psi (x : ℝ) : ℝ := x * Real.log x - x + 1

/-- Paper XII, Lemma 2.2: `ψ(1) = 0`. -/
@[simp] lemma psi_one : psi 1 = 0 := by
  simp [psi]

/-- Paper XII, Lemma 2.2: `ψ'(x) = log x` for `x > 0`. -/
lemma psi_hasDerivAt {x : ℝ} (hx : 0 < x) : HasDerivAt psi (Real.log x) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  -- product rule: d/dx (x · log x) = 1·log x + x·x⁻¹
  have hmul : HasDerivAt (fun y : ℝ => y * Real.log y)
      (1 * Real.log x + x * x⁻¹) x := hid.mul hlog
  have hmul' : HasDerivAt (fun y : ℝ => y * Real.log y) (Real.log x + 1) x := by
    have e : 1 * Real.log x + x * x⁻¹ = Real.log x + 1 := by
      rw [one_mul, mul_inv_cancel₀ hx.ne']
    rwa [e] at hmul
  have hsub : HasDerivAt (fun y : ℝ => y * Real.log y - y)
      (Real.log x + 1 - 1) x := hmul'.sub hid
  have hfin : HasDerivAt (fun y : ℝ => y * Real.log y - y + 1)
      (Real.log x + 1 - 1) x := hsub.add_const 1
  have e2 : Real.log x + 1 - 1 = Real.log x := by ring
  rw [e2] at hfin
  exact hfin

/-- Paper XII, Lemma 2.2: `ψ` is strictly decreasing on `[0,1]`. -/
lemma psi_strictAntiOn : StrictAntiOn psi (Set.Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn psi (Set.Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun x : ℝ => x * Real.log x) (Set.Icc (0:ℝ) 1) :=
      Real.continuous_mul_log.continuousOn
    exact (h1.sub continuousOn_id).add continuousOn_const
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) hcont
  intro x hx
  rw [interior_Icc] at hx
  rw [(psi_hasDerivAt hx.1).deriv]
  exact Real.log_neg hx.1 hx.2

/-- Paper XII, Lemma 2.2: `ψ` is strictly increasing on `[1,∞)`. -/
lemma psi_strictMonoOn : StrictMonoOn psi (Set.Ici (1 : ℝ)) := by
  have hcont : ContinuousOn psi (Set.Ici (1:ℝ)) := by
    have h1 : ContinuousOn (fun x : ℝ => x * Real.log x) (Set.Ici (1:ℝ)) :=
      continuousOn_id.mul
        (Real.continuousOn_log.mono (fun x hx => (lt_of_lt_of_le one_pos hx).ne'))
    exact (h1.sub continuousOn_id).add continuousOn_const
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) hcont
  intro x hx
  rw [interior_Ici] at hx
  rw [(psi_hasDerivAt (lt_trans one_pos hx)).deriv]
  exact Real.log_pos hx

/-- Paper XII, Lemma 2.2: `ψ ≥ 0` on `[0,∞)`. -/
lemma psi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ psi x := by
  rcases lt_trichotomy x 1 with h | h | h
  · have := psi_strictAntiOn (Set.mem_Icc.mpr ⟨hx, le_of_lt h⟩)
      (Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩) h
    rw [psi_one] at this; linarith
  · subst h; rw [psi_one]
  · have := psi_strictMonoOn (Set.mem_Ici.mpr (le_refl 1))
      (Set.mem_Ici.mpr (le_of_lt h)) h
    rw [psi_one] at this; linarith


/-- Paper XII, Section 2.  Relative entropy from uniform,
`D(P‖U) = E_U[X log X]`. -/
noncomputable def Dkl (P : ProbLaw n) : ℝ := EU (fun s => dens P s * Real.log (dens P s))

/-- Paper XII, Lemma 2.2: `D(P‖U) = E_U[ψ(X)] = (1/N) ∑_s ψ(X(s))`. -/
lemma Dkl_eq_EU_psi (P : ProbLaw n) :
    Dkl P = EU (fun s => psi (dens P s)) := by
  have hsum1 : (∑ _s : Point n, (1:ℝ)) = (N n : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, card_point]; simp
  have hsumX : (∑ s, dens P s) = (N n : ℝ) := by
    have h := EU_dens_eq_one P; simp only [EU] at h
    field_simp at h; linarith
  simp only [Dkl, EU, psi]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum1, hsumX]
  ring

/-- Paper XII, Lemma 2.1 (Pinsker).  `E_U|X - 1| = ∑_s |P(s) - 1/N| ≤ √(2 D(P‖U))`. -/
lemma pinsker (P : ProbLaw n) :
    EU (fun s => |dens P s - 1|) ≤ Real.sqrt (2 * Dkl P) := by
  -- Pointwise Pinsker:  for x > 0,  3(x-1)^2 ≤ (2x+4) ψ(x).
  have hpt : ∀ x : ℝ, 0 < x → 3 * (x - 1) ^ 2 ≤ (2 * x + 4) * psi x := by
    -- G(x) = (2x+4)ψ(x) - 3(x-1)^2 ,  with derivative Gp.
    have hderivG : ∀ x : ℝ, 0 < x →
        HasDerivAt (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2)
          (2 * psi x + (2 * x + 4) * Real.log x - 6 * (x - 1)) x := by
      intro x hx
      have hpsi := psi_hasDerivAt hx
      have h1 : HasDerivAt (fun y : ℝ => 2 * y + 4) 2 x := by
        simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).add_const (4:ℝ)
      have h2 : HasDerivAt (fun y : ℝ => (2 * y + 4) * psi y)
          (2 * psi x + (2 * x + 4) * Real.log x) x := h1.mul hpsi
      have hb : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const (1:ℝ)
      have h3 : HasDerivAt (fun y : ℝ => (y - 1) ^ 2) (2 * (x - 1)) x := by
        have hmul : HasDerivAt (fun y : ℝ => (y - 1) * (y - 1))
            (1 * (x - 1) + (x - 1) * 1) x := hb.mul hb
        have e : (fun y : ℝ => (y - 1) * (y - 1)) = (fun y : ℝ => (y - 1) ^ 2) := by
          funext y; ring
        rw [e] at hmul
        rw [show (2:ℝ) * (x - 1) = 1 * (x - 1) + (x - 1) * 1 from by ring]
        exact hmul
      have h4 : HasDerivAt (fun y : ℝ => 3 * (y - 1) ^ 2) (6 * (x - 1)) x := by
        have h := h3.const_mul (3:ℝ)
        rw [show (6:ℝ) * (x - 1) = 3 * (2 * (x - 1)) from by ring]
        exact h
      exact h2.sub h4
    -- Gp(x) = 2ψ(x) + (2x+4)log x - 6(x-1) ,  with derivative Gpp.
    have hderivGp : ∀ x : ℝ, 0 < x →
        HasDerivAt (fun y => 2 * psi y + (2 * y + 4) * Real.log y - 6 * (y - 1))
          (2 * Real.log x + (2 * Real.log x + (2 * x + 4) * x⁻¹) - 6) x := by
      intro x hx
      have hpsi := psi_hasDerivAt hx
      have hlog := Real.hasDerivAt_log (ne_of_gt hx)
      have h1 : HasDerivAt (fun y : ℝ => 2 * y + 4) 2 x := by
        simpa using ((hasDerivAt_id x).const_mul (2:ℝ)).add_const (4:ℝ)
      have t1 : HasDerivAt (fun y : ℝ => 2 * psi y) (2 * Real.log x) x := hpsi.const_mul (2:ℝ)
      have t2 : HasDerivAt (fun y : ℝ => (2 * y + 4) * Real.log y)
          (2 * Real.log x + (2 * x + 4) * x⁻¹) x := h1.mul hlog
      have t3 : HasDerivAt (fun y : ℝ => 6 * (y - 1)) 6 x := by
        simpa using ((hasDerivAt_id x).sub_const (1:ℝ)).const_mul (6:ℝ)
      exact (t1.add t2).sub t3
    -- Gp is monotone on (0,∞) because Gpp ≥ 0.
    have hGp_cont : ContinuousOn
        (fun y => 2 * psi y + (2 * y + 4) * Real.log y - 6 * (y - 1)) (Set.Ioi (0:ℝ)) :=
      fun x hx => (hderivGp x hx).continuousAt.continuousWithinAt
    have hGp_diff : DifferentiableOn ℝ
        (fun y => 2 * psi y + (2 * y + 4) * Real.log y - 6 * (y - 1))
        (interior (Set.Ioi (0:ℝ))) := by
      rw [interior_Ioi]
      exact fun x hx => (hderivGp x hx).differentiableAt.differentiableWithinAt
    have hGp_mono : MonotoneOn
        (fun y => 2 * psi y + (2 * y + 4) * Real.log y - 6 * (y - 1)) (Set.Ioi (0:ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioi 0) hGp_cont hGp_diff
      intro x hx
      rw [interior_Ioi] at hx
      rw [(hderivGp x hx).deriv]
      have hlog : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
      rw [Real.log_inv] at hlog
      have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx)
      nlinarith [hlog, hxinv, hx]
    -- Gp(1) = 0, hence Gp ≥ 0 on [1,∞) and Gp ≤ 0 on (0,1].
    have hGp_nonneg : ∀ x : ℝ, 1 ≤ x →
        0 ≤ 2 * psi x + (2 * x + 4) * Real.log x - 6 * (x - 1) := by
      intro x hx1
      have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx1
      have key : (2 * psi (1:ℝ) + (2 * (1:ℝ) + 4) * Real.log 1 - 6 * ((1:ℝ) - 1))
          ≤ (2 * psi x + (2 * x + 4) * Real.log x - 6 * (x - 1)) :=
        hGp_mono (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hx0) hx1
      have h1 : (2 * psi (1:ℝ) + (2 * (1:ℝ) + 4) * Real.log 1 - 6 * ((1:ℝ) - 1)) = 0 := by
        simp [psi_one]
      linarith [key, h1]
    have hGp_nonpos : ∀ x : ℝ, 0 < x → x ≤ 1 →
        2 * psi x + (2 * x + 4) * Real.log x - 6 * (x - 1) ≤ 0 := by
      intro x hx0 hx1
      have key : (2 * psi x + (2 * x + 4) * Real.log x - 6 * (x - 1))
          ≤ (2 * psi (1:ℝ) + (2 * (1:ℝ) + 4) * Real.log 1 - 6 * ((1:ℝ) - 1)) :=
        hGp_mono (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr one_pos) hx1
      have h1 : (2 * psi (1:ℝ) + (2 * (1:ℝ) + 4) * Real.log 1 - 6 * ((1:ℝ) - 1)) = 0 := by
        simp [psi_one]
      linarith [key, h1]
    -- G is monotone on [1,∞) and antitone on (0,1], with G(1)=0.
    have hGcont_ici : ContinuousOn
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (Set.Ici (1:ℝ)) :=
      fun x hx => (hderivG x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
    have hGdiff_ici : DifferentiableOn ℝ
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (interior (Set.Ici (1:ℝ))) := by
      rw [interior_Ici]
      exact fun x hx => (hderivG x (lt_trans one_pos hx)).differentiableAt.differentiableWithinAt
    have hGcont_ioc : ContinuousOn
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (Set.Ioc (0:ℝ) 1) :=
      fun x hx => (hderivG x hx.1).continuousAt.continuousWithinAt
    have hGdiff_ioc : DifferentiableOn ℝ
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (interior (Set.Ioc (0:ℝ) 1)) := by
      rw [interior_Ioc]
      exact fun x hx => (hderivG x hx.1).differentiableAt.differentiableWithinAt
    have hG_mono : MonotoneOn
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (Set.Ici (1:ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1) hGcont_ici hGdiff_ici
      intro x hx
      rw [interior_Ici] at hx
      rw [(hderivG x (lt_trans one_pos hx)).deriv]
      exact hGp_nonneg x (le_of_lt hx)
    have hG_anti : AntitoneOn
        (fun y => (2 * y + 4) * psi y - 3 * (y - 1) ^ 2) (Set.Ioc (0:ℝ) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) hGcont_ioc hGdiff_ioc
      intro x hx
      rw [interior_Ioc] at hx
      rw [(hderivG x hx.1).deriv]
      exact hGp_nonpos x hx.1 (le_of_lt hx.2)
    have hG1 : (2 * (1:ℝ) + 4) * psi 1 - 3 * ((1:ℝ) - 1) ^ 2 = 0 := by simp [psi_one]
    have hG_nonneg_ge : ∀ x : ℝ, 1 ≤ x → 0 ≤ (2 * x + 4) * psi x - 3 * (x - 1) ^ 2 := by
      intro x hx1
      have key : ((2 * (1:ℝ) + 4) * psi 1 - 3 * ((1:ℝ) - 1) ^ 2)
          ≤ ((2 * x + 4) * psi x - 3 * (x - 1) ^ 2) :=
        hG_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx1) hx1
      linarith [key, hG1]
    have hG_nonneg_le : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 ≤ (2 * x + 4) * psi x - 3 * (x - 1) ^ 2 := by
      intro x hx0 hx1
      have key : ((2 * (1:ℝ) + 4) * psi 1 - 3 * ((1:ℝ) - 1) ^ 2)
          ≤ ((2 * x + 4) * psi x - 3 * (x - 1) ^ 2) :=
        hG_anti (Set.mem_Ioc.mpr ⟨hx0, hx1⟩) (Set.mem_Ioc.mpr ⟨one_pos, le_rfl⟩) hx1
      linarith [key, hG1]
    intro x hx
    rcases le_total 1 x with hle | hle
    · have hge := hG_nonneg_ge x hle
      linarith [hge]
    · have hle' := hG_nonneg_le x hx hle
      linarith [hle']
  -- Basic facts about the density X = N·P.
  have hXpos : ∀ s : Point n, 0 < dens P s := by
    intro s
    have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
    simp only [dens]
    exact mul_pos hN (P.pos s)
  have hsumX : (∑ s : Point n, dens P s) = (N n : ℝ) := by
    have h := EU_dens_eq_one P
    simp only [EU] at h
    field_simp at h
    linarith
  have hpsi_sum : (∑ s : Point n, psi (dens P s)) = (N n : ℝ) * Dkl P := by
    rw [Dkl_eq_EU_psi]
    simp only [EU]
    rw [mul_comm (N n : ℝ) ((∑ s : Point n, psi (dens P s)) / (N n : ℝ)),
       div_mul_cancel₀ _ (N_ne_zero n)]
  have arg_nonneg : ∀ s : Point n, (0:ℝ) ≤ (2 * dens P s + 4) / 3 := by
    intro s
    have := hXpos s
    apply div_nonneg
    · linarith
    · norm_num
  -- Product identity for the Cauchy–Schwarz split.
  have prodeq : ∀ s : Point n,
      Real.sqrt ((2 * dens P s + 4) / 3)
        * Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) = |dens P s - 1| := by
    intro s
    have hXs := hXpos s
    have hpos : (0:ℝ) < 2 * dens P s + 4 := by linarith
    have hne : (2 * dens P s + 4) ≠ 0 := ne_of_gt hpos
    rw [← Real.sqrt_mul (arg_nonneg s)]
    have hid : (2 * dens P s + 4) / 3 * (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4))
        = (dens P s - 1) ^ 2 := by
      field_simp
    rw [hid, Real.sqrt_sq_eq_abs]
  have hSprod : (∑ s : Point n,
        Real.sqrt ((2 * dens P s + 4) / 3)
          * Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)))
      = ∑ s : Point n, |dens P s - 1| :=
    Finset.sum_congr rfl (fun s _ => prodeq s)
  -- ∑ f² = 2N.
  have hsum24 : (∑ s : Point n, (2 * dens P s + 4)) = 6 * (N n : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumX, Finset.sum_const, Finset.card_univ,
       card_point, nsmul_eq_mul]
    ring
  have hf2 : (∑ s : Point n, Real.sqrt ((2 * dens P s + 4) / 3) ^ 2) = 2 * (N n : ℝ) := by
    have hcong : ∀ s : Point n,
        Real.sqrt ((2 * dens P s + 4) / 3) ^ 2 = (2 * dens P s + 4) / 3 :=
      fun s => Real.sq_sqrt (arg_nonneg s)
    rw [Finset.sum_congr rfl (fun s _ => hcong s), ← Finset.sum_div, hsum24]
    ring
  -- ∑ g² ≤ ∑ ψ(X).
  have g2le : ∀ s : Point n,
      Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2 ≤ psi (dens P s) := by
    intro s
    have hXs := hXpos s
    have hpos : (0:ℝ) < 2 * dens P s + 4 := by linarith
    have harg : (0:ℝ) ≤ 3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4) := by
      apply div_nonneg
      · positivity
      · linarith
    rw [Real.sq_sqrt harg, div_le_iff₀ hpos]
    have hp := hpt (dens P s) hXs
    rw [mul_comm (psi (dens P s)) (2 * dens P s + 4)]
    exact hp
  have hg2 : (∑ s : Point n, Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2)
      ≤ ∑ s : Point n, psi (dens P s) :=
    Finset.sum_le_sum (fun s _ => g2le s)
  -- Cauchy–Schwarz.
  have CS : (∑ s : Point n,
        Real.sqrt ((2 * dens P s + 4) / 3)
          * Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4))) ^ 2
      ≤ (∑ s : Point n, Real.sqrt ((2 * dens P s + 4) / 3) ^ 2)
        * (∑ s : Point n, Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Point n))
      (fun s => Real.sqrt ((2 * dens P s + 4) / 3))
      (fun s => Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)))
    simpa only [] using h
  -- Assemble the squared bound  S² ≤ 2N²·D.
  have hCbound : (∑ s : Point n, Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2)
      ≤ (N n : ℝ) * Dkl P :=
    le_trans hg2 (le_of_eq hpsi_sum)
  have h2Nnonneg : (0:ℝ) ≤ 2 * (N n : ℝ) := by positivity
  have hS2 : (∑ s : Point n, |dens P s - 1|) ^ 2 ≤ 2 * (N n : ℝ) * ((N n : ℝ) * Dkl P) := by
    have hstep : (∑ s : Point n, |dens P s - 1|) ^ 2
        ≤ (2 * (N n : ℝ))
          * (∑ s : Point n, Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2) := by
      rw [← hSprod, ← hf2]
      exact CS
    calc (∑ s : Point n, |dens P s - 1|) ^ 2
        ≤ (2 * (N n : ℝ))
            * (∑ s : Point n, Real.sqrt (3 * (dens P s - 1) ^ 2 / (2 * dens P s + 4)) ^ 2) := hstep
      _ ≤ (2 * (N n : ℝ)) * ((N n : ℝ) * Dkl P) :=
          mul_le_mul_of_nonneg_left hCbound h2Nnonneg
      _ = 2 * (N n : ℝ) * ((N n : ℝ) * Dkl P) := by ring
  -- Take square roots and divide by N.
  have hSnonneg : (0:ℝ) ≤ ∑ s : Point n, |dens P s - 1| :=
    Finset.sum_nonneg (fun s _ => abs_nonneg _)
  have hNsqrt : Real.sqrt ((N n : ℝ) ^ 2 * (2 * Dkl P)) = (N n : ℝ) * Real.sqrt (2 * Dkl P) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N n : ℝ) ^ 2),
       Real.sqrt_sq (by positivity : (0:ℝ) ≤ (N n : ℝ))]
  have key : (∑ s : Point n, |dens P s - 1|) ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) := by
    rw [← hNsqrt, ← Real.sqrt_sq hSnonneg]
    apply Real.sqrt_le_sqrt
    calc (∑ s : Point n, |dens P s - 1|) ^ 2
        ≤ 2 * (N n : ℝ) * ((N n : ℝ) * Dkl P) := hS2
      _ = (N n : ℝ) ^ 2 * (2 * Dkl P) := by ring
  have hNpos : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have hEU : EU (fun s => |dens P s - 1|)
      = (∑ s : Point n, |dens P s - 1|) / (N n : ℝ) := rfl
  rw [hEU, div_le_iff₀ hNpos]
  calc (∑ s : Point n, |dens P s - 1|)
      ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) := key
    _ = Real.sqrt (2 * Dkl P) * (N n : ℝ) := by ring
/-! ## Self-calibrated laws (Definition 1.1) -/

/-- Paper XII, Definition 1.1.  The tilt field
`T(s) = ∑_{a≠0} h_a ε_a χ_a(s)`. -/
noncomputable def tilt (ε : Orientation n) (h : NonzeroMask n → ℝ) (s : Point n) : ℝ :=
  ∑ a : NonzeroMask n, h a * ε.sign a * chi a.1 s

/-- Paper XII, Definition 1.1 (calibrated law).  `P` (full support, from
`ProbLaw`) is *calibrated for the orientation `ε`* iff there exist reals
`(h_a)_{a≠0}` such that

* `P(s) = exp(∑_{a≠0} h_a ε_a χ_a(s)) / Z`, with
  `Z = ∑_r exp(∑_{a≠0} h_a ε_a χ_a(r))`, and
* the self-calibration fixed point `E_P[ε_a χ_a] = e^{-h_a}` holds for every
  `a ≠ 0`. -/
def Calibrated (P : ProbLaw n) (ε : Orientation n) : Prop :=
  ∃ h : NonzeroMask n → ℝ,
    (∀ s, P.P s
        = Real.exp (tilt ε h s) / (∑ r, Real.exp (tilt ε h r)))
    ∧ (∀ a : NonzeroMask n,
        EP P (fun s => ε.sign a * chi a.1 s) = Real.exp (- h a))

end WalshDelta
