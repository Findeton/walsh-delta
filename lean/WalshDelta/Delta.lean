import Mathlib
import WalshDelta.Basic
import WalshDelta.Calibration

/-!
# Walsh–delta: the delta laws in closed form (Paper XII, Sections 1.2 and 4)

Formalization of the delta orientations `ε⋆` (Section 1.2), Proposition 4.1
(their calibrated law is an explicit two-level law governed by the root `u⋆`
of `p(u) = u^{N+1} + u^N + (N-1)u - 1`), the resulting gap
`D_δ = ŵm(ε⋆)`, and Lemma 4.2 (`0 < D_δ < 1/(N-1)` with `N·D_δ → 1`).

The delta orientation itself, `deltaOrientation sstar` with
`ε⋆_a = -χ_a(sstar)`, is defined in `WalshDelta.Basic`; we reuse it verbatim.

## Section 3 interface used here

`ŵm(ε) = D(P_ε ‖ U)` is the relative entropy of the *unique* calibrated law
`P_ε` of `ε` (Theorem 3.1).  The existence/uniqueness of `P_ε` (Theorem 3.1)
and translation covariance (Lemma 3.2) live in the Section-3 development; the
declarations `exists_unique_calibrated`, `calLaw`, `mhat`, `tauOrient`,
`mhat_tauOrient` below are exactly that interface, restated here as the part of
Section 3 that Section 4 consumes.  At assembly they are to be unified with the
Section-3 module (identical statements).
-/

namespace WalshDelta

open Classical

open scoped BigOperators
open Filter Topology

variable {n : ℕ}

/-- For `n ≥ 2`, `1 < N = 2ⁿ` as a real (in fact `4 ≤ N`). -/
lemma one_lt_N (n : ℕ) (hn : 2 ≤ n) : (1:ℝ) < (N n : ℝ) := by
  have h4 : (4:ℕ) ≤ N n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : (4:ℝ) ≤ (N n : ℝ) := by exact_mod_cast h4
  linarith

/-! ## Walsh orthogonality / inversion helpers (Section 1.1, used in §4) -/

/-- Paper XII, Section 1.1: bilinearity of the pairing gives multiplicativity of
`χ_a` in its POINT argument, `χ_a(s+t) = χ_a(s)·χ_a(t)` (companion of
`chi_add`, which is multiplicativity in the mask). -/
lemma chi_right_add (a s t : Point n) : chi a (s + t) = chi a s * chi a t := by
  have hadd : dotZ2 a (s + t) = dotZ2 a s + dotZ2 a t := by
    simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have key : ∀ x y : ZMod 2, (if x + y = 0 then (1:ℝ) else -1)
      = (if x = 0 then (1:ℝ) else -1) * (if y = 0 then (1:ℝ) else -1) := by
    intro x y; rcases hv x with hx | hx <;> rcases hv y with hy | hy <;>
      subst hx <;> subst hy <;> simp [show (1:ZMod 2) + 1 = 0 from by decide]
  simp only [chi, hadd]; exact key _ _

/-- Paper XII, Section 1.1 (Walsh orthogonality), used in the Prop 4.1 proof:
`∑_s χ_a(s) = N·[a = 0]`. -/
lemma sum_chi (a : Point n) :
    (∑ s, chi a s) = if a = 0 then (N n : ℝ) else 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl]
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, card_point, nsmul_eq_mul, mul_one]
  · rw [if_neg ha]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    simp only [Pi.zero_apply] at hj
    set ej : Point n := Pi.single j (1 : ZMod 2) with hej
    have hdot : dotZ2 a ej = a j := by
      unfold dotZ2
      rw [Finset.sum_eq_single j]
      · rw [hej, Pi.single_eq_same, mul_one]
      · intro i _ hij; rw [hej, Pi.single_eq_of_ne hij, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hchi_ej : chi a ej = -1 := by unfold chi; rw [hdot, if_neg hj]
    have hbij : (∑ s, chi a (s + ej)) = ∑ s, chi a s :=
      Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi a (s + ej)) (chi a) (fun x => rfl)
    have hflip : (∑ s, chi a (s + ej)) = ∑ s, (- chi a s) :=
      Finset.sum_congr rfl (fun s _ => by rw [chi_right_add, hchi_ej, mul_neg_one])
    rw [hflip, Finset.sum_neg_distrib] at hbij
    linarith [hbij]

/-- Paper XII, Section 4 (Walsh inversion, used in the closed form of `X`):
`∑_{a≠0} χ_a(s) = N·[s = 0] - 1`.  This is `sum_chi` read on the self-dual
group (masks and points share the type). -/
lemma sum_nonzero_chi (s : Point n) :
    (∑ a : NonzeroMask n, chi a.1 s) = (if s = 0 then (N n : ℝ) else 0) - 1 := by
  have hsub : (∑ a ∈ Finset.univ.erase (0 : Point n), chi a s)
      = ∑ a : NonzeroMask n, chi a.1 s :=
    Finset.sum_subtype _ (fun x => by simp [Finset.mem_erase]) (fun a => chi a s)
  have herase : (∑ a ∈ Finset.univ.erase (0 : Point n), chi a s)
      = (∑ a : Point n, chi a s) - chi 0 s :=
    Finset.sum_erase_eq_sub (Finset.mem_univ 0)
  have hsym : (∑ a : Point n, chi a s) = ∑ a : Point n, chi s a :=
    Finset.sum_congr rfl (fun a _ => by
      unfold chi dotZ2; rw [Finset.sum_congr rfl (fun i _ => mul_comm (a i) (s i))])
  rw [← hsub, herase, hsym, sum_chi s, chi_zero]

/-! ## The delta polynomial `p` and its positive root `u⋆` (Prop 4.1) -/

/-- Paper XII, Proposition 4.1.  The delta polynomial
`p(u) = u^{N+1} + u^N + (N-1)u - 1`, whose unique positive root controls the
delta law. -/
def deltaPoly (n : ℕ) (u : ℝ) : ℝ :=
  u ^ (N n + 1) + u ^ (N n) + ((N n : ℝ) - 1) * u - 1

/-- Paper XII, Proposition 4.1: `p(0) = -1 < 0`. -/
lemma deltaPoly_zero (n : ℕ) : deltaPoly n 0 = -1 := by
  have h1 : N n ≠ 0 := (N_pos n).ne'
  rw [deltaPoly, zero_pow (by omega : N n + 1 ≠ 0), zero_pow h1]
  ring

/-- Paper XII, Proposition 4.1: `p` is strictly increasing on `[0,∞)` (its
derivative `(N+1)u^N + N u^{N-1} + (N-1)` is positive there). -/
lemma deltaPoly_strictMonoOn (n : ℕ) (hn : 2 ≤ n) :
    StrictMonoOn (deltaPoly n) (Set.Ici (0 : ℝ)) := by
  have hN1 : (1:ℝ) < (N n : ℝ) := one_lt_N n hn
  intro x hx y _ hxy
  simp only [Set.mem_Ici] at hx
  unfold deltaPoly
  have h1 : x ^ (N n + 1) ≤ y ^ (N n + 1) := pow_le_pow_left₀ hx hxy.le _
  have h2 : x ^ (N n) ≤ y ^ (N n) := pow_le_pow_left₀ hx hxy.le _
  have h3 : ((N n : ℝ) - 1) * x < ((N n : ℝ) - 1) * y :=
    mul_lt_mul_of_pos_left hxy (by linarith)
  linarith

/-- Paper XII, Proposition 4.1: `p(1/(N-1)) > 0`. -/
lemma deltaPoly_pos_at_bound (n : ℕ) (hn : 2 ≤ n) :
    0 < deltaPoly n (1 / ((N n : ℝ) - 1)) := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  set c := 1 / ((N n : ℝ) - 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcancel : ((N n : ℝ) - 1) * c = 1 := by rw [hc, mul_one_div, div_self hN1.ne']
  have hval : deltaPoly n c = c ^ (N n + 1) + c ^ (N n) := by
    unfold deltaPoly; rw [hcancel]; ring
  rw [hval]
  exact add_pos (pow_pos hcpos _) (pow_pos hcpos _)

/-- Paper XII, Proposition 4.1: `p` has a unique positive root, and it lies in
`(0, 1/(N-1))`.  (Existence/uniqueness follow from `deltaPoly_zero`,
`deltaPoly_pos_at_bound`, and strict monotonicity on `[0,∞)`.) -/
theorem uStar_exists_unique (n : ℕ) (hn : 2 ≤ n) :
    ∃! u : ℝ, 0 < u ∧ deltaPoly n u = 0 := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  set c := 1 / ((N n : ℝ) - 1) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcont : Continuous (deltaPoly n) := by unfold deltaPoly; fun_prop
  have hp0 : deltaPoly n 0 = -1 := deltaPoly_zero n
  have hpc : 0 < deltaPoly n c := deltaPoly_pos_at_bound n hn
  have hmem : (0:ℝ) ∈ Set.Icc (deltaPoly n 0) (deltaPoly n c) := by
    rw [hp0]; exact ⟨by linarith, le_of_lt hpc⟩
  obtain ⟨u, hu_mem, hu_zero⟩ := intermediate_value_Icc hcpos.le hcont.continuousOn hmem
  have hupos : 0 < u := by
    rcases lt_or_eq_of_le hu_mem.1 with h | h
    · exact h
    · exfalso; rw [← h, hp0] at hu_zero; norm_num at hu_zero
  refine ⟨u, ⟨hupos, hu_zero⟩, ?_⟩
  rintro v ⟨hvpos, hvzero⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hlt := deltaPoly_strictMonoOn n hn (Set.mem_Ici.mpr hvpos.le) (Set.mem_Ici.mpr hupos.le) h
    rw [hvzero, hu_zero] at hlt; exact absurd hlt (lt_irrefl 0)
  · have hlt := deltaPoly_strictMonoOn n hn (Set.mem_Ici.mpr hupos.le) (Set.mem_Ici.mpr hvpos.le) h
    rw [hvzero, hu_zero] at hlt; exact absurd hlt (lt_irrefl 0)

/-- Paper XII, Proposition 4.1.  The unique positive root `u⋆` of `p`
(a junk value `0` off the meaningful range `n ≥ 2`, so that `u⋆` is total). -/
noncomputable def uStar (n : ℕ) : ℝ :=
  if h : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0 then h.choose else 0

/-- Paper XII, Proposition 4.1: `u⋆` is a positive root of `p` (for `n ≥ 2`). -/
lemma uStar_spec (n : ℕ) (hn : 2 ≤ n) :
    0 < uStar n ∧ deltaPoly n (uStar n) = 0 := by
  have hx : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0 := (uStar_exists_unique n hn).exists
  rw [uStar, dif_pos hx]
  exact hx.choose_spec

/-- Paper XII, Proposition 4.1: `u⋆ > 0`. -/
lemma uStar_pos (n : ℕ) (hn : 2 ≤ n) : 0 < uStar n := (uStar_spec n hn).1

/-- Paper XII, Proposition 4.1: `p(u⋆) = 0`. -/
lemma deltaPoly_uStar (n : ℕ) (hn : 2 ≤ n) : deltaPoly n (uStar n) = 0 :=
  (uStar_spec n hn).2

/-- Paper XII, Proposition 4.1: `u⋆ ∈ (0, 1/(N-1))`. -/
lemma uStar_lt (n : ℕ) (hn : 2 ≤ n) : uStar n < 1 / ((N n : ℝ) - 1) := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hb : (0:ℝ) ≤ 1 / ((N n : ℝ) - 1) := le_of_lt (by positivity)
  by_contra hle
  push_neg at hle
  have hmono := (deltaPoly_strictMonoOn n hn).monotoneOn
    (Set.mem_Ici.mpr hb) (Set.mem_Ici.mpr (uStar_pos n hn).le) hle
  rw [deltaPoly_uStar n hn] at hmono
  linarith [deltaPoly_pos_at_bound n hn]

/-- Paper XII, Proposition 4.1: the calibration fixed point on the log-side,
`(1-(N-1)u)/(1+u) = u^N`, cleared of denominators, is exactly `p(u) = 0`. -/
lemma deltaPoly_root_iff (n : ℕ) (u : ℝ) :
    deltaPoly n u = 0 ↔ 1 - ((N n : ℝ) - 1) * u = u ^ (N n) * (1 + u) := by
  unfold deltaPoly
  rw [pow_succ, mul_add, mul_one]
  constructor <;> intro h <;> linarith

/-! ## The two-level delta law `X_δ` (Prop 4.1) -/

/-- Paper XII, Proposition 4.1.  The high level `A = 1 - (N-1)u⋆` (the value of
the density `X_δ` at the extinguished point `s⋆`). -/
noncomputable def deltaA (n : ℕ) : ℝ := 1 - ((N n : ℝ) - 1) * uStar n

/-- Paper XII, Proposition 4.1.  The bulk level `B = 1 + u⋆` (the value of the
density `X_δ` at every point `s ≠ s⋆`). -/
noncomputable def deltaB (n : ℕ) : ℝ := 1 + uStar n

/-- Paper XII, Proposition 4.1: `A = 1-(N-1)u⋆ > 0` (positivity of the Gibbs
law forces `u⋆ < 1/(N-1)`). -/
lemma deltaA_pos (n : ℕ) (hn : 2 ≤ n) : 0 < deltaA n := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hu := uStar_lt n hn
  have hlt : ((N n : ℝ) - 1) * uStar n < 1 := by
    have := (lt_div_iff₀ hN1).mp hu; nlinarith [this]
  unfold deltaA; linarith

/-- Paper XII, Proposition 4.1: `A = 1-(N-1)u⋆ < 1` (since `u⋆ > 0`). -/
lemma deltaA_lt_one (n : ℕ) (hn : 2 ≤ n) : deltaA n < 1 := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hu := uStar_pos n hn
  unfold deltaA; nlinarith [mul_pos hN1 hu]

/-- Paper XII, Proposition 4.1: `B = 1+u⋆ > 1`. -/
lemma deltaB_gt_one (n : ℕ) (hn : 2 ≤ n) : 1 < deltaB n := by
  have := uStar_pos n hn
  simp only [deltaB]; linarith

/-- `u⋆ ≥ 0` for every `n` (a positive root, or the junk value `0`). -/
lemma uStar_nonneg (n : ℕ) : 0 ≤ uStar n := by
  unfold uStar
  by_cases h : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0
  · rw [dif_pos h]; exact le_of_lt h.choose_spec.1
  · rw [dif_neg h]

/-- `A = 1-(N-1)u⋆ > 0` for EVERY `n` (no `n ≥ 2` needed): if `u⋆` is a genuine
root then `p(u⋆)=0` forces `(N-1)u⋆ = 1 - u⋆^{N+1} - u⋆^N < 1`; otherwise `u⋆=0`
and `A = 1`. -/
lemma deltaA_pos_all (n : ℕ) : 0 < deltaA n := by
  unfold deltaA
  by_cases h : ∃ u : ℝ, 0 < u ∧ deltaPoly n u = 0
  · have hspec : 0 < uStar n ∧ deltaPoly n (uStar n) = 0 := by
      unfold uStar; rw [dif_pos h]; exact h.choose_spec
    obtain ⟨hpos, hroot⟩ := hspec
    unfold deltaPoly at hroot
    nlinarith [hroot, pow_pos hpos (N n + 1), pow_pos hpos (N n)]
  · have h0 : uStar n = 0 := by unfold uStar; rw [dif_neg h]
    rw [h0]; simp

/-- Paper XII, Proposition 4.1 (two-level law).  The calibrated law of the
delta orientation at `s⋆`: the probability law with density
`X_δ(s⋆) = A = 1-(N-1)u⋆` and `X_δ(s) = B = 1+u⋆` for `s ≠ s⋆`, i.e.
`P(s) = X_δ(s)/N`. -/
noncomputable def deltaLaw (sstar : Point n) : ProbLaw n where
  P := fun s => (if s = sstar then deltaA n else deltaB n) / (N n : ℝ)
  pos := by
    have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
    have hA : 0 < deltaA n := deltaA_pos_all n
    have hB : 0 < deltaB n := by
      have := uStar_nonneg n; simp only [deltaB]; linarith
    intro s
    apply div_pos _ hN
    split
    · exact hA
    · exact hB
  sum_one := by
    have hN : (N n : ℝ) ≠ 0 := N_ne_zero n
    have hsum : (∑ s, (if s = sstar then deltaA n else deltaB n)) = (N n : ℝ) := by
      have hsplit : ∀ s : Point n, (if s = sstar then deltaA n else deltaB n)
          = deltaB n + (if s = sstar then (deltaA n - deltaB n) else 0) := by
        intro s; split <;> ring
      rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, card_point,
          Finset.sum_ite_eq' Finset.univ sstar (fun _ => deltaA n - deltaB n),
          if_pos (Finset.mem_univ sstar), nsmul_eq_mul]
      unfold deltaA deltaB
      ring
    rw [← Finset.sum_div, hsum, div_self hN]

/-- Paper XII, Proposition 4.1 (density in closed form): the density of
`deltaLaw sstar` w.r.t. uniform is the two-level field
`X_δ(s) = if s = s⋆ then A else B`. -/
lemma dens_deltaLaw (sstar s : Point n) :
    dens (deltaLaw sstar) s = if s = sstar then deltaA n else deltaB n := by
  have hN : (N n : ℝ) ≠ 0 := N_ne_zero n
  simp only [dens, deltaLaw]
  rw [mul_div_cancel₀ _ hN]  -- TODO(api): verify `mul_div_cancel₀ : b ≠ 0 → b * (a / b) = a`

/-! ## Section-3 interface: unique calibrated law `P_ε` and the gap `ŵm` -/

/-- Paper XII, Theorem 3.1 (existence and uniqueness).  Every orientation has
exactly one calibrated law `P_ε` (the unique minimizer of the strictly convex
coercive `G_ε`). -/
theorem exists_unique_calibrated (ε : Orientation n) :
    ∃! P : ProbLaw n, Calibrated P ε :=
  calibrated_exists_unique ε

-- `calLaw`, `calLaw_calibrated`, `mhat`, `Ddelta` are canonical in `Calibration`
-- (imported).  `calLaw_unique` is not in `Calibration`, so keep it here:
/-- Paper XII, Theorem 3.1: any calibrated law for `ε` equals `P_ε = calLaw ε`. -/
lemma calLaw_unique (ε : Orientation n) {P : ProbLaw n} (hP : Calibrated P ε) :
    P = calLaw ε :=
  (exists_unique_calibrated ε).unique hP (calLaw_calibrated ε)

/-! ## Lemma 3.2 (translation covariance), the part §4 uses -/

/-- Paper XII, Lemma 3.2.  The translated orientation `(τ_t ε)_a = ε_a χ_a(t)`.
-/
def tauOrient (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := by
    intro a
    rcases ε.is_sign a with h | h <;> rcases chi_mem a.1 t with g | g <;>
      rw [h, g] <;> norm_num

/-- Paper XII, Lemma 3.2: `P_{τ_t ε}(s) = P_ε(s + t)`. -/
theorem calLaw_tauOrient (t : Point n) (ε : Orientation n) (s : Point n) :
    (calLaw (tauOrient t ε)).P s = (calLaw ε).P (s + t) := by
  obtain ⟨h, hP, hcal⟩ := calLaw_calibrated ε
  have hsign : ∀ a : NonzeroMask n, (tauOrient t ε).sign a = ε.sign a * chi a.1 t :=
    fun a => rfl
  have htilt : ∀ (s : Point n), tilt (tauOrient t ε) h s = tilt ε h (s + t) := by
    intro s
    unfold tilt
    apply Finset.sum_congr rfl
    intro a _
    rw [hsign a, chi_right_add]
    ring
  have hZ : (∑ r, Real.exp (tilt (tauOrient t ε) h r)) = ∑ r, Real.exp (tilt ε h r) := by
    have hstep : (∑ r, Real.exp (tilt (tauOrient t ε) h r))
        = ∑ r, Real.exp (tilt ε h (r + t)) :=
      Finset.sum_congr rfl (fun r _ => by rw [htilt r])
    rw [hstep]
    exact Fintype.sum_equiv (Equiv.addRight t)
      (fun r => Real.exp (tilt ε h (r + t)))
      (fun r => Real.exp (tilt ε h r))
      (fun x => rfl)
  let Q : ProbLaw n :=
    { P := fun s => (calLaw ε).P (s + t)
      pos := fun s => (calLaw ε).pos (s + t)
      sum_one := by
        rw [← (calLaw ε).sum_one]
        exact Fintype.sum_equiv (Equiv.addRight t)
          (fun s => (calLaw ε).P (s + t)) (fun s => (calLaw ε).P s) (fun x => rfl) }
  have hcalib : Calibrated Q (tauOrient t ε) := by
    refine ⟨h, ?_, ?_⟩
    · intro s
      show (calLaw ε).P (s + t)
          = Real.exp (tilt (tauOrient t ε) h s) / (∑ r, Real.exp (tilt (tauOrient t ε) h r))
      rw [hP (s + t), htilt s, hZ]
    · intro a
      rw [← hcal a]
      show (∑ s, Q.P s * ((tauOrient t ε).sign a * chi a.1 s))
          = ∑ s, (calLaw ε).P s * (ε.sign a * chi a.1 s)
      rw [← Fintype.sum_equiv (Equiv.addRight t)
          (fun s => (calLaw ε).P (s + t) * (ε.sign a * chi a.1 (s + t)))
          (fun s => (calLaw ε).P s * (ε.sign a * chi a.1 s))
          (fun x => rfl)]
      apply Finset.sum_congr rfl
      intro s _
      show (calLaw ε).P (s + t) * ((tauOrient t ε).sign a * chi a.1 s)
          = (calLaw ε).P (s + t) * (ε.sign a * chi a.1 (s + t))
      rw [hsign a, chi_right_add]
      ring
  have hQeQ : Q = calLaw (tauOrient t ε) := calLaw_unique (tauOrient t ε) hcalib
  have key : (calLaw (tauOrient t ε)).P s = Q.P s := by rw [← hQeQ]
  exact key
/-- Paper XII, Lemma 3.2: `ŵm(τ_t ε) = ŵm(ε)` (relative entropy to the
translation-invariant `U` is unchanged by a translate). -/
theorem mhat_tauOrient (t : Point n) (ε : Orientation n) :
    mhat (tauOrient t ε) = mhat ε := by
  have hsum :
      (∑ s, dens (calLaw (tauOrient t ε)) s * Real.log (dens (calLaw (tauOrient t ε)) s))
        = ∑ s, dens (calLaw ε) s * Real.log (dens (calLaw ε) s) := by
    have h1 :
        (∑ s, dens (calLaw (tauOrient t ε)) s * Real.log (dens (calLaw (tauOrient t ε)) s))
          = ∑ s, dens (calLaw ε) (s + t) * Real.log (dens (calLaw ε) (s + t)) :=
      Finset.sum_congr rfl (fun s _ => by simp only [dens, calLaw_tauOrient t ε s])
    rw [h1]
    exact Equiv.sum_comp (Equiv.addRight t)
      (fun u => dens (calLaw ε) u * Real.log (dens (calLaw ε) u))
  simp only [mhat, Dkl, EU, hsum]
/-- Paper XII, Lemma 3.2 (delta orbit): `τ_t (ε⋆ at s⋆) = ε⋆ at s⋆ + t`; the
`N` delta orientations form a single translation orbit. -/
theorem tauOrient_deltaOrientation (t sstar : Point n) :
    tauOrient t (deltaOrientation sstar) = deltaOrientation (sstar + t) := by
  apply Orientation.ext
  intro a
  show (- chi a.1 sstar) * chi a.1 t = - chi a.1 (sstar + t)
  rw [chi_right_add]
  ring

/-! ## Proposition 4.1: the calibrated law of the delta orientation -/

/-- Paper XII, Proposition 4.1.  The two-level law `deltaLaw sstar` IS calibrated
for the delta orientation at `s⋆` (with all tilts equal, `h_a = -log u⋆ > 0`).
-/
theorem calibrated_deltaLaw (sstar : Point n) (hn : 2 ≤ n) :
    Calibrated (deltaLaw sstar) (deltaOrientation sstar) := by
  -- basic facts
  have hu : 0 < uStar n := uStar_pos n hn
  have hune : uStar n ≠ 0 := hu.ne'
  have hNne : (N n : ℝ) ≠ 0 := N_ne_zero n
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hexpL : Real.exp (Real.log (uStar n)) = uStar n := Real.exp_log hu
  have hD : (0:ℝ) < (uStar n) ^ (N n) + ((N n : ℝ) - 1) := add_pos (pow_pos hu (N n)) hN1
  -- root identity
  have hroot : 1 - ((N n : ℝ) - 1) * uStar n = (uStar n) ^ (N n) * (1 + uStar n) :=
    (deltaPoly_root_iff n (uStar n)).mp (deltaPoly_uStar n hn)
  have hDB : ((uStar n) ^ (N n) + ((N n : ℝ) - 1)) * (1 + uStar n) = (N n : ℝ) := by
    linear_combination -hroot
  have hAD : deltaA n * ((uStar n) ^ (N n) + ((N n : ℝ) - 1)) = (uStar n) ^ (N n) * (N n : ℝ) := by
    unfold deltaA
    linear_combination ((uStar n) ^ (N n) + ((N n : ℝ) - 1)) * hroot + (uStar n) ^ (N n) * hDB
  have hBD : deltaB n * ((uStar n) ^ (N n) + ((N n : ℝ) - 1)) = (N n : ℝ) := by
    unfold deltaB
    linear_combination hDB
  -- tilt closed form
  have htilt : ∀ s : Point n,
      tilt (deltaOrientation sstar) (fun _ => -Real.log (uStar n)) s
        = Real.log (uStar n) * ((if s = sstar then (N n : ℝ) else 0) - 1) := by
    intro s
    have hchar : (sstar + s = 0) ↔ (s = sstar) := by
      constructor
      · intro hh
        funext i
        have hi := congrFun hh i
        simp only [Pi.add_apply, Pi.zero_apply] at hi
        have key : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
        exact key _ _ hi
      · intro hh
        funext i
        have hi := congrFun hh i
        simp only [Pi.add_apply, Pi.zero_apply]
        have key : ∀ x y : ZMod 2, y = x → x + y = 0 := by decide
        exact key _ _ hi
    unfold tilt
    have hstep : ∀ a : NonzeroMask n,
        (fun _ : NonzeroMask n => -Real.log (uStar n)) a * (deltaOrientation sstar).sign a * chi a.1 s
          = Real.log (uStar n) * chi a.1 (sstar + s) := by
      intro a
      show (-Real.log (uStar n)) * (- chi a.1 sstar) * chi a.1 s
          = Real.log (uStar n) * chi a.1 (sstar + s)
      rw [chi_right_add]; ring
    rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum, sum_nonzero_chi (sstar + s)]
    by_cases hs : s = sstar
    · rw [if_pos (hchar.mpr hs), if_pos hs]
    · rw [if_neg (fun hc => hs (hchar.mp hc)), if_neg hs]
  -- exp of tilt, pointwise
  have hg : ∀ r : Point n,
      Real.exp (tilt (deltaOrientation sstar) (fun _ => -Real.log (uStar n)) r)
        = if r = sstar then (uStar n) ^ (N n) / uStar n else 1 / uStar n := by
    intro r
    rw [htilt r]
    by_cases hr : r = sstar
    · rw [if_pos hr, if_pos hr,
        show Real.log (uStar n) * ((N n : ℝ) - 1)
            = (N n : ℝ) * Real.log (uStar n) + (-(Real.log (uStar n))) from by ring,
        Real.exp_add, Real.exp_nat_mul, hexpL, Real.exp_neg, hexpL, div_eq_mul_inv]
    · rw [if_neg hr, if_neg hr,
        show Real.log (uStar n) * ((0 : ℝ) - 1) = -(Real.log (uStar n)) from by ring,
        Real.exp_neg, hexpL, one_div]
  -- normalizer
  have hZ : (∑ r, Real.exp (tilt (deltaOrientation sstar) (fun _ => -Real.log (uStar n)) r))
      = ((uStar n) ^ (N n) + ((N n : ℝ) - 1)) / uStar n := by
    rw [Finset.sum_congr rfl (fun r _ => hg r)]
    have hsplit : ∀ r : Point n,
        (if r = sstar then (uStar n) ^ (N n) / uStar n else 1 / uStar n)
          = 1 / uStar n + (if r = sstar then ((uStar n) ^ (N n) / uStar n - 1 / uStar n) else 0) := by
      intro r; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun r _ => hsplit r), Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, card_point,
        Finset.sum_ite_eq' Finset.univ sstar (fun _ => (uStar n) ^ (N n) / uStar n - 1 / uStar n),
        if_pos (Finset.mem_univ sstar), nsmul_eq_mul]
    field_simp
    ring
  -- assemble
  refine ⟨fun _ => -Real.log (uStar n), ?_, ?_⟩
  · -- first calibration condition
    intro s
    have hZne : (∑ r, Real.exp (tilt (deltaOrientation sstar) (fun _ => -Real.log (uStar n)) r)) ≠ 0 := by
      rw [hZ]; exact (div_pos hD hu).ne'
    rw [eq_div_iff hZne, hZ, hg s]
    show (if s = sstar then deltaA n else deltaB n) / (N n : ℝ)
          * (((uStar n) ^ (N n) + ((N n : ℝ) - 1)) / uStar n)
        = (if s = sstar then (uStar n) ^ (N n) / uStar n else 1 / uStar n)
    by_cases hs : s = sstar
    · rw [if_pos hs, if_pos hs, div_mul_div_comm, hAD,
        div_eq_div_iff (mul_ne_zero hNne hune) hune]
      ring
    · rw [if_neg hs, if_neg hs, div_mul_div_comm, hBD,
        div_eq_div_iff (mul_ne_zero hNne hune) hune]
      ring
  · -- second calibration condition
    intro a
    simp only [neg_neg]
    rw [hexpL]
    unfold EP
    have hfe : ∀ s : Point n,
        (deltaLaw sstar).P s * ((deltaOrientation sstar).sign a * chi a.1 s)
          = (- chi a.1 sstar) / (N n : ℝ)
              * ((if s = sstar then deltaA n else deltaB n) * chi a.1 s) := by
      intro s
      show ((if s = sstar then deltaA n else deltaB n) / (N n : ℝ))
            * ((- chi a.1 sstar) * chi a.1 s)
          = (- chi a.1 sstar) / (N n : ℝ)
              * ((if s = sstar then deltaA n else deltaB n) * chi a.1 s)
      ring
    rw [Finset.sum_congr rfl (fun s _ => hfe s), ← Finset.mul_sum]
    have hS : (∑ s, (if s = sstar then deltaA n else deltaB n) * chi a.1 s)
        = (deltaA n - deltaB n) * chi a.1 sstar := by
      have hsplit : ∀ s : Point n,
          (if s = sstar then deltaA n else deltaB n) * chi a.1 s
            = deltaB n * chi a.1 s
                + (if s = sstar then (deltaA n - deltaB n) * chi a.1 s else 0) := by
        intro s; split_ifs <;> ring
      rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib, ← Finset.mul_sum,
          sum_chi a.1, if_neg a.2, mul_zero, zero_add,
          Finset.sum_ite_eq' Finset.univ sstar (fun s => (deltaA n - deltaB n) * chi a.1 s),
          if_pos (Finset.mem_univ sstar)]
    rw [hS]
    have hchisq : chi a.1 sstar * chi a.1 sstar = 1 := by
      rcases chi_mem a.1 sstar with h | h <;> rw [h] <;> norm_num
    have hAB : deltaA n - deltaB n = -((N n : ℝ) * uStar n) := by
      unfold deltaA deltaB; ring
    rw [hAB,
      show (- chi a.1 sstar) / (N n : ℝ) * ((-((N n : ℝ) * uStar n)) * chi a.1 sstar)
          = (N n : ℝ) * uStar n * (chi a.1 sstar * chi a.1 sstar) / (N n : ℝ) from by ring,
      hchisq, mul_one, mul_comm (N n : ℝ) (uStar n), mul_div_assoc, div_self hNne, mul_one]
/-- Paper XII, Proposition 4.1: consequently `deltaLaw sstar` is THE calibrated
law of the delta orientation, `P_{ε⋆} = deltaLaw sstar` (Theorem 3.1
uniqueness). -/
theorem calLaw_deltaOrientation (sstar : Point n) (hn : 2 ≤ n) :
    calLaw (deltaOrientation sstar) = deltaLaw sstar :=
  (calLaw_unique (deltaOrientation sstar) (calibrated_deltaLaw sstar hn)).symm

/-- Paper XII, Proposition 4.1: hence `ŵm(ε⋆) = D(deltaLaw ‖ U)`. -/
theorem mhat_deltaOrientation (sstar : Point n) (hn : 2 ≤ n) :
    mhat (deltaOrientation sstar) = Dkl (deltaLaw sstar) := by
  unfold mhat
  rw [calLaw_deltaOrientation sstar hn]

/-! ## The delta gap `D_δ` and its closed form (Prop 4.1) -/

-- `Ddelta` is canonical in `Calibration` (imported).

/-- Paper XII, Proposition 4.1 (closed form):
`D_δ = (1/N)[A log A + (N-1) B log B]` with `A = 1-(N-1)u⋆`, `B = 1+u⋆`. -/
theorem Ddelta_closedForm (n : ℕ) (hn : 2 ≤ n) :
    Ddelta n
      = (deltaA n * Real.log (deltaA n)
          + ((N n : ℝ) - 1) * (deltaB n * Real.log (deltaB n))) / (N n : ℝ) := by
  unfold Ddelta
  rw [mhat_deltaOrientation (0 : Point n) hn, Dkl, EU]
  congr 1
  have hsplit : ∀ s : Point n,
      dens (deltaLaw (0 : Point n)) s * Real.log (dens (deltaLaw (0 : Point n)) s)
        = deltaB n * Real.log (deltaB n)
          + (if s = (0 : Point n)
              then deltaA n * Real.log (deltaA n) - deltaB n * Real.log (deltaB n)
              else 0) := by
    intro s
    rw [dens_deltaLaw]
    by_cases h : s = (0 : Point n)
    · simp only [if_pos h]; ring
    · simp only [if_neg h]; ring
  rw [Finset.sum_congr rfl (fun s _ => hsplit s), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, card_point,
      Finset.sum_ite_eq' Finset.univ (0 : Point n)
        (fun _ => deltaA n * Real.log (deltaA n) - deltaB n * Real.log (deltaB n)),
      if_pos (Finset.mem_univ (0 : Point n)), nsmul_eq_mul]
  ring
/-! ## Symmetry Lemma 3.2: all `N` delta orientations share `D_δ` -/

/-- Paper XII, Lemma 3.2 / §4 remark: all `N` delta orientations share the single
value `D_δ`, since they form one translation orbit and `ŵm` is
translation-invariant. -/
theorem mhat_deltaOrientation_const (sstar : Point n) :
    mhat (deltaOrientation sstar) = Ddelta n := by
  have h := mhat_tauOrient sstar (deltaOrientation (0 : Point n))
  rw [tauOrient_deltaOrientation, zero_add] at h
  exact h

/-! ## Lemma 4.2: the elementary delta bound -/

/-- Paper XII, Lemma 4.2: `D_δ > 0` (the calibrated delta law is not uniform). -/
theorem Ddelta_pos (n : ℕ) (hn : 2 ≤ n) : 0 < Ddelta n := by
  have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have hA : 0 < deltaA n := deltaA_pos_all n
  have hAlt : deltaA n < 1 := deltaA_lt_one n hn
  have hB : 0 < deltaB n := by
    have := uStar_nonneg n; simp only [deltaB]; linarith
  have hstep : Ddelta n = EU (fun s => psi (dens (deltaLaw (0:Point n)) s)) := by
    unfold Ddelta
    rw [mhat_deltaOrientation (0:Point n) hn, Dkl_eq_EU_psi]
  rw [hstep, EU]
  apply div_pos _ hN
  apply Finset.sum_pos'
  · intro s _
    rw [dens_deltaLaw]
    apply psi_nonneg
    split
    · exact hA.le
    · exact hB.le
  · refine ⟨0, Finset.mem_univ 0, ?_⟩
    rw [dens_deltaLaw, if_pos rfl]
    have hlt := psi_strictAntiOn (Set.mem_Icc.mpr ⟨hA.le, hAlt.le⟩)
      (Set.mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩) hAlt
    rw [psi_one] at hlt
    exact hlt
/-- Paper XII, Lemma 4.2: `D_δ < 1/(N-1)`.  (From `A log A ≤ 0`,
`log(1+u⋆) ≤ u⋆`, and `1 + u⋆ < N/(N-1)`.) -/
theorem Ddelta_lt (n : ℕ) (hn : 2 ≤ n) : Ddelta n < 1 / ((N n : ℝ) - 1) := by
  have hN1 : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
  have hNpos : (0:ℝ) < (N n : ℝ) := by linarith
  have hA_pos := deltaA_pos n hn
  have hA_lt := deltaA_lt_one n hn
  have hu_pos := uStar_pos n hn
  have hu_lt := uStar_lt n hn
  have hB_pos : (0:ℝ) < deltaB n := by simp only [deltaB]; linarith
  have hlogA : Real.log (deltaA n) ≤ 0 := Real.log_nonpos hA_pos.le hA_lt.le
  have hAlog : deltaA n * Real.log (deltaA n) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨hA_pos.le, hlogA⟩)
  have hlogB : Real.log (deltaB n) ≤ uStar n := by
    have h := Real.log_le_sub_one_of_pos hB_pos
    simp only [deltaB] at h ⊢; linarith
  have hBlog : deltaB n * Real.log (deltaB n) ≤ deltaB n * uStar n :=
    mul_le_mul_of_nonneg_left hlogB hB_pos.le
  rw [Ddelta_closedForm n hn, div_lt_div_iff₀ hNpos hN1]
  simp only [deltaB] at hBlog ⊢
  have htu : uStar n * ((N n:ℝ) - 1) < 1 := (lt_div_iff₀ hN1).mp hu_lt
  have hnum : deltaA n * Real.log (deltaA n)
        + ((N n:ℝ) - 1) * ((1 + uStar n) * Real.log (1 + uStar n))
      ≤ ((N n:ℝ) - 1) * ((1 + uStar n) * uStar n) := by
    have h2 : ((N n:ℝ) - 1) * ((1 + uStar n) * Real.log (1 + uStar n))
        ≤ ((N n:ℝ) - 1) * ((1 + uStar n) * uStar n) :=
      mul_le_mul_of_nonneg_left hBlog hN1.le
    linarith
  have hPpos : 0 < uStar n * ((N n:ℝ) - 1) := mul_pos hu_pos hN1
  have hQ : (1 + uStar n) * ((N n:ℝ) - 1) < (N n:ℝ) := by nlinarith [htu]
  have hQpos : 0 < (1 + uStar n) * ((N n:ℝ) - 1) :=
    mul_pos (by linarith : (0:ℝ) < 1 + uStar n) hN1
  have hPQ : (uStar n * ((N n:ℝ) - 1)) * ((1 + uStar n) * ((N n:ℝ) - 1)) < 1 * (N n:ℝ) :=
    mul_lt_mul'' htu hQ hPpos.le hQpos.le
  have hmul := mul_le_mul_of_nonneg_right hnum hN1.le
  nlinarith [hmul, hPQ]
/-- Paper XII, Lemma 4.2 (statement as in the paper): `0 < D_δ < 1/(N-1)` for
every `n ≥ 2`. -/
theorem Lemma_4_2 (n : ℕ) (hn : 2 ≤ n) :
    0 < Ddelta n ∧ Ddelta n < 1 / ((N n : ℝ) - 1) :=
  ⟨Ddelta_pos n hn, Ddelta_lt n hn⟩

/-- Paper XII, Lemma 4.2 (remark): the bound is asymptotically tight,
`N·D_δ → 1` as `n → ∞`.  (From `p(u⋆) = 0` one gets
`u⋆ = (1/(N-1))(1 - O(N^{-N}))`, whence `N·D_δ → 1`.) -/
theorem N_Ddelta_tendsto_one :
    Tendsto (fun n : ℕ => (N n : ℝ) * Ddelta n) atTop (𝓝 1) := by
  -- N n → ∞
  have hN : Tendsto (fun n : ℕ => (N n : ℝ)) atTop atTop :=
    Tendsto.congr (fun n => by simp only [N]; push_cast; ring)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
  -- N n - 1 → ∞
  have hNm1 : Tendsto (fun n : ℕ => (N n : ℝ) - 1) atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-1 : ℝ) hN
    simpa [sub_eq_add_neg] using this
  -- 1/(N-1) → 0
  have hinv : Tendsto (fun n : ℕ => ((N n : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
    hNm1.inv_tendsto_atTop
  -- u⋆ → 0
  have hu : Tendsto (fun n : ℕ => uStar n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    · exact Eventually.of_forall (fun n => uStar_nonneg n)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have h := uStar_lt n hn
      rw [one_div] at h
      exact h.le
  -- deltaA n → 0
  have hA : Tendsto (fun n : ℕ => deltaA n) atTop (𝓝 0) := by
    have hupper : Tendsto (fun n : ℕ => uStar n * (1 + uStar n)) atTop (𝓝 0) := by
      have := hu.mul (hu.const_add (1 : ℝ))
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Eventually.of_forall (fun n => (deltaA_pos_all n).le)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      -- relation: deltaA n = u^N (1+u)
      have hroot := deltaPoly_uStar n hn
      rw [deltaPoly_root_iff] at hroot
      have hNpos : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
      have h4 : (4:ℝ) ≤ (N n : ℝ) := by
        have hnat : (4:ℕ) ≤ N n := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        exact_mod_cast hnat
      have hu1 : uStar n ≤ 1 := by
        have hle : (1:ℝ) / ((N n : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hNpos]; linarith
        exact le_of_lt (lt_of_lt_of_le (uStar_lt n hn) hle)
      show deltaA n ≤ uStar n * (1 + uStar n)
      unfold deltaA
      rw [hroot]
      apply mul_le_mul_of_nonneg_right
      · exact pow_le_of_le_one (uStar_nonneg n) hu1 (N_pos n).ne'
      · linarith [uStar_nonneg n]
  -- (N-1)·u → 1
  have hNm1u : Tendsto (fun n : ℕ => ((N n : ℝ) - 1) * uStar n) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 - deltaA n) atTop (𝓝 1) := by
      simpa using hA.const_sub (1 : ℝ)
    exact Tendsto.congr (fun n => by unfold deltaA; ring) h1
  -- lower / upper envelopes for term2
  have hLow : Tendsto (fun n : ℕ => 1 - deltaA n) atTop (𝓝 1) := by
    simpa using hA.const_sub (1 : ℝ)
  have hUp : Tendsto (fun n : ℕ => (1 - deltaA n) * (1 + uStar n)) atTop (𝓝 1) := by
    have := (hA.const_sub (1 : ℝ)).mul (hu.const_add (1 : ℝ))
    simpa using this
  -- term2 → 1
  have hterm2 : Tendsto
      (fun n : ℕ => ((N n : ℝ) - 1) * (deltaB n * Real.log (deltaB n)))
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLow hUp
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hid : (1:ℝ) - deltaA n = ((N n : ℝ) - 1) * uStar n := by unfold deltaA; ring
      have hBu : deltaB n = 1 + uStar n := rfl
      have hBpos : 0 < deltaB n := by rw [hBu]; linarith [uStar_nonneg n]
      have hNm1pos : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
      rw [hid]
      have hlb := Real.self_sub_one_le_mul_log hBpos.le
      have huv : uStar n = deltaB n - 1 := by rw [hBu]; ring
      have hule : uStar n ≤ deltaB n * Real.log (deltaB n) := by rw [huv]; exact hlb
      exact mul_le_mul_of_nonneg_left hule hNm1pos.le
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hid : (1:ℝ) - deltaA n = ((N n : ℝ) - 1) * uStar n := by unfold deltaA; ring
      have hBu : deltaB n = 1 + uStar n := rfl
      have hBpos : 0 < deltaB n := by rw [hBu]; linarith [uStar_nonneg n]
      have hNm1pos : (0:ℝ) < (N n : ℝ) - 1 := by have := one_lt_N n hn; linarith
      rw [hid]
      have hub := Real.log_le_sub_one_of_pos hBpos
      have h1 : deltaB n * Real.log (deltaB n) ≤ deltaB n * (deltaB n - 1) :=
        mul_le_mul_of_nonneg_left hub hBpos.le
      have h2 : deltaB n * (deltaB n - 1) = uStar n * (1 + uStar n) := by rw [hBu]; ring
      rw [h2] at h1
      calc ((N n : ℝ) - 1) * (deltaB n * Real.log (deltaB n))
          ≤ ((N n : ℝ) - 1) * (uStar n * (1 + uStar n)) :=
            mul_le_mul_of_nonneg_left h1 hNm1pos.le
        _ = ((N n : ℝ) - 1) * uStar n * (1 + uStar n) := by ring
  -- term1 → 0 (x log x continuous at 0)
  have hterm1 : Tendsto (fun n : ℕ => deltaA n * Real.log (deltaA n)) atTop (𝓝 0) := by
    have hc : Tendsto (fun x : ℝ => x * Real.log x) (𝓝 0) (𝓝 (0 * Real.log 0)) :=
      Real.continuous_mul_log.continuousAt
    have := hc.comp hA
    simpa [Function.comp_def] using this
  -- sum → 1
  have hsum : Tendsto
      (fun n : ℕ => deltaA n * Real.log (deltaA n)
        + ((N n : ℝ) - 1) * (deltaB n * Real.log (deltaB n))) atTop (𝓝 1) := by
    have := hterm1.add hterm2
    simpa using this
  -- transfer to N·Ddelta via closed form
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hNne : (N n : ℝ) ≠ 0 := by exact_mod_cast (N_pos n).ne'
  rw [Ddelta_closedForm n hn]
  field_simp
end WalshDelta
