import Mathlib
import WalshDelta.Basic
import WalshDelta.Calibration

/-!
# Walsh–delta: structure of low-entropy laws and the deep-dip trichotomy

Formalization of **Sections 5 and 6** of Paper XII,

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube".

Throughout, `P` is the calibrated law of an orientation `ε`, `X = dens P = N·P`,
`D = Dkl P ≤ 1/60`, and all decimal constants are safe-rounded exactly as in the
paper.

## What this file provides

* the dip / bulk / spike decomposition of the cube by the value of `X`
  (Section 5, "The dip/bulk/spike decomposition"): `dipSet`, `bulkSet`,
  `spikeSet`, the depth `depth s = -log X(s)`, and the **dip transform**
  `dipTransform a = ∑_{s ∈ 𝒮} β_s χ_a(s) = Φ(a)`;
* `Lemma 5.1` (parameter floor), `Lemma 5.2` (bookkeeping, including the
  calculus fact `|log x| ≤ 2|x-1|` on `[1/2,2]`), `Proposition 5.3` (spectral
  floor and sign readout: `|Φ(a)| ≥ N(h_min - ε_G) > 1.24416 N` and
  `ε_a = -sgn Φ(a)`), `Proposition 5.4` (dominance criterion);
* the shallow-depth bound `Σ_sh < 0.543149 N`, and `Theorem 6.1` (deep-dip
  trichotomy), with the cases `m = 0, 1, 2` isolated as sub-lemmas carrying the
  paper's numbers.

Every lemma is now **fully proved and kernel-verified** (no `sorry`, no
`native_decide`): the tight numeric constants (`hPrime_gt`,
`three_psi_exp_neg5_gt`) are discharged by exact interval arithmetic on Mathlib's
`exp_one_gt_d9` / `log_two,three,five_gt_d9` bounds, and `Theorem 6.1`
(`deep_dip_trichotomy`) depends only on `[propext, Classical.choice, Quot.sound]`.
-/

namespace WalshDelta

open scoped BigOperators

open Classical

variable {n : ℕ}

/-! ## Calibration data with an explicit parameter vector

`Calibrated P ε` (Basic.lean) is `∃ h, …`.  Section 5 works with a fixed choice
of the calibration parameters `h = (h_a)_{a≠0}`; `CalibratedWith P ε h` names the
body of that existential so lemmas may refer to `h_a` and `h_min` directly. -/

/-- Paper XII, Definition 1.1 (calibration with named parameters).  The body of
`Calibrated P ε` for the specific parameter vector `h`. -/
def CalibratedWith (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ) :
    Prop :=
  (∀ s, P.P s = Real.exp (tilt ε h s) / (∑ r, Real.exp (tilt ε h r)))
    ∧ (∀ a : NonzeroMask n,
        EP P (fun s => ε.sign a * chi a.1 s) = Real.exp (- h a))

/-- Paper XII, Definition 1.1: `P` is calibrated for `ε` iff it is calibrated
with *some* parameter vector `h`. -/
lemma calibrated_iff (P : ProbLaw n) (ε : Orientation n) :
    Calibrated P ε ↔ ∃ h : NonzeroMask n → ℝ, CalibratedWith P ε h := Iff.rfl

-- `IsDelta` is canonical in `Basic` (imported).

/-- `IsDelta ε` unpacked against `deltaOrientation` (the bridge from Basic's
equality form `ε = deltaOrientation s⋆` to the sign form). -/
lemma isDelta_iff (ε : Orientation n) :
    IsDelta ε ↔ ∃ sstar : Point n,
      ∀ a : NonzeroMask n, ε.sign a = (deltaOrientation sstar).sign a := by
  unfold IsDelta
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨s, fun _ => rfl⟩
  · rintro ⟨s, hs⟩; exact ⟨s, Orientation.ext hs⟩

/-! ## The minimum parameter `h_min` -/

/-- Paper XII, Section 5.  `h_min = min_{a≠0} h_a` (the smallest calibration
parameter; the minimum ranges over the nonempty finite set of nonzero masks). -/
noncomputable def hMin [Nonempty (NonzeroMask n)] (h : NonzeroMask n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty h

/-- Paper XII, Section 5: `h_min ≤ h_a` for every nonzero mask `a`. -/
lemma hMin_le [Nonempty (NonzeroMask n)] (h : NonzeroMask n → ℝ)
    (a : NonzeroMask n) : hMin h ≤ h a :=
  Finset.inf'_le _ (Finset.mem_univ a)  -- TODO(api): confirm `Finset.inf'_le`.

/-! ## The dip / bulk / spike decomposition (Section 5) -/

/-- Paper XII, Section 5 (dips).  `𝒮 = {s : X(s) ≤ 1/2}`. -/
noncomputable def dipSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => dens P s ≤ 1/2)

/-- Paper XII, Section 5 (bulk).  `𝒯 = {s : 1/2 < X(s) ≤ 2}`. -/
noncomputable def bulkSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => 1/2 < dens P s ∧ dens P s ≤ 2)

/-- Paper XII, Section 5 (spikes).  `𝒮' = {s : X(s) > 2}`. -/
noncomputable def spikeSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => 2 < dens P s)

/-- Paper XII, Section 5.  The **depth** of a dip, `β_s = -log X(s) ≥ log 2`
(finite, since calibrated laws have full support). -/
noncomputable def depth (P : ProbLaw n) (s : Point n) : ℝ := - Real.log (dens P s)

/-- Paper XII, Section 5.  The spike excess `ν_s = X(s) - 1`. -/
noncomputable def spikeExcess (P : ProbLaw n) (s : Point n) : ℝ := dens P s - 1

/-- Paper XII, Section 5.  The spike log `γ_s = log X(s)`. -/
noncomputable def spikeLog (P : ProbLaw n) (s : Point n) : ℝ := Real.log (dens P s)

/-- Paper XII, Section 5.  `k = |𝒮|`, the number of dips. -/
noncomputable def dipCount (P : ProbLaw n) : ℕ := (dipSet P).card

/-- Paper XII, Section 5 (dip transform).
`Φ(a) = ∑_{s ∈ 𝒮} β_s χ_a(s)` for `a ∈ 𝔽₂ⁿ` (with `Φ ≡ 0` if `𝒮 = ∅`). -/
noncomputable def dipTransform (P : ProbLaw n) (a : Point n) : ℝ :=
  ∑ s ∈ dipSet P, depth P s * chi a s

/-- Paper XII, Section 5.  The Walsh coefficient of `log X`,
`widehat{log X}(a) = (1/N) ∑_s log X(s) χ_a(s) = E_U[log X · χ_a]`. -/
noncomputable def logXhat (P : ProbLaw n) (a : Point n) : ℝ :=
  xhat (fun s => Real.log (dens P s)) a

/-- Paper XII, Proposition 5.3.  The Gibbs error scale `ε_G = (5/2)√(2D)`
(so that `ε_G ≤ (5/2)√(1/30) < 0.45644` when `D ≤ 1/60`). -/
noncomputable def epsG (P : ProbLaw n) : ℝ := (5/2) * Real.sqrt (2 * Dkl P)

/-- Paper XII, Proposition 5.3(ii).  The floor constant
`h' = (1/2)log 30 - (5/2)√(1/30) = 1.244163…`, the common worst case (at
`D = 1/60`) of the decreasing `(1/2)log(1/2D)` and the increasing `(5/2)√(2D)`. -/
noncomputable def hPrime : ℝ := (1/2) * Real.log 30 - (5/2) * Real.sqrt (1/30)

/-! ## Auxiliary identities and `ψ` values -/

/-- Paper XII, Lemma 2.2 / Section 2: `N·D = ∑_s ψ(X(s))`. -/
lemma N_mul_Dkl (P : ProbLaw n) :
    (N n : ℝ) * Dkl P = ∑ s, psi (dens P s) := by
  rw [Dkl_eq_EU_psi]
  simp only [EU]
  rw [mul_comm, div_mul_cancel₀ _ (N_ne_zero n)]
  -- TODO(api): confirm `div_mul_cancel₀` signature (a / b * b = a for b ≠ 0).

/-- Paper XII, Lemma 5.2(i): `ψ(1/2) = (1 - log 2)/2 = 0.153426…`. -/
lemma psi_half : psi (1/2 : ℝ) = (1 - Real.log 2) / 2 := by
  have hlog : Real.log (1/2 : ℝ) = - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
  unfold psi
  rw [hlog]; ring

/-- Paper XII, Theorem 6.1: `ψ(e^{-5}) = 1 - 6 e^{-5}` (deep-dip contribution). -/
lemma psi_exp_neg5 : psi (Real.exp (-5)) = 1 - 6 * Real.exp (-5) := by
  unfold psi
  rw [Real.log_exp]; ring

/-! ## Lemma 5.1 (parameter floor) -/

/-- Paper XII, Lemma 5.1 (parameter floor).  For the calibrated law with
parameters `h` and `D = Dkl P ≤ 1/60`, every nonzero mask `a` satisfies
`|x_a| ≤ √(2D)` and `h_a ≥ (1/2)log(1/2D) ≥ (1/2)log 30 > 1.70059`
(here `x_a = xhat (dens P) a`). -/
lemma parameter_floor (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    |xhat (dens P) a.1| ≤ Real.sqrt (2 * Dkl P)
    ∧ (1/2) * Real.log (1 / (2 * Dkl P)) ≤ h a
    ∧ (1.70059 : ℝ) < h a := by
  have hN : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  -- |χ_a| = 1
  have habs_chi : ∀ s, |chi a.1 s| = 1 := fun s => by
    rcases chi_mem a.1 s with hc | hc <;> rw [hc] <;> norm_num
  -- χ is symmetric in mask/point, and additive in the point argument
  have chi_symm : ∀ b c : Point n, chi b c = chi c b := by
    intro b c
    have hdot : dotZ2 b c = dotZ2 c b := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    unfold chi; rw [hdot]
  have chi_radd : ∀ s t : Point n, chi a.1 (s + t) = chi a.1 s * chi a.1 t := by
    intro s t
    rw [chi_symm a.1 (s + t), chi_add s t a.1, chi_symm s a.1, chi_symm t a.1]
  -- ∑ χ_a = 0 (a ≠ 0)  [Walsh orthogonality, inline]
  have hchi_sum : (∑ s, chi a.1 s) = 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp a.2
    simp only [Pi.zero_apply] at hj
    set ej : Point n := Pi.single j (1 : ZMod 2) with hej
    have hdot : dotZ2 a.1 ej = a.1 j := by
      unfold dotZ2
      rw [Finset.sum_eq_single j]
      · rw [hej, Pi.single_eq_same, mul_one]
      · intro i _ hij; rw [hej, Pi.single_eq_of_ne hij, mul_zero]
      · intro hh; exact absurd (Finset.mem_univ j) hh
    have hchi_ej : chi a.1 ej = -1 := by unfold chi; rw [hdot, if_neg hj]
    have hbij : (∑ s, chi a.1 (s + ej)) = ∑ s, chi a.1 s :=
      Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi a.1 (s + ej)) (chi a.1) (fun x => rfl)
    have hflip : (∑ s, chi a.1 (s + ej)) = ∑ s, (- chi a.1 s) :=
      Finset.sum_congr rfl (fun s _ => by rw [chi_radd, hchi_ej, mul_neg_one])
    rw [hflip, Finset.sum_neg_distrib] at hbij
    linarith [hbij]
  -- x_a = E_U[(X-1) χ_a]
  have hxeq : xhat (dens P) a.1 = EU (fun s => (dens P s - 1) * chi a.1 s) := by
    simp only [xhat, EU]
    congr 1
    have hpt : ∀ s, (dens P s - 1) * chi a.1 s
        = dens P s * chi a.1 s - chi a.1 s := fun s => by ring
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, hchi_sum, sub_zero]
  -- (a) |x_a| ≤ √(2D)  via Pinsker
  have habs_le : |xhat (dens P) a.1| ≤ Real.sqrt (2 * Dkl P) := by
    have hstep : |∑ s, (dens P s - 1) * chi a.1 s| ≤ ∑ s, |dens P s - 1| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun s _ => by rw [abs_mul, habs_chi s, mul_one])
    rw [hxeq]
    refine le_trans ?_ (pinsker P)
    unfold EU
    rw [abs_div, abs_of_nonneg hN.le]
    gcongr
  -- calibration:  ε_a · x_a = e^{-h_a}
  have hEP : EP P (fun s => ε.sign a * chi a.1 s) = ε.sign a * xhat (dens P) a.1 := by
    rw [xhat_dens_eq_EP]
    simp only [EP]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hkey : ε.sign a * xhat (dens P) a.1 = Real.exp (- h a) := by
    rw [← hEP]; exact hcal.2 a
  -- |x_a| = e^{-h_a}
  have hsign1 : |ε.sign a| = 1 := by
    rcases ε.is_sign a with hs | hs <;> rw [hs] <;> norm_num
  have habs_eq : |xhat (dens P) a.1| = Real.exp (- h a) := by
    have hb : |ε.sign a * xhat (dens P) a.1| = |Real.exp (- h a)| := by rw [hkey]
    rw [abs_mul, hsign1, one_mul, abs_of_pos (Real.exp_pos _)] at hb
    exact hb
  -- e^{-h_a} ≤ √(2D), hence D > 0
  have hexp_le : Real.exp (- h a) ≤ Real.sqrt (2 * Dkl P) := habs_eq ▸ habs_le
  have hsqrt_pos : 0 < Real.sqrt (2 * Dkl P) := lt_of_lt_of_le (Real.exp_pos _) hexp_le
  have h2D_pos : 0 < 2 * Dkl P := Real.sqrt_pos.mp hsqrt_pos
  -- (b)  (1/2) log(1/(2D)) ≤ h_a
  have hlog_le : - h a ≤ Real.log (Real.sqrt (2 * Dkl P)) :=
    (Real.le_log_iff_exp_le hsqrt_pos).mpr hexp_le
  have hlogsqrt : Real.log (Real.sqrt (2 * Dkl P)) = (1/2) * Real.log (2 * Dkl P) := by
    rw [Real.log_sqrt h2D_pos.le]; ring
  have hlog_inv : Real.log (1 / (2 * Dkl P)) = - Real.log (2 * Dkl P) := by
    rw [one_div, Real.log_inv]
  have hb : (1/2) * Real.log (1 / (2 * Dkl P)) ≤ h a := by
    rw [hlogsqrt] at hlog_le
    rw [hlog_inv]
    linarith [hlog_le]
  -- (c)  1.70059 < h_a
  have h30 : (30:ℝ) ≤ 1 / (2 * Dkl P) := by
    rw [le_div_iff₀ h2D_pos]; linarith
  have hloglog : Real.log 30 ≤ Real.log (1 / (2 * Dkl P)) :=
    Real.log_le_log (by norm_num) h30
  have hlog30 : (3.4011973 : ℝ) < Real.log 30 := by
    have e : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30:ℝ) = 2 * 3 * 5 by norm_num,
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
    rw [e]
    have h2 := Real.log_two_gt_d9
    have h3 := Real.log_three_gt_d9
    have h5 := Real.log_five_gt_d9
    linarith
  refine ⟨habs_le, hb, ?_⟩
  have hbc : (1/2) * Real.log (1 / (2 * Dkl P)) ≤ h a := hb
  linarith [hloglog, hlog30, hbc]
/-! ## Lemma 5.2 (bookkeeping) -/

/-- Paper XII, Lemma 5.2(iii) (calculus fact).  `|log x| ≤ 2|x-1|` on `[1/2,2]`. -/
lemma log_abs_le_two_abs_sub_one {x : ℝ} (h1 : (1:ℝ)/2 ≤ x) (h2 : x ≤ 2) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hx : (0:ℝ) < x := by linarith
  by_cases hle : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hle), abs_of_nonneg (by linarith : (0:ℝ) ≤ x - 1)]
    have := Real.log_le_sub_one_of_pos hx
    linarith
  · have hlt : x < 1 := not_le.mp hle
    rw [abs_of_neg (Real.log_neg hx hlt), abs_of_neg (by linarith : x - 1 < 0)]
    have hinv : (0:ℝ) < 1 / x := by positivity
    have hlog := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_div one_ne_zero hx.ne', Real.log_one] at hlog
    have hx2 : 1 / x ≤ 2 := by rw [div_le_iff₀ hx]; linarith
    have hprod : (2 * x - 1) * (1 - x) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    have hxx : 1 / x - 1 ≤ 2 - 2 * x := by
      rw [div_sub_one hx.ne', div_le_iff₀ hx]; nlinarith [hprod]
    linarith

/-- Paper XII, Lemma 5.2 (bookkeeping).  With `D = Dkl P ≤ 1/60` and
`ε := √(2D)`:

* (i) `k ≤ DN/ψ(1/2) < 0.108630 N` (with `ψ(1/2) = (1-log 2)/2 = 0.153426…`);
* (ii) `∑_{𝒮'} γ_s ≤ ∑_{𝒮'} ν_s ≤ Nε/2`;
* (iii) `(1/N) ∑_{𝒯} |log X| ≤ 2ε`. -/
lemma bookkeeping (P : ProbLaw n) (hD : Dkl P ≤ 1/60) :
    -- (i)
    ((dipCount P : ℝ) ≤ Dkl P * (N n : ℝ) / psi (1/2)
        ∧ (dipCount P : ℝ) < 0.108630 * (N n : ℝ))
    -- (ii)
    ∧ (∑ s ∈ spikeSet P, spikeLog P s ≤ ∑ s ∈ spikeSet P, spikeExcess P s
        ∧ ∑ s ∈ spikeSet P, spikeExcess P s ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2)
    -- (iii)
    ∧ (1 / (N n : ℝ)) * (∑ s ∈ bulkSet P, |Real.log (dens P s)|)
        ≤ 2 * Real.sqrt (2 * Dkl P) := by
  -- shared facts
  have hNpos : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have hdpos : ∀ s, 0 < dens P s := by
    intro s
    simp only [dens]
    exact mul_pos hNpos (P.pos s)
  have hsumX : (∑ s, dens P s) = (N n : ℝ) := by
    have h := EU_dens_eq_one P; simp only [EU] at h
    field_simp at h; linarith
  have hsum0 : (∑ s, (dens P s - 1)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hone : (∑ _s : Point n, (1:ℝ)) = (N n : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, card_point]; simp
    rw [hsumX, hone]; ring
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hcbound : (0.1534264096:ℝ) < psi (1/2) := by
    rw [psi_half]; linarith
  have hcpos : (0:ℝ) < psi (1/2) := by linarith
  -- |x| = 2·max(x,0) - x
  have hpt : ∀ s, |dens P s - 1| = 2 * max (dens P s - 1) 0 - (dens P s - 1) := by
    intro s
    rcases le_or_gt (0:ℝ) (dens P s - 1) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right (le_of_lt h), abs_of_neg h]; ring
  have hsumabs : ∑ s, |dens P s - 1| = 2 * ∑ s, max (dens P s - 1) 0 := by
    have h1 : ∑ s, |dens P s - 1|
        = ∑ s, (2 * max (dens P s - 1) 0 - (dens P s - 1)) :=
      Finset.sum_congr rfl (fun s _ => hpt s)
    rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum0]; ring
  -- ∑|X-1| ≤ N√(2D)  (Pinsker)
  have hsumabs_le : ∑ s, |dens P s - 1| ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) := by
    have hp := pinsker P
    simp only [EU] at hp
    rw [div_le_iff₀ hNpos] at hp
    calc ∑ s, |dens P s - 1| ≤ Real.sqrt (2 * Dkl P) * (N n : ℝ) := hp
      _ = (N n : ℝ) * Real.sqrt (2 * Dkl P) := by ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- (i) first: dipCount ≤ Dkl·N/ψ(1/2)
    have hstep : ∀ s ∈ dipSet P, psi (1/2) ≤ psi (dens P s) := by
      intro s hs
      simp only [dipSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact psi_strictAntiOn.antitoneOn
        (Set.mem_Icc.mpr ⟨le_of_lt (hdpos s), by linarith⟩)
        (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) hs
    have hsum1 : ∑ s ∈ dipSet P, psi (1/2) ≤ ∑ s ∈ dipSet P, psi (dens P s) :=
      Finset.sum_le_sum hstep
    have hsum2 : ∑ s ∈ dipSet P, psi (dens P s) ≤ ∑ s, psi (dens P s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _; exact psi_nonneg (le_of_lt (hdpos s))
    have hconst : (dipCount P : ℝ) * psi (1/2) = ∑ _s ∈ dipSet P, psi (1/2) := by
      rw [Finset.sum_const, nsmul_eq_mul]; rfl
    have key : (dipCount P : ℝ) * psi (1/2) ≤ (N n : ℝ) * Dkl P := by
      rw [hconst, N_mul_Dkl]; exact le_trans hsum1 hsum2
    rw [le_div_iff₀ hcpos]
    calc (dipCount P : ℝ) * psi (1/2) ≤ (N n : ℝ) * Dkl P := key
      _ = Dkl P * (N n : ℝ) := by ring
  · -- (i) second: dipCount < 0.108630 N
    have hstep : ∀ s ∈ dipSet P, psi (1/2) ≤ psi (dens P s) := by
      intro s hs
      simp only [dipSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact psi_strictAntiOn.antitoneOn
        (Set.mem_Icc.mpr ⟨le_of_lt (hdpos s), by linarith⟩)
        (Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩) hs
    have hsum1 : ∑ s ∈ dipSet P, psi (1/2) ≤ ∑ s ∈ dipSet P, psi (dens P s) :=
      Finset.sum_le_sum hstep
    have hsum2 : ∑ s ∈ dipSet P, psi (dens P s) ≤ ∑ s, psi (dens P s) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _; exact psi_nonneg (le_of_lt (hdpos s))
    have hconst : (dipCount P : ℝ) * psi (1/2) = ∑ _s ∈ dipSet P, psi (1/2) := by
      rw [Finset.sum_const, nsmul_eq_mul]; rfl
    have key : (dipCount P : ℝ) * psi (1/2) ≤ (N n : ℝ) * Dkl P := by
      rw [hconst, N_mul_Dkl]; exact le_trans hsum1 hsum2
    have hdnn : (0:ℝ) ≤ (dipCount P : ℝ) := Nat.cast_nonneg _
    nlinarith [key, mul_le_mul_of_nonneg_left hD (le_of_lt hNpos),
      mul_nonneg hdnn (le_of_lt (sub_pos.mpr hcbound)), hNpos, hcbound, hdnn]
  · -- (ii) first: ∑ γ ≤ ∑ ν
    apply Finset.sum_le_sum
    intro s hs
    simp only [spikeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    unfold spikeLog spikeExcess
    exact Real.log_le_sub_one_of_pos (hdpos s)
  · -- (ii) second: ∑ ν ≤ Nε/2
    have hspike_eq : ∑ s ∈ spikeSet P, spikeExcess P s
        = ∑ s ∈ spikeSet P, max (dens P s - 1) 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp only [spikeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      unfold spikeExcess
      rw [max_eq_left (by linarith : (0:ℝ) ≤ dens P s - 1)]
    have hspike_le : ∑ s ∈ spikeSet P, max (dens P s - 1) 0
        ≤ ∑ s, max (dens P s - 1) 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro s _ _; exact le_max_right _ _
    calc ∑ s ∈ spikeSet P, spikeExcess P s
        = ∑ s ∈ spikeSet P, max (dens P s - 1) 0 := hspike_eq
      _ ≤ ∑ s, max (dens P s - 1) 0 := hspike_le
      _ = (1/2) * ∑ s, |dens P s - 1| := by rw [hsumabs]; ring
      _ ≤ (1/2) * ((N n : ℝ) * Real.sqrt (2 * Dkl P)) := by
          exact mul_le_mul_of_nonneg_left hsumabs_le (by norm_num)
      _ = (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2 := by ring
  · -- (iii)
    have hiii_step : ∀ s ∈ bulkSet P, |Real.log (dens P s)| ≤ 2 * |dens P s - 1| := by
      intro s hs
      simp only [bulkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact log_abs_le_two_abs_sub_one (le_of_lt hs.1) hs.2
    have hbulk_sum : ∑ s ∈ bulkSet P, |Real.log (dens P s)|
        ≤ 2 * ∑ s, |dens P s - 1| := by
      calc ∑ s ∈ bulkSet P, |Real.log (dens P s)|
          ≤ ∑ s ∈ bulkSet P, 2 * |dens P s - 1| := Finset.sum_le_sum hiii_step
        _ = 2 * ∑ s ∈ bulkSet P, |dens P s - 1| := by rw [Finset.mul_sum]
        _ ≤ 2 * ∑ s, |dens P s - 1| := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro s _ _; exact abs_nonneg _
    have hbulk_le : ∑ s ∈ bulkSet P, |Real.log (dens P s)|
        ≤ 2 * ((N n : ℝ) * Real.sqrt (2 * Dkl P)) := by
      calc ∑ s ∈ bulkSet P, |Real.log (dens P s)|
          ≤ 2 * ∑ s, |dens P s - 1| := hbulk_sum
        _ ≤ 2 * ((N n : ℝ) * Real.sqrt (2 * Dkl P)) :=
            mul_le_mul_of_nonneg_left hsumabs_le (by norm_num : (0:ℝ) ≤ 2)
    rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hNpos]
    calc ∑ s ∈ bulkSet P, |Real.log (dens P s)|
        ≤ 2 * ((N n : ℝ) * Real.sqrt (2 * Dkl P)) := hbulk_le
      _ = 2 * Real.sqrt (2 * Dkl P) * (N n : ℝ) := by ring
/-! ## Proposition 5.3 (spectral floor and sign readout) -/

/-- Paper XII, Proposition 5.3(ii): the floor constant beats `1.244163`
(`h' = 1.244163…`; certified numeric bound). -/
lemma hPrime_gt : (1.244163 : ℝ) < hPrime := by
  rw [hPrime]
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [show (30:ℝ) = 2 * 3 * 5 by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  have hlog2 := Real.log_two_gt_d9
  have hlog3 := Real.log_three_gt_d9
  have hlog5 := Real.log_five_gt_d9
  have hsqrt : Real.sqrt (1/30) < 0.18257427 := by
    rw [show (1/30 : ℝ) = 1/30 by norm_num]
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hlog30 : (3.4011973811 : ℝ) < Real.log 30 := by
    rw [h30]; linarith
  nlinarith [hsqrt, hlog30, Real.sqrt_nonneg (1/30 : ℝ)]
/-- Paper XII, Proposition 5.3(ii): at `D ≤ 1/60`, `h_min - ε_G ≥ h'`.
Both `(1/2)log(1/2D)` (decreasing) and `(5/2)√(2D)` (increasing) are worst at
`D = 1/60`. -/
lemma hMin_sub_epsG_ge_hPrime [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) :
    hPrime ≤ hMin h - epsG P := by
  -- Dkl P ≥ 0
  have hDnn : 0 ≤ Dkl P := by
    rw [Dkl_eq_EU_psi]
    unfold EU
    apply div_nonneg _ (le_of_lt (by exact_mod_cast N_pos n))
    apply Finset.sum_nonneg
    intro s _
    apply psi_nonneg
    have hpos : 0 < dens P s := by
      unfold dens; exact mul_pos (by exact_mod_cast N_pos n) (P.pos s)
    exact hpos.le
  -- epsG bound: epsG P ≤ (5/2) * √(1/30)
  have h2D : 2 * Dkl P ≤ 1/30 := by linarith
  have hsqrt_le : Real.sqrt (2 * Dkl P) ≤ Real.sqrt (1/30) := Real.sqrt_le_sqrt h2D
  have hepsG_le : epsG P ≤ (5/2) * Real.sqrt (1/30) := by
    unfold epsG
    nlinarith [hsqrt_le, Real.sqrt_nonneg (2 * Dkl P), Real.sqrt_nonneg (1/30:ℝ)]
  rcases eq_or_lt_of_le hDnn with hD0 | hDpos
  · -- Dkl P = 0, so epsG P = 0
    have hepsG0 : epsG P = 0 := by
      unfold epsG; rw [← hD0]; simp
    -- hMin h ≥ 1.70059
    have hmin_ge : (1.70059 : ℝ) ≤ hMin h := by
      unfold hMin
      apply Finset.le_inf'
      intro a _
      obtain ⟨_, _, h3⟩ := parameter_floor P ε h hcal hD a
      exact h3.le
    -- hPrime ≤ 1.70059
    have hlog30_ub : Real.log 30 ≤ (3.4011973822 : ℝ) := by
      have e1 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
        rw [show (30:ℝ) = 2 * 3 * 5 by norm_num,
          Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
      rw [e1]
      have := Real.log_two_lt_d9
      have := Real.log_three_lt_d9
      have := Real.log_five_lt_d9
      linarith
    have hsqrt_lb : (1/10 : ℝ) ≤ Real.sqrt (1/30) := by
      have h1 : Real.sqrt (1/100) ≤ Real.sqrt (1/30) := Real.sqrt_le_sqrt (by norm_num)
      have h2 : Real.sqrt (1/100 : ℝ) = 1/10 := by
        rw [show (1/100:ℝ) = (1/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith [h1, h2.ge, h2.le]
    have hPrime_ub : hPrime ≤ (1.70059 : ℝ) := by
      unfold hPrime
      nlinarith [hlog30_ub, hsqrt_lb]
    rw [hepsG0]; linarith [hmin_ge, hPrime_ub]
  · -- Dkl P > 0
    have h2Dpos : 0 < 2 * Dkl P := by linarith
    have hle30 : (30:ℝ) ≤ 1 / (2 * Dkl P) := by
      rw [le_div_iff₀ h2Dpos]; linarith
    have hlog30 : Real.log 30 ≤ Real.log (1 / (2 * Dkl P)) :=
      Real.log_le_log (by norm_num) hle30
    have hmin_ge : (1/2) * Real.log (1 / (2 * Dkl P)) ≤ hMin h := by
      unfold hMin
      apply Finset.le_inf'
      intro a _
      obtain ⟨_, h2, _⟩ := parameter_floor P ε h hcal hD a
      exact h2
    unfold hPrime
    linarith [hepsG_le, hmin_ge, hlog30]
/-- Paper XII, Proposition 5.3 (spectral floor and sign readout).  With
`ε_G = (5/2)√(2D)` and `D = Dkl P ≤ 1/60` (so `ε_G < 0.45644` and
`h_min > 2ε_G`), for every nonzero mask `a`:

* (i) `|widehat{log X}(a) + Φ(a)/N| ≤ ε_G`;
* (ii) `|Φ(a)| ≥ N(h_min - ε_G) > 1.24416 N`;
* (iii) `ε_a = -sgn Φ(a)`. -/
lemma spectral_floor [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    -- (i)
    |logXhat P a.1 + dipTransform P a.1 / (N n : ℝ)| ≤ epsG P
    -- (ii)
    ∧ (N n : ℝ) * (hMin h - epsG P) ≤ |dipTransform P a.1|
    ∧ (1.24416 : ℝ) * (N n : ℝ) < |dipTransform P a.1|
    -- (iii)
    ∧ ε.sign a = - Real.sign (dipTransform P a.1) := by
  -- basic positivity
  have hNpos : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have hZpos : (0 : ℝ) < ∑ r, Real.exp (tilt ε h r) :=
    Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
  -- parameter floor: h a > 0
  have hha : (1.70059 : ℝ) < h a := (parameter_floor P ε h hcal hD a).2.2
  have hha_pos : (0 : ℝ) < h a := by linarith
  -- density and log density
  have hdens : ∀ s, dens P s
      = (N n : ℝ) * Real.exp (tilt ε h s) / (∑ r, Real.exp (tilt ε h r)) := by
    intro s; unfold dens; rw [hcal.1 s, mul_div_assoc]
  have hlogdens : ∀ s, Real.log (dens P s)
      = (Real.log (N n : ℝ) - Real.log (∑ r, Real.exp (tilt ε h r))) + tilt ε h s := by
    intro s
    rw [hdens s]
    have hx : (0 : ℝ) < (N n : ℝ) * Real.exp (tilt ε h s) := mul_pos hNpos (Real.exp_pos _)
    rw [Real.log_div hx.ne' hZpos.ne', Real.log_mul hNpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  -- Walsh orthogonality  ∑_s χ_c(s) = N·[c=0]  (reproved locally; Delta not imported)
  have sumChi : ∀ c : Point n, (∑ s, chi c s) = if c = 0 then (N n : ℝ) else 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc; rw [if_pos rfl]
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
        · intro hcon; exact absurd (Finset.mem_univ j) hcon
      have hcj : c j = 1 := by
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (c j) with hz | hz
        · exact absurd hz hj
        · exact hz
      have hadddot : ∀ s, dotZ2 c (s + ej) = dotZ2 c s + c j := by
        intro s
        have h1 : dotZ2 c (s + ej) = dotZ2 c s + dotZ2 c ej := by
          simp only [dotZ2, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [h1, hdot]
      have hflip : ∀ s, chi c (s + ej) = - chi c s := by
        intro s
        unfold chi
        rw [hadddot s, hcj]
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (dotZ2 c s) with hz | hz <;>
          rw [hz] <;> simp [show ((1 : ZMod 2) + 1) = 0 from by decide]
      have hbij : (∑ s, chi c (s + ej)) = ∑ s, chi c s :=
        Fintype.sum_equiv (Equiv.addRight ej) (fun s => chi c (s + ej)) (chi c) (fun x => rfl)
      have hneg : (∑ s, chi c (s + ej)) = ∑ s, (- chi c s) :=
        Finset.sum_congr rfl (fun s _ => hflip s)
      rw [hneg, Finset.sum_neg_distrib] at hbij
      linarith [hbij]
  -- character orthogonality against the fixed mask a
  have orth : ∀ b : NonzeroMask n,
      (∑ s, chi b.1 s * chi a.1 s) = if b = a then (N n : ℝ) else 0 := by
    intro b
    have hmul : ∀ s, chi b.1 s * chi a.1 s = chi (b.1 + a.1) s :=
      fun s => (chi_add b.1 a.1 s).symm
    simp_rw [hmul]
    rw [sumChi (b.1 + a.1)]
    by_cases hba : b = a
    · subst hba
      have hz : b.1 + b.1 = 0 := by
        funext i; simp only [Pi.add_apply, Pi.zero_apply]
        exact (by decide : ∀ z : ZMod 2, z + z = 0) (b.1 i)
      rw [if_pos hz, if_pos rfl]
    · have hne : b.1 + a.1 ≠ 0 := by
        intro hcontra
        apply hba
        have heq : b.1 = a.1 := by
          funext i
          have hi := congrFun hcontra i
          simp only [Pi.add_apply, Pi.zero_apply] at hi
          exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hi
        exact Subtype.ext heq
      rw [if_neg hne, if_neg hba]
  -- KEY identity: widehat{log X}(a) = h a * ε_a
  have hchar : logXhat P a.1 = h a * ε.sign a := by
    have hsum : (∑ s, Real.log (dens P s) * chi a.1 s) = (N n : ℝ) * (h a * ε.sign a) := by
      have e1 : (∑ s, Real.log (dens P s) * chi a.1 s)
          = ∑ s, (((Real.log (N n : ℝ) - Real.log (∑ r, Real.exp (tilt ε h r))) * chi a.1 s)
              + tilt ε h s * chi a.1 s) := by
        apply Finset.sum_congr rfl; intro s _
        rw [hlogdens s]; ring
      rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum, sumChi a.1, if_neg a.2, mul_zero, zero_add]
      have e2 : (∑ s, tilt ε h s * chi a.1 s)
          = ∑ b : NonzeroMask n, h b * ε.sign b * (∑ s, chi b.1 s * chi a.1 s) := by
        unfold tilt
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        ring
      rw [e2]
      simp_rw [orth]
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl]; ring
      · intro b _ hba; rw [if_neg hba]; ring
      · intro hnot; exact absurd (Finset.mem_univ a) hnot
    simp only [logXhat, xhat, EU]
    rw [hsum, mul_comm (N n : ℝ) (h a * ε.sign a), mul_div_assoc, div_self (N_ne_zero n), mul_one]
  -- dip/bulk/spike partition of the sum of  log X · χ_a
  have hpart : (∑ s, Real.log (dens P s) * chi a.1 s)
      = (∑ s ∈ dipSet P, Real.log (dens P s) * chi a.1 s)
        + (∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s)
        + (∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s) := by
    have hunion : dipSet P ∪ bulkSet P ∪ spikeSet P = Finset.univ := by
      ext s
      simp only [Finset.mem_union, dipSet, bulkSet, spikeSet, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]
      by_cases hle : dens P s ≤ 1/2
      · exact Or.inl (Or.inl hle)
      · have hlt := not_le.mp hle
        by_cases h2 : dens P s ≤ 2
        · exact Or.inl (Or.inr ⟨hlt, h2⟩)
        · exact Or.inr (not_le.mp h2)
    have hDB : Disjoint (dipSet P) (bulkSet P) := by
      rw [Finset.disjoint_left]
      intro s hsD hsB
      simp only [dipSet, bulkSet, Finset.mem_filter] at hsD hsB
      linarith [hsD.2, hsB.2.1]
    have hDBS : Disjoint (dipSet P ∪ bulkSet P) (spikeSet P) := by
      rw [Finset.disjoint_left]
      intro s hs hsS
      simp only [spikeSet, Finset.mem_filter] at hsS
      rw [Finset.mem_union] at hs
      simp only [dipSet, bulkSet, Finset.mem_filter] at hs
      rcases hs with hh | hh
      · linarith [hh.2, hsS.2]
      · linarith [hh.2.2, hsS.2]
    calc (∑ s, Real.log (dens P s) * chi a.1 s)
        = ∑ s ∈ (dipSet P ∪ bulkSet P ∪ spikeSet P), Real.log (dens P s) * chi a.1 s := by
          rw [hunion]
      _ = (∑ s ∈ (dipSet P ∪ bulkSet P), Real.log (dens P s) * chi a.1 s)
            + ∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s := Finset.sum_union hDBS
      _ = (∑ s ∈ dipSet P, Real.log (dens P s) * chi a.1 s)
            + (∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s)
            + ∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s := by
          rw [Finset.sum_union hDB]
  -- dip transform is minus the dip part
  have hdipT : dipTransform P a.1
      = - ∑ s ∈ dipSet P, (Real.log (dens P s) * chi a.1 s) := by
    unfold dipTransform depth
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _; ring
  have hlogX : logXhat P a.1 = (∑ s, Real.log (dens P s) * chi a.1 s) / (N n : ℝ) := by
    simp only [logXhat, xhat, EU]
  have hcombine : logXhat P a.1 + dipTransform P a.1 / (N n : ℝ)
      = ((∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s)
          + ∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s) / (N n : ℝ) := by
    rw [hlogX, hdipT, hpart, ← add_div]
    congr 1
    ring
  -- bookkeeping bounds
  obtain ⟨-, ⟨hspikeLE, hspikeEx⟩, hbulk⟩ := bookkeeping P hD
  have habschi : ∀ s, |chi a.1 s| = 1 := by
    intro s; rcases chi_mem a.1 s with hc | hc <;> rw [hc] <;> norm_num
  have hspikeAbs : (∑ s ∈ spikeSet P, |Real.log (dens P s)|)
      = ∑ s ∈ spikeSet P, spikeLog P s := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [spikeSet, Finset.mem_filter] at hs
    unfold spikeLog
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [hs.2]))]
  have hBu : (∑ s ∈ bulkSet P, |Real.log (dens P s)|)
      ≤ 2 * Real.sqrt (2 * Dkl P) * (N n : ℝ) := by
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hNpos] at hbulk
    linarith [hbulk]
  have hSp : (∑ s ∈ spikeSet P, |Real.log (dens P s)|)
      ≤ (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2 := by
    rw [hspikeAbs]; linarith [hspikeLE, hspikeEx]
  -- (i)
  have hbound_i : |logXhat P a.1 + dipTransform P a.1 / (N n : ℝ)| ≤ epsG P := by
    rw [hcombine, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    have hbabs : |∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s|
        ≤ ∑ s ∈ bulkSet P, |Real.log (dens P s)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro s _; rw [abs_mul, habschi s, mul_one]
    have hsabs : |∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s|
        ≤ ∑ s ∈ spikeSet P, |Real.log (dens P s)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro s _; rw [abs_mul, habschi s, mul_one]
    have htri := abs_add_le (∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s)
        (∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s)
    have hgoal : epsG P * (N n : ℝ)
        = 2 * Real.sqrt (2 * Dkl P) * (N n : ℝ) + (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2 := by
      unfold epsG; ring
    rw [hgoal]
    calc |∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s
            + ∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s|
        ≤ |∑ s ∈ bulkSet P, Real.log (dens P s) * chi a.1 s|
            + |∑ s ∈ spikeSet P, Real.log (dens P s) * chi a.1 s| := htri
      _ ≤ (∑ s ∈ bulkSet P, |Real.log (dens P s)|)
            + (∑ s ∈ spikeSet P, |Real.log (dens P s)|) := add_le_add hbabs hsabs
      _ ≤ 2 * Real.sqrt (2 * Dkl P) * (N n : ℝ)
            + (N n : ℝ) * Real.sqrt (2 * Dkl P) / 2 := add_le_add hBu hSp
  -- |widehat{log X}(a)| = h a
  have habsLog : |logXhat P a.1| = h a := by
    rw [hchar, abs_mul, abs_of_pos hha_pos]
    rcases ε.is_sign a with hs | hs <;> rw [hs] <;> simp
  -- (ii)
  have hii : (N n : ℝ) * (hMin h - epsG P) ≤ |dipTransform P a.1| := by
    have key : |logXhat P a.1|
        ≤ |logXhat P a.1 + dipTransform P a.1 / (N n : ℝ)|
          + |dipTransform P a.1 / (N n : ℝ)| := by
      have hh := abs_add_le (logXhat P a.1 + dipTransform P a.1 / (N n : ℝ))
          (-(dipTransform P a.1 / (N n : ℝ)))
      have he : (logXhat P a.1 + dipTransform P a.1 / (N n : ℝ))
          + -(dipTransform P a.1 / (N n : ℝ)) = logXhat P a.1 := by ring
      rw [he, abs_neg] at hh
      exact hh
    rw [habsLog] at key
    have hvabs : |dipTransform P a.1 / (N n : ℝ)| = |dipTransform P a.1| / (N n : ℝ) := by
      rw [abs_div, abs_of_pos hNpos]
    rw [hvabs] at key
    have hMinle := hMin_le h a
    have hstep : hMin h - epsG P ≤ |dipTransform P a.1| / (N n : ℝ) := by
      linarith [key, hbound_i, hMinle]
    rw [le_div_iff₀ hNpos] at hstep
    linarith [hstep]
  -- (iii)
  have hiii : (1.24416 : ℝ) * (N n : ℝ) < |dipTransform P a.1| := by
    have h1 := hMin_sub_epsG_ge_hPrime P ε h hcal hD
    have h2 := hPrime_gt
    have hlit : (1.24416 : ℝ) < 1.244163 := by norm_num
    have hlt : (1.24416 : ℝ) < hMin h - epsG P := by linarith
    have h4 : (1.24416 : ℝ) * (N n : ℝ) < (hMin h - epsG P) * (N n : ℝ) :=
      mul_lt_mul_of_pos_right hlt hNpos
    have h5 : (hMin h - epsG P) * (N n : ℝ) ≤ |dipTransform P a.1| := by
      rw [mul_comm]; exact hii
    linarith [h4, h5]
  -- (iv)
  have hhaG : epsG P < h a := by
    have h1 := hMin_sub_epsG_ge_hPrime P ε h hcal hD
    have h2 := hPrime_gt
    have hMinle := hMin_le h a
    have hlit : (0 : ℝ) < 1.244163 := by norm_num
    linarith
  have hiv : ε.sign a = - Real.sign (dipTransform P a.1) := by
    have hb := hbound_i
    rw [hchar] at hb
    rcases ε.is_sign a with hs | hs
    · rw [hs, mul_one] at hb
      have hup : h a + dipTransform P a.1 / (N n : ℝ) ≤ epsG P :=
        le_trans (le_abs_self _) hb
      have hdN_neg : dipTransform P a.1 / (N n : ℝ) < 0 := by linarith [hup, hhaG]
      have hd_neg : dipTransform P a.1 < 0 := by
        have hmul := mul_neg_of_neg_of_pos hdN_neg hNpos
        rwa [div_mul_cancel₀ (dipTransform P a.1) (N_ne_zero n)] at hmul
      rw [hs, Real.sign_of_neg hd_neg]; norm_num
    · rw [hs, mul_neg_one] at hb
      have hlow : -epsG P ≤ -(h a) + dipTransform P a.1 / (N n : ℝ) :=
        neg_le_of_abs_le hb
      have hdN_pos : 0 < dipTransform P a.1 / (N n : ℝ) := by linarith [hlow, hhaG]
      have hd_pos : 0 < dipTransform P a.1 := by
        have hmul := mul_pos hdN_pos hNpos
        rwa [div_mul_cancel₀ (dipTransform P a.1) (N_ne_zero n)] at hmul
      rw [hs, Real.sign_of_pos hd_pos]
  exact ⟨hbound_i, hii, hiii, hiv⟩
/-- Paper XII, Proposition 5.3(ii)–(iii): `Φ(a) ≠ 0` for every `a ≠ 0`; in
particular `𝒮 ≠ ∅` automatically. -/
lemma dipTransform_ne_zero [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (a : NonzeroMask n) :
    dipTransform P a.1 ≠ 0 := by
  have hfloor := (spectral_floor P ε h hcal hD a).2.2.1
  have hNpos : (0 : ℝ) < (N n : ℝ) := by
    have : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    simpa [N] using this
  have hpos : (0 : ℝ) < |dipTransform P a.1| := by
    have : (0 : ℝ) < (1.24416 : ℝ) * (N n : ℝ) := by positivity
    linarith
  exact abs_pos.mp hpos
/-! ## Proposition 5.4 (dominance criterion) -/

/-- Paper XII, Proposition 5.4 (dominance criterion).  If some dip `s₁ ∈ 𝒮`
carries at least half the total depth,
`β_{s₁} ≥ ∑_{s ∈ 𝒮 ∖ {s₁}} β_s`, then `ε` is the delta orientation at `s₁`
(`ε_a = -χ_a(s₁)` for every `a ≠ 0`). -/
lemma dominance_criterion [Nonempty (NonzeroMask n)]
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60)
    (s₁ : Point n) (hs₁ : s₁ ∈ dipSet P)
    (hdom : (∑ s ∈ (dipSet P).erase s₁, depth P s) ≤ depth P s₁) :
    ∀ a : NonzeroMask n, ε.sign a = - chi a.1 s₁ := by
  have hNpos : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have depth_nonneg : ∀ s ∈ dipSet P, 0 ≤ depth P s := by
    intro s hs
    simp only [dipSet, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    have hpos : 0 < dens P s := mul_pos hNpos (P.pos s)
    have hlog : Real.log (dens P s) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
    simp only [depth]; linarith
  have chi_abs : ∀ (b t : Point n), |chi b t| = 1 := by
    intro b t; rcases chi_mem b t with hh | hh <;> rw [hh] <;> norm_num
  intro a
  have hsign := (spectral_floor P ε h hcal hD a).2.2.2
  have hne := dipTransform_ne_zero P ε h hcal hD a
  have hsplit : dipTransform P a.1
      = depth P s₁ * chi a.1 s₁ + ∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s :=
    (Finset.add_sum_erase (dipSet P) (fun s => depth P s * chi a.1 s) hs₁).symm
  have hR_abs : |∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s| ≤ depth P s₁ := by
    calc |∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s|
        ≤ ∑ s ∈ (dipSet P).erase s₁, |depth P s * chi a.1 s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ (dipSet P).erase s₁, depth P s := by
          apply Finset.sum_congr rfl
          intro s hs
          have hs' : s ∈ dipSet P := Finset.mem_of_mem_erase hs
          rw [abs_mul, chi_abs a.1 s, mul_one, abs_of_nonneg (depth_nonneg s hs')]
      _ ≤ depth P s₁ := hdom
  set R := ∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s with hRdef
  have hcc : chi a.1 s₁ * chi a.1 s₁ = 1 := by
    rcases chi_mem a.1 s₁ with hh | hh <;> rw [hh] <;> norm_num
  have key : chi a.1 s₁ * dipTransform P a.1 = depth P s₁ + chi a.1 s₁ * R := by
    have : chi a.1 s₁ * dipTransform P a.1
        = depth P s₁ * (chi a.1 s₁ * chi a.1 s₁) + chi a.1 s₁ * R := by
      rw [hsplit]; ring
    rw [this, hcc, mul_one]
  have hcR : |chi a.1 s₁ * R| = |R| := by rw [abs_mul, chi_abs a.1 s₁, one_mul]
  have hbound : -|R| ≤ chi a.1 s₁ * R := by
    have hh := neg_abs_le (chi a.1 s₁ * R); rwa [hcR] at hh
  have hnn : 0 ≤ chi a.1 s₁ * dipTransform P a.1 := by
    rw [key]; linarith [hbound, hR_abs]
  have hne_prod : chi a.1 s₁ * dipTransform P a.1 ≠ 0 := by
    apply mul_ne_zero _ hne
    rcases chi_mem a.1 s₁ with hh | hh <;> rw [hh] <;> norm_num
  have hprod_pos : 0 < chi a.1 s₁ * dipTransform P a.1 :=
    lt_of_le_of_ne hnn (Ne.symm hne_prod)
  have hsign_eq : Real.sign (dipTransform P a.1) = chi a.1 s₁ := by
    rcases chi_mem a.1 s₁ with hc | hc
    · rw [hc] at hprod_pos ⊢
      rw [one_mul] at hprod_pos
      exact Real.sign_of_pos hprod_pos
    · rw [hc] at hprod_pos ⊢
      rw [neg_one_mul] at hprod_pos
      exact Real.sign_of_neg (neg_pos.mp hprod_pos)
  rw [hsign, hsign_eq]
/-! ## Section 6: deep dips, the shallow-depth bound, and the trichotomy -/

/-- Paper XII, Theorem 6.1 (deep dips).  `{s : X(s) ≤ e^{-5}}` (equivalently
`β_s ≥ 5`). -/
noncomputable def deepDipSet (P : ProbLaw n) : Finset (Point n) :=
  Finset.univ.filter (fun s => dens P s ≤ Real.exp (-5))

/-- Paper XII, Theorem 6.1.  `m = |{s : X(s) ≤ e^{-5}}|`, the number of deep dips. -/
noncomputable def deepDipCount (P : ProbLaw n) : ℕ := (deepDipSet P).card

/-- Paper XII, Theorem 6.1 (shallow dips).  Dips that are not deep,
`{s ∈ 𝒮 : X(s) > e^{-5}}` (`β_s < 5`). -/
noncomputable def shallowDipSet (P : ProbLaw n) : Finset (Point n) :=
  (dipSet P).filter (fun s => Real.exp (-5) < dens P s)

/-- Paper XII, Theorem 6.1.  The shallow total depth
`Σ_sh = ∑_{shallow s} β_s`. -/
noncomputable def shallowDepthSum (P : ProbLaw n) : ℝ :=
  ∑ s ∈ shallowDipSet P, depth P s

/-- Paper XII, Theorem 6.1 (shallow-depth bound).
`Σ_sh < 5k ≤ 5N/(60 ψ(1/2)) < 0.543149 N`. -/
lemma shallowDepthSum_lt (P : ProbLaw n) (hD : Dkl P ≤ 1/60) :
    shallowDepthSum P < 0.543149 * (N n : ℝ) := by
  -- subset & cardinalities
  have hsub : shallowDipSet P ⊆ dipSet P := Finset.filter_subset _ _
  -- each shallow dip has depth ≤ 5
  have hdepth : ∀ s ∈ shallowDipSet P, depth P s ≤ 5 := by
    intro s hs
    have hs2 : Real.exp (-5) < dens P s := by
      simp only [shallowDipSet, Finset.mem_filter] at hs
      exact hs.2
    have hlog : Real.log (Real.exp (-5)) ≤ Real.log (dens P s) :=
      Real.log_le_log (Real.exp_pos _) (le_of_lt hs2)
    rw [Real.log_exp] at hlog
    unfold depth
    linarith
  -- sum bound
  have hsum : shallowDepthSum P ≤ 5 * ((shallowDipSet P).card : ℝ) := by
    unfold shallowDepthSum
    calc ∑ s ∈ shallowDipSet P, depth P s
        ≤ ∑ _s ∈ shallowDipSet P, (5:ℝ) := Finset.sum_le_sum hdepth
      _ = ((shallowDipSet P).card : ℝ) * 5 := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * ((shallowDipSet P).card : ℝ) := by ring
  -- card shallow ≤ dipCount
  have hcard : ((shallowDipSet P).card : ℝ) ≤ (dipCount P : ℝ) := by
    unfold dipCount
    exact_mod_cast Finset.card_le_card hsub
  -- bookkeeping (i)
  have hk : (dipCount P : ℝ) ≤ Dkl P * (N n : ℝ) / psi (1/2) := (bookkeeping P hD).1.1
  -- numerics on psi(1/2)
  have hph : psi (1/2 : ℝ) = (1 - Real.log 2)/2 := psi_half
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hphpos : (0:ℝ) < psi (1/2) := by rw [hph]; linarith
  have hNr : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  -- turn hk into a division-free form
  have hk' : (dipCount P : ℝ) * psi (1/2) ≤ Dkl P * (N n : ℝ) :=
    (le_div_iff₀ hphpos).mp hk
  -- shallowDepthSum ≤ 5 * dipCount
  have hSD : shallowDepthSum P ≤ 5 * (dipCount P : ℝ) := by
    calc shallowDepthSum P ≤ 5 * ((shallowDipSet P).card : ℝ) := hsum
      _ ≤ 5 * (dipCount P : ℝ) := by linarith
  -- key: 5 * dipCount * psi(1/2) ≤ (1/12) * N
  have hDN : Dkl P * (N n : ℝ) ≤ (1/60) * (N n : ℝ) := by
    apply mul_le_mul_of_nonneg_right hD (le_of_lt hNr)
  have hstep : 5 * ((dipCount P : ℝ) * psi (1/2)) ≤ (1/12) * (N n : ℝ) := by
    have : 5 * ((dipCount P : ℝ) * psi (1/2)) ≤ 5 * (Dkl P * (N n : ℝ)) := by linarith
    calc 5 * ((dipCount P : ℝ) * psi (1/2)) ≤ 5 * ((1/60) * (N n : ℝ)) := by linarith
      _ = (1/12) * (N n : ℝ) := by ring
  -- final: multiply goal by psi(1/2) > 0
  have hgoal_ph : 5 * (dipCount P : ℝ) * psi (1/2) < 0.543149 * (N n : ℝ) * psi (1/2) := by
    have h1 : 5 * (dipCount P : ℝ) * psi (1/2) ≤ (1/12) * (N n : ℝ) := by
      have : 5 * (dipCount P : ℝ) * psi (1/2) = 5 * ((dipCount P : ℝ) * psi (1/2)) := by ring
      rw [this]; exact hstep
    have h2 : (1/12) * (N n : ℝ) < 0.543149 * (N n : ℝ) * psi (1/2) := by
      rw [hph]
      have hkey : (1/12 : ℝ) < 0.543149 * ((1 - Real.log 2)/2) := by nlinarith [hlog2]
      nlinarith [hkey, hNr]
    linarith
  -- cancel psi(1/2) > 0
  have hfinal : 5 * (dipCount P : ℝ) < 0.543149 * (N n : ℝ) :=
    lt_of_mul_lt_mul_right hgoal_ph (le_of_lt hphpos)
  linarith
/-- Paper XII, Theorem 6.1: `3ψ(e^{-5}) = 3(1 - 6e^{-5}) > 2.878716` (certified
numeric bound). -/
lemma three_psi_exp_neg5_gt : (2.878716 : ℝ) < 3 * (1 - 6 * Real.exp (-5)) := by
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [show (5:ℝ) = (5:ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have hlb : (2.7182818283:ℝ) ^ 5 < Real.exp 5 := by
    rw [h5]
    gcongr
    linarith [Real.exp_one_gt_d9]
  have hpos : (0:ℝ) < Real.exp 5 := Real.exp_pos 5
  have hneg : Real.exp (-5) = 1 / Real.exp 5 := by
    rw [Real.exp_neg, one_div]
  have hbound : Real.exp (-5) < 0.006738 := by
    rw [hneg, div_lt_iff₀ hpos]
    nlinarith [hlb]
  nlinarith [hbound, Real.exp_pos (-5)]
/-! ### Ruling out `m ≤ 2` (the three cases of Theorem 6.1) -/

/-- Paper XII, Theorem 6.1, **Case `m = 0`**.  If every dip is shallow then for
any `a ≠ 0` (present since `N ≥ 4`),
`|Φ(a)| ≤ Σ_sh < 0.543149 N < 1.24416 N ≤ |Φ(a)|` — impossible.  Hence
`m ≠ 0`.  (This subsumes `k = 0`, where `Φ ≡ 0`.) -/
lemma deepDipCount_ne_zero [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 0 := by
  intro hzero
  -- a nonzero mask exists
  have a : NonzeroMask n := Classical.arbitrary _
  -- deepDipSet is empty
  have hempty : deepDipSet P = ∅ := by
    unfold deepDipCount at hzero
    exact Finset.card_eq_zero.mp hzero
  -- every dip is shallow, so shallowDipSet = dipSet
  have hset : shallowDipSet P = dipSet P := by
    unfold shallowDipSet
    apply Finset.filter_true_of_mem
    intro s hs
    by_contra hle
    push_neg at hle
    have hmem : s ∈ deepDipSet P :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, hle⟩
    rw [hempty] at hmem
    exact absurd hmem (Finset.notMem_empty s)
  -- N > 0
  have hNpos : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  -- |Φ(a)| ≤ Σ_sh
  have habs : |dipTransform P a.1| ≤ shallowDepthSum P := by
    rw [shallowDepthSum, hset]
    unfold dipTransform
    calc |∑ s ∈ dipSet P, depth P s * chi a.1 s|
        ≤ ∑ s ∈ dipSet P, |depth P s * chi a.1 s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ dipSet P, depth P s := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [abs_mul]
          have hchi : |chi a.1 s| = 1 := by
            rcases chi_mem a.1 s with hc | hc <;> simp [hc]
          rw [hchi, mul_one]
          have hdle : dens P s ≤ 1 / 2 := (Finset.mem_filter.mp hs).2
          have hdpos : 0 < dens P s := by
            unfold dens
            exact mul_pos hNpos (P.pos s)
          have hdepth : 0 ≤ depth P s := by
            unfold depth
            rw [neg_nonneg]
            exact Real.log_nonpos hdpos.le (by linarith)
          exact abs_of_nonneg hdepth
  -- spectral floor: 1.24416 N < |Φ(a)|
  have hfloor : (1.24416 : ℝ) * (N n : ℝ) < |dipTransform P a.1| :=
    (spectral_floor P ε h hcal hD a).2.2.1
  -- shallow-depth bound
  have hshallow : shallowDepthSum P < 0.543149 * (N n : ℝ) :=
    shallowDepthSum_lt P hD
  linarith
/-- Paper XII, Theorem 6.1, **Case `m = 1`**.  A single deep dip `s₁` must, by
the floor `|Φ(a)| ≤ β_{s₁} + Σ_sh` and Prop 5.3(ii), satisfy
`β_{s₁} ≥ Nh' - Σ_sh > 0.701014 N > Σ_sh`, so `s₁` dominates and Prop 5.4 makes
`ε` a delta orientation — contradicting `¬ IsDelta ε`.  Hence `m ≠ 1`. -/
lemma deepDipCount_ne_one [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 1 := by
  intro hone
  have hcard : (deepDipSet P).card = 1 := hone
  obtain ⟨s₁, hs₁eq⟩ := Finset.card_eq_one.mp hcard
  -- numeric facts
  have hNpos : (0:ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
  have hexp5 : Real.exp (-5:ℝ) < 1/2 := by
    have h6 : (6:ℝ) ≤ Real.exp 5 := by have := Real.add_one_le_exp (5:ℝ); linarith
    have hmul : Real.exp (-5) * Real.exp 5 = 1 := by rw [← Real.exp_add]; norm_num
    have hpos : (0:ℝ) < Real.exp (-5) := Real.exp_pos _
    nlinarith [h6, hmul, hpos]
  -- s₁ is the unique deep dip
  have hs1deep : s₁ ∈ deepDipSet P := by rw [hs₁eq]; exact Finset.mem_singleton_self s₁
  have hs1dens : dens P s₁ ≤ Real.exp (-5) := by
    simpa only [deepDipSet, Finset.mem_filter, Finset.mem_univ, true_and] using hs1deep
  have hs1dip : s₁ ∈ dipSet P := by
    simp only [dipSet, Finset.mem_filter, Finset.mem_univ, true_and]
    linarith
  -- depth nonneg on dips
  have hdepth_nonneg : ∀ s ∈ dipSet P, 0 ≤ depth P s := by
    intro s hs
    have hdens_le : dens P s ≤ 1/2 := by
      simpa only [dipSet, Finset.mem_filter, Finset.mem_univ, true_and] using hs
    have hdens_pos : 0 < dens P s := by
      unfold dens; exact mul_pos hNpos (P.pos s)
    unfold depth
    have hlog : Real.log (dens P s) < 0 := Real.log_neg hdens_pos (by linarith)
    linarith
  have hd1 : 0 ≤ depth P s₁ := hdepth_nonneg s₁ hs1dip
  -- a nonzero mask
  obtain ⟨a⟩ := (inferInstance : Nonempty (NonzeroMask n))
  have habs_chi : ∀ s, |chi a.1 s| = 1 := by
    intro s; rcases chi_mem a.1 s with hc | hc <;> rw [hc] <;> norm_num
  -- the erased dips are all shallow
  have hsub : (dipSet P).erase s₁ ⊆ shallowDipSet P := by
    intro s hs
    rw [Finset.mem_erase] at hs
    obtain ⟨hne, hsdip⟩ := hs
    simp only [shallowDipSet, Finset.mem_filter]
    refine ⟨hsdip, ?_⟩
    have hnotdeep : s ∉ deepDipSet P := by
      rw [hs₁eq, Finset.mem_singleton]; exact hne
    simp only [deepDipSet, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnotdeep
    exact hnotdeep
  have herase_le : (∑ s ∈ (dipSet P).erase s₁, depth P s) ≤ shallowDepthSum P := by
    unfold shallowDepthSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro s hs _
    simp only [shallowDipSet, Finset.mem_filter] at hs
    exact hdepth_nonneg s hs.1
  have hshallow : shallowDepthSum P < 0.543149 * (N n : ℝ) := shallowDepthSum_lt P hD
  -- triangle inequality on the dip transform
  have hsplit : dipTransform P a.1
      = depth P s₁ * chi a.1 s₁ + ∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s := by
    unfold dipTransform
    exact (Finset.add_sum_erase (dipSet P) (fun s => depth P s * chi a.1 s) hs1dip).symm
  have hB : |∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s|
      ≤ ∑ s ∈ (dipSet P).erase s₁, depth P s := by
    calc |∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s|
        ≤ ∑ s ∈ (dipSet P).erase s₁, |depth P s * chi a.1 s| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ s ∈ (dipSet P).erase s₁, depth P s := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mem_erase] at hs
          rw [abs_mul, habs_chi s, mul_one, abs_of_nonneg (hdepth_nonneg s hs.2)]
  have hA : |depth P s₁ * chi a.1 s₁| = depth P s₁ := by
    rw [abs_mul, habs_chi s₁, mul_one, abs_of_nonneg hd1]
  have htri : |dipTransform P a.1| ≤ depth P s₁ + ∑ s ∈ (dipSet P).erase s₁, depth P s := by
    rw [hsplit]
    calc |depth P s₁ * chi a.1 s₁ + ∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s|
        ≤ |depth P s₁ * chi a.1 s₁| + |∑ s ∈ (dipSet P).erase s₁, depth P s * chi a.1 s| :=
          abs_add_le _ _
      _ ≤ depth P s₁ + ∑ s ∈ (dipSet P).erase s₁, depth P s := by
          rw [hA]; gcongr
  -- spectral floor
  have hfloor := (spectral_floor P ε h hcal hD a).2.2.1
  -- dominance
  have hdomineq : (∑ s ∈ (dipSet P).erase s₁, depth P s) ≤ depth P s₁ := by
    linarith [hfloor, htri, herase_le, hshallow, hNpos]
  have hdom := dominance_criterion P ε h hcal hD s₁ hs1dip hdomineq
  -- conclude IsDelta, contradiction
  apply hnd
  rw [isDelta_iff]
  exact ⟨s₁, fun a' => hdom a'⟩
/-- Paper XII, Theorem 6.1, **Case `m = 2`**.  With deep dips `s₁,s₂`
(`β_{s₁} ≥ β_{s₂}`), choosing `a` with `χ_a(s₁+s₂) = -1` (an `N/2`-set not
containing `0`) gives `|Φ(a)| ≤ |β_{s₁}-β_{s₂}| + Σ_sh`, whence
`β_{s₁}-β_{s₂} ≥ Nh'-Σ_sh > 0.701014 N`, so
`β_{s₁} - (β_{s₂}+Σ_sh) > 0.157865 N > 0`: `s₁` again dominates and Prop 5.4
gives `IsDelta ε` — contradiction.  Hence `m ≠ 2`. -/
lemma deepDipCount_ne_two [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    deepDipCount P ≠ 2 := by
  intro hcard
  unfold deepDipCount at hcard
  -- Numeric fact `e^{-5} < 1/2`.
  have hexp_half : Real.exp (-5) < 1/2 := by
    have h1 : Real.exp (-5) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by norm_num)
    have he : (2:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp (-1) < 1/2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ hpos]; linarith
    linarith
  -- Membership characterizations.
  have hmem_dip : ∀ s, s ∈ dipSet P ↔ dens P s ≤ 1/2 := by
    intro s; unfold dipSet; rw [Finset.mem_filter]; simp
  have hmem_deep : ∀ s, s ∈ deepDipSet P ↔ dens P s ≤ Real.exp (-5) := by
    intro s; unfold deepDipSet; rw [Finset.mem_filter]; simp
  have hmem_shallow : ∀ s, s ∈ shallowDipSet P ↔
      (dens P s ≤ 1/2 ∧ Real.exp (-5) < dens P s) := by
    intro s; unfold shallowDipSet; rw [Finset.mem_filter, hmem_dip]
  -- Deep dips are dips; the dip set partitions into deep and shallow.
  have hdeep_sub : deepDipSet P ⊆ dipSet P := by
    intro s hs
    rw [hmem_dip]; rw [hmem_deep] at hs
    exact le_trans hs hexp_half.le
  have hpart : dipSet P = deepDipSet P ∪ shallowDipSet P := by
    ext s
    rw [Finset.mem_union, hmem_dip, hmem_deep, hmem_shallow]
    constructor
    · intro hs
      by_cases hd : dens P s ≤ Real.exp (-5)
      · exact Or.inl hd
      · exact Or.inr ⟨hs, not_le.mp hd⟩
    · rintro (hd | ⟨h1, _⟩)
      · exact le_trans hd hexp_half.le
      · exact h1
  have hdisj : Disjoint (deepDipSet P) (shallowDipSet P) := by
    rw [Finset.disjoint_left]
    intro s hsd hss
    rw [hmem_deep] at hsd; rw [hmem_shallow] at hss
    linarith [hsd, hss.2]
  -- Nonnegativity of depth on dips.
  have hshallow_nonneg : ∀ s ∈ shallowDipSet P, 0 ≤ depth P s := by
    intro s hs
    rw [hmem_shallow] at hs
    have hpos : 0 < dens P s := mul_pos (by exact_mod_cast N_pos n) (P.pos s)
    unfold depth
    have hlog : Real.log (dens P s) ≤ 0 := Real.log_nonpos hpos.le (by linarith [hs.1])
    linarith
  -- Symmetric core: two distinct deep dips `s₁,s₂` with `depth s₂ ≤ depth s₁`.
  suffices H : ∀ s₁ s₂ : Point n, s₁ ≠ s₂ → deepDipSet P = {s₁, s₂} →
      depth P s₂ ≤ depth P s₁ → False by
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard
    rcases le_total (depth P x) (depth P y) with hle | hle
    · exact H y x (Ne.symm hxy) (by rw [hset]; exact Finset.pair_comm x y) hle
    · exact H x y hxy hset hle
  intro s₁ s₂ hne hdeep hdd
  -- Membership of the two deep dips.
  have hs₁deep : s₁ ∈ deepDipSet P := by rw [hdeep]; exact Finset.mem_insert_self _ _
  have hs₁dip : s₁ ∈ dipSet P := hdeep_sub hs₁deep
  -- Build a nonzero mask `a` with `χ_a(s₂) = -χ_a(s₁)`.
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have ha0ne : (Pi.single j (1 : ZMod 2) : Point n) ≠ 0 := by
    intro hc
    have := congrFun hc j
    rw [Pi.single_eq_same] at this
    exact one_ne_zero this
  have hdot : ∀ w : Point n, dotZ2 (Pi.single j (1 : ZMod 2)) w = w j := by
    intro w
    unfold dotZ2
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_mul]
    · intro i _ hij; rw [Pi.single_eq_of_ne hij, zero_mul]
    · intro hcon; exact absurd (Finset.mem_univ j) hcon
  set a : NonzeroMask n := ⟨Pi.single j (1 : ZMod 2), ha0ne⟩ with ha
  have hchi : chi a.1 s₂ = - chi a.1 s₁ := by
    show chi (Pi.single j (1:ZMod 2)) s₂ = - chi (Pi.single j (1:ZMod 2)) s₁
    unfold chi
    rw [hdot s₁, hdot s₂]
    have hv : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hv (s₁ j) with h1 | h1 <;> rcases hv (s₂ j) with h2 | h2
    · exact absurd (h1.trans h2.symm) hj
    · rw [if_neg (by rw [h2]; decide), if_pos h1]
    · rw [if_pos h2, if_neg (by rw [h1]; decide)]; norm_num
    · exact absurd (h1.trans h2.symm) hj
  -- Expand the dip transform at `a`.
  have hexpand : dipTransform P a.1
      = (depth P s₁ - depth P s₂) * chi a.1 s₁
        + ∑ s ∈ shallowDipSet P, depth P s * chi a.1 s := by
    unfold dipTransform
    rw [hpart, Finset.sum_union hdisj, hdeep, Finset.sum_pair hne, hchi]
    ring
  -- Bound the shallow remainder.
  have hR : |∑ s ∈ shallowDipSet P, depth P s * chi a.1 s| ≤ shallowDepthSum P := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    unfold shallowDepthSum
    apply Finset.sum_le_sum
    intro s hs
    rw [abs_mul]
    have hchiabs : |chi a.1 s| = 1 := by
      rcases chi_mem a.1 s with hh | hh <;> rw [hh] <;> norm_num
    rw [hchiabs, mul_one, abs_of_nonneg (hshallow_nonneg s hs)]
  -- Upper bound on `|Φ(a)|`.
  have hupper : |dipTransform P a.1| ≤ (depth P s₁ - depth P s₂) + shallowDepthSum P := by
    rw [hexpand]
    refine le_trans (abs_add_le _ _) ?_
    have hc1 : |(depth P s₁ - depth P s₂) * chi a.1 s₁| = depth P s₁ - depth P s₂ := by
      rw [abs_mul]
      have hchiabs : |chi a.1 s₁| = 1 := by
        rcases chi_mem a.1 s₁ with hh | hh <;> rw [hh] <;> norm_num
      rw [hchiabs, mul_one, abs_of_nonneg (by linarith [hdd])]
    rw [hc1]; linarith [hR]
  -- Spectral floor.
  have hNpos : 0 < (N n : ℝ) := by exact_mod_cast N_pos n
  have hsf := spectral_floor P ε h hcal hD a
  have hmse := hMin_sub_epsG_ge_hPrime P ε h hcal hD
  have hfloor : (N n : ℝ) * hPrime ≤ |dipTransform P a.1| :=
    le_trans (mul_le_mul_of_nonneg_left hmse hNpos.le) hsf.2.1
  have hcomb : (N n : ℝ) * hPrime ≤ (depth P s₁ - depth P s₂) + shallowDepthSum P :=
    le_trans hfloor hupper
  -- Numeric constants.
  have hshallow_lt := shallowDepthSum_lt P hD
  have hhp := hPrime_gt
  have hNhp : (1.244163 : ℝ) * (N n:ℝ) < (N n:ℝ) * hPrime := by nlinarith [hhp, hNpos]
  have hkey : depth P s₂ + shallowDepthSum P ≤ depth P s₁ := by
    linarith [hcomb, hNhp, hshallow_lt, hNpos]
  -- Dominance: `s₁` carries at least half the total dip depth.
  have hdomhyp : (∑ s ∈ (dipSet P).erase s₁, depth P s) ≤ depth P s₁ := by
    have hsd : (∑ s ∈ shallowDipSet P, depth P s) = shallowDepthSum P := rfl
    have hsum_dip : (∑ s ∈ dipSet P, depth P s)
        = depth P s₁ + depth P s₂ + shallowDepthSum P := by
      rw [hpart, Finset.sum_union hdisj, hdeep, Finset.sum_pair hne, hsd]
    rw [Finset.sum_erase_eq_sub hs₁dip, hsum_dip]
    linarith [hkey]
  have hdom := dominance_criterion P ε h hcal hD s₁ hs₁dip hdomhyp
  exact hnd ⟨s₁, Orientation.ext (fun b => hdom b)⟩
/-- Paper XII, Theorem 6.1 (conclusion of the case analysis).  Ruling out
`m ∈ {0,1,2}` gives `m ≥ 3`. -/
lemma deepDipCount_ge_three [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n) (h : NonzeroMask n → ℝ)
    (hcal : CalibratedWith P ε h) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    3 ≤ deepDipCount P := by
  have h0 := deepDipCount_ne_zero hn P ε h hcal hD hnd
  have h1 := deepDipCount_ne_one hn P ε h hcal hD hnd
  have h2 := deepDipCount_ne_two hn P ε h hcal hD hnd
  omega

/-- Paper XII, Theorem 6.1 (deep-dip trichotomy).  Let `ε` be an orientation
that is **not** a delta orientation, and suppose its calibrated law has
`D = Dkl P ≤ 1/60`.  Then at least three points of the cube satisfy
`X(s) ≤ e^{-5}`, and consequently

  `N·D ≥ 3 ψ(e^{-5}) = 3(1 - 6e^{-5}) > 2.878716`.

(The hypothesis `2 ≤ n` encodes the standing `N ≥ 4` assumption of Section 5,
used to guarantee nonzero masks exist.) -/
theorem deep_dip_trichotomy [Nonempty (NonzeroMask n)] (hn : 2 ≤ n)
    (P : ProbLaw n) (ε : Orientation n)
    (hcal : Calibrated P ε) (hD : Dkl P ≤ 1/60) (hnd : ¬ IsDelta ε) :
    3 ≤ deepDipCount P
    ∧ 3 * psi (Real.exp (-5)) ≤ (N n : ℝ) * Dkl P
    ∧ (2.878716 : ℝ) < (N n : ℝ) * Dkl P := by
  obtain ⟨h, hcalw⟩ := hcal
  have hge3 : 3 ≤ deepDipCount P := deepDipCount_ge_three hn P ε h hcalw hD hnd
  -- basic facts about e^{-5}
  have hpe0 : (0 : ℝ) ≤ Real.exp (-5) := (Real.exp_pos _).le
  have hpe1 : Real.exp (-5) ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  have hpsi_nn : 0 ≤ psi (Real.exp (-5)) := psi_nonneg hpe0
  -- density positivity
  have hdpos : ∀ s : Point n, 0 < dens P s := by
    intro s
    have hN : (0 : ℝ) < (N n : ℝ) := by exact_mod_cast N_pos n
    exact mul_pos hN (P.pos s)
  -- step 1: on each deep dip, ψ(e^{-5}) ≤ ψ(dens)
  have h1 : ∑ _s ∈ deepDipSet P, psi (Real.exp (-5))
      ≤ ∑ s ∈ deepDipSet P, psi (dens P s) := by
    apply Finset.sum_le_sum
    intro s hs
    have hmem : dens P s ≤ Real.exp (-5) := (Finset.mem_filter.mp hs).2
    have hdnn : 0 ≤ dens P s := (hdpos s).le
    have hd1 : dens P s ≤ 1 := le_trans hmem hpe1
    exact psi_strictAntiOn.antitoneOn
      (Set.mem_Icc.mpr ⟨hdnn, hd1⟩) (Set.mem_Icc.mpr ⟨hpe0, hpe1⟩) hmem
  -- step 2: restrict the full sum to the deep dip set
  have h2 : ∑ s ∈ deepDipSet P, psi (dens P s) ≤ ∑ s, psi (dens P s) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun s _ _ => psi_nonneg (hdpos s).le)
  -- constant sum evaluation
  have hconst : ∑ _s ∈ deepDipSet P, psi (Real.exp (-5))
      = ((deepDipSet P).card : ℝ) * psi (Real.exp (-5)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- card lower bound in ℝ
  have hcard : (3 : ℝ) ≤ ((deepDipSet P).card : ℝ) := by
    have : (3 : ℕ) ≤ (deepDipSet P).card := hge3
    exact_mod_cast this
  have hkey : 3 * psi (Real.exp (-5)) ≤ ∑ s, psi (dens P s) := by
    have hlow : 3 * psi (Real.exp (-5))
        ≤ ((deepDipSet P).card : ℝ) * psi (Real.exp (-5)) :=
      mul_le_mul_of_nonneg_right hcard hpsi_nn
    calc 3 * psi (Real.exp (-5))
        ≤ ((deepDipSet P).card : ℝ) * psi (Real.exp (-5)) := hlow
      _ = ∑ _s ∈ deepDipSet P, psi (Real.exp (-5)) := hconst.symm
      _ ≤ ∑ s ∈ deepDipSet P, psi (dens P s) := h1
      _ ≤ ∑ s, psi (dens P s) := h2
  have hND : 3 * psi (Real.exp (-5)) ≤ (N n : ℝ) * Dkl P := by
    rw [N_mul_Dkl]; exact hkey
  refine ⟨hge3, hND, ?_⟩
  have hpe := psi_exp_neg5
  have hgt := three_psi_exp_neg5_gt
  rw [hpe] at hND
  linarith
end WalshDelta
