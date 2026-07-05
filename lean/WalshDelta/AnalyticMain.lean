import Mathlib
import WalshDelta.Basic
import WalshDelta.Trichotomy
import WalshDelta.Symmetry
import WalshDelta.Delta
import WalshDelta.Calibration

/-!
# Walsh–delta: the analytic main theorem for `n ≥ 6` (Paper XII, Section 7)

Formalization of Section 7 of

  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube"  (Paper XII).

This module assembles the analytic (`n ≥ 6`) half of the main theorem:

* **Theorem 7.1** — for `n ≥ 6` and any non-delta orientation `ε`,
  `mhat ε > D_δ`, proved by the paper's two-case split
  (`D > 1/60` uses Lemma 4.2 and `N - 1 ≥ 63`; `D ≤ 1/60` uses Theorem 6.1
  and the arithmetic fact `2.878716·(N-1) > N`).
* **Corollary 1.3** — the quantitative floor
  `N·mhat ε ≥ min(N/60, 2.878716)` for non-delta `ε`, together with
  `N·D_δ < N/(N-1) ≤ 64/63`.
* **Theorem 1.2 (the `n ≥ 6` half)** — `mhat ε ≥ D_δ` with equality iff `ε`
  is a delta orientation.

## Interfaces to Sections 3, 4, 6

Section 7 consumes the following results, proved in the paper's earlier
sections and now `import`ed (fully proved, no `sorry`) from the existence /
delta-law / deep-dip modules; each is labeled with its paper number:

  * `calibrated_exists_unique`  — Theorem 3.1 (existence and uniqueness of the
    calibrated law `P_ε`), whence `Pcal`, `mhat`;
  * `translation_covariance`, `tau_deltaOrientation`, `mhat_deltaOrientation`
    — Lemma 3.2 (all `N` delta orientations share the value `D_δ`);
  * `Ddelta_lt` — Lemma 4.2 (`0 < D_δ < 1/(N-1)`);
  * `deep_dip_trichotomy` — Theorem 6.1 (deep-dip trichotomy).
-/

namespace WalshDelta

open scoped BigOperators

variable {n : ℕ}

/-! ## The calibrated law `P_ε` and the entropy functional `mhat` (Theorem 3.1) -/

-- (removed redundant `calibrated_exists_unique`; canonical in an imported module)
/-- Paper XII, Theorem 3.1.  The unique calibrated law `P_ε` of the
orientation `ε`. -/
noncomputable def Pcal (ε : Orientation n) : ProbLaw n :=
  (calibrated_exists_unique ε).exists.choose  -- TODO(api): verify `ExistsUnique.exists`

/-- Paper XII, Theorem 3.1: `P_ε := Pcal ε` is indeed calibrated for `ε`. -/
lemma Pcal_calibrated (ε : Orientation n) : Calibrated (Pcal ε) ε :=
  (calibrated_exists_unique ε).exists.choose_spec

-- (removed redundant `mhat`; canonical in an imported module)
/-! ## Delta orientations: the predicate and the shared value `D_δ` -/

-- (removed redundant `IsDelta`; canonical in an imported module)
/-- Helper: the product of two `±1`-valued reals is `±1`-valued. -/
lemma mul_pm_one {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inl (by norm_num)

/-- Paper XII, Lemma 3.2.  The translated orientation
`(τ_t ε)_a = ε_a · χ_a(t)`. -/
def tau (t : Point n) (ε : Orientation n) : Orientation n where
  sign := fun a => ε.sign a * chi a.1 t
  is_sign := fun a => mul_pm_one (ε.is_sign a) (chi_mem a.1 t)

/-- Paper XII, Lemma 3.2 (translation covariance).  For `t ∈ G`,
`P_{τ_t ε}(s) = P_ε(s + t)` and `m̂(τ_t ε) = m̂(ε)`. -/
theorem translation_covariance (t : Point n) (ε : Orientation n) :
    (∀ s, (Pcal (tau t ε)).P s = (Pcal ε).P (s + t)) ∧
      mhat (tau t ε) = mhat ε := by
  have hcal : ∀ ε' : Orientation n, Pcal ε' = calLaw ε' :=
    fun ε' => calLaw_unique ε' (Pcal_calibrated ε')
  have htau : tau t ε = tauOrient t ε := rfl
  refine ⟨?_, ?_⟩
  · intro s
    rw [hcal, hcal, htau]
    exact calLaw_tauOrient t ε s
  · rw [htau]
    exact mhat_tauOrient t ε
/-- Paper XII, Lemma 3.2 (delta orbit).
`τ_t(ε⋆ at s⋆) = ε⋆ at s⋆ + t`: the `N` delta orientations form a single
translation orbit. -/
theorem tau_deltaOrientation (t sstar : Point n) :
    tau t (deltaOrientation sstar) = deltaOrientation (sstar + t) := by
  apply Orientation.ext
  intro a
  show (- chi a.1 sstar) * chi a.1 t = - chi a.1 (sstar + t)
  rw [chi_right_add]
  ring
/-! ## Lemma 4.2 (elementary delta bound) -/

-- (removed redundant `Ddelta_lt`; canonical in an imported module)
/-! ## Theorem 6.1 (deep-dip trichotomy) -/

-- (removed redundant `deep_dip_trichotomy`; canonical in an imported module)
/-! ## Arithmetic facts used in the case split -/

/-- Paper XII, Section 6/7: `ψ(e^{-5}) = 1 - 6 e^{-5}`. -/
lemma psi_exp_neg_five : psi (Real.exp (-5)) = 1 - 6 * Real.exp (-5) := by
  unfold psi
  rw [Real.log_exp]
  ring

/-- Paper XII, Theorem 6.1: `3 ψ(e^{-5}) = 3(1 - 6 e^{-5}) = 2.8787169… >
2.878716`. -/
lemma three_psi_gt : (2.878716 : ℝ) < 3 * (1 - 6 * Real.exp (-5)) := by
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
/-- Paper XII, Section 7 (arithmetic fact).  `2.878716·(N-1) > N` for every
`N ≥ 2` (equivalently `N > 2.878716/1.878716 = 1.532…`). -/
lemma calib_N_bound (hN2 : (2 : ℝ) ≤ (N n : ℝ)) :
    (N n : ℝ) < 2.878716 * ((N n : ℝ) - 1) := by
  nlinarith [hN2]  -- linear in N: `1.878716·N > 2.878716`, true for N ≥ 2

/-! ## Theorem 7.1 (the main theorem for `n ≥ 6`) -/

/-- Paper XII, Theorem 7.1.  Let `n ≥ 6` and let `ε` be any orientation that is
not a delta orientation.  Then `m̂(ε) > D_δ`. -/
theorem main_analytic (hn : 6 ≤ n) (ε : Orientation n) (hnd : ¬ IsDelta ε) :
    Ddelta n < mhat ε := by
  have hnpos : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  haveI hne : Nonempty (NonzeroMask n) := by
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    refine ⟨⟨Pi.single i (1 : ZMod 2), ?_⟩⟩
    intro h
    have hh := congrFun h i
    simp only [Pi.single_eq_same, Pi.zero_apply] at hh
    exact one_ne_zero hh
  -- N n ≥ 64
  have hN64 : (64 : ℝ) ≤ (N n : ℝ) := by
    have hle : (2:ℕ)^6 ≤ N n := by
      rw [show N n = 2^n from rfl]; exact Nat.pow_le_pow_right (by norm_num) hn
    calc (64:ℝ) = ((2^6 : ℕ) : ℝ) := by norm_num
      _ ≤ (N n : ℝ) := by exact_mod_cast hle
  have hNm1 : (63 : ℝ) ≤ (N n : ℝ) - 1 := by linarith
  have hNpos : (0:ℝ) < (N n : ℝ) := by linarith
  have hNm1pos : (0:ℝ) < (N n : ℝ) - 1 := by linarith
  have hmhat : mhat ε = Dkl (calLaw ε) := rfl
  rw [hmhat]
  have hdd : Ddelta n < 1 / ((N n : ℝ) - 1) := Ddelta_lt n hn2
  by_cases hcase : Dkl (calLaw ε) ≤ 1/60
  · -- deep-dip trichotomy case
    have htri := deep_dip_trichotomy hn2 (calLaw ε) ε (calLaw_calibrated ε) hcase hnd
    have hbound : (2.878716 : ℝ) < (N n : ℝ) * Dkl (calLaw ε) := htri.2.2
    have hcalib : (N n : ℝ) < 2.878716 * ((N n : ℝ) - 1) := calib_N_bound (by linarith)
    have hB : (1:ℝ) / ((N n : ℝ) - 1) < 2.878716 / (N n : ℝ) := by
      rw [lt_div_iff₀ hNpos, div_mul_eq_mul_div, one_mul, div_lt_iff₀ hNm1pos]
      linarith [hcalib]
    have hC : (2.878716 : ℝ) / (N n : ℝ) < Dkl (calLaw ε) :=
      (div_lt_iff₀ hNpos).mpr (by rw [mul_comm]; exact hbound)
    linarith [hdd, hB, hC]
  · -- D > 1/60 case
    have hcase' : (1:ℝ)/60 < Dkl (calLaw ε) := not_le.mp hcase
    have h63 : (1:ℝ) / ((N n : ℝ) - 1) ≤ 1 / 63 :=
      one_div_le_one_div_of_le (by norm_num) hNm1
    linarith [hdd, h63, hcase']
theorem corollary_1_3 (hn : 6 ≤ n) (ε : Orientation n) (hnd : ¬ IsDelta ε) :
    min ((N n : ℝ) / 60) 2.878716 ≤ (N n : ℝ) * mhat ε
      ∧ (N n : ℝ) * Ddelta n < (N n : ℝ) / ((N n : ℝ) - 1)
      ∧ (N n : ℝ) / ((N n : ℝ) - 1) ≤ 64 / 63 := by
  haveI : Nonempty (NonzeroMask n) := by
    have hpos : 0 < n := by omega
    refine ⟨⟨fun _ => 1, ?_⟩⟩
    intro hcontra
    have h2 := congrFun hcontra ⟨0, hpos⟩
    simp only [Pi.zero_apply] at h2
    exact one_ne_zero h2
  have hNpos : (0 : ℝ) < (N n : ℝ) := by
    have : 0 < N n := by unfold N; positivity
    exact_mod_cast this
  have hN64 : (64 : ℝ) ≤ (N n : ℝ) := by
    have : (64 : ℕ) ≤ N n := by
      unfold N
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact_mod_cast this
  have hNm1 : (0 : ℝ) < (N n : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    rcases le_or_gt (Dkl (calLaw ε)) (1 / 60) with hD | hD
    · have htri := deep_dip_trichotomy (by omega) (calLaw ε) ε (calLaw_calibrated ε) hD hnd
      have hstar : (2.878716 : ℝ) < (N n : ℝ) * mhat ε := by
        unfold mhat; exact htri.2.2
      calc min ((N n : ℝ) / 60) 2.878716 ≤ 2.878716 := min_le_right _ _
        _ ≤ (N n : ℝ) * mhat ε := le_of_lt hstar
    · have hstar : (N n : ℝ) / 60 < (N n : ℝ) * mhat ε := by
        unfold mhat
        have heq : (N n : ℝ) / 60 = (N n : ℝ) * (1 / 60) := by ring
        rw [heq]
        exact mul_lt_mul_of_pos_left hD hNpos
      calc min ((N n : ℝ) / 60) 2.878716 ≤ (N n : ℝ) / 60 := min_le_left _ _
        _ ≤ (N n : ℝ) * mhat ε := le_of_lt hstar
  · -- Part 2
    have hdl := Ddelta_lt n (by omega)
    calc (N n : ℝ) * Ddelta n < (N n : ℝ) * (1 / ((N n : ℝ) - 1)) :=
          mul_lt_mul_of_pos_left hdl hNpos
      _ = (N n : ℝ) / ((N n : ℝ) - 1) := by rw [mul_one_div]
  · -- Part 3
    rw [div_le_div_iff₀ hNm1 (by norm_num)]
    linarith
theorem main_equality_analytic (hn : 6 ≤ n) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  constructor
  · -- Ddelta n ≤ mhat ε
    by_cases h : IsDelta ε
    · obtain ⟨sstar, rfl⟩ := h
      rw [mhat_deltaOrientation_const sstar]
    · exact le_of_lt (main_analytic hn ε h)
  · constructor
    · intro heq
      by_contra hnd
      exact absurd heq (ne_of_gt (main_analytic hn ε hnd))
    · intro h
      obtain ⟨sstar, rfl⟩ := h
      rw [mhat_deltaOrientation_const sstar]
end WalshDelta
