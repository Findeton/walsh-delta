import WalshDelta.Basic
import WalshDelta.Calibration
import WalshDelta.Symmetry
import WalshDelta.Delta
import WalshDelta.Trichotomy
import WalshDelta.AnalyticMain
import WalshDelta.Certified

/-!
# Paper XII — the main theorem, assembled

`theorem_1_2` is the headline result.  Its proof is **complete** here: it case-
splits on `n` and defers to the two halves — `AnalyticMain.main_equality_analytic`
(`n ≥ 6`, analytic) and `Certified.theorem_8_3` (`2 ≤ n ≤ 5`, certified
computation).  Those two halves are the remaining `sorry`s; the assembly itself
is proved.  All modules now share the canonical `mhat` / `Ddelta` / `IsDelta`
(Calibration / Calibration / Basic), so the whole library links.
-/

namespace WalshDelta

variable {n : ℕ}

/-- Paper XII, **Theorem 1.2** (main theorem).  For every `n ≥ 2` and every
orientation `ε`, the entropy gap `m̂(ε) = D(P_ε ‖ U)` is at least the delta value
`D_δ`, with equality **iff** `ε` is one of the `N` delta orientations. -/
theorem theorem_1_2 (hn : 2 ≤ n) (ε : Orientation n) :
    Ddelta n ≤ mhat ε ∧ (mhat ε = Ddelta n ↔ IsDelta ε) := by
  by_cases h6 : 6 ≤ n
  · exact main_equality_analytic h6 ε
  · exact theorem_8_3 ⟨hn, by omega⟩ ε

/-- Paper XII, **Corollary 1.3** (quantitative floor, `n ≥ 6`): this is exactly
`AnalyticMain.corollary_1_3`. -/
theorem corollary_1_3_top (hn : 6 ≤ n) (ε : Orientation n) (hnd : ¬ IsDelta ε) :
    min ((N n : ℝ) / 60) 2.878716 ≤ (N n : ℝ) * mhat ε :=
  (corollary_1_3 hn ε hnd).1

end WalshDelta
