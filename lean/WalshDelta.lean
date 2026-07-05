/-
  WalshDelta — Lean 4 + Mathlib formalization of paper XII,
  "The delta orientation is the unique entropy minimizer for self-calibrated
   ±1 Walsh tilts on the Boolean cube".

  The whole library links: all eight modules share the canonical
  `mhat`/`Ddelta` (Calibration) and `IsDelta` (Basic).  Every theorem STATEMENT
  type-checks against Mathlib; the remaining work is the `sorry` proof leaves
  (see STATUS.md).  The headline result is `WalshDelta.theorem_1_2`.
-/
import WalshDelta.Basic
import WalshDelta.Calibration
import WalshDelta.Symmetry
import WalshDelta.Delta
import WalshDelta.Trichotomy
import WalshDelta.AnalyticMain
import WalshDelta.Certified
import WalshDelta.Main
