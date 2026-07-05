# WalshDelta — Lean 4 formalization of paper XII

A Lean 4 + Mathlib formalization of

> **The delta orientation is the unique entropy minimizer for self-calibrated
> ±1 Walsh tilts on the Boolean cube** (paper XII; `../papers/paper-XII-walsh-delta.md`,
> Zenodo `10.5281/zenodo.21181813`).

> ✅ **The whole library compiles and links** against Mathlib (Lean `v4.32.0-rc1`):
> `lake build` succeeds with **0 errors**, and the headline `theorem_1_2` is a
> **complete, machine-checked assembly** (`#print axioms` → `[propext, sorryAx,
> Classical.choice, Quot.sound]`). ⚠️ **Not a finished proof:** 93 `sorry` leaves
> remain (the mathematical content); `sorryAx` shows until they are discharged.
> See **`STATUS.md`**.

## Layout

```
lakefile.toml          -- Mathlib dependency (rev is a <pin-me> placeholder)
lean-toolchain         -- pinned Lean version
WalshDelta.lean        -- root: imports all modules (the library links)
WalshDelta/
  Basic.lean           -- §1.1 objects; §2 Pinsker (2.1) + entropy integrand ψ (2.2)
  Calibration.lean     -- §3 Theorem 3.1 (existence & uniqueness); mhat
  Symmetry.lean        -- §3 Lemmas 3.2, 3.3 (translation + GL(n,2) covariance)
  Delta.lean           -- §1.2 + §4 Prop 4.1 (delta law); Lemma 4.2
  Trichotomy.lean      -- §5 apparatus + §6 Theorem 6.1 (deep-dip trichotomy)
  AnalyticMain.lean    -- §7 Theorem 7.1; main theorem for n ≥ 6; Cor 1.3
  Certified.lean       -- §8 Lemmas 8.1/8.2 + Theorem 8.3 (2 ≤ n ≤ 5, 176-orbit)
  Main.lean            -- Theorem 1.2 (assembled) + Corollary 1.3
BLUEPRINT.md           -- module graph, name↔paper map, Mathlib deps, plan
STATUS.md              -- HONEST status: sorry inventory, review results, blockers
```

The headline target is `WalshDelta.Main.theorem_1_2`.

## Build (once Mathlib is pinned)

```
# pin the mathlib `rev` in lakefile.toml to match lean-toolchain, then:
lake exe cache get
lake build
```

`lake build` links the whole library (0 errors, 93 `sorry` warnings). The
headline result is `WalshDelta.theorem_1_2`.

## Contributing

This is a good blueprint-driven target for the Lean/Mathlib community
(PFR/FLT-style). The two hard frontiers are the analytic quantitative
inequalities (n ≥ 6) and the certified finite computation (2 ≤ n ≤ 5), the
latter to be done in exact rational/interval arithmetic via the
Newton–Kantorovich certificates over the 176-orbit Γ₅ transversal — **not**
`native_decide`. See `STATUS.md` §"path to compiled / bug-free".
