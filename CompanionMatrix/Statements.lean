/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import CompanionMatrix.Order2Phi

/-!
# Stated but NOT proved

Everything in this file is a *statement* (a `Prop`), not a theorem. Nothing here is proved,
nothing here is used by the proved files, and the project contains no placeholder proofs.
A statement is moved out of this file only when it has a full proof.

* `Theorem1LeftVector` : the left-singular-vector claim inside Theorem 1 of the revised draft,
  `u_1(N) → x_∞ = normalize(ρ, 1)` (as lines). The proved `Φ∞` limit
  (`CompanionMatrix.theorem1_phi`) does not depend on it.

Not stated at all, on purpose:
* the *negative* half of the paper's Proposition 2 ("a tie at the top means `v_1(N)` does not
  converge"). As written it is not a theorem (see the review notes), so it is not formalized.
-/

namespace CompanionMatrix

open RealInnerProductSpace Filter Topology Matrix

/-- `Φ_Nᵀ` acting on `EuclideanSpace ℝ (Fin 2)`; its top right singular vectors are the top
left singular vectors of `Φ_N`. -/
noncomputable def transportTOp (a b : ℕ → ℝ) (N : ℕ) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun w => WithLp.toLp 2 ((transport a b N)ᵀ *ᵥ WithLp.ofLp w)

/-- **Stated, not proved.** Theorem 1, left vector, finite `ρ`:
`|⟪(ρ, 1), u_1(N)⟫| / ‖(ρ, 1)‖ → 1` for any top left singular vectors `u_1(N)`. -/
def Theorem1LeftVector : Prop :=
  ∀ (a b f d : ℕ → ℝ), IsSolution a b f → IsSolution a b d →
    f 1 * d 0 - d 1 * f 0 ≠ 0 →
    Tendsto (fun n => f n / d n) atTop (𝓝 0) → (∀ᶠ n in atTop, d n ≠ 0) →
    ∀ ρ : ℝ, Tendsto (fun N => d (N + 1) / d N) atTop (𝓝 ρ) →
    ∀ u : ℕ → EuclideanSpace ℝ (Fin 2), (∀ N, IsTopSingular (transportTOp a b N) (u N)) →
      Tendsto (fun N => |⟪(!₂[ρ, 1] : EuclideanSpace ℝ (Fin 2)), u N⟫| /
        ‖(!₂[ρ, 1] : EuclideanSpace ℝ (Fin 2))‖) atTop (𝓝 1)

end CompanionMatrix
