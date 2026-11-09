/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import CompanionMatrix.LemmaB
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Theorem 2: strict dominance forces the top right singular vector to converge

This is the positive half of Proposition 2 of the paper (Theorem 2 of the revised draft).

* `CompanionMatrix.tendsto_of_rankOne_approx` : the abstract form. If
  `A_N w = ⟪c, w⟫ m_N + R_N w` with `‖R_N w‖ ≤ ε_N ‖m_N‖` on unit vectors and `ε_N → 0`, then
  every choice of top right singular vectors `v_N` satisfies `|⟪c, v_N⟫| / ‖c‖ → 1`, i.e. the
  line of `v_N` converges to the line of `c`.
* `CompanionMatrix.theorem2` : the solution-basis form. Let `s` be a basis of seeds, `Φ_N` the
  transport, and suppose the mode `m_{i₀}(N) = Φ_N (s i₀)` strictly dominates:
  `‖m_j(N)‖ / ‖m_{i₀}(N)‖ → 0` for every `j ≠ i₀`. Let `c` represent the coordinate functional
  `s.coord i₀` ("coefficient of the dominant mode"). Then `|⟪c, v_N⟫| / ‖c‖ → 1`.
  Nothing is assumed about the relative sizes of the non-dominant modes, so ties among them
  play no role.
* `CompanionMatrix.inner_coordVec_of_ne` : `c` is orthogonal to every non-dominant seed, so its
  line is the normal to their span.

"Converges" is convergence of the line (`|cos ∠(v_N, c)| → 1`): singular vectors are only
defined up to sign, so no sign choice is made.
-/

namespace CompanionMatrix

open RealInnerProductSpace Filter Topology

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

omit [InnerProductSpace ℝ V] in
/-- Scaling `A` by a positive constant does not change its top singular vectors. -/
theorem IsTopSingular.smul {A : V → W} {v : V} (hv : IsTopSingular A v) {t : ℝ} (ht : 0 ≤ t) :
    IsTopSingular (fun w => t • A w) v := by
  refine ⟨hv.1, fun w hw => ?_⟩
  simp only [norm_smul, Real.norm_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left (hv.2 w hw) ht

/-- **Abstract dominance theorem.** -/
theorem tendsto_of_rankOne_approx (A R : ℕ → V → W) (m : ℕ → W) (c : V) (ε : ℕ → ℝ)
    (hc : c ≠ 0) (hA : ∀ N w, A N w = ⟪c, w⟫ • m N + R N w)
    (hR : ∀ᶠ N in atTop, m N ≠ 0 ∧ ∀ w, ‖w‖ = 1 → ‖R N w‖ ≤ ε N * ‖m N‖)
    (hε : Tendsto ε atTop (𝓝 0))
    (v : ℕ → V) (hv : ∀ N, IsTopSingular (A N) (v N)) :
    Tendsto (fun N => |⟪c, v N⟫| / ‖c‖) atTop (𝓝 1) := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hlow : Tendsto (fun N => 1 - 2 * ε N / ‖c‖) atTop (𝓝 1) := by
    have := ((hε.const_mul 2).div_const ‖c‖).const_sub 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hR] with N ⟨hmN, hRN⟩
    have hmn : 0 < ‖m N‖ := norm_pos_iff.mpr hmN
    -- rescale by `‖m N‖⁻¹` and apply Lemma B
    have hv' := (hv N).smul (inv_nonneg.mpr hmn.le)
    refine lemmaB_cos (fun w => ‖m N‖⁻¹ • A N w) (fun w => ‖m N‖⁻¹ • R N w)
      (‖m N‖⁻¹ • m N) c (ε N) ?_ hc ?_ ?_ (v N) hv'
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hmn.ne']
    · intro w
      simp only [hA, smul_add, smul_comm (‖m N‖⁻¹) (⟪c, w⟫)]
    · intro w hw
      rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hmn, mul_comm]
      exact hRN w hw
  · filter_upwards with N
    rw [div_le_one hcn]
    calc |⟪c, v N⟫| ≤ ‖c‖ * ‖v N‖ := abs_real_inner_le_norm _ _
      _ = ‖c‖ := by rw [(hv N).1, mul_one]


/-- A vector `c` representing the coordinate functional `s.coord i₀` is orthogonal to every
other seed `s j`, `j ≠ i₀`. -/
theorem inner_coordVec_of_ne {ι : Type*} [DecidableEq ι] (s : Module.Basis ι ℝ V) (i₀ : ι)
    (c : V) (hc : ∀ w, ⟪c, w⟫ = s.coord i₀ w) {j : ι} (hj : j ≠ i₀) : ⟪c, s j⟫ = 0 := by
  rw [hc, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simpa using hj

/-- A vector `c` representing `s.coord i₀` is nonzero. -/
theorem coordVec_ne_zero {ι : Type*} (s : Module.Basis ι ℝ V) (i₀ : ι)
    (c : V) (hc : ∀ w, ⟪c, w⟫ = s.coord i₀ w) : c ≠ 0 := by
  rintro rfl
  have := hc (s i₀)
  simp [Module.Basis.coord_apply] at this

/-- **Theorem 2 (strict dominance).** -/
theorem theorem2 [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Module.Basis ι ℝ V) (i₀ : ι)
    (Φ : ℕ → V →ₗ[ℝ] W)
    (hm : ∀ᶠ N in atTop, Φ N (s i₀) ≠ 0)
    (hdom : ∀ j, j ≠ i₀ → Tendsto (fun N => ‖Φ N (s j)‖ / ‖Φ N (s i₀)‖) atTop (𝓝 0))
    (c : V) (hc : ∀ w, ⟪c, w⟫ = s.coord i₀ w)
    (v : ℕ → V) (hv : ∀ N, IsTopSingular (Φ N) (v N)) :
    Tendsto (fun N => |⟪c, v N⟫| / ‖c‖) atTop (𝓝 1) := by
  -- operator-norm bounds for the coordinate functionals
  let K : ι → ℝ := fun j => ‖LinearMap.toContinuousLinearMap (s.coord j)‖
  have hK : ∀ j w, ‖w‖ = 1 → |s.coord j w| ≤ K j := by
    intro j w hw
    have := (LinearMap.toContinuousLinearMap (s.coord j)).le_opNorm w
    rw [LinearMap.coe_toContinuousLinearMap', hw, mul_one, Real.norm_eq_abs] at this
    exact this
  let ε : ℕ → ℝ := fun N =>
    ∑ j ∈ Finset.univ.erase i₀, K j * (‖Φ N (s j)‖ / ‖Φ N (s i₀)‖)
  have hε : Tendsto ε atTop (𝓝 0) := by
    have : Tendsto ε atTop (𝓝 (∑ j ∈ Finset.univ.erase i₀, K j * 0)) :=
      tendsto_finsetSum _ fun j hj =>
        (hdom j (Finset.ne_of_mem_erase hj)).const_mul (K j)
    simpa using this
  -- the decomposition `Φ_N w = ⟪c, w⟫ m_{i₀}(N) + R_N w`
  let R : ℕ → V → W := fun N w =>
    ∑ j ∈ Finset.univ.erase i₀, s.coord j w • Φ N (s j)
  have hexp : ∀ N w, Φ N w = ∑ j, s.coord j w • Φ N (s j) := by
    intro N w
    conv_lhs => rw [← s.sum_repr w]
    rw [map_sum]
    simp only [map_smul, Module.Basis.coord_apply]
  have hA : ∀ N w, Φ N w = ⟪c, w⟫ • Φ N (s i₀) + R N w := by
    intro N w
    rw [hexp, hc, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  refine tendsto_of_rankOne_approx (fun N => Φ N) R (fun N => Φ N (s i₀)) c ε
    (coordVec_ne_zero s i₀ c hc) hA ?_ hε v hv
  filter_upwards [hm] with N hmN
  refine ⟨hmN, fun w hw => ?_⟩
  have hmn : 0 < ‖Φ N (s i₀)‖ := norm_pos_iff.mpr hmN
  calc ‖R N w‖ ≤ ∑ j ∈ Finset.univ.erase i₀, ‖s.coord j w • Φ N (s j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.univ.erase i₀, K j * ‖Φ N (s j)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK j w hw) (norm_nonneg _)
    _ = ε N * ‖Φ N (s i₀)‖ := by
        simp only [ε, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp

end CompanionMatrix
