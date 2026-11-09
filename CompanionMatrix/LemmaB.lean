/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Lemma B: rank-one perturbation of a top singular vector

Let `A = x bᵀ + E` act between real inner product spaces, i.e. `A w = ⟪b, w⟫ x + E w`, with
`‖x‖ = 1` and `‖E w‖ ≤ η` for every unit `w`. A *top right singular vector* of `A` is a unit
vector `v` maximizing `‖A w‖` over the unit sphere. Mathlib has no singular vectors, so this
maximizing property is the definition we use; it is exactly the variational characterization.

* `CompanionMatrix.lemmaB` : `‖b‖ - 2η ≤ |⟪b, v⟫|`.
* `CompanionMatrix.lemmaB_cos` : for `b ≠ 0`, `1 - 2η/‖b‖ ≤ |cos ∠(v, b)| = |⟪b, v⟫| / ‖b‖`.
* `CompanionMatrix.lemmaB_left` : the same bound for a top *left* singular vector `u` and `x`,
  stated through the transpose `Aᵀ u = ⟪x, u⟫ b + Eᵀ u` (with `‖Eᵀ u‖ ≤ η` on unit vectors).

The hypothesis `η < ‖b‖/2` from the paper is not needed: without it the bound is just weaker.
-/

namespace CompanionMatrix

open RealInnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- `v` is a top right singular vector of `A`: a unit vector maximizing `‖A w‖` on the unit
sphere. -/
def IsTopSingular (A : V → W) (v : V) : Prop :=
  ‖v‖ = 1 ∧ ∀ w : V, ‖w‖ = 1 → ‖A w‖ ≤ ‖A v‖

/-- **Lemma B.** If `A w = ⟪b, w⟫ x + E w` with `‖x‖ = 1` and `‖E w‖ ≤ η` on unit vectors, then
any top right singular vector `v` of `A` satisfies `‖b‖ - 2η ≤ |⟪b, v⟫|`. -/
theorem lemmaB (A E : V → W) (x : W) (b : V) (η : ℝ) (hx : ‖x‖ = 1)
    (hA : ∀ w, A w = ⟪b, w⟫ • x + E w) (hE : ∀ w, ‖w‖ = 1 → ‖E w‖ ≤ η)
    (v : V) (hv : IsTopSingular A v) : ‖b‖ - 2 * η ≤ |⟪b, v⟫| := by
  obtain ⟨hv1, hvmax⟩ := hv
  -- upper bound on `‖A v‖`
  have hup : ‖A v‖ ≤ |⟪b, v⟫| + η := by
    rw [hA]
    calc ‖⟪b, v⟫ • x + E v‖ ≤ ‖⟪b, v⟫ • x‖ + ‖E v‖ := norm_add_le _ _
      _ ≤ |⟪b, v⟫| + η := by
        rw [norm_smul, hx, mul_one, Real.norm_eq_abs]; linarith [hE v hv1]
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have h0 : 0 ≤ η := le_trans (norm_nonneg _) (hE v hv1)
    simp only [norm_zero, inner_zero_left, abs_zero]; linarith
  -- lower bound on `σ₁ ≥ ‖A b̂‖`
  set bh : V := ‖b‖⁻¹ • b with hbh
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hbh1 : ‖bh‖ = 1 := by
    rw [hbh, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbn.ne']
  have hinner : ⟪b, bh⟫ = ‖b‖ := by
    rw [hbh, inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hlow : ‖b‖ - η ≤ ‖A bh‖ := by
    rw [hA, hinner]
    have h1 : ‖‖b‖ • x‖ = ‖b‖ := by rw [norm_smul, hx, mul_one, norm_norm]
    have h2 := norm_sub_norm_le (‖b‖ • x) (-(E bh))
    rw [sub_neg_eq_add, norm_neg, h1] at h2
    linarith [hE bh hbh1]
  linarith [hvmax bh hbh1]

/-- **Lemma B**, cosine form: `1 - 2η/‖b‖ ≤ |⟪b, v⟫| / ‖b‖` for `b ≠ 0`. -/
theorem lemmaB_cos (A E : V → W) (x : W) (b : V) (η : ℝ) (hx : ‖x‖ = 1) (hb : b ≠ 0)
    (hA : ∀ w, A w = ⟪b, w⟫ • x + E w) (hE : ∀ w, ‖w‖ = 1 → ‖E w‖ ≤ η)
    (v : V) (hv : IsTopSingular A v) : 1 - 2 * η / ‖b‖ ≤ |⟪b, v⟫| / ‖b‖ := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have := lemmaB A E x b η hx hA hE v hv
  rw [le_div_iff₀ hbn, sub_mul, one_mul, div_mul_cancel₀ _ hbn.ne']
  exact this

/-- **Lemma B**, left singular vector. Let `B = Aᵀ`, so `B u = ⟪x, u⟫ b + E' u` with
`‖E' u‖ ≤ η` on unit vectors. A top left singular vector `u` of `A` is a top right singular
vector of `B`, and then `1 - 2η/‖b‖ ≤ |⟪x, u⟫|`. -/
theorem lemmaB_left (B E' : W → V) (x : W) (b : V) (η : ℝ) (hx : ‖x‖ = 1) (hb : b ≠ 0)
    (hB : ∀ u, B u = ⟪x, u⟫ • b + E' u) (hE : ∀ u, ‖u‖ = 1 → ‖E' u‖ ≤ η)
    (u : W) (hu : IsTopSingular B u) : 1 - 2 * η / ‖b‖ ≤ |⟪x, u⟫| := by
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  set bh : V := ‖b‖⁻¹ • b
  have hbh1 : ‖bh‖ = 1 := by
    simp only [bh, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbn.ne']
  have hB' : ∀ u, B u = ⟪‖b‖ • x, u⟫ • bh + E' u := by
    intro u
    rw [hB, inner_smul_left, smul_smul]
    congr 1
    simp only [RCLike.conj_to_real]
    congr 1
    field_simp
  have h := lemmaB B E' bh (‖b‖ • x) η hbh1 hB' hE u hu
  rw [norm_smul, norm_norm, hx, mul_one, inner_smul_left, RCLike.conj_to_real, abs_mul,
    abs_of_pos hbn] at h
  rw [show 1 - 2 * η / ‖b‖ = (‖b‖ - 2 * η) / ‖b‖ by field_simp, div_le_iff₀ hbn]
  linarith

end CompanionMatrix
