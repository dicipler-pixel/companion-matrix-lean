/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import CompanionMatrix.Dominance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Theorem 1: the order-2 theorem (first statement)

Order-2 recurrence `u_n = a_n u_{n-1} + b_n u_{n-2}` with companion matrix
`T(n) = !![a_n, b_n; 1, 0]` and transport `Φ_N = T(N) ⋯ T(1)`, so that
`Φ_N (u_0, u_{-1})ᵀ = (u_N, u_{N-1})ᵀ`.

**Indexing.** Lean sequences start at `0`, so a solution is stored shifted by one:
`u k` stands for `u_{k-1}`. Thus `u 0 = u_{-1}`, `u 1 = u_0`, and the recurrence reads
`u (n+2) = a (n+1) * u (n+1) + b (n+1) * u n`. The seed is `(u 1, u 0) = (u_0, u_{-1})`.

* `CompanionMatrix.transport_mulVec` : `Φ_N (u_0, u_{-1}) = (u_N, u_{N-1})`.
* `CompanionMatrix.theorem1` : if `f` is minimal (`f_n / d_n → 0` for a solution `d` with
  independent seed, `d_n ≠ 0` eventually), then every choice of top right singular vectors
  `v_1(N)` of `Φ_N` converges, as a line, to the Casoratian dual `(-f_{-1}, f_0)` of the
  minimal seed: `|⟪(-f_{-1}, f_0), v_1(N)⟫| / ‖(-f_{-1}, f_0)‖ → 1`.

The conclusion does not mention `d`, so the limit is independent of the complementary solution.
No Poincaré-type assumption on `a, b` is made, and `T(n)` need not be invertible.
-/

namespace CompanionMatrix

open RealInnerProductSpace Filter Topology Matrix

/-- The companion matrix `T(n) = !![a_n, b_n; 1, 0]`. -/
def transfer (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![a n, b n; 1, 0]

/-- The transport `Φ_N = T(N) ⋯ T(1)` (`Φ_0 = 1`). -/
def transport (a b : ℕ → ℝ) : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 0 => 1
  | N + 1 => transfer a b (N + 1) * transport a b N

/-- `u` solves `u_n = a_n u_{n-1} + b_n u_{n-2}`, stored shifted (`u k = u_{k-1}`). -/
def IsSolution (a b : ℕ → ℝ) (u : ℕ → ℝ) : Prop :=
  ∀ n, u (n + 2) = a (n + 1) * u (n + 1) + b (n + 1) * u n

theorem transport_mulVec {a b u : ℕ → ℝ} (hu : IsSolution a b u) (N : ℕ) :
    transport a b N *ᵥ ![u 1, u 0] = ![u (N + 1), u N] := by
  induction N with
  | zero => simp [transport]
  | succ N ih =>
    rw [transport, ← Matrix.mulVec_mulVec, ih]
    ext i; fin_cases i
    · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu N]
    · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `Φ_N` acting on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def transportOp (a b : ℕ → ℝ) (N : ℕ) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
  fun w => WithLp.toLp 2 (transport a b N *ᵥ WithLp.ofLp w)

theorem norm_sq_vec2 (x y : ℝ) : ‖(!₂[x, y] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; rfl

theorem inner_vec2 (x y : ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    ⟪(!₂[x, y] : EuclideanSpace ℝ (Fin 2)), w⟫ = x * w 0 + y * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial]
  change w 0 * x + w 1 * y = _
  ring

theorem abs_apply_le_of_norm_eq_one (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ = 1) (i : Fin 2) :
    |w i| ≤ 1 := by
  have h := EuclideanSpace.real_norm_sq_eq w
  rw [hw, Fin.sum_univ_two] at h
  rw [abs_le_one_iff_mul_self_le_one]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]

/-- Minimality gives `‖F_N‖ / ‖D_N‖ → 0` for the transported seed vectors. -/
theorem tendsto_ratio {f d : ℕ → ℝ} (hmin : Tendsto (fun n => f n / d n) atTop (𝓝 0))
    (hd0 : ∀ᶠ n in atTop, d n ≠ 0) :
    Tendsto (fun N => ‖(!₂[f (N + 1), f N] : EuclideanSpace ℝ (Fin 2))‖ /
      ‖(!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2))‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ n in atTop, |f n| ≤ (ε / 2) * |d n| := by
    have := (Metric.tendsto_nhds.mp hmin) (ε / 2) (by positivity)
    filter_upwards [this, hd0] with n hn hdn
    rw [Real.dist_eq, sub_zero, abs_div, div_lt_iff₀ (abs_pos.mpr hdn)] at hn
    exact hn.le
  have h2 : ∀ᶠ N in atTop, |f (N + 1)| ≤ (ε / 2) * |d (N + 1)| :=
    (tendsto_add_atTop_nat 1).eventually h1
  filter_upwards [h1, h2] with N hN hN1
  set F : EuclideanSpace ℝ (Fin 2) := !₂[f (N + 1), f N]
  set D : EuclideanSpace ℝ (Fin 2) := !₂[d (N + 1), d N]
  have hsq : ‖F‖ ^ 2 ≤ ((ε / 2) * ‖D‖) ^ 2 := by
    rw [mul_pow, norm_sq_vec2, norm_sq_vec2]
    have a1 : f (N + 1) ^ 2 ≤ (ε / 2) ^ 2 * d (N + 1) ^ 2 := by
      rw [← sq_abs (f _), ← sq_abs (d _), ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hN1 2
    have a2 : f N ^ 2 ≤ (ε / 2) ^ 2 * d N ^ 2 := by
      rw [← sq_abs (f _), ← sq_abs (d _), ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hN 2
    linarith
  have hle : ‖F‖ ≤ (ε / 2) * ‖D‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  rcases eq_or_lt_of_le (norm_nonneg D) with hD | hD
  · rw [← hD, div_zero]; exact hε
  · rw [div_lt_iff₀ hD]; nlinarith

/-- **Theorem 1 (order 2), first statement.** -/
theorem theorem1 {a b f d : ℕ → ℝ} (hf : IsSolution a b f) (hd : IsSolution a b d)
    (hdet : f 1 * d 0 - d 1 * f 0 ≠ 0)
    (hmin : Tendsto (fun n => f n / d n) atTop (𝓝 0)) (hd0 : ∀ᶠ n in atTop, d n ≠ 0)
    (v : ℕ → EuclideanSpace ℝ (Fin 2)) (hv : ∀ N, IsTopSingular (transportOp a b N) (v N)) :
    Tendsto (fun N => |⟪(!₂[-f 0, f 1] : EuclideanSpace ℝ (Fin 2)), v N⟫| /
      ‖(!₂[-f 0, f 1] : EuclideanSpace ℝ (Fin 2))‖) atTop (𝓝 1) := by
  set δ := f 1 * d 0 - d 1 * f 0 with hδ
  set c : EuclideanSpace ℝ (Fin 2) := !₂[-f 0, f 1] with hc_def
  -- coordinates of `w` in the seed basis: `w = α(w) f_seed + β(w) d_seed`
  let α : EuclideanSpace ℝ (Fin 2) → ℝ := fun w => (d 0 * w 0 - d 1 * w 1) / δ
  have hcne : c ≠ 0 := by
    intro h
    have h0 : c 0 = 0 := by rw [h]; rfl
    have h1 : c 1 = 0 := by rw [h]; rfl
    simp only [c] at h0 h1
    change -f 0 = 0 at h0
    change f 1 = 0 at h1
    apply hdet; rw [hδ, h1, neg_eq_zero.mp h0]; ring
  let m : ℕ → EuclideanSpace ℝ (Fin 2) := fun N => δ⁻¹ • !₂[d (N + 1), d N]
  let R : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun N w => α w • !₂[f (N + 1), f N]
  have hA : ∀ N w, transportOp a b N w = ⟪c, w⟫ • m N + R N w := by
    intro N w
    set β : ℝ := (f 1 * w 1 - f 0 * w 0) / δ with hβ
    have hw : WithLp.ofLp w = (α w) • ![f 1, f 0] + β • ![d 1, d 0] := by
      ext i; fin_cases i
      · change w 0 = α w * f 1 + β * d 1
        simp only [α, hβ]; field_simp; ring
      · change w 1 = α w * f 0 + β * d 0
        simp only [α, hβ]; field_simp; ring
    have hT : transportOp a b N w = WithLp.toLp 2 ((α w) • ![f (N + 1), f N] +
        β • ![d (N + 1), d N]) := by
      show WithLp.toLp 2 (transport a b N *ᵥ WithLp.ofLp w) = _
      rw [hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, transport_mulVec hf,
        transport_mulVec hd]
    rw [hT, inner_vec2]
    ext i; fin_cases i
    · change α w * f (N + 1) + β * d (N + 1)
        = (-f 0 * w 0 + f 1 * w 1) * (δ⁻¹ * d (N + 1)) + α w * f (N + 1)
      rw [hβ]; field_simp; ring
    · change α w * f N + β * d N
        = (-f 0 * w 0 + f 1 * w 1) * (δ⁻¹ * d N) + α w * f N
      rw [hβ]; field_simp; ring
  -- the error bound
  set K : ℝ := (|d 0| + |d 1|) / |δ| with hK
  have hαK : ∀ w : EuclideanSpace ℝ (Fin 2), ‖w‖ = 1 → |α w| ≤ K := by
    intro w hw
    have h0 := abs_apply_le_of_norm_eq_one w hw 0
    have h1 := abs_apply_le_of_norm_eq_one w hw 1
    simp only [α, K, abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg _)
    calc |d 0 * w 0 - d 1 * w 1| ≤ |d 0 * w 0| + |d 1 * w 1| := abs_sub _ _
      _ = |d 0| * |w 0| + |d 1| * |w 1| := by rw [abs_mul, abs_mul]
      _ ≤ |d 0| * 1 + |d 1| * 1 := by gcongr
      _ = |d 0| + |d 1| := by ring
  let ε : ℕ → ℝ := fun N => K * |δ| * (‖(!₂[f (N + 1), f N] : EuclideanSpace ℝ (Fin 2))‖ /
      ‖(!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2))‖)
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa using (tendsto_ratio hmin hd0).const_mul (K * |δ|)
  have hδpos : 0 < |δ| := abs_pos.mpr hdet
  refine tendsto_of_rankOne_approx (transportOp a b) R m c ε hcne hA ?_ hε v hv
  filter_upwards [hd0] with N hdN
  have hD : (!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    apply hdN
    have : (!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2)) 1 = 0 := by rw [h]; rfl
    exact this
  have hDn : 0 < ‖(!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2))‖ := norm_pos_iff.mpr hD
  refine ⟨smul_ne_zero (inv_ne_zero hdet) hD, fun w hw => ?_⟩
  simp only [R, m, ε, norm_smul, norm_inv, Real.norm_eq_abs]
  rw [show K * |δ| * (‖(!₂[f (N + 1), f N] : EuclideanSpace ℝ (Fin 2))‖ /
      ‖(!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2))‖) *
      (|δ|⁻¹ * ‖(!₂[d (N + 1), d N] : EuclideanSpace ℝ (Fin 2))‖)
      = K * ‖(!₂[f (N + 1), f N] : EuclideanSpace ℝ (Fin 2))‖ by field_simp]
  exact mul_le_mul_of_nonneg_right (hαK w hw) (norm_nonneg _)

end CompanionMatrix
