/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import CompanionMatrix.LemmaA
import CompanionMatrix.Order2
import Mathlib.Topology.Instances.Matrix

/-!
# Theorem 1, second statement: the limit of `Φ(P_N)`

With `P_N = Φ_N / ‖Φ_N‖_F`, Theorem 1 of the revised draft says: if a complementary solution
`d` has `d_N / d_{N-1} → ρ`, then `Φ(P_N) → 1 - (x_∞ ⬝ v_∞)²`, with `x_∞ = normalize(ρ, 1)`
(read as `(1, 0)` for `ρ = ±∞`) and `v_∞ = normalize(-f_{-1}, f_0)`.

* `CompanionMatrix.tendsto_psi_transport` : the general form. If, for some scaling `s_N ≠ 0`,
  `D_N / s_N → x_∞ ≠ 0` and `F_N / s_N → 0`, then
  `Φ(P_N) → 1 - (x_∞ ⬝ c)² / ((x_∞ ⬝ x_∞)(c ⬝ c))` with `c = (-f_{-1}, f_0)`.
* `CompanionMatrix.theorem1_phi` : finite `ρ` (`x_∞ = (ρ, 1)`).
* `CompanionMatrix.theorem1_phi_infty` : `ρ = ±∞`, written `d_{N-1} / d_N → 0` (`x_∞ = (1, 0)`).

The formula is written without normalizing `x_∞` and `c`; it equals `1 - (x̂_∞ ⬝ ĉ)²`.
The statement about the left singular vector `u_1(N) → x_∞` is not formalized here
(see `CompanionMatrix.Statements`); it is not needed for the `Φ` limit, because `Φ` of the
normalized matrix is a scale-free continuous function of `Φ_N`.
-/

namespace CompanionMatrix

open Filter Topology Matrix

/-- `Φ_N = F_N aᵀ + D_N bᵀ` with `aᵀ, bᵀ` the rows of `[f_seed | d_seed]⁻¹`. -/
theorem transport_eq_vecMulVec {a b f d : ℕ → ℝ} (hf : IsSolution a b f) (hd : IsSolution a b d)
    (hdet : f 1 * d 0 - d 1 * f 0 ≠ 0) (N : ℕ) :
    transport a b N =
      vecMulVec ![f (N + 1), f N] ((f 1 * d 0 - d 1 * f 0)⁻¹ • ![d 0, -d 1]) +
      vecMulVec ![d (N + 1), d N] ((f 1 * d 0 - d 1 * f 0)⁻¹ • ![-f 0, f 1]) := by
  set δ := f 1 * d 0 - d 1 * f 0 with hδ
  have hw : ∀ w : Fin 2 → ℝ, w = ((d 0 * w 0 - d 1 * w 1) / δ) • ![f 1, f 0] +
      ((f 1 * w 1 - f 0 * w 0) / δ) • ![d 1, d 0] := by
    intro w; ext i; fin_cases i
    · change w 0 = (d 0 * w 0 - d 1 * w 1) / δ * f 1 + (f 1 * w 1 - f 0 * w 0) / δ * d 1
      field_simp; rw [hδ]; ring
    · change w 1 = (d 0 * w 0 - d 1 * w 1) / δ * f 0 + (f 1 * w 1 - f 0 * w 0) / δ * d 0
      field_simp; rw [hδ]; ring
  ext i j
  have hcol : transport a b N i j = (transport a b N *ᵥ Pi.single j 1) i := by
    rw [mulVec_single_one]; rfl
  rw [hcol, hw (Pi.single j 1), Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    transport_mulVec hf, transport_mulVec hd]
  fin_cases i <;> fin_cases j <;>
    simp <;> field_simp

theorem continuous_frobSq {n : Type*} [Fintype n] :
    Continuous fun A : Matrix n n ℝ => frobSq A := by
  unfold frobSq
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_id.matrix_elem i j).pow 2

theorem continuous_phi {n : Type*} [Fintype n] : Continuous fun A : Matrix n n ℝ => phi A := by
  simp_rw [phi_eq_frobSq]
  exact (continuous_frobSq.comp ((continuous_id.matrix_mul continuous_id.matrix_transpose).sub
    (continuous_id.matrix_transpose.matrix_mul continuous_id))).div_const 2

/-- **General form of the `Φ∞` statement.** -/
theorem tendsto_psi_transport {a b f d : ℕ → ℝ} (hf : IsSolution a b f) (hd : IsSolution a b d)
    (hdet : f 1 * d 0 - d 1 * f 0 ≠ 0) (s : ℕ → ℝ) (hs : ∀ᶠ N in atTop, s N ≠ 0)
    (xinf : Fin 2 → ℝ) (hxinf : xinf ⬝ᵥ xinf ≠ 0)
    (hx : Tendsto (fun N => (s N)⁻¹ • ![d (N + 1), d N]) atTop (𝓝 xinf))
    (hF : Tendsto (fun N => (s N)⁻¹ • ![f (N + 1), f N]) atTop (𝓝 0)) :
    Tendsto (fun N => psi (transport a b N)) atTop
      (𝓝 (1 - (xinf ⬝ᵥ ![-f 0, f 1]) ^ 2 / ((xinf ⬝ᵥ xinf) * (![-f 0, f 1] ⬝ᵥ ![-f 0, f 1])))) := by
  set δ := f 1 * d 0 - d 1 * f 0 with hδ
  set c : Fin 2 → ℝ := ![-f 0, f 1] with hc
  set a' : Fin 2 → ℝ := δ⁻¹ • ![d 0, -d 1]
  set b' : Fin 2 → ℝ := δ⁻¹ • c
  have hcc : c ⬝ᵥ c ≠ 0 := by
    intro h
    have h' : f 0 ^ 2 + f 1 ^ 2 = 0 := by
      have : c ⬝ᵥ c = f 0 ^ 2 + f 1 ^ 2 := by simp [hc, dotProduct, Fin.sum_univ_two]; ring
      rw [← this, h]
    have h0 : f 0 = 0 := by nlinarith [sq_nonneg (f 0), sq_nonneg (f 1)]
    have h1 : f 1 = 0 := by nlinarith [sq_nonneg (f 0), sq_nonneg (f 1)]
    apply hdet; rw [hδ, h0, h1]; ring
  have hbb : b' ⬝ᵥ b' ≠ 0 := by
    simp only [b', smul_dotProduct, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero hdet) (mul_ne_zero (inv_ne_zero hdet) hcc)
  -- the rescaled transport `G_N = Φ_N / s_N` converges to `x_∞ b'ᵀ`
  let G : ℕ → Matrix (Fin 2) (Fin 2) ℝ := fun N =>
    vecMulVec ((s N)⁻¹ • ![f (N + 1), f N]) a' + vecMulVec ((s N)⁻¹ • ![d (N + 1), d N]) b'
  have hG : Tendsto G atTop (𝓝 (vecMulVec 0 a' + vecMulVec xinf b')) := by
    have c1 : Continuous fun u : Fin 2 → ℝ => vecMulVec u a' :=
      continuous_id.matrix_vecMulVec continuous_const
    have c2 : Continuous fun u : Fin 2 → ℝ => vecMulVec u b' :=
      continuous_id.matrix_vecMulVec continuous_const
    exact ((c1.tendsto 0).comp hF).add ((c2.tendsto xinf).comp hx)
  have hG0 : vecMulVec 0 a' + vecMulVec xinf b' = vecMulVec xinf b' := by
    ext i j; simp [vecMulVec_apply]
  rw [hG0] at hG
  have hlim : psi (vecMulVec xinf b') =
      1 - (xinf ⬝ᵥ c) ^ 2 / ((xinf ⬝ᵥ xinf) * (c ⬝ᵥ c)) := by
    rw [psi_vecMulVec _ _ hxinf hbb]
    simp only [b', dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have hfrob : frobSq (vecMulVec xinf b') ≠ 0 := by
    rw [frobSq_vecMulVec]; exact mul_ne_zero hxinf hbb
  have hpsi : Tendsto (fun N => psi (G N)) atTop (𝓝 (psi (vecMulVec xinf b'))) := by
    unfold psi
    exact ((continuous_phi.tendsto _).comp hG).div
      (((continuous_frobSq.tendsto _).comp hG).pow 2) (pow_ne_zero 2 hfrob)
  rw [← hlim]
  refine hpsi.congr' ?_
  filter_upwards [hs] with N hsN
  rw [← psi_smul (s N)⁻¹ (inv_ne_zero hsN) (transport a b N), transport_eq_vecMulVec hf hd hdet N]
  congr 1
  ext i j
  simp only [G, a', b', hc, hδ, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

section Normalized

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup

/-- **Theorem 1, `Φ∞` statement, finite `ρ`.** If `d_N / d_{N-1} → ρ` (in Lean indexing,
`d (N+1) / d N → ρ`), then `Φ(Φ_N / ‖Φ_N‖_F) → 1 - (x ⬝ c)² / ((x ⬝ x)(c ⬝ c))` with
`x = (ρ, 1)` and `c = (-f_{-1}, f_0)`. -/
theorem theorem1_phi {a b f d : ℕ → ℝ} (hf : IsSolution a b f) (hd : IsSolution a b d)
    (hdet : f 1 * d 0 - d 1 * f 0 ≠ 0)
    (hmin : Tendsto (fun n => f n / d n) atTop (𝓝 0)) (hd0 : ∀ᶠ n in atTop, d n ≠ 0)
    (ρ : ℝ) (hρ : Tendsto (fun N => d (N + 1) / d N) atTop (𝓝 ρ)) :
    Tendsto (fun N => phi (‖transport a b N‖⁻¹ • transport a b N)) atTop
      (𝓝 (1 - (![ρ, 1] ⬝ᵥ ![-f 0, f 1]) ^ 2 /
        ((![ρ, 1] ⬝ᵥ ![ρ, 1]) * (![-f 0, f 1] ⬝ᵥ ![-f 0, f 1])))) := by
  simp_rw [phi_normalize]
  refine tendsto_psi_transport hf hd hdet d hd0 ![ρ, 1] ?_ ?_ ?_
  · have h : (![ρ, 1] ⬝ᵥ ![ρ, 1] : ℝ) = ρ * ρ + 1 := by simp [dotProduct, Fin.sum_univ_two]
    rw [h]; nlinarith [mul_self_nonneg ρ]
  · rw [tendsto_pi_nhds]; intro i; fin_cases i
    · refine hρ.congr' ?_
      filter_upwards with N; simp [div_eq_inv_mul]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hd0] with N hN; simp [inv_mul_cancel₀ hN]
  · rw [tendsto_pi_nhds]; intro i; fin_cases i
    · have h1 : Tendsto (fun N => f (N + 1) / d (N + 1)) atTop (𝓝 0) :=
        hmin.comp (tendsto_add_atTop_nat 1)
      have := h1.mul hρ
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [hd0, (tendsto_add_atTop_nat 1).eventually hd0] with N hN hN1
      simp; field_simp
    · refine hmin.congr' ?_
      filter_upwards with N; simp [div_eq_inv_mul]

/-- **Theorem 1, `Φ∞` statement, `ρ = ±∞`**, written as `d_{N-1} / d_N → 0`
(Lean: `d N / d (N+1) → 0`); here `x_∞ = (1, 0)`. -/
theorem theorem1_phi_infty {a b f d : ℕ → ℝ} (hf : IsSolution a b f) (hd : IsSolution a b d)
    (hdet : f 1 * d 0 - d 1 * f 0 ≠ 0)
    (hmin : Tendsto (fun n => f n / d n) atTop (𝓝 0)) (hd0 : ∀ᶠ n in atTop, d n ≠ 0)
    (hρ : Tendsto (fun N => d N / d (N + 1)) atTop (𝓝 0)) :
    Tendsto (fun N => phi (‖transport a b N‖⁻¹ • transport a b N)) atTop
      (𝓝 (1 - (![1, 0] ⬝ᵥ ![-f 0, f 1]) ^ 2 /
        ((![1, 0] ⬝ᵥ ![1, 0]) * (![-f 0, f 1] ⬝ᵥ ![-f 0, f 1])))) := by
  simp_rw [phi_normalize]
  have hd1 : ∀ᶠ N in atTop, d (N + 1) ≠ 0 := (tendsto_add_atTop_nat 1).eventually hd0
  refine tendsto_psi_transport hf hd hdet (fun N => d (N + 1)) hd1 ![1, 0] ?_ ?_ ?_
  · simp [dotProduct, Fin.sum_univ_two]
  · rw [tendsto_pi_nhds]; intro i; fin_cases i
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hd1] with N hN; simp [inv_mul_cancel₀ hN]
    · refine hρ.congr' ?_
      filter_upwards with N; simp [div_eq_inv_mul]
  · rw [tendsto_pi_nhds]; intro i; fin_cases i
    · refine (hmin.comp (tendsto_add_atTop_nat 1)).congr' ?_
      filter_upwards with N; simp [div_eq_inv_mul]
    · have := hmin.mul hρ
      rw [zero_mul] at this
      refine this.congr' ?_
      filter_upwards [hd0, hd1] with N hN hN1
      simp; field_simp

end Normalized

end CompanionMatrix
