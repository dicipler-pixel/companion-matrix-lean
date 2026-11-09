/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.Matrix.Normed

/-!
# Lemma A: range and rank-one value of the non-normality measure `Φ`

For a real square matrix `P` put
`Φ(P) = ½ ‖[P, Pᵀ]‖_F² = ½ ‖P Pᵀ - Pᵀ P‖_F²` (Frobenius norm).

* `CompanionMatrix.phi_eq` : the exact identity `Φ(P) = ‖P Pᵀ‖_F² - ‖P²‖_F²`.
* `CompanionMatrix.phi_nonneg`, `CompanionMatrix.phi_le_one` : Lemma A(i),
  `0 ≤ Φ(P) ≤ 1` whenever `‖P‖_F = 1`.
* `CompanionMatrix.phi_vecMulVec` : Lemma A(ii), `Φ(x yᵀ) = 1 - (x ⬝ y)²` for unit `x, y`.

The Frobenius norm is Mathlib's `Matrix.frobeniusNormedAddCommGroup`, enabled as a local
instance. No Böttcher–Wenzel inequality is needed.
-/

namespace CompanionMatrix

open Matrix

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup

variable {n : Type*} [Fintype n]

/-- The non-normality measure `Φ(P) = ½ ‖P Pᵀ - Pᵀ P‖_F²`. -/
noncomputable def phi (P : Matrix n n ℝ) : ℝ :=
  ‖P * Pᵀ - Pᵀ * P‖ ^ 2 / 2

/-- The squared Frobenius norm is the sum of the squared entries. -/
theorem frobenius_norm_sq {m : Type*} [Fintype m] (A : Matrix m n ℝ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  rw [frobenius_norm_def]
  simp_rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))]

/-- The squared Frobenius norm is `trace (A Aᵀ)`. -/
theorem frobenius_norm_sq_eq_trace {m : Type*} [Fintype m] (A : Matrix m n ℝ) :
    ‖A‖ ^ 2 = trace (A * Aᵀ) := by
  rw [frobenius_norm_sq]
  simp [trace, Matrix.mul_apply, sq]

/-- The exact identity behind Lemma A(i): `½‖[P,Pᵀ]‖_F² = ‖P Pᵀ‖_F² - ‖P²‖_F²`. -/
theorem phi_eq (P : Matrix n n ℝ) : phi P = ‖P * Pᵀ‖ ^ 2 - ‖P * P‖ ^ 2 := by
  unfold phi
  rw [frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace, frobenius_norm_sq_eq_trace]
  simp only [transpose_sub, transpose_mul, transpose_transpose, sub_mul, mul_sub,
    trace_sub, Matrix.mul_assoc]
  have h1 : trace (Pᵀ * (P * (Pᵀ * P))) = trace (P * (Pᵀ * (P * Pᵀ))) := by
    rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
  have h2 : trace (P * (Pᵀ * (Pᵀ * P))) = trace (P * (P * (Pᵀ * Pᵀ))) := by
    rw [show P * (Pᵀ * (Pᵀ * P)) = (P * Pᵀ * Pᵀ) * P by simp only [Matrix.mul_assoc],
      trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h3 : trace (Pᵀ * (P * (P * Pᵀ))) = trace (P * (P * (Pᵀ * Pᵀ))) := by
    rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [h1, h2, h3]
  ring

/-- Lemma A(i), lower bound. -/
theorem phi_nonneg (P : Matrix n n ℝ) : 0 ≤ phi P := by
  unfold phi; positivity

/-- Lemma A(i), upper bound: `Φ(P) ≤ 1` whenever `‖P‖_F = 1`. -/
theorem phi_le_one (P : Matrix n n ℝ) (hP : ‖P‖ = 1) : phi P ≤ 1 := by
  rw [phi_eq]
  have h : ‖P * Pᵀ‖ ≤ 1 := by
    calc ‖P * Pᵀ‖ ≤ ‖P‖ * ‖Pᵀ‖ := frobenius_norm_mul P Pᵀ
      _ = 1 := by rw [frobenius_norm_transpose, hP, one_mul]
  have h0 : 0 ≤ ‖P * Pᵀ‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖P * P‖]

/-- Lemma A(i): `0 ≤ Φ(P) ≤ 1` whenever `‖P‖_F = 1`. -/
theorem phi_mem_Icc (P : Matrix n n ℝ) (hP : ‖P‖ = 1) : phi P ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨phi_nonneg P, phi_le_one P hP⟩

/-- Lemma A(ii): for unit vectors `x, y`, `Φ(x yᵀ) = 1 - (x ⬝ y)²`. -/
theorem phi_vecMulVec (x y : n → ℝ) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) :
    phi (vecMulVec x y) = 1 - (x ⬝ᵥ y) ^ 2 := by
  unfold phi
  rw [transpose_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, hx, hy,
    one_smul, one_smul, frobenius_norm_sq]
  have e : ∀ i j, (vecMulVec x x - vecMulVec y y) i j ^ 2
      = x i * x i * (x j * x j) - 2 * (x i * y i * (x j * y j)) + y i * y i * (y j * y j) := by
    intro i j; simp only [Matrix.sub_apply, vecMulVec_apply]; ring
  have key : ∑ i, ∑ j, (vecMulVec x x - vecMulVec y y) i j ^ 2
      = (x ⬝ᵥ x) * (x ⬝ᵥ x) - 2 * ((x ⬝ᵥ y) * (x ⬝ᵥ y)) + (y ⬝ᵥ y) * (y ⬝ᵥ y) := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, dotProduct]
  rw [key, hx, hy]
  ring

/-! ### Scale-free form, used for the `Φ∞` limit -/

/-- Sum of squared entries (the squared Frobenius norm, written without the norm instance). -/
def frobSq {m : Type*} [Fintype m] (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- `Φ` of the Frobenius-normalized matrix, written scale-free: `ψ(A) = Φ(A) / ‖A‖_F⁴`. -/
noncomputable def psi (A : Matrix n n ℝ) : ℝ := phi A / frobSq A ^ 2

theorem norm_sq_eq_frobSq {m : Type*} [Fintype m] (A : Matrix m n ℝ) : ‖A‖ ^ 2 = frobSq A :=
  frobenius_norm_sq A

theorem phi_eq_frobSq (A : Matrix n n ℝ) : phi A = frobSq (A * Aᵀ - Aᵀ * A) / 2 := by
  rw [phi, norm_sq_eq_frobSq]

theorem frobSq_smul {m : Type*} [Fintype m] (t : ℝ) (A : Matrix m n ℝ) :
    frobSq (t • A) = t ^ 2 * frobSq A := by
  simp only [frobSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, mul_pow]

theorem phi_smul (t : ℝ) (A : Matrix n n ℝ) : phi (t • A) = t ^ 4 * phi A := by
  rw [phi_eq_frobSq, phi_eq_frobSq]
  have : (t • A) * (t • A)ᵀ - (t • A)ᵀ * (t • A) = (t ^ 2) • (A * Aᵀ - Aᵀ * A) := by
    rw [transpose_smul, smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, sq]
  rw [this, frobSq_smul]; ring

/-- `ψ` is invariant under nonzero rescaling. -/
theorem psi_smul (t : ℝ) (ht : t ≠ 0) (A : Matrix n n ℝ) : psi (t • A) = psi A := by
  unfold psi
  rw [phi_smul, frobSq_smul]
  rcases eq_or_ne (frobSq A) 0 with h | h
  · simp [h]
  · field_simp

/-- `Φ(A / ‖A‖_F) = ψ(A)`. -/
theorem phi_normalize (A : Matrix n n ℝ) : phi (‖A‖⁻¹ • A) = psi A := by
  rw [phi_smul, psi, ← norm_sq_eq_frobSq, inv_pow, ← div_eq_inv_mul]; ring

theorem frobSq_vecMulVec (x y : n → ℝ) : frobSq (vecMulVec x y) = (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  simp only [frobSq, vecMulVec_apply, dotProduct, Finset.sum_mul_sum, mul_pow]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Lemma A(ii) without normalization:
`Φ(x yᵀ) = (x⬝x)²(y⬝y)² - (x⬝x)(y⬝y)(x⬝y)²`. -/
theorem phi_vecMulVec' (x y : n → ℝ) :
    phi (vecMulVec x y) = (x ⬝ᵥ x) ^ 2 * (y ⬝ᵥ y) ^ 2 - (x ⬝ᵥ x) * (y ⬝ᵥ y) * (x ⬝ᵥ y) ^ 2 := by
  rw [phi_eq_frobSq, transpose_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec]
  have e : ∀ i j, (vecMulVec x ((y ⬝ᵥ y) • x) - vecMulVec y ((x ⬝ᵥ x) • y)) i j ^ 2
      = (y ⬝ᵥ y) ^ 2 * (x i * x i * (x j * x j))
        - 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) * (x i * y i * (x j * y j))
        + (x ⬝ᵥ x) ^ 2 * (y i * y i * (y j * y j)) := by
    intro i j; simp only [Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]; ring
  have key : frobSq (vecMulVec x ((y ⬝ᵥ y) • x) - vecMulVec y ((x ⬝ᵥ x) • y))
      = (y ⬝ᵥ y) ^ 2 * ((x ⬝ᵥ x) * (x ⬝ᵥ x)) - 2 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) * ((x ⬝ᵥ y) * (x ⬝ᵥ y))
        + (x ⬝ᵥ x) ^ 2 * ((y ⬝ᵥ y) * (y ⬝ᵥ y)) := by
    simp only [frobSq, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    simp only [dotProduct]
  rw [key]; ring

/-- `ψ(x yᵀ) = 1 - (x⬝y)² / ((x⬝x)(y⬝y))` for nonzero `x, y`. -/
theorem psi_vecMulVec (x y : n → ℝ) (hx : x ⬝ᵥ x ≠ 0) (hy : y ⬝ᵥ y ≠ 0) :
    psi (vecMulVec x y) = 1 - (x ⬝ᵥ y) ^ 2 / ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
  rw [psi, phi_vecMulVec', frobSq_vecMulVec]
  field_simp

end CompanionMatrix
