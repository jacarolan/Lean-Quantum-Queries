import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Trace bound for a flat tensor spectrum

This file isolates the operator inequality used to pass from a flat spectral
sector of a random-permutation moment state to the ideal-world acceptance
bound.

Let `lam` be the eigenvalue list of a positive operator, and let `F` be a set
on which every eigenvalue is at most `beta`.  Let `P` be a positive
semidefinite matrix whose diagonal support lies in `F × F`.  Then

`trace (P * diag(lam ⊗ lam)) ≤ beta^2 * trace P`.

For an orthogonal projector onto an `r`-dimensional subspace contained in the
flat tensor sector, `trace P = r`; hence the right-hand side is `r * beta^2`.
The proof is elementary: expand the trace in the eigenbasis and bound each
nonnegative diagonal contribution separately.
-/

namespace LeanQuantumQueries.Permutation

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal matrix whose entries are the product-spectrum values
`lam i * lam j`. -/
noncomputable def tensorSpectrumDiagonal (lam : ι → ℝ) :
    Matrix (ι × ι) (ι × ι) ℝ :=
  Matrix.diagonal fun ij => lam ij.1 * lam ij.2

/-- The trace of a matrix times a diagonal tensor spectrum only uses the
matrix's diagonal entries. -/
theorem trace_mul_tensorSpectrumDiagonal
    (P : Matrix (ι × ι) (ι × ι) ℝ) (lam : ι → ℝ) :
    Matrix.trace (P * tensorSpectrumDiagonal lam) =
      ∑ ij, P ij ij * (lam ij.1 * lam ij.2) := by
  simp [Matrix.trace, tensorSpectrumDiagonal]

/-- Elementary weighted cutoff inequality.  The weights need only be
nonnegative and vanish away from `F × F`. -/
theorem weighted_tensor_cutoff
    (lam : ι → ℝ) (F : Finset ι) (w : ι × ι → ℝ) (beta : ℝ)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hbeta : 0 ≤ beta)
    (hflat : ∀ i ∈ F, lam i ≤ beta)
    (hw_nonneg : ∀ ij, 0 ≤ w ij)
    (hsupport : ∀ ij, ij.1 ∉ F ∨ ij.2 ∉ F → w ij = 0) :
    (∑ ij, w ij * (lam ij.1 * lam ij.2)) ≤
      (∑ ij, w ij) * beta ^ 2 := by
  classical
  calc
    (∑ ij, w ij * (lam ij.1 * lam ij.2)) ≤
        ∑ ij, w ij * beta ^ 2 := by
      apply Finset.sum_le_sum
      intro ij _
      by_cases hi : ij.1 ∈ F
      · by_cases hj : ij.2 ∈ F
        · have hprod : lam ij.1 * lam ij.2 ≤ beta ^ 2 := by
            nlinarith [hlam_nonneg ij.1, hlam_nonneg ij.2,
              hflat ij.1 hi, hflat ij.2 hj]
          exact mul_le_mul_of_nonneg_left hprod (hw_nonneg ij)
        · have hw0 : w ij = 0 := hsupport ij (Or.inr hj)
          simp [hw0]
      · have hw0 : w ij = 0 := hsupport ij (Or.inl hi)
        simp [hw0]
    _ = (∑ ij, w ij) * beta ^ 2 := by
      rw [Finset.sum_mul]

/-- **Flat tensor trace inequality.**  If `P` is positive semidefinite and its
diagonal support is contained in `F × F`, then testing the tensor product
spectrum costs at most `beta^2` per unit of projector trace.

For the application, `P` is an orthogonal projector.  Positivity supplies the
nonnegative diagonal weights, and `trace P` is its rank. -/
theorem trace_psd_tensor_cutoff_le_trace
    (P : Matrix (ι × ι) (ι × ι) ℝ)
    (lam : ι → ℝ) (F : Finset ι) (beta : ℝ)
    (hP : P.PosSemidef)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hbeta : 0 ≤ beta)
    (hflat : ∀ i ∈ F, lam i ≤ beta)
    (hsupport : ∀ ij, ij.1 ∉ F ∨ ij.2 ∉ F → P ij ij = 0) :
    Matrix.trace (P * tensorSpectrumDiagonal lam) ≤
      Matrix.trace P * beta ^ 2 := by
  rw [trace_mul_tensorSpectrumDiagonal]
  simpa [Matrix.trace] using
    (weighted_tensor_cutoff lam F (fun ij => P ij ij) beta
      hlam_nonneg hbeta hflat
      (fun ij => hP.diag_nonneg) hsupport)

/-- Rank-form corollary.  Any upper bound `r` on the trace of `P` gives the
usual `r * beta^2` bound.  For an orthogonal projector, take `r` to be the
subspace dimension. -/
theorem trace_psd_tensor_cutoff_le_rank
    (P : Matrix (ι × ι) (ι × ι) ℝ)
    (lam : ι → ℝ) (F : Finset ι) (beta r : ℝ)
    (hP : P.PosSemidef)
    (hlam_nonneg : ∀ i, 0 ≤ lam i)
    (hbeta : 0 ≤ beta)
    (hflat : ∀ i ∈ F, lam i ≤ beta)
    (hsupport : ∀ ij, ij.1 ∉ F ∨ ij.2 ∉ F → P ij ij = 0)
    (htrace : Matrix.trace P ≤ r) :
    Matrix.trace (P * tensorSpectrumDiagonal lam) ≤ r * beta ^ 2 := by
  calc
    Matrix.trace (P * tensorSpectrumDiagonal lam) ≤
        Matrix.trace P * beta ^ 2 :=
      trace_psd_tensor_cutoff_le_trace P lam F beta hP
        hlam_nonneg hbeta hflat hsupport
    _ ≤ r * beta ^ 2 :=
      mul_le_mul_of_nonneg_right htrace (sq_nonneg beta)

end LeanQuantumQueries.Permutation
