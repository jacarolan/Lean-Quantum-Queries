import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Order

/-!
# Purity and eigenvalues of a real Hermitian matrix
-/

namespace LeanQuantumQueries.Permutation

open scoped BigOperators
open Matrix

/-- For a real Hermitian matrix, the trace of its square is the sum of the
squares of its eigenvalues. -/
theorem Matrix.IsHermitian.sum_sq_eigenvalues_eq_trace_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i) ^ 2) = Matrix.trace (A * A) := by
  let U := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal hA.eigenvalues
  have hspectral : A = (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) := by
    simpa [U, D, Matrix.conjStarAlgAut_apply, Function.comp_def] using
      hA.spectral_theorem
  rw [hspectral]
  calc
    (∑ i, (hA.eigenvalues i) ^ 2) = Matrix.trace (D * D) := by
      simp [D, Matrix.trace, Matrix.mul_apply, pow_two]
    _ = Matrix.trace
        (((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) *
          ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ))) := by
      have hunit : star (U : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 :=
        U.property
      calc
        Matrix.trace (D * D) =
            Matrix.trace ((D * D) *
              (star (U : Matrix n n ℝ) * (U : Matrix n n ℝ))) := by
                rw [hunit, Matrix.mul_one]
        _ = Matrix.trace
            ((U : Matrix n n ℝ) * (D * D) *
              star (U : Matrix n n ℝ)) := by
                rw [← Matrix.trace_mul_cycle]
                simp [Matrix.mul_assoc]
        _ = Matrix.trace
            (((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) *
              ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ))) := by
                rw [hunit]
                simp [Matrix.mul_assoc]

end LeanQuantumQueries.Permutation
