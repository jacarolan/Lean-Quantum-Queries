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
  have hspectral :
      A = (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.spectral_theorem
  have hunit :
      star (U : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 :=
    Unitary.coe_star_mul_self U
  have hmul :
      (((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) *
          ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ))) =
        (U : Matrix n n ℝ) * (D * D) * star (U : Matrix n n ℝ) := by
    calc
      (((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) *
          ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ))) =
        (U : Matrix n n ℝ) * D *
          (star (U : Matrix n n ℝ) * (U : Matrix n n ℝ)) *
          D * star (U : Matrix n n ℝ) := by
            simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℝ) * D * 1 * D *
          star (U : Matrix n n ℝ) := by rw [hunit]
      _ = (U : Matrix n n ℝ) * (D * D) *
          star (U : Matrix n n ℝ) := by
            simp [Matrix.mul_assoc]
  have htraceConj :
      Matrix.trace
          ((U : Matrix n n ℝ) * (D * D) * star (U : Matrix n n ℝ)) =
        Matrix.trace (D * D) := by
    rw [Matrix.trace_mul_cycle]
    rw [hunit]
    simp
  calc
    (∑ i, (hA.eigenvalues i) ^ 2) = Matrix.trace (D * D) := by
      simp [D, pow_two]
    _ = Matrix.trace
        (((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ)) *
          ((U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ))) := by
      rw [hmul, htraceConj]
    _ = Matrix.trace (A * A) := by
      rw [hspectral]

end LeanQuantumQueries.Permutation
