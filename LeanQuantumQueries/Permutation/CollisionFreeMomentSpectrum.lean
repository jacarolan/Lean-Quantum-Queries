import LeanQuantumQueries.Permutation.CollisionFreeMatrixPurity
import LeanQuantumQueries.Permutation.HermitianPurity
import Mathlib.Analysis.Matrix.PosDef

/-!
# Flat spectral sector of the actual collision-free moment matrix

This file instantiates the abstract purity-to-flatness theorem with the
explicit positive semidefinite moment matrix.  There are no remaining spectral
or purity hypotheses in the final theorem.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators
open Matrix

/-- Eigenvalues of the actual collision-free moment matrix. -/
noncomputable def collisionFreeMomentEigenvalues (N q : ℕ) :
    PartialPerm N q → ℝ :=
  (collisionFreeMomentMatrix_posSemidef N q).isHermitian.eigenvalues

/-- The actual moment eigenvalues are nonnegative. -/
theorem collisionFreeMomentEigenvalues_nonneg
    (N q : ℕ) (i : PartialPerm N q) :
    0 ≤ collisionFreeMomentEigenvalues N q i := by
  exact (collisionFreeMomentMatrix_posSemidef N q).eigenvalues_nonneg i

/-- Their sum is one. -/
theorem sum_collisionFreeMomentEigenvalues
    {N q : ℕ} (hqN : q ≤ N) :
    ∑ i, collisionFreeMomentEigenvalues N q i = 1 := by
  have htrace :=
    (collisionFreeMomentMatrix_posSemidef N q).isHermitian.trace_eq_sum_eigenvalues
  have hmatrix := collisionFreeMomentMatrix_trace (N := N) (q := q) hqN
  unfold collisionFreeMomentEigenvalues
  simpa [hmatrix] using htrace.symm

/-- Their squared sum is the exact collision-free purity. -/
theorem sum_sq_collisionFreeMomentEigenvalues
    {N q : ℕ} (h2qN : 2 * q ≤ N) :
    ∑ i, (collisionFreeMomentEigenvalues N q i) ^ 2 =
      collisionFreeBeta N q := by
  unfold collisionFreeMomentEigenvalues
  rw [Matrix.IsHermitian.sum_sq_eigenvalues_eq_trace_sq
    (collisionFreeMomentMatrix_posSemidef N q).isHermitian]
  exact trace_collisionFreeMomentMatrix_sq_eq_beta h2qN

/-- Final representation-free flatness theorem for the actual moment matrix.
At cutoff parameter `A`, the retained eigenspaces have total spectral mass at
least `1 - 1/A`, and every retained eigenvalue is at most the explicit bound
`A * collisionFreeBetaUpper N q`. -/
theorem collisionFreeMoment_flat_sector_explicit
    {N q : ℕ} (A : ℝ)
    (h2qN : 2 * q ≤ N) (hA : 0 < A) :
    1 - 1 / A ≤
        ∑ i ∈ flatIndices
          (collisionFreeMomentEigenvalues N q)
          (collisionFreeBetaUpper N q) A,
          collisionFreeMomentEigenvalues N q i ∧
      ∀ i ∈ flatIndices
          (collisionFreeMomentEigenvalues N q)
          (collisionFreeBetaUpper N q) A,
        collisionFreeMomentEigenvalues N q i ≤
          A * collisionFreeBetaUpper N q := by
  have hqN : q ≤ N := by omega
  exact collisionFree_flat_sector_explicit
    (collisionFreeMomentEigenvalues N q) A
    (collisionFreeMomentEigenvalues_nonneg N q)
    (sum_collisionFreeMomentEigenvalues hqN)
    (sum_sq_collisionFreeMomentEigenvalues h2qN)
    h2qN hA

end PartialPerm
end LeanQuantumQueries.Permutation
