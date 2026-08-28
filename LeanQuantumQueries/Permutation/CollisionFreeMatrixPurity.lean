import LeanQuantumQueries.Permutation.CollisionFreeEnsemblePurity

/-!
# Purity of the collision-free moment matrix

This file identifies the Hilbert--Schmidt purity of the explicit moment matrix
with the average squared overlap of the collision-free permutation ensemble.
Combining this with the previous counting theorem gives the exact value
`collisionFreeBeta N q`.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators
open Matrix

variable {N q : ℕ}

/-- The permutation-side Gram matrix of the extension incidence matrix. -/
noncomputable def permutationCogram (N q : ℕ) :
    Matrix (Equiv.Perm (Fin N)) (Equiv.Perm (Fin N)) ℝ :=
  extensionIncidence N q * (extensionIncidence N q)ᴴ

/-- Its entries are the unnormalized collision-free state overlaps. -/
theorem permutationCogram_apply
    (π σ : Equiv.Perm (Fin N)) :
    permutationCogram N q π σ = agreementCount π σ q := by
  unfold permutationCogram
  rw [Matrix.mul_apply]
  simpa [Matrix.conjTranspose_apply, star_trivial] using
    (sum_extensionIncidence_mul_eq_agreement
      (N := N) (q := q) π σ)

/-- Agreement counts are symmetric. -/
theorem agreementCount_symm
    (π σ : Equiv.Perm (Fin N)) :
    agreementCount π σ q = agreementCount σ π q := by
  unfold agreementCount
  apply Fintype.sum_congr
  intro S
  by_cases h : AgreesOn π σ S
  · have hs : AgreesOn σ π S := fun x hx => (h x hx).symm
    simp only [agreementIndicator, if_pos h, if_pos hs]
  · have hs : ¬ AgreesOn σ π S := by
      intro hs
      exact h (fun x hx => (hs x hx).symm)
    simp only [agreementIndicator, if_neg h, if_neg hs]

/-- Cyclicity of trace identifies the squares of the two incidence Gram
matrices. -/
theorem trace_incidence_gram_sq_eq_cogram_sq (N q : ℕ) :
    Matrix.trace
        (((extensionIncidence N q)ᴴ * extensionIncidence N q) *
          ((extensionIncidence N q)ᴴ * extensionIncidence N q)) =
      Matrix.trace (permutationCogram N q * permutationCogram N q) := by
  let B := extensionIncidence N q
  calc
    Matrix.trace ((Bᴴ * B) * (Bᴴ * B)) =
        Matrix.trace (Bᴴ * (B * (Bᴴ * B))) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace ((B * (Bᴴ * B)) * Bᴴ) := by
          exact Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((B * Bᴴ) * (B * Bᴴ)) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (permutationCogram N q * permutationCogram N q) := rfl

/-- The trace of the square of the cogram is the raw average-overlap sum. -/
theorem trace_permutationCogram_sq (N q : ℕ) :
    Matrix.trace (permutationCogram N q * permutationCogram N q) =
      rawAgreementPurity N q := by
  classical
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  simp_rw [Matrix.mul_apply, permutationCogram_apply]
  unfold rawAgreementPurity
  apply Fintype.sum_congr
  intro π
  apply Fintype.sum_congr
  intro σ
  rw [agreementCount_symm σ π]
  ring

/-- Matrix purity is exactly ensemble purity. -/
theorem trace_collisionFreeMomentMatrix_sq_eq_ensemble
    (hqN : q ≤ N) :
    Matrix.trace
        (collisionFreeMomentMatrix N q * collisionFreeMomentMatrix N q) =
      collisionFreeEnsemblePurity N q := by
  have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
  have hchoose : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hqN
  unfold collisionFreeMomentMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
    trace_incidence_gram_sq_eq_cogram_sq,
    trace_permutationCogram_sq]
  unfold momentNormalizer collisionFreeEnsemblePurity
  field_simp [hfac, hchoose]
  ring

/-- Exact Hilbert--Schmidt purity of the actual moment matrix. -/
theorem trace_collisionFreeMomentMatrix_sq_eq_beta
    (h2qN : 2 * q ≤ N) :
    Matrix.trace
        (collisionFreeMomentMatrix N q * collisionFreeMomentMatrix N q) =
      collisionFreeBeta N q := by
  have hqN : q ≤ N := by omega
  rw [trace_collisionFreeMomentMatrix_sq_eq_ensemble hqN,
    collisionFreeEnsemblePurity_eq hqN,
    collisionFreePurity_real_eq_beta h2qN]

end PartialPerm
end LeanQuantumQueries.Permutation
