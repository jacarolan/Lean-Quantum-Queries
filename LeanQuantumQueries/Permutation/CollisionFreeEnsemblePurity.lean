import LeanQuantumQueries.Permutation.CollisionFreeAgreement

/-!
# Purity of the actual collision-free permutation ensemble

For total permutations `π,σ`, the overlap of their collision-free `q`-query
states is the fraction of `q`-subsets on which they agree.  This file expands
the average squared overlap, exchanges the four finite sums, and counts the
permutations agreeing on each union.  The result is exactly the scalar
`collisionFreePurity` evaluated earlier.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- Unnormalized overlap count of two collision-free permutation states. -/
noncomputable def agreementCount
    (π σ : Equiv.Perm (Fin N)) (q : ℕ) : ℝ :=
  ∑ S : QSubset N q, agreementIndicator π σ S

/-- Raw double sum of squared overlap counts. -/
noncomputable def rawAgreementPurity (N q : ℕ) : ℝ :=
  ∑ π : Equiv.Perm (Fin N),
    ∑ σ : Equiv.Perm (Fin N), (agreementCount π σ q) ^ 2

/-- Expanding the squared overlaps and counting the second permutation gives a
closed union-factorial sum. -/
theorem rawAgreementPurity_eq :
    rawAgreementPurity N q =
      (Nat.factorial N : ℝ) *
        ∑ S : QSubset N q,
          ∑ T : QSubset N q,
            (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) := by
  classical
  rw [rawAgreementPurity]
  simp_rw [agreementCount, pow_two, Fintype.sum_mul_sum]
  calc
    (∑ π : Equiv.Perm (Fin N),
        ∑ σ : Equiv.Perm (Fin N),
          ∑ S : QSubset N q,
            ∑ T : QSubset N q,
              agreementIndicator π σ S * agreementIndicator π σ T) =
      ∑ π : Equiv.Perm (Fin N),
        ∑ S : QSubset N q,
          ∑ T : QSubset N q,
            ∑ σ : Equiv.Perm (Fin N),
              agreementIndicator π σ S * agreementIndicator π σ T := by
        apply Fintype.sum_congr
        intro π
        rw [Finset.sum_comm]
        apply Fintype.sum_congr
        intro S
        rw [Finset.sum_comm]
    _ = ∑ π : Equiv.Perm (Fin N),
        ∑ S : QSubset N q,
          ∑ T : QSubset N q,
            (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) := by
        apply Fintype.sum_congr
        intro π
        apply Fintype.sum_congr
        intro S
        apply Fintype.sum_congr
        intro T
        exact sum_agreementIndicator_mul π S T
    _ = (Nat.factorial N : ℝ) *
        ∑ S : QSubset N q,
          ∑ T : QSubset N q,
            (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        simp [nsmul_eq_mul]

/-- Average squared overlap of the actual normalized collision-free states. -/
noncomputable def collisionFreeEnsemblePurity (N q : ℕ) : ℝ :=
  rawAgreementPurity N q /
    ((Nat.factorial N : ℝ) ^ 2 * (Nat.choose N q : ℝ) ^ 2)

/-- Factorial ratio for a union of two subsets, in real form. -/
theorem factorial_ratio_eq_collisionKernel_real
    (S T : QSubset N q) :
    (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) /
        Nat.factorial N =
      (collisionKernel S T : ℝ) := by
  have hu : (S.1 ∪ T.1).card ≤ N := by
    simpa using Finset.card_le_univ (S.1 ∪ T.1)
  have hq := factorial_ratio_eq_inv_descFactorial
    (N := N) (u := (S.1 ∪ T.1).card) hu
  unfold collisionKernel
  have hq_real := congrArg (Rat.castHom ℝ) hq
  simpa using hq_real

/-- The actual ensemble purity is exactly the previously evaluated
collision-free purity scalar. -/
theorem collisionFreeEnsemblePurity_eq
    (hqN : q ≤ N) :
    collisionFreeEnsemblePurity N q =
      (collisionFreePurity N q : ℝ) := by
  have hfac : (Nat.factorial N : ℝ) ≠ 0 := by positivity
  have hchoose : (Nat.choose N q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hqN
  have hsum_div :
      (∑ S : QSubset N q,
        ∑ T : QSubset N q,
          (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) /
            Nat.factorial N) =
        (∑ S : QSubset N q,
          ∑ T : QSubset N q,
            (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ)) /
          Nat.factorial N := by
    calc
      (∑ S : QSubset N q,
        ∑ T : QSubset N q,
          (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) /
            Nat.factorial N) =
          ∑ S : QSubset N q,
            (∑ T : QSubset N q,
              (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ)) /
                Nat.factorial N := by
            apply Fintype.sum_congr
            intro S
            exact Finset.sum_div
      _ = (∑ S : QSubset N q,
            ∑ T : QSubset N q,
              (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ)) /
            Nat.factorial N := Finset.sum_div
  rw [collisionFreeEnsemblePurity, rawAgreementPurity_eq]
  rw [collisionFreePurity]
  push_cast
  calc
    (Nat.factorial N : ℝ) *
          (∑ S : QSubset N q,
            ∑ T : QSubset N q,
              (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ)) /
        ((Nat.factorial N : ℝ) ^ 2 * (Nat.choose N q : ℝ) ^ 2) =
      (∑ S : QSubset N q,
        ∑ T : QSubset N q,
          (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) /
            Nat.factorial N) /
        (Nat.choose N q : ℝ) ^ 2 := by
          rw [hsum_div]
          field_simp [hfac, hchoose]
          ring
    _ = (∑ S : QSubset N q,
        ∑ T : QSubset N q, (collisionKernel S T : ℝ)) /
          (Nat.choose N q : ℝ) ^ 2 := by
          congr 1
          apply Fintype.sum_congr
          intro S
          apply Fintype.sum_congr
          intro T
          exact factorial_ratio_eq_collisionKernel_real S T

end PartialPerm
end LeanQuantumQueries.Permutation
