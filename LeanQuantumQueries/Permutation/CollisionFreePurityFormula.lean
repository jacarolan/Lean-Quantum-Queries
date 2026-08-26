import LeanQuantumQueries.Permutation.CollisionFreePurity
import Mathlib.Data.Nat.Choose.Cast

/-!
# Closed form for the collision-free moment purity

This file evaluates the double collision-free moment sum by partitioning a
second `q`-subset according to its intersection size with the first one.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- Partition all `q`-subsets by their intersection size with `S`. -/
noncomputable def qSubsetEquivOverlapSigma (S : QSubset N q) :
    QSubset N q ≃ Sigma (fun j : Fin (q + 1) => SubsetOverlap S j.1) where
  toFun T :=
    ⟨⟨(S.1 ∩ T.1).card, by
        have hle : (S.1 ∩ T.1).card ≤ S.1.card :=
          Finset.card_le_card Finset.inter_subset_left
        rw [S.2] at hle
        exact Nat.lt_succ_of_le hle⟩,
      ⟨T, rfl⟩⟩
  invFun X := X.2.1
  left_inv T := rfl
  right_inv X := by
    rcases X with ⟨j, T⟩
    apply Sigma.ext
    · exact Fin.ext T.2
    · apply Subtype.ext
      rfl

/-- The cardinality of the union of two `q`-subsets in an overlap class. -/
theorem card_union_of_subsetOverlap
    (S : QSubset N q) (j : ℕ) (T : SubsetOverlap S j) :
    (S.1 ∪ T.1.1).card = q + (q - j) := by
  have h := Finset.card_union_add_card_inter S.1 T.1.1
  rw [S.2, T.1.2, T.2] at h
  omega

/-- The probability kernel occurring in the purity calculation: a uniform
random permutation fixes `S ∪ T` pointwise with this probability. -/
noncomputable def collisionKernel (S T : QSubset N q) : ℚ :=
  1 / (N.descFactorial ((S.1 ∪ T.1).card) : ℚ)

/-- The residual combinatorial factor in the exact purity formula. -/
noncomputable def overlapFactor (q : ℕ) : ℚ :=
  ∑ j : Fin (q + 1),
    (Nat.choose q j.1 : ℚ) / Nat.factorial (q - j.1)

/-- The row sum of the collision kernel, grouped by intersection size. -/
theorem sum_collisionKernel_row_grouped
    (S : QSubset N q) :
    ∑ T : QSubset N q, collisionKernel S T =
      ∑ j : Fin (q + 1),
        ((Nat.choose q j.1 : ℚ) *
            Nat.choose (N - q) (q - j.1)) /
          (N.descFactorial (q + (q - j.1)) : ℚ) := by
  rw [Equiv.sum_comp (qSubsetEquivOverlapSigma S)]
  rw [Fintype.sum_sigma]
  apply Fintype.sum_congr
  intro j
  simp [collisionKernel, card_union_of_subsetOverlap,
    card_subsetOverlap]

end PartialPerm
end LeanQuantumQueries.Permutation
