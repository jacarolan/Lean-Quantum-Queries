import LeanQuantumQueries.IndependentMatchingMeansFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Numerical consequences proved by the concrete block-orbit construction.
This is a proposition about existing sector data, not additional data. -/
structure SectorNumericsF (q t : ℕ) : Prop where
  t_pos : 1 ≤ t
  coord_le : d ≤ t
  orbit_lower : ∀ i, q ≤ 8 * (S.orbit i).card
  incomplete_gap : ∀ (u : Fin B) i, ¬ S.Complete i →
    (S.orbit i).card ≤ 8 * (S.missingValues u i).card

/-- Coordinates whose orbit contains `u`. -/
def atUIndicesF (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => u ∈ S.orbit i

/-- Complete coordinates whose orbit contains `u`. -/
def completeAtUIndicesF (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => S.Complete i ∧ u ∈ S.orbit i

/-- Incomplete coordinates. -/
def incompleteIndicesF : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i

/-- Incomplete coordinates whose orbit contains `u`. -/
def incompleteAtUIndicesF (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i ∧ u ∈ S.orbit i

@[simp] theorem mem_atUIndicesF_iff (u : Fin B) (i : Fin d) :
    i ∈ S.atUIndicesF u ↔ u ∈ S.orbit i := by
  simp [atUIndicesF]

@[simp] theorem mem_completeAtUIndicesF_iff (u : Fin B) (i : Fin d) :
    i ∈ S.completeAtUIndicesF u ↔ S.Complete i ∧ u ∈ S.orbit i := by
  simp [completeAtUIndicesF]

@[simp] theorem mem_incompleteIndicesF_iff (i : Fin d) :
    i ∈ S.incompleteIndicesF ↔ ¬ S.Complete i := by
  simp [incompleteIndicesF]

@[simp] theorem mem_incompleteAtUIndicesF_iff (u : Fin B) (i : Fin d) :
    i ∈ S.incompleteAtUIndicesF u ↔ ¬ S.Complete i ∧ u ∈ S.orbit i := by
  simp [incompleteAtUIndicesF]

/-- Mean of one coefficient row. -/
noncomputable def rowMeanF {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ := S.coordAvg i (c.val i)

/-- Variance of one centered row. -/
noncomputable def rowVarianceF {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ :=
  S.rawNormSq (S.lift i (S.centered i (c.val i)))

/-- Sum of all centered row variances. -/
noncomputable def totalVarianceF {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i, S.rowVarianceF c i

/-- Product-table upper sum for occupation of `u`. -/
noncomputable def rawOccupiedUpperF {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i ∈ S.atUIndicesF u,
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)

/-- Row and total variance are nonnegative. -/
theorem rowVarianceF_nonneg {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : 0 ≤ S.rowVarianceF c i := by
  rw [rowVarianceF, S.rawNormSq_lift]
  unfold coordAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · positivity

theorem totalVarianceF_nonneg {u : Fin B} (c : S.OutsideCoeff u) :
    0 ≤ S.totalVarianceF c := by
  unfold totalVarianceF
  exact Finset.sum_nonneg fun i _ => S.rowVarianceF_nonneg c i

/-- Exact additive norm decomposition. -/
theorem rawNormSq_synth_eq_mean_varianceF {u : Fin B}
    (c : S.OutsideCoeff u) :
    S.rawNormSq (S.synth c.val) =
      (S.totalMean c.val) ^ 2 + S.totalVarianceF c := by
  exact S.rawNormSq_synth c.val

/-- Variance over a subset is at most total variance. -/
theorem sum_rowVarianceF_le_total {u : Fin B}
    (c : S.OutsideCoeff u) (I : Finset (Fin d)) :
    (∑ i ∈ I, S.rowVarianceF c i) ≤ S.totalVarianceF c := by
  unfold totalVarianceF
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  exact S.rowVarianceF_nonneg c i

/-- Every coordinate subset has at most `t` elements. -/
theorem card_indexSetF_le_t {q t : ℕ} (H : S.SectorNumericsF q t)
    (I : Finset (Fin d)) : I.card ≤ t :=
  le_trans (Finset.card_le_univ I) H.coord_le

end SectorData
end IndependentMatchingBlockOccupancy
