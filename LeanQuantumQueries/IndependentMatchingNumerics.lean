import LeanQuantumQueries.IndependentMatchingMeansVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Numerical consequences that will be proved from the concrete block-orbit
construction.  This is a predicate, not additional sector data. -/
structure SectorNumerics (q t : ℕ) : Prop where
  t_pos : 1 ≤ t
  coord_le : d ≤ t
  orbit_lower : ∀ i, q ≤ 8 * (S.orbit i).card
  incomplete_gap : ∀ (u : Fin B) i, ¬ S.Complete i →
    (S.orbit i).card ≤ 8 * (S.missingValues u i).card

/-- Coordinates whose orbit contains the distinguished block. -/
def atUIndices (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => u ∈ S.orbit i

/-- Complete coordinates whose orbit contains the distinguished block. -/
def completeAtUIndices (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => S.Complete i ∧ u ∈ S.orbit i

/-- Structurally incomplete coordinates. -/
def incompleteIndices : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i

/-- Incomplete coordinates whose orbit contains the distinguished block. -/
def incompleteAtUIndices (u : Fin B) : Finset (Fin d) :=
  Finset.univ.filter fun i => ¬ S.Complete i ∧ u ∈ S.orbit i

@[simp] theorem mem_atUIndices_iff (u : Fin B) (i : Fin d) :
    i ∈ S.atUIndices u ↔ u ∈ S.orbit i := by
  simp [atUIndices]

@[simp] theorem mem_completeAtUIndices_iff (u : Fin B) (i : Fin d) :
    i ∈ S.completeAtUIndices u ↔ S.Complete i ∧ u ∈ S.orbit i := by
  simp [completeAtUIndices]

@[simp] theorem mem_incompleteIndices_iff (i : Fin d) :
    i ∈ S.incompleteIndices ↔ ¬ S.Complete i := by
  simp [incompleteIndices]

@[simp] theorem mem_incompleteAtUIndices_iff (u : Fin B) (i : Fin d) :
    i ∈ S.incompleteAtUIndices u ↔ ¬ S.Complete i ∧ u ∈ S.orbit i := by
  simp [incompleteAtUIndices]

/-- Mean of one coefficient row. -/
noncomputable def rowMean {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ := S.coordAvg i (c.val i)

/-- Variance of one centered coefficient row. -/
noncomputable def rowVariance {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : ℝ :=
  S.rawNormSq (S.lift i (S.centered i (c.val i)))

/-- Sum of all centered row variances. -/
noncomputable def totalVariance {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i, S.rowVariance c i

/-- Product-table occupied-energy upper sum. -/
noncomputable def rawOccupiedUpper {u : Fin B} (c : S.OutsideCoeff u) : ℝ :=
  ∑ i ∈ S.atUIndices u,
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)

/-- Each row variance is nonnegative. -/
theorem rowVariance_nonneg {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) : 0 ≤ S.rowVariance c i := by
  rw [rowVariance, S.rawNormSq_lift]
  unfold coordAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · positivity

/-- Total variance is nonnegative. -/
theorem totalVariance_nonneg {u : Fin B} (c : S.OutsideCoeff u) :
    0 ≤ S.totalVariance c := by
  unfold totalVariance
  exact Finset.sum_nonneg fun i _ => S.rowVariance_nonneg c i

/-- Exact norm decomposition in row notation. -/
theorem rawNormSq_synth_eq_mean_variance {u : Fin B}
    (c : S.OutsideCoeff u) :
    S.rawNormSq (S.synth c.val) =
      (S.totalMean c.val) ^ 2 + S.totalVariance c := by
  exact S.rawNormSq_synth c.val

/-- Variance over any coordinate subset is at most total variance. -/
theorem sum_rowVariance_le_total {u : Fin B}
    (c : S.OutsideCoeff u) (I : Finset (Fin d)) :
    (∑ i ∈ I, S.rowVariance c i) ≤ S.totalVariance c := by
  unfold totalVariance
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  exact S.rowVariance_nonneg c i

/-- Every coordinate subset has cardinality at most `t`. -/
theorem card_indexSet_le_t {q t : ℕ} (H : S.SectorNumerics q t)
    (I : Finset (Fin d)) : I.card ≤ t :=
  le_trans (Finset.card_le_univ I) H.coord_le

end SectorData
end IndependentMatchingBlockOccupancy
