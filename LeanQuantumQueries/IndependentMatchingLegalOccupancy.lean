import LeanQuantumQueries.IndependentMatchingGoodInner
import LeanQuantumQueries.IndependentMatchingProductOccupancyVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Sum over legal placements is bounded by the corresponding nonnegative raw
sum. -/
theorem sum_legal_le_sum_raw
    (F : S.RawPlacement → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ x : S.Placement, F x.1) ≤ ∑ x : S.RawPlacement, F x := by
  classical
  rw [S.sum_placement_eq_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset S.Legal Finset.univ)
  intro x _ _
  exact hF x

/-- A legal placement occupying `u` contributes to at least one coordinate
cylinder. -/
theorem legalOccupied_pointwise_le (u : Fin B) (f : S.RawVector)
    (x : S.Placement) :
    (if S.Occupied u x then (f x.1) ^ 2 else 0) ≤
      ∑ i ∈ S.atUIndices u,
        S.rawAtU u i x.1 * (f x.1) ^ 2 := by
  classical
  by_cases hx : S.Occupied u x
  · rcases hx with ⟨i, hi⟩
    have hiU : i ∈ S.atUIndices u := by
      apply (S.mem_atUIndices_iff u i).2
      rw [← hi]
      exact (x.1 i).2
    simp only [hx, ↓reduceIte]
    have hterm :
        (f x.1) ^ 2 = S.rawAtU u i x.1 * (f x.1) ^ 2 := by
      simp [rawAtU, rawFiber, hi]
    rw [hterm]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg
        (by simp [rawAtU, rawFiber]) (sq_nonneg _)) hiU
  · simp only [hx, ↓reduceIte]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by simp [rawAtU, rawFiber]) (sq_nonneg _)

/-- Legal occupied energy is at most the raw-cardinality multiple of the
normalized product occupied upper sum. -/
theorem occupiedEnergy_restrict_le_rawCard_mul_upper
    {u : Fin B} (c : S.OutsideCoeff u) :
    S.occupiedEnergy u (S.restrict (S.synth c.val)) ≤
      (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpper c := by
  classical
  unfold occupiedEnergy
  have hlegal :
      (∑ x : S.Placement,
        if S.Occupied u x then (S.synth c.val x.1) ^ 2 else 0) ≤
      ∑ x : S.Placement,
        ∑ i ∈ S.atUIndices u,
          S.rawAtU u i x.1 * (S.synth c.val x.1) ^ 2 := by
    exact Finset.sum_le_sum fun x _ =>
      S.legalOccupied_pointwise_le u (S.synth c.val) x
  have hraw :
      (∑ x : S.Placement,
        ∑ i ∈ S.atUIndices u,
          S.rawAtU u i x.1 * (S.synth c.val x.1) ^ 2) ≤
      ∑ x : S.RawPlacement,
        ∑ i ∈ S.atUIndices u,
          S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
    apply S.sum_legal_le_sum_raw
    intro x
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (by simp [rawAtU, rawFiber]) (sq_nonneg _)
  have hcardavg :
      (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpper c =
      ∑ x : S.RawPlacement,
        ∑ i ∈ S.atUIndices u,
          S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
    unfold rawOccupiedUpper
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ S.atUIndices u,
          (Fintype.card S.RawPlacement : ℝ) *
            S.rawAvg (fun x =>
              S.rawAtU u i x * (S.synth c.val x) ^ 2) =
          ∑ i ∈ S.atUIndices u,
            ∑ x : S.RawPlacement,
              S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact S.rawCard_mul_rawAvg _
      _ = ∑ x : S.RawPlacement,
          ∑ i ∈ S.atUIndices u,
            S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
        rw [Finset.sum_comm]
  rw [hcardavg]
  exact le_trans hlegal hraw

/-- Squared occupied energy is subadditive up to the factor two. -/
theorem occupiedEnergy_add_le_two
    (u : Fin B) (f g : S.Vector) :
    S.occupiedEnergy u (f + g) ≤
      2 * S.occupiedEnergy u f + 2 * S.occupiedEnergy u g := by
  classical
  unfold occupiedEnergy
  calc
    (∑ x, if S.Occupied u x then ((f + g) x) ^ 2 else 0) ≤
        ∑ x, if S.Occupied u x then
          (2 * (f x) ^ 2 + 2 * (g x) ^ 2) else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : S.Occupied u x
      · simp only [hx, ↓reduceIte, Pi.add_apply]
        nlinarith [sq_nonneg (f x - g x)]
      · simp [hx]
    _ = 2 * (∑ x, if S.Occupied u x then (f x) ^ 2 else 0) +
        2 * (∑ x, if S.Occupied u x then (g x) ^ 2 else 0) := by
      simp only [ite_add, ite_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]

/-- Occupied energy is at most total energy. -/
theorem occupiedEnergy_le_totalEnergy (u : Fin B) (f : S.Vector) :
    S.occupiedEnergy u f ≤ S.totalEnergy f := by
  classical
  unfold occupiedEnergy totalEnergy
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : S.Occupied u x
  · simp [hx]
  · simp [hx, sq_nonneg]

end SectorData
end IndependentMatchingBlockOccupancy
