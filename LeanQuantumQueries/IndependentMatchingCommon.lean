import LeanQuantumQueries.IndependentMatchingSpaces

open scoped BigOperators InnerProductSpace

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Every term in the raw non-`u` sum is an outside generator for a complete
rooting family. -/
theorem rawOutsideSum_mem_rawOutside (u : Fin B) (i : Fin d)
    (hi : S.Complete i) : S.rawOutsideSum u i ∈ S.rawOutsideSpace u := by
  classical
  unfold rawOutsideSum
  apply Submodule.sum_mem
  intro a hmem
  apply Submodule.subset_span
  have hi' : S.compat i = S.orbit i := hi
  refine ⟨i, a, ?_, Finset.ne_of_mem_erase hmem, rfl⟩
  rw [hi']
  exact Finset.mem_of_mem_erase hmem

/-- A raw distinguished fiber is an inside generator for a complete family
whose orbit contains the distinguished block. -/
theorem rawAtU_mem_rawInside (u : Fin B) (i : Fin d)
    (hi : S.Complete i) (hui : u ∈ S.orbit i) :
    S.rawAtU u i ∈ S.rawInsideSpace u := by
  apply Submodule.subset_span
  have hi' : S.compat i = S.orbit i := hi
  refine ⟨i, ?_, rfl⟩
  rw [hi']
  exact hui

/-- The raw non-`u` sum is `1 - rawAtU`. -/
theorem rawOutsideSum_eq_one_sub_rawAtU (u : Fin B) (i : Fin d)
    (hui : u ∈ S.orbit i) :
    S.rawOutsideSum u i = (1 : S.RawVector) - S.rawAtU u i := by
  classical
  have hsum := S.sum_rawFibers_eq_one i
  rw [← Finset.sum_erase_add _ _ hui] at hsum
  simp only [rawOutsideSum, rawAtU] at hsum ⊢
  rw [← hsum]
  abel

/-- If the distinguished block is absent from a complete orbit, its raw
outside sum is the all-ones vector. -/
theorem rawOutsideSum_eq_one_of_not_mem (u : Fin B) (i : Fin d)
    (hui : u ∉ S.orbit i) :
    S.rawOutsideSum u i = (1 : S.RawVector) := by
  classical
  unfold rawOutsideSum
  rw [Finset.erase_eq_self.mpr hui]
  exact S.sum_rawFibers_eq_one i

/-- Exact raw common-direction identity for two complete families. -/
theorem rawAtU_sub_rawAtU_eq_rawOutsideSums (u : Fin B) (i j : Fin d)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    S.rawAtU u i - S.rawAtU u j =
      S.rawOutsideSum u j - S.rawOutsideSum u i := by
  rw [S.rawOutsideSum_eq_one_sub_rawAtU u i hui,
    S.rawOutsideSum_eq_one_sub_rawAtU u j huj]
  abel

/-- Difference of two complete raw `u`-fibers is exactly common. -/
theorem rawCompleteDifference_mem_inter (u : Fin B) (i j : Fin d)
    (hi : S.Complete i) (hj : S.Complete j)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    S.rawAtU u i - S.rawAtU u j ∈
      S.rawInsideSpace u ⊓ S.rawOutsideSpace u := by
  rw [Submodule.mem_inf]
  constructor
  · exact Submodule.sub_mem _
      (S.rawAtU_mem_rawInside u i hi hui)
      (S.rawAtU_mem_rawInside u j hj huj)
  · rw [S.rawAtU_sub_rawAtU_eq_rawOutsideSums u i j hui huj]
    exact Submodule.sub_mem _
      (S.rawOutsideSum_mem_rawOutside u j hj)
      (S.rawOutsideSum_mem_rawOutside u i hi)

/-- A complete raw family avoiding `u` provides the constant function in the
raw outside space. -/
theorem rawOne_mem_outside_of_complete_avoiding (u : Fin B) (h : Fin d)
    (hh : S.Complete h) (huh : u ∉ S.orbit h) :
    (1 : S.RawVector) ∈ S.rawOutsideSpace u := by
  rw [← S.rawOutsideSum_eq_one_of_not_mem u h huh]
  exact S.rawOutsideSum_mem_rawOutside u h hh

/-- If one complete family avoids `u`, each complete raw `u`-fiber is itself
exactly common. -/
theorem rawCompleteAtU_mem_inter_of_avoiding (u : Fin B) (i h : Fin d)
    (hi : S.Complete i) (hh : S.Complete h)
    (hui : u ∈ S.orbit i) (huh : u ∉ S.orbit h) :
    S.rawAtU u i ∈ S.rawInsideSpace u ⊓ S.rawOutsideSpace u := by
  rw [Submodule.mem_inf]
  constructor
  · exact S.rawAtU_mem_rawInside u i hi hui
  · have hone := S.rawOne_mem_outside_of_complete_avoiding u h hh huh
    have hout := S.rawOutsideSum_mem_rawOutside u i hi
    rw [S.rawOutsideSum_eq_one_sub_rawAtU u i hui] at hout
    have hsub := Submodule.sub_mem _ hone hout
    simpa using hsub

/-- Explicit raw vectors that must be removed as exact common directions. -/
def rawCommonGenerators (u : Fin B) : Set S.RawVector :=
  {v | ∃ i j : Fin d, S.Complete i ∧ S.Complete j ∧
      u ∈ S.orbit i ∧ u ∈ S.orbit j ∧
      v = S.rawAtU u i - S.rawAtU u j} ∪
  {v | ∃ i h : Fin d, S.Complete i ∧ S.Complete h ∧
      u ∈ S.orbit i ∧ u ∉ S.orbit h ∧ v = S.rawAtU u i}

/-- Span of the explicit exact common directions. -/
noncomputable def rawCommonSpace (u : Fin B) : Submodule ℝ S.RawVector :=
  Submodule.span ℝ (S.rawCommonGenerators u)

/-- Every explicit raw common direction really belongs to both raw spaces. -/
theorem rawCommonSpace_le_inter (u : Fin B) :
    S.rawCommonSpace u ≤ S.rawInsideSpace u ⊓ S.rawOutsideSpace u := by
  apply Submodule.span_le.2
  intro v hv
  rcases hv with hv | hv
  · rcases hv with ⟨i, j, hi, hj, hui, huj, rfl⟩
    exact S.rawCompleteDifference_mem_inter u i j hi hj hui huj
  · rcases hv with ⟨i, h, hi, hh, hui, huh, rfl⟩
    exact S.rawCompleteAtU_mem_inter_of_avoiding u i h hi hh hui huh

/-- Restricting an explicit raw common vector produces a vector in the actual
legal-table intersection. -/
theorem restrict_rawCommon_mem_inter (u : Fin B) {v : S.RawVector}
    (hv : v ∈ S.rawCommonSpace u) :
    S.restrict v ∈ S.insideSpace u ⊓ S.outsideSpace u := by
  have hv' := S.rawCommonSpace_le_inter u hv
  rw [Submodule.mem_inf] at hv' ⊢
  constructor
  · rw [← S.map_rawInside_eq_inside u]
    exact ⟨v, hv'.1, rfl⟩
  · rw [← S.map_rawOutside_eq_outside u]
    exact ⟨v, hv'.2, rfl⟩

/-- Orthogonality to the explicit raw common space, expressed using the
normalized product-table inner product. -/
def RawCommonOrthogonal (u : Fin B) (f : S.RawVector) : Prop :=
  ∀ v, v ∈ S.rawCommonSpace u → S.rawInner f v = 0

end SectorData
end IndependentMatchingBlockOccupancy
