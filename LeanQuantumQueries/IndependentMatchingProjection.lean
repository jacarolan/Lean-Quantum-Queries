import LeanQuantumQueries.IndependentMatchingCommon

open scoped BigOperators ComplexConjugate

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Orthogonal projection onto the explicit raw common subspace.  The raw
placement table is already a finite-dimensional real inner-product space. -/
noncomputable def rawCommonPartD (u : Fin B) (f : S.RawVector) : S.RawVector :=
  (((S.rawCommonSpace u).orthogonalProjection f : S.rawCommonSpace u) :
    S.RawVector)

/-- Remainder after removing the explicit common component. -/
noncomputable def rawCommonRemainderD (u : Fin B) (f : S.RawVector) :
    S.RawVector := f - S.rawCommonPartD u f

/-- The projected component is common. -/
theorem rawCommonPartD_mem (u : Fin B) (f : S.RawVector) :
    S.rawCommonPartD u f ∈ S.rawCommonSpace u :=
  (((S.rawCommonSpace u).orthogonalProjection f : S.rawCommonSpace u)).property

/-- The remainder belongs to the orthogonal complement of the common
subspace. -/
theorem rawCommonRemainderD_mem_orthogonal
    (u : Fin B) (f : S.RawVector) :
    S.rawCommonRemainderD u f ∈ (S.rawCommonSpace u)ᗮ := by
  simpa [rawCommonRemainderD, rawCommonPartD] using
    (S.rawCommonSpace u).sub_orthogonalProjection_mem f

/-- The standard finite-product inner product is the unnormalized table
sum. -/
theorem standard_inner_eq_sum (f g : S.RawVector) :
    ⟪f, g⟫_ℝ = ∑ x, f x * g x := by
  simp [RCLike.inner_apply]

/-- Standard orthogonality implies normalized raw-table orthogonality. -/
theorem rawCommonRemainderD_rawOrthogonal
    (u : Fin B) (f : S.RawVector) :
    S.RawCommonOrthogonal u (S.rawCommonRemainderD u f) := by
  intro p hp
  have hz := S.rawCommonRemainderD_mem_orthogonal u f
  rw [Submodule.mem_orthogonal] at hz
  have hstd : ⟪p, S.rawCommonRemainderD u f⟫_ℝ = 0 := hz p hp
  have hstd' : ⟪S.rawCommonRemainderD u f, p⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hstd
  rw [S.standard_inner_eq_sum] at hstd'
  unfold RawCommonOrthogonal rawInner rawAvg
  rw [hstd']
  simp

/-- Exact common-plus-remainder decomposition. -/
theorem rawCommonPartD_add_remainder
    (u : Fin B) (f : S.RawVector) :
    S.rawCommonPartD u f + S.rawCommonRemainderD u f = f := by
  unfold rawCommonRemainderD
  abel

/-- Pythagorean identity in normalized raw-table energy. -/
theorem rawNormSq_common_decompositionD
    (u : Fin B) (f : S.RawVector) :
    S.rawNormSq f =
      S.rawNormSq (S.rawCommonPartD u f) +
        S.rawNormSq (S.rawCommonRemainderD u f) := by
  have horth := S.rawCommonRemainderD_rawOrthogonal u f
    (S.rawCommonPartD u f) (S.rawCommonPartD_mem u f)
  have horth' :
      S.rawInner (S.rawCommonPartD u f)
        (S.rawCommonRemainderD u f) = 0 := by
    unfold rawInner rawAvg at horth ⊢
    simpa [mul_comm] using horth
  rw [← S.rawCommonPartD_add_remainder u f]
  unfold rawNormSq
  rw [S.rawInner_add_left, S.rawInner_add_right,
    S.rawInner_add_right, horth, horth']
  ring

end SectorData
end IndependentMatchingBlockOccupancy
