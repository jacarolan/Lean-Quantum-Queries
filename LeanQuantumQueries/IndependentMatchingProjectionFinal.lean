import LeanQuantumQueries.IndependentMatchingCommon

open scoped BigOperators ComplexConjugate

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Euclidean realization of the raw finite table. -/
abbrev RawEuclideanF := EuclideanSpace ℝ S.RawPlacement

/-- Linear equivalence between real table functions and their Euclidean
realization. -/
noncomputable def rawEuclideanEquivF :
    S.RawVector ≃ₗ[ℝ] S.RawEuclideanF where
  toFun f := WithLp.toLp 2 f
  invFun f := WithLp.ofLp f
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

/-- Euclidean inner product is the unnormalized coordinate sum. -/
theorem rawEuclidean_inner_eq_sumF (f g : S.RawVector) :
    ⟪S.rawEuclideanEquivF f, S.rawEuclideanEquivF g⟫_ℝ =
      ∑ x, f x * g x := by
  simp [rawEuclideanEquivF, RCLike.inner_apply]

/-- Euclidean image of the explicit raw common subspace. -/
noncomputable def euclideanCommonSpaceF (u : Fin B) :
    Submodule ℝ S.RawEuclideanF :=
  (S.rawCommonSpace u).map S.rawEuclideanEquivF.toLinearMap

/-- Orthogonal projection onto the explicit common space, transported back to
raw functions. -/
noncomputable def rawCommonPartF (u : Fin B) (f : S.RawVector) : S.RawVector :=
  S.rawEuclideanEquivF.symm
    (((S.euclideanCommonSpaceF u).orthogonalProjection
      (S.rawEuclideanEquivF f) : S.euclideanCommonSpaceF u) :
        S.RawEuclideanF)

/-- Orthogonal remainder. -/
noncomputable def rawCommonRemainderF (u : Fin B) (f : S.RawVector) :
    S.RawVector := f - S.rawCommonPartF u f

/-- The projected component is in the explicit raw common subspace. -/
theorem rawCommonPartF_mem (u : Fin B) (f : S.RawVector) :
    S.rawCommonPartF u f ∈ S.rawCommonSpace u := by
  let pE : S.RawEuclideanF :=
    (((S.euclideanCommonSpaceF u).orthogonalProjection
      (S.rawEuclideanEquivF f) : S.euclideanCommonSpaceF u) :
        S.RawEuclideanF)
  have hpE : pE ∈ S.euclideanCommonSpaceF u :=
    (((S.euclideanCommonSpaceF u).orthogonalProjection
      (S.rawEuclideanEquivF f) : S.euclideanCommonSpaceF u)).property
  rcases hpE with ⟨p, hp, hpe⟩
  have hback : S.rawEuclideanEquivF.symm pE = p := by
    apply S.rawEuclideanEquivF.injective
    rw [S.rawEuclideanEquivF.apply_symm_apply]
    exact hpe.symm
  change S.rawEuclideanEquivF.symm pE ∈ S.rawCommonSpace u
  rw [hback]
  exact hp

/-- Euclidean orthogonality of the remainder. -/
theorem rawCommonRemainderF_euclidean_orthogonal
    (u : Fin B) (f : S.RawVector) :
    S.rawEuclideanEquivF (S.rawCommonRemainderF u f) ∈
      (S.euclideanCommonSpaceF u)ᗮ := by
  have h := (S.euclideanCommonSpaceF u).sub_orthogonalProjection_mem
    (S.rawEuclideanEquivF f)
  change S.rawEuclideanEquivF f -
      (((S.euclideanCommonSpaceF u).orthogonalProjection
        (S.rawEuclideanEquivF f) : S.euclideanCommonSpaceF u) :
          S.RawEuclideanF) ∈
    (S.euclideanCommonSpaceF u)ᗮ at h
  simpa [rawCommonRemainderF, rawCommonPartF] using h

/-- The remainder is orthogonal in the normalized raw inner product. -/
theorem rawCommonRemainderF_rawOrthogonal
    (u : Fin B) (f : S.RawVector) :
    S.RawCommonOrthogonal u (S.rawCommonRemainderF u f) := by
  intro p hp
  have hpE : S.rawEuclideanEquivF p ∈ S.euclideanCommonSpaceF u :=
    ⟨p, hp, rfl⟩
  have hz := S.rawCommonRemainderF_euclidean_orthogonal u f
  rw [Submodule.mem_orthogonal] at hz
  have hstd :
      ⟪S.rawEuclideanEquivF p,
        S.rawEuclideanEquivF (S.rawCommonRemainderF u f)⟫_ℝ = 0 :=
    hz _ hpE
  rw [S.rawEuclidean_inner_eq_sumF] at hstd
  have hsum :
      (∑ x, S.rawCommonRemainderF u f x * p x) = 0 := by
    simpa [mul_comm] using hstd
  unfold RawCommonOrthogonal rawInner rawAvg
  rw [hsum]
  simp

/-- Exact common-plus-remainder decomposition. -/
theorem rawCommonPartF_add_remainder
    (u : Fin B) (f : S.RawVector) :
    S.rawCommonPartF u f + S.rawCommonRemainderF u f = f := by
  unfold rawCommonRemainderF
  abel

/-- Pythagorean identity in normalized raw-table energy. -/
theorem rawNormSq_common_decompositionF
    (u : Fin B) (f : S.RawVector) :
    S.rawNormSq f =
      S.rawNormSq (S.rawCommonPartF u f) +
        S.rawNormSq (S.rawCommonRemainderF u f) := by
  have horth := S.rawCommonRemainderF_rawOrthogonal u f
    (S.rawCommonPartF u f) (S.rawCommonPartF_mem u f)
  have horth' :
      S.rawInner (S.rawCommonPartF u f)
        (S.rawCommonRemainderF u f) = 0 := by
    unfold rawInner rawAvg at horth ⊢
    simpa [mul_comm] using horth
  rw [← S.rawCommonPartF_add_remainder u f]
  unfold rawNormSq
  rw [S.rawInner_add_left, S.rawInner_add_right,
    S.rawInner_add_right, horth, horth']
  ring

end SectorData
end IndependentMatchingBlockOccupancy
