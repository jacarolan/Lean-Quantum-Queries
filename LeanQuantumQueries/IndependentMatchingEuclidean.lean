import LeanQuantumQueries.IndependentMatchingCommon

open scoped BigOperators ComplexConjugate

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Euclidean realization of the finite raw placement table. -/
abbrev RawEuclidean := EuclideanSpace ℝ S.RawPlacement

/-- The function table and its Euclidean realization are linearly
equivalent. -/
noncomputable def rawEuclideanEquiv : S.RawVector ≃ₗ[ℝ] S.RawEuclidean where
  toFun f := WithLp.toLp 2 f
  invFun f := WithLp.ofLp f
  left_inv f := rfl
  right_inv f := rfl
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] theorem rawEuclideanEquiv_apply (f : S.RawVector) (x : S.RawPlacement) :
    WithLp.ofLp (S.rawEuclideanEquiv f) x = f x := by
  rfl

@[simp] theorem rawEuclideanEquiv_symm_apply
    (f : S.RawEuclidean) (x : S.RawPlacement) :
    S.rawEuclideanEquiv.symm f x = WithLp.ofLp f x := by
  rfl

/-- Euclidean inner product is the unnormalized finite-table sum. -/
theorem rawEuclidean_inner_eq_sum (f g : S.RawVector) :
    ⟪S.rawEuclideanEquiv f, S.rawEuclideanEquiv g⟫_ℝ =
      ∑ x, f x * g x := by
  simp [rawEuclideanEquiv, RCLike.inner_apply]

/-- The normalized raw inner product differs from the Euclidean one only by
the positive table cardinality. -/
theorem rawInner_eq_euclidean_div (f g : S.RawVector) :
    S.rawInner f g =
      ⟪S.rawEuclideanEquiv f, S.rawEuclideanEquiv g⟫_ℝ /
        (Fintype.card S.RawPlacement : ℝ) := by
  rw [S.rawEuclidean_inner_eq_sum]
  rfl

/-- Euclidean image of the explicit raw common subspace. -/
noncomputable def euclideanCommonSpace (u : Fin B) :
    Submodule ℝ S.RawEuclidean :=
  (S.rawCommonSpace u).map S.rawEuclideanEquiv.toLinearMap

/-- Orthogonal projection of a raw vector onto the explicit common space,
transported back to the function table. -/
noncomputable def rawCommonPart (u : Fin B) (f : S.RawVector) : S.RawVector :=
  S.rawEuclideanEquiv.symm
    (((S.euclideanCommonSpace u).orthogonalProjection
      (S.rawEuclideanEquiv f) : S.euclideanCommonSpace u) :
        S.RawEuclidean)

/-- Remainder after removing the raw common part. -/
noncomputable def rawCommonRemainder (u : Fin B) (f : S.RawVector) :
    S.RawVector := f - S.rawCommonPart u f

/-- The projected part lies in the explicit raw common space. -/
theorem rawCommonPart_mem (u : Fin B) (f : S.RawVector) :
    S.rawCommonPart u f ∈ S.rawCommonSpace u := by
  let pE : S.RawEuclidean :=
    (((S.euclideanCommonSpace u).orthogonalProjection
      (S.rawEuclideanEquiv f) : S.euclideanCommonSpace u) :
        S.RawEuclidean)
  have hpE : pE ∈ S.euclideanCommonSpace u :=
    (((S.euclideanCommonSpace u).orthogonalProjection
      (S.rawEuclideanEquiv f) : S.euclideanCommonSpace u)).property
  rcases hpE with ⟨p, hp, hpe⟩
  have hback : S.rawEuclideanEquiv.symm pE = p := by
    apply S.rawEuclideanEquiv.injective
    rw [S.rawEuclideanEquiv.apply_symm_apply]
    exact hpe.symm
  change S.rawEuclideanEquiv.symm pE ∈ S.rawCommonSpace u
  rw [hback]
  exact hp

/-- The remainder is Euclidean-orthogonal to the explicit common space. -/
theorem rawCommonRemainder_euclidean_orthogonal
    (u : Fin B) (f : S.RawVector) :
    S.rawEuclideanEquiv (S.rawCommonRemainder u f) ∈
      (S.euclideanCommonSpace u)ᗮ := by
  have h := (S.euclideanCommonSpace u).sub_orthogonalProjection_mem
    (S.rawEuclideanEquiv f)
  change S.rawEuclideanEquiv f -
      (((S.euclideanCommonSpace u).orthogonalProjection
        (S.rawEuclideanEquiv f) : S.euclideanCommonSpace u) :
          S.RawEuclidean) ∈
    (S.euclideanCommonSpace u)ᗮ at h
  simpa [rawCommonRemainder, rawCommonPart] using h

/-- The remainder is orthogonal in the normalized raw inner product. -/
theorem rawCommonRemainder_rawOrthogonal
    (u : Fin B) (f : S.RawVector) :
    S.RawCommonOrthogonal u (S.rawCommonRemainder u f) := by
  intro p hp
  have hpE : S.rawEuclideanEquiv p ∈ S.euclideanCommonSpace u :=
    ⟨p, hp, rfl⟩
  have hzE := S.rawCommonRemainder_euclidean_orthogonal u f
  rw [Submodule.mem_orthogonal] at hzE
  have hinner :
      ⟪S.rawEuclideanEquiv p,
        S.rawEuclideanEquiv (S.rawCommonRemainder u f)⟫_ℝ = 0 :=
    hzE _ hpE
  have hinner' :
      ⟪S.rawEuclideanEquiv (S.rawCommonRemainder u f),
        S.rawEuclideanEquiv p⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hinner
  rw [S.rawInner_eq_euclidean_div, hinner']
  simp

/-- Exact decomposition into common and orthogonal parts. -/
theorem rawCommonPart_add_remainder
    (u : Fin B) (f : S.RawVector) :
    S.rawCommonPart u f + S.rawCommonRemainder u f = f := by
  unfold rawCommonRemainder
  abel

/-- Pythagorean identity for the normalized raw norm. -/
theorem rawNormSq_common_decomposition
    (u : Fin B) (f : S.RawVector) :
    S.rawNormSq f =
      S.rawNormSq (S.rawCommonPart u f) +
        S.rawNormSq (S.rawCommonRemainder u f) := by
  have horth := S.rawCommonRemainder_rawOrthogonal u f
    (S.rawCommonPart u f) (S.rawCommonPart_mem u f)
  rw [← S.rawCommonPart_add_remainder u f]
  unfold rawNormSq
  rw [S.rawInner_add_left, S.rawInner_add_right,
    S.rawInner_add_right]
  have horth' :
      S.rawInner (S.rawCommonPart u f)
        (S.rawCommonRemainder u f) = 0 := by
    unfold rawInner rawAvg at horth ⊢
    simpa [mul_comm] using horth
  rw [horth, horth']
  ring

end SectorData
end IndependentMatchingBlockOccupancy
