import LeanQuantumQueries.IndependentMatchingSectorNormFinal
import LeanQuantumQueries.IndependentMatchingNumericsFromClassesFinal

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Real fourth root of a natural size parameter. -/
noncomputable def fourthRootNatF (N : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (N : ℝ))

/-- The fourth root of a square is the square root of its nonnegative base. -/
theorem fourthRootNatF_sq (Q : ℕ) :
    S.fourthRootNatF (Q ^ 2) = Real.sqrt (Q : ℝ) := by
  unfold fourthRootNatF
  have hQ : 0 ≤ (Q : ℝ) := by positivity
  have hcast : ((Q ^ 2 : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by
    norm_num
  rw [hcast, Real.sqrt_sq_eq_abs, abs_of_nonneg hQ]

/-- User-facing finite-sector norm bound derived from eligible endpoint-type
classes rather than a separate numerical hypothesis. -/
theorem quotient_occupiedPart_norm_from_classesF
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    S.legalL2NormF (S.occupiedPartF u f) ≤
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        Real.sqrt ((8 * q : ℕ) : ℝ)) * S.legalL2NormF f := by
  have Hnum : S.SectorNumericsF (8 * q) t :=
    S.sectorNumericsF_of_eligibleClasses H
  have hlarge' : 32 * t ^ 3 ≤ 8 * q := by omega
  have hq : 0 < 8 * q := by
    have ht : 1 ≤ t := H.t_pos
    omega
  exact S.quotient_occupiedPart_norm_bound_divF hq Hnum hlarge' hf

/-- Exact `N^{-1/4}` form when the ambient size is the square of the effective
block scale. -/
theorem quotient_occupiedPart_norm_fourthRootF
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    S.legalL2NormF (S.occupiedPartF u f) ≤
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        S.fourthRootNatF ((8 * q) ^ 2)) * S.legalL2NormF f := by
  rw [S.fourthRootNatF_sq (8 * q)]
  exact S.quotient_occupiedPart_norm_from_classesF H hlarge hf

end SectorData
end IndependentMatchingBlockOccupancy
