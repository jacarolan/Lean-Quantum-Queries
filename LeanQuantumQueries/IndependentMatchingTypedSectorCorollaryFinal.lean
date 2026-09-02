import LeanQuantumQueries.IndependentMatchingTypedSectorFinal
import LeanQuantumQueries.IndependentMatchingSectorNormFinal

namespace IndependentMatchingBlockOccupancy
namespace TypedSectorInputF

variable {d q : ℕ} (X : TypedSectorInputF d q)

/-- Concrete typed-sector squared occupied-energy estimate. -/
theorem quotient_occupiedEnergy_boundF
    {t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {u : Fin (8 * q)} {f : (X.sectorDataF).Vector}
    (hf : (X.sectorDataF).InOutsideQuotient u f) :
    ((8 * q : ℕ) : ℝ) *
        (X.sectorDataF).occupiedEnergy u f ≤
      1504 * (t : ℝ) ^ 3 *
        (X.sectorDataF).totalEnergy f := by
  have H := X.sectorNumericsF ht hdt
  have hlarge' : 32 * t ^ 3 ≤ 8 * q := by omega
  exact (X.sectorDataF).quotient_occupiedEnergy_bound_for_vectorF
    H hlarge' hf

/-- Concrete typed-sector norm estimate. -/
theorem quotient_occupiedPart_norm_boundF
    {t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {u : Fin (8 * q)} {f : (X.sectorDataF).Vector}
    (hf : (X.sectorDataF).InOutsideQuotient u f) :
    Real.sqrt (((8 * q : ℕ) : ℝ)) *
        (X.sectorDataF).legalL2NormF
          ((X.sectorDataF).occupiedPartF u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        (X.sectorDataF).legalL2NormF f := by
  have H := X.sectorNumericsF ht hdt
  have hlarge' : 32 * t ^ 3 ≤ 8 * q := by omega
  exact (X.sectorDataF).quotient_occupiedPart_norm_boundF
    H hlarge' hf

/-- Exact fourth-root form with ambient size `N=(8q)^2`. -/
theorem quotient_occupiedPart_norm_fourthRootF
    {t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {u : Fin (8 * q)} {f : (X.sectorDataF).Vector}
    (hf : (X.sectorDataF).InOutsideQuotient u f) :
    (X.sectorDataF).fourthRootNatF ((8 * q) ^ 2) *
        (X.sectorDataF).legalL2NormF
          ((X.sectorDataF).occupiedPartF u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        (X.sectorDataF).legalL2NormF f := by
  rw [(X.sectorDataF).fourthRootNatF_sq (8 * q)]
  exact X.quotient_occupiedPart_norm_boundF ht hdt hlarge hf

end TypedSectorInputF
end IndependentMatchingBlockOccupancy
