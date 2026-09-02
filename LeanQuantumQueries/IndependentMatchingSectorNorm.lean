import LeanQuantumQueries.IndependentMatchingQuotientEnergyVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Euclidean norm on the legal placement table, written directly from the
finite sum used in the theorem. -/
noncomputable def legalL2Norm (f : S.Vector) : ℝ :=
  Real.sqrt (S.totalEnergy f)

/-- Projection onto placements occupying the distinguished block. -/
def occupiedPart (u : Fin B) (f : S.Vector) : S.Vector :=
  fun x => if S.Occupied u x then f x else 0

/-- Squared norm of the occupied projection. -/
theorem totalEnergy_occupiedPart (u : Fin B) (f : S.Vector) :
    S.totalEnergy (S.occupiedPart u f) = S.occupiedEnergy u f := by
  classical
  unfold totalEnergy occupiedEnergy occupiedPart
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S.Occupied u x <;> simp [hx]

/-- The legal `L²` norm is nonnegative and squares to total energy. -/
theorem legalL2Norm_nonneg (f : S.Vector) :
    0 ≤ S.legalL2Norm f := Real.sqrt_nonneg _

theorem legalL2Norm_sq (f : S.Vector) :
    (S.legalL2Norm f) ^ 2 = S.totalEnergy f := by
  unfold legalL2Norm
  rw [sq_sqrt]
  unfold totalEnergy
  positivity

/-- Norm of the occupied projection squares to occupied energy. -/
theorem legalL2Norm_occupiedPart_sq (u : Fin B) (f : S.Vector) :
    (S.legalL2Norm (S.occupiedPart u f)) ^ 2 =
      S.occupiedEnergy u f := by
  rw [S.legalL2Norm_sq, S.totalEnergy_occupiedPart]

/-- Square-root form of the sector quotient estimate.  The numerical constant
`39` is valid because `1504 < 39²`. -/
theorem quotient_occupiedPart_norm_bound
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    Real.sqrt (q : ℝ) * S.legalL2Norm (S.occupiedPart u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * S.legalL2Norm f := by
  have henergy := S.quotient_occupiedEnergy_bound_for_vectorV H hlarge hf
  have hq0 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have ht0 : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
  have hocc0 := S.legalL2Norm_nonneg (S.occupiedPart u f)
  have hnorm0 := S.legalL2Norm_nonneg f
  have hsqrtq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hsqrtt : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hocc := S.legalL2Norm_occupiedPart_sq u f
  have htot := S.legalL2Norm_sq f
  have hsquare :
      (Real.sqrt (q : ℝ) * S.legalL2Norm (S.occupiedPart u f)) ^ 2 ≤
        (39 * (t : ℝ) * Real.sqrt (t : ℝ) * S.legalL2Norm f) ^ 2 := by
    nlinarith
  nlinarith

/-- Divided form, convenient when comparing with `N^{-1/4}`. -/
theorem quotient_occupiedPart_norm_bound_div
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (hq : 0 < q)
    (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    S.legalL2Norm (S.occupiedPart u f) ≤
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        Real.sqrt (q : ℝ)) * S.legalL2Norm f := by
  have h := S.quotient_occupiedPart_norm_bound H hlarge hf
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hq)
  apply (le_div_iff₀ hsqrt).2
  calc
    Real.sqrt (q : ℝ) * S.legalL2Norm (S.occupiedPart u f) ≤
        39 * (t : ℝ) * Real.sqrt (t : ℝ) * S.legalL2Norm f := h
    _ = Real.sqrt (q : ℝ) *
        ((39 * (t : ℝ) * Real.sqrt (t : ℝ) /
          Real.sqrt (q : ℝ)) * S.legalL2Norm f) := by
      field_simp [ne_of_gt hsqrt]
      ring

end SectorData
end IndependentMatchingBlockOccupancy
