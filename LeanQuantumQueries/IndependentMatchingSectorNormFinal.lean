import LeanQuantumQueries.IndependentMatchingQuotientEnergyFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Euclidean norm on the legal placement table. -/
noncomputable def legalL2NormF (f : S.Vector) : ℝ :=
  Real.sqrt (S.totalEnergy f)

/-- Projection onto legal placements occupying `u`. -/
def occupiedPartF (u : Fin B) (f : S.Vector) : S.Vector :=
  fun x => if S.Occupied u x then f x else 0

/-- Occupied projection energy. -/
theorem totalEnergy_occupiedPartF (u : Fin B) (f : S.Vector) :
    S.totalEnergy (S.occupiedPartF u f) = S.occupiedEnergy u f := by
  classical
  unfold totalEnergy occupiedEnergy occupiedPartF
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S.Occupied u x <;> simp [hx]

/-- Basic norm identities. -/
theorem legalL2NormF_nonneg (f : S.Vector) :
    0 ≤ S.legalL2NormF f := Real.sqrt_nonneg _

theorem legalL2NormF_sq (f : S.Vector) :
    (S.legalL2NormF f) ^ 2 = S.totalEnergy f := by
  unfold legalL2NormF
  rw [sq_sqrt]
  unfold totalEnergy
  positivity

theorem legalL2NormF_occupiedPart_sq (u : Fin B) (f : S.Vector) :
    (S.legalL2NormF (S.occupiedPartF u f)) ^ 2 =
      S.occupiedEnergy u f := by
  rw [S.legalL2NormF_sq, S.totalEnergy_occupiedPartF]

/-- Square-root form of the legal quotient occupancy estimate. -/
theorem quotient_occupiedPart_norm_boundF
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    Real.sqrt (q : ℝ) * S.legalL2NormF (S.occupiedPartF u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * S.legalL2NormF f := by
  let x : ℝ := Real.sqrt (q : ℝ) *
    S.legalL2NormF (S.occupiedPartF u f)
  let y : ℝ := 39 * (t : ℝ) * Real.sqrt (t : ℝ) *
    S.legalL2NormF f
  have henergy := S.quotient_occupiedEnergy_bound_for_vectorF H hlarge hf
  have hsqrtq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hsqrtt : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hocc := S.legalL2NormF_occupiedPart_sq u f
  have htot := S.legalL2NormF_sq f
  have hx : 0 ≤ x := by
    unfold x
    positivity
  have hy : 0 ≤ y := by
    unfold y
    positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by
    unfold x y
    rw [mul_pow, hsqrtq, hocc]
    rw [show
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) * S.legalL2NormF f) ^ 2 =
        1521 * (t : ℝ) ^ 3 * S.totalEnergy f by
      rw [mul_pow, mul_pow, mul_pow, hsqrtt, htot]
      ring]
    have htotal : 0 ≤ S.totalEnergy f := by
      unfold totalEnergy
      positivity
    exact le_trans henergy (by
      have ht : 0 ≤ (t : ℝ) ^ 3 := by positivity
      nlinarith)
  apply le_of_not_gt
  intro hyx
  have hxpos : 0 < x := lt_of_le_of_lt hy hyx
  have hprod : 0 < (x - y) * (x + y) := by
    apply mul_pos
    · exact sub_pos.mpr hyx
    · exact add_pos_of_pos_of_nonneg hxpos hy
  have hsquarelt : y ^ 2 < x ^ 2 := by
    nlinarith
  exact (not_lt_of_ge hsq) hsquarelt

/-- Divided form used for the `N^{-1/4}` corollary. -/
theorem quotient_occupiedPart_norm_bound_divF
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (hq : 0 < q)
    (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    S.legalL2NormF (S.occupiedPartF u f) ≤
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        Real.sqrt (q : ℝ)) * S.legalL2NormF f := by
  have h := S.quotient_occupiedPart_norm_boundF H hlarge hf
  have hsqrt : 0 < Real.sqrt (q : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hq)
  rw [show
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) /
        Real.sqrt (q : ℝ)) * S.legalL2NormF f =
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        S.legalL2NormF f) / Real.sqrt (q : ℝ) by ring]
  apply (le_div_iff₀ hsqrt).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

end SectorData
end IndependentMatchingBlockOccupancy
