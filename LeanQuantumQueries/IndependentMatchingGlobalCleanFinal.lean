import LeanQuantumQueries.IndependentMatchingSectorCorollaryFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy

/-- A finite sector with coordinate and block counts hidden. -/
structure PackedSectorF where
  d : ℕ
  B : ℕ
  data : SectorData d B

namespace PackedSectorF

abbrev Vector (S : PackedSectorF) := S.data.Vector
abbrev Block (S : PackedSectorF) := Fin S.B

end PackedSectorF

variable {ι : Type*} [Fintype ι]

/-- Orthogonal direct sum of legal sector tables. -/
abbrev GlobalVectorF (S : ι → PackedSectorF) :=
  ∀ s, (S s).Vector

/-- Sum of sector squared norms. -/
noncomputable def globalTotalEnergyF (S : ι → PackedSectorF)
    (f : GlobalVectorF S) : ℝ :=
  ∑ s, (S s).data.totalEnergy (f s)

/-- Sum of sector occupied energies. -/
noncomputable def globalOccupiedEnergyF (S : ι → PackedSectorF)
    (u : ∀ s, (S s).Block) (f : GlobalVectorF S) : ℝ :=
  ∑ s, (S s).data.occupiedEnergy (u s) (f s)

/-- Sectorwise occupied projection. -/
def globalOccupiedPartF (S : ι → PackedSectorF)
    (u : ∀ s, (S s).Block) (f : GlobalVectorF S) :
    GlobalVectorF S :=
  fun s => (S s).data.occupiedPartF (u s) (f s)

/-- Direct-sum Euclidean norm. -/
noncomputable def globalL2NormF (S : ι → PackedSectorF)
    (f : GlobalVectorF S) : ℝ :=
  Real.sqrt (globalTotalEnergyF S f)

/-- Sectorwise quotient condition. -/
def InGlobalOutsideQuotientF (S : ι → PackedSectorF)
    (u : ∀ s, (S s).Block) (f : GlobalVectorF S) : Prop :=
  ∀ s, (S s).data.InOutsideQuotient (u s) (f s)

/-- Fourth root independent of any sector. -/
noncomputable def fourthRootNatGlobalF (N : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (N : ℝ))

/-- Fourth root of a square. -/
theorem fourthRootNatGlobalF_sq (Q : ℕ) :
    fourthRootNatGlobalF (Q ^ 2) = Real.sqrt (Q : ℝ) := by
  unfold fourthRootNatGlobalF
  have hQ : 0 ≤ (Q : ℝ) := by positivity
  have hcast : ((Q ^ 2 : ℕ) : ℝ) = (Q : ℝ) ^ 2 := by
    norm_num
  rw [hcast, Real.sqrt_sq_eq_abs, abs_of_nonneg hQ]

/-- Global total energy is nonnegative. -/
theorem globalTotalEnergyF_nonneg (S : ι → PackedSectorF)
    (f : GlobalVectorF S) : 0 ≤ globalTotalEnergyF S f := by
  unfold globalTotalEnergyF
  apply Finset.sum_nonneg
  intro s _
  unfold SectorData.totalEnergy
  positivity

/-- Energy of the global occupied projection. -/
theorem globalTotalEnergyF_occupiedPart
    (S : ι → PackedSectorF) (u : ∀ s, (S s).Block)
    (f : GlobalVectorF S) :
    globalTotalEnergyF S (globalOccupiedPartF S u f) =
      globalOccupiedEnergyF S u f := by
  unfold globalTotalEnergyF globalOccupiedEnergyF globalOccupiedPartF
  apply Finset.sum_congr rfl
  intro s _
  exact (S s).data.totalEnergy_occupiedPartF (u s) (f s)

/-- Square of the global norm. -/
theorem globalL2NormF_sq (S : ι → PackedSectorF)
    (f : GlobalVectorF S) :
    (globalL2NormF S f) ^ 2 = globalTotalEnergyF S f := by
  unfold globalL2NormF
  rw [sq_sqrt]
  exact globalTotalEnergyF_nonneg S f

/-- Sectorwise squared estimates aggregate with no loss. -/
theorem global_occupiedEnergy_boundF
    (S : ι → PackedSectorF) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVectorF S}
    (hf : InGlobalOutsideQuotientF S u f) :
    ((8 * q : ℕ) : ℝ) * globalOccupiedEnergyF S u f ≤
      1504 * (t : ℝ) ^ 3 * globalTotalEnergyF S f := by
  unfold globalOccupiedEnergyF globalTotalEnergyF
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have Hnum : (S s).data.SectorNumericsF (8 * q) t :=
    (S s).data.sectorNumericsF_of_eligibleClasses (H s)
  have hlarge' : 32 * t ^ 3 ≤ 8 * q := by omega
  exact (S s).data.quotient_occupiedEnergy_bound_for_vectorF
    Hnum hlarge' (hf s)

/-- Global norm estimate. -/
theorem global_occupiedPart_norm_boundF
    (S : ι → PackedSectorF) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVectorF S}
    (hf : InGlobalOutsideQuotientF S u f) :
    Real.sqrt (((8 * q : ℕ) : ℝ)) *
        globalL2NormF S (globalOccupiedPartF S u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2NormF S f := by
  let x : ℝ := Real.sqrt (((8 * q : ℕ) : ℝ)) *
    globalL2NormF S (globalOccupiedPartF S u f)
  let y : ℝ := 39 * (t : ℝ) * Real.sqrt (t : ℝ) *
    globalL2NormF S f
  have henergy := global_occupiedEnergy_boundF S u H hlarge hf
  have hsqrtq :
      (Real.sqrt (((8 * q : ℕ) : ℝ))) ^ 2 =
        (((8 * q : ℕ) : ℝ)) := by
    rw [sq_sqrt]
    positivity
  have hsqrtt : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hocc :
      (globalL2NormF S (globalOccupiedPartF S u f)) ^ 2 =
        globalOccupiedEnergyF S u f := by
    rw [globalL2NormF_sq, globalTotalEnergyF_occupiedPart]
  have htot := globalL2NormF_sq S f
  have hx : 0 ≤ x := by unfold x; positivity
  have hy : 0 ≤ y := by unfold y; positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by
    unfold x y
    rw [mul_pow, hsqrtq, hocc]
    rw [show
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2NormF S f) ^ 2 =
        1521 * (t : ℝ) ^ 3 * globalTotalEnergyF S f by
      rw [mul_pow, mul_pow, mul_pow, hsqrtt, htot]
      ring]
    have htotal := globalTotalEnergyF_nonneg S f
    exact le_trans henergy (by
      have ht : 0 ≤ (t : ℝ) ^ 3 := by positivity
      nlinarith)
  apply le_of_not_gt
  intro hyx
  have hxpos : 0 < x := lt_of_le_of_lt hy hyx
  have hsq' : y ^ 2 < x ^ 2 := by
    have hprod : 0 < (x - y) * (x + y) :=
      mul_pos (sub_pos.mpr hyx) (add_pos_of_pos_of_nonneg hxpos hy)
    nlinarith
  exact (not_lt_of_ge hsq) hsq'

/-- Exact global `N^{-1/4}` form for `N=(8q)^2`. -/
theorem global_occupiedPart_norm_fourthRootF
    (S : ι → PackedSectorF) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVectorF S}
    (hf : InGlobalOutsideQuotientF S u f) :
    fourthRootNatGlobalF ((8 * q) ^ 2) *
        globalL2NormF S (globalOccupiedPartF S u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2NormF S f := by
  rw [fourthRootNatGlobalF_sq (8 * q)]
  exact global_occupiedPart_norm_boundF S u H hlarge hf

end IndependentMatchingBlockOccupancy
