import LeanQuantumQueries.IndependentMatchingSectorCorollaryFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy

/-- A sector with its finite coordinate and block counts hidden existentially. -/
structure PackedSector where
  d : ℕ
  B : ℕ
  data : SectorData d B

namespace PackedSector

/-- Legal vectors in a packed sector. -/
abbrev Vector (S : PackedSector) := S.data.Vector

/-- A distinguished local block in a packed sector. -/
abbrev Block (S : PackedSector) := Fin S.B

end PackedSector

variable {ι : Type*} [Fintype ι]

/-- Orthogonal direct sum of legal sector tables, represented as a dependent
finite product. -/
abbrev GlobalVector (S : ι → PackedSector) :=
  ∀ s, (S s).Vector

/-- Sum of sector squared norms. -/
noncomputable def globalTotalEnergy (S : ι → PackedSector)
    (f : GlobalVector S) : ℝ :=
  ∑ s, (S s).data.totalEnergy (f s)

/-- Sum of sector occupied energies. -/
noncomputable def globalOccupiedEnergy (S : ι → PackedSector)
    (u : ∀ s, (S s).Block) (f : GlobalVector S) : ℝ :=
  ∑ s, (S s).data.occupiedEnergy (u s) (f s)

/-- Sectorwise occupied projection. -/
def globalOccupiedPart (S : ι → PackedSector)
    (u : ∀ s, (S s).Block) (f : GlobalVector S) :
    GlobalVector S :=
  fun s => (S s).data.occupiedPartF (u s) (f s)

/-- Direct-sum Euclidean norm. -/
noncomputable def globalL2Norm (S : ι → PackedSector)
    (f : GlobalVector S) : ℝ :=
  Real.sqrt (globalTotalEnergy S f)

/-- Sectorwise legal quotient condition. -/
def InGlobalOutsideQuotient (S : ι → PackedSector)
    (u : ∀ s, (S s).Block) (f : GlobalVector S) : Prop :=
  ∀ s, (S s).data.InOutsideQuotient (u s) (f s)

/-- Total energy is nonnegative. -/
theorem globalTotalEnergy_nonneg (S : ι → PackedSector)
    (f : GlobalVector S) : 0 ≤ globalTotalEnergy S f := by
  unfold globalTotalEnergy
  apply Finset.sum_nonneg
  intro s _
  unfold SectorData.totalEnergy
  positivity

/-- Global occupied projection has the summed occupied energy. -/
theorem globalTotalEnergy_occupiedPart
    (S : ι → PackedSector) (u : ∀ s, (S s).Block)
    (f : GlobalVector S) :
    globalTotalEnergy S (globalOccupiedPart S u f) =
      globalOccupiedEnergy S u f := by
  unfold globalTotalEnergy globalOccupiedEnergy globalOccupiedPart
  apply Finset.sum_congr rfl
  intro s _
  exact (S s).data.totalEnergy_occupiedPartF (u s) (f s)

/-- Global norm square. -/
theorem globalL2Norm_sq (S : ι → PackedSector)
    (f : GlobalVector S) :
    (globalL2Norm S f) ^ 2 = globalTotalEnergy S f := by
  unfold globalL2Norm
  rw [sq_sqrt]
  exact globalTotalEnergy_nonneg S f

/-- Sectorwise squared estimates sum with no loss. -/
theorem global_occupiedEnergy_bound
    (S : ι → PackedSector) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVector S}
    (hf : InGlobalOutsideQuotient S u f) :
    ((8 * q : ℕ) : ℝ) * globalOccupiedEnergy S u f ≤
      1504 * (t : ℝ) ^ 3 * globalTotalEnergy S f := by
  unfold globalOccupiedEnergy globalTotalEnergy
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have Hnum : (S s).data.SectorNumericsF (8 * q) t :=
    (S s).data.sectorNumericsF_of_eligibleClasses (H s)
  have hlarge' : 32 * t ^ 3 ≤ 8 * q := by omega
  exact (S s).data.quotient_occupiedEnergy_bound_for_vectorF
    Hnum hlarge' (hf s)

/-- Global norm form. -/
theorem global_occupiedPart_norm_bound
    (S : ι → PackedSector) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVector S}
    (hf : InGlobalOutsideQuotient S u f) :
    Real.sqrt (((8 * q : ℕ) : ℝ)) *
        globalL2Norm S (globalOccupiedPart S u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2Norm S f := by
  let x : ℝ := Real.sqrt (((8 * q : ℕ) : ℝ)) *
    globalL2Norm S (globalOccupiedPart S u f)
  let y : ℝ := 39 * (t : ℝ) * Real.sqrt (t : ℝ) *
    globalL2Norm S f
  have henergy := global_occupiedEnergy_bound S u H hlarge hf
  have hsqrtq :
      (Real.sqrt (((8 * q : ℕ) : ℝ))) ^ 2 =
        (((8 * q : ℕ) : ℝ)) := by
    rw [sq_sqrt]
    positivity
  have hsqrtt : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := by
    rw [sq_sqrt]
    positivity
  have hocc :
      (globalL2Norm S (globalOccupiedPart S u f)) ^ 2 =
        globalOccupiedEnergy S u f := by
    rw [globalL2Norm_sq, globalTotalEnergy_occupiedPart]
  have htot := globalL2Norm_sq S f
  have hx : 0 ≤ x := by unfold x; positivity
  have hy : 0 ≤ y := by unfold y; positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by
    unfold x y
    rw [mul_pow, hsqrtq, hocc]
    rw [show
      (39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2Norm S f) ^ 2 =
        1521 * (t : ℝ) ^ 3 * globalTotalEnergy S f by
      rw [mul_pow, mul_pow, mul_pow, hsqrtt, htot]
      ring]
    have htotal := globalTotalEnergy_nonneg S f
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

/-- Exact fourth-root form for ambient size `N=(8q)^2`. -/
theorem global_occupiedPart_norm_fourthRoot
    (S : ι → PackedSector) (u : ∀ s, (S s).Block)
    {q t : ℕ} (H : ∀ s, (S s).data.EligibleClassWitnessF q t)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : GlobalVector S}
    (hf : InGlobalOutsideQuotient S u f) :
    (S (Classical.choice inferInstance)).data.fourthRootNatF ((8 * q) ^ 2) *
        globalL2Norm S (globalOccupiedPart S u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) * globalL2Norm S f := by
  have h := global_occupiedPart_norm_bound S u H hlarge hf
  have hroot :
      (S (Classical.choice inferInstance)).data.fourthRootNatF ((8 * q) ^ 2) =
        Real.sqrt (((8 * q : ℕ) : ℝ)) :=
    (S (Classical.choice inferInstance)).data.fourthRootNatF_sq (8 * q)
  rw [hroot]
  exact h

end IndependentMatchingBlockOccupancy
