import LeanQuantumQueries.IndependentMatchingGlobalCleanFinal
import LeanQuantumQueries.IndependentMatchingTypedSectorCorollaryFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy

/-- A concrete typed sector with a hidden number of observed coordinates and
a proof that this number is at most `t`. -/
structure PackedTypedSectorF (q t : ℕ) where
  d : ℕ
  input : TypedSectorInputF d q
  coord_le : d ≤ t

namespace PackedTypedSectorF

/-- Underlying finite-table packed sector. -/
noncomputable def toPackedSector (S : PackedTypedSectorF q t) : PackedSectorF :=
  { d := S.d
    B := 8 * q
    data := S.input.sectorDataF }

end PackedTypedSectorF

variable {ι : Type*} [Fintype ι]

/-- Global legal vector for a family of concrete typed sectors. -/
abbrev TypedGlobalVectorF {q t : ℕ}
    (S : ι → PackedTypedSectorF q t) :=
  GlobalVectorF (fun s => (S s).toPackedSector)

/-- Distinguished local block in every concrete typed sector. -/
abbrev TypedGlobalBlockF {q t : ℕ}
    (S : ι → PackedTypedSectorF q t) :=
  ∀ s, Fin (8 * q)

/-- Global quotient condition for concrete typed sectors. -/
def InTypedGlobalOutsideQuotientF
    {q t : ℕ} (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S) (f : TypedGlobalVectorF S) : Prop :=
  InGlobalOutsideQuotientF
    (fun s => (S s).toPackedSector) u f

/-- Every concrete typed sector supplies the eligible-class witness required
by the abstract direct-sum theorem. -/
theorem typedGlobal_eligibleClassWitnessF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t) :
    ∀ s, ((S s).toPackedSector).data.EligibleClassWitnessF q t := by
  intro s
  exact (S s).input.eligibleClassWitnessF ht (S s).coord_le

/-- Global squared occupied-energy estimate for concrete typed sectors. -/
theorem typedGlobal_occupiedEnergy_boundF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : TypedGlobalVectorF S}
    (hf : InTypedGlobalOutsideQuotientF S u f) :
    ((8 * q : ℕ) : ℝ) *
        globalOccupiedEnergyF
          (fun s => (S s).toPackedSector) u f ≤
      1504 * (t : ℝ) ^ 3 *
        globalTotalEnergyF
          (fun s => (S s).toPackedSector) f := by
  exact global_occupiedEnergy_boundF
    (fun s => (S s).toPackedSector) u
    (typedGlobal_eligibleClassWitnessF ht S) hlarge hf

/-- Global norm estimate for concrete typed sectors. -/
theorem typedGlobal_occupiedPart_norm_boundF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : TypedGlobalVectorF S}
    (hf : InTypedGlobalOutsideQuotientF S u f) :
    Real.sqrt (((8 * q : ℕ) : ℝ)) *
        globalL2NormF (fun s => (S s).toPackedSector)
          (globalOccupiedPartF
            (fun s => (S s).toPackedSector) u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        globalL2NormF (fun s => (S s).toPackedSector) f := by
  exact global_occupiedPart_norm_boundF
    (fun s => (S s).toPackedSector) u
    (typedGlobal_eligibleClassWitnessF ht S) hlarge hf

/-- Exact global fourth-root theorem for `N=(8q)^2`. -/
theorem typedGlobal_occupiedPart_norm_fourthRootF
    {q t : ℕ} (ht : 1 ≤ t)
    (S : ι → PackedTypedSectorF q t)
    (u : TypedGlobalBlockF S)
    (hlarge : 4 * t ^ 3 ≤ q)
    {f : TypedGlobalVectorF S}
    (hf : InTypedGlobalOutsideQuotientF S u f) :
    fourthRootNatGlobalF ((8 * q) ^ 2) *
        globalL2NormF (fun s => (S s).toPackedSector)
          (globalOccupiedPartF
            (fun s => (S s).toPackedSector) u f) ≤
      39 * (t : ℝ) * Real.sqrt (t : ℝ) *
        globalL2NormF (fun s => (S s).toPackedSector) f := by
  exact global_occupiedPart_norm_fourthRootF
    (fun s => (S s).toPackedSector) u
    (typedGlobal_eligibleClassWitnessF ht S) hlarge hf

end IndependentMatchingBlockOccupancy
