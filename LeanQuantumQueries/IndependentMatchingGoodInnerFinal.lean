import LeanQuantumQueries.IndependentMatchingClippingFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

private theorem rawCard_posInnerF :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  classical
  let x : S.RawPlacement := fun i =>
    ⟨(S.orbit_nonempty i).choose, (S.orbit_nonempty i).choose_spec⟩
  haveI : Nonempty S.RawPlacement := ⟨x⟩
  exact_mod_cast Fintype.card_pos

/-- Normalized inner product over injective placements. -/
noncomputable def rawGoodInnerF (f g : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then f x * g x else 0)

/-- Normalized inner product over noninjective placements. -/
noncomputable def rawBadInnerF (f g : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then 0 else f x * g x)

/-- Raw inner product splits into legal and collision parts. -/
theorem rawInner_eq_good_add_badF (f g : S.RawVector) :
    S.rawInner f g = S.rawGoodInnerF f g + S.rawBadInnerF f g := by
  unfold rawInner rawGoodInnerF rawBadInnerF
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx]

/-- Diagonal good and bad inner products are the corresponding energies. -/
theorem rawGoodInnerF_self (f : S.RawVector) :
    S.rawGoodInnerF f f = S.rawGoodEnergyF f := by
  unfold rawGoodInnerF rawGoodEnergyF
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

theorem rawBadInnerF_self (f : S.RawVector) :
    S.rawBadInnerF f f = S.rawBadEnergyF f := by
  unfold rawBadInnerF rawBadEnergyF
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

/-- Clear the denominator in a raw average. -/
theorem rawCard_mul_rawAvgF (F : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawAvg F = ∑ x, F x := by
  unfold rawAvg
  field_simp [ne_of_gt S.rawCard_posInnerF]

/-- A subtype sum is the corresponding filtered raw-table sum. -/
theorem sum_placement_eq_filterF (F : S.RawPlacement → ℝ) :
    (∑ x : S.Placement, F x.1) =
      ∑ x ∈ (Finset.univ.filter S.Legal), F x := by
  classical
  let e : S.Placement ↪ S.RawPlacement :=
    ⟨Subtype.val, Subtype.val_injective⟩
  calc
    (∑ x : S.Placement, F x.1) =
        ∑ y ∈ (Finset.univ.map e), F y := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ x ∈ (Finset.univ.filter S.Legal), F x := by
      congr 1
      ext x
      simp [e]

/-- Exact conversion between normalized good inner product and the actual
legal-table inner product. -/
theorem rawCard_mul_rawGoodInnerF_eq_inner (f g : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawGoodInnerF f g =
      S.inner (S.restrict f) (S.restrict g) := by
  unfold rawGoodInnerF inner restrict
  rw [S.rawCard_mul_rawAvgF]
  rw [S.sum_placement_eq_filterF]
  simpa [Finset.sum_filter]

/-- Exact conversion for legal energy. -/
theorem rawCard_mul_rawGoodEnergyF_eq_totalEnergy (f : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawGoodEnergyF f =
      S.totalEnergy (S.restrict f) := by
  rw [← S.rawGoodInnerF_self]
  rw [S.rawCard_mul_rawGoodInnerF_eq_inner]
  unfold inner totalEnergy
  simp [pow_two]

/-- Legal orthogonality implies zero normalized good inner product. -/
theorem rawGoodInnerF_eq_zero_of_inner_eq_zero
    (f g : S.RawVector)
    (h : S.inner (S.restrict f) (S.restrict g) = 0) :
    S.rawGoodInnerF f g = 0 := by
  have hc := S.rawCard_mul_rawGoodInnerF_eq_inner f g
  rw [h] at hc
  exact (mul_eq_zero.mp hc).resolve_left
    (ne_of_gt S.rawCard_posInnerF)

/-- Additivity in the first argument. -/
theorem rawGoodInnerF_add_left (f g h : S.RawVector) :
    S.rawGoodInnerF (f + g) h =
      S.rawGoodInnerF f h + S.rawGoodInnerF g h := by
  unfold rawGoodInnerF
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, add_mul]

theorem rawBadInnerF_add_left (f g h : S.RawVector) :
    S.rawBadInnerF (f + g) h =
      S.rawBadInnerF f h + S.rawBadInnerF g h := by
  unfold rawBadInnerF
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, add_mul]

/-- Bad cross terms are controlled by bad energies. -/
theorem two_mul_rawBadInnerF_le (f g : S.RawVector) :
    2 * S.rawBadInnerF f g ≤
      S.rawBadEnergyF f + S.rawBadEnergyF g := by
  unfold rawBadInnerF rawBadEnergyF
  have hpoint : ∀ x,
      2 * (if S.Legal x then 0 else f x * g x) ≤
        (if S.Legal x then 0 else (f x) ^ 2) +
          (if S.Legal x then 0 else (g x) ^ 2) := by
    intro x
    by_cases hx : S.Legal x
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      nlinarith [sq_nonneg (f x - g x)]
  have havg := S.rawAvg_monoF hpoint
  have hleft :
      S.rawAvg (fun x =>
        2 * (if S.Legal x then 0 else f x * g x)) =
        2 * S.rawAvg (fun x =>
          if S.Legal x then 0 else f x * g x) := by
    rw [show (fun x =>
        2 * (if S.Legal x then 0 else f x * g x)) =
      (2 : ℝ) • (fun x =>
        if S.Legal x then 0 else f x * g x) by
          funext x
          simp]
    rw [S.rawAvg_smul]
  have hright :
      S.rawAvg (fun x =>
        (if S.Legal x then 0 else (f x) ^ 2) +
          (if S.Legal x then 0 else (g x) ^ 2)) =
        S.rawAvg (fun x => if S.Legal x then 0 else (f x) ^ 2) +
          S.rawAvg (fun x => if S.Legal x then 0 else (g x) ^ 2) :=
    S.rawAvg_add _ _
  rw [hleft, hright] at havg
  exact havg

end SectorData
end IndependentMatchingBlockOccupancy
