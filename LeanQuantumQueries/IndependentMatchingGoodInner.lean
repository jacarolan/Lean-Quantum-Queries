import LeanQuantumQueries.IndependentMatchingClippingVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

private theorem rawCard_posG :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  classical
  let x : S.RawPlacement := fun i =>
    ⟨(S.orbit_nonempty i).choose, (S.orbit_nonempty i).choose_spec⟩
  haveI : Nonempty S.RawPlacement := ⟨x⟩
  exact_mod_cast Fintype.card_pos

/-- Product-normalized inner product restricted to injective placements. -/
noncomputable def rawGoodInner (f g : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then f x * g x else 0)

/-- Product-normalized inner product restricted to noninjective placements. -/
noncomputable def rawBadInner (f g : S.RawVector) : ℝ :=
  S.rawAvg (fun x => if S.Legal x then 0 else f x * g x)

/-- Raw inner product splits into legal and collision parts. -/
theorem rawInner_eq_good_add_bad (f g : S.RawVector) :
    S.rawInner f g = S.rawGoodInner f g + S.rawBadInner f g := by
  unfold rawInner rawGoodInner rawBadInner
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx]

/-- Diagonal good and bad inner products are the corresponding energies. -/
theorem rawGoodInner_self (f : S.RawVector) :
    S.rawGoodInner f f = S.rawGoodEnergy f := by
  unfold rawGoodInner rawGoodEnergy
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

theorem rawBadInner_self (f : S.RawVector) :
    S.rawBadInner f f = S.rawBadEnergy f := by
  unfold rawBadInner rawBadEnergy
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, pow_two]

/-- Clear the denominator in a raw average. -/
theorem rawCard_mul_rawAvg (F : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawAvg F = ∑ x, F x := by
  unfold rawAvg
  field_simp [ne_of_gt S.rawCard_posG]

/-- Sum over legal placements as a filtered raw-table sum. -/
theorem sum_placement_eq_filter (F : S.RawPlacement → ℝ) :
    (∑ x : S.Placement, F x.1) =
      ∑ x ∈ (Finset.univ.filter S.Legal), F x := by
  classical
  let e : S.Placement ↪ S.RawPlacement :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      (∑ x : S.Placement, F x.1) =
        ∑ y ∈ (Finset.univ.map e), F y := by
    rw [Finset.sum_map]
    rfl
  rw [hmap]
  congr 1
  ext x
  simp [e]

/-- Exact relation between normalized good inner product and the actual legal
placement inner product. -/
theorem rawCard_mul_rawGoodInner_eq_inner (f g : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawGoodInner f g =
      S.inner (S.restrict f) (S.restrict g) := by
  unfold rawGoodInner inner restrict
  rw [S.rawCard_mul_rawAvg]
  rw [S.sum_placement_eq_filter]
  simp [Finset.sum_filter]

/-- Exact relation for total legal energy. -/
theorem rawCard_mul_rawGoodEnergy_eq_totalEnergy (f : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawGoodEnergy f =
      S.totalEnergy (S.restrict f) := by
  rw [← S.rawGoodInner_self]
  rw [S.rawCard_mul_rawGoodInner_eq_inner]
  unfold inner totalEnergy
  simp [pow_two]

/-- Zero legal inner product is equivalent to zero normalized good inner
product. -/
theorem rawGoodInner_eq_zero_of_inner_eq_zero
    (f g : S.RawVector)
    (h : S.inner (S.restrict f) (S.restrict g) = 0) :
    S.rawGoodInner f g = 0 := by
  have hcard := ne_of_gt S.rawCard_posG
  have hc := S.rawCard_mul_rawGoodInner_eq_inner f g
  rw [h] at hc
  exact (mul_eq_zero.mp hc).resolve_left hcard

/-- Good inner product is additive in the first argument. -/
theorem rawGoodInner_add_left (f g h : S.RawVector) :
    S.rawGoodInner (f + g) h =
      S.rawGoodInner f h + S.rawGoodInner g h := by
  unfold rawGoodInner
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, add_mul]

/-- Bad inner product is additive in the first argument. -/
theorem rawBadInner_add_left (f g h : S.RawVector) :
    S.rawBadInner (f + g) h =
      S.rawBadInner f h + S.rawBadInner g h := by
  unfold rawBadInner
  rw [← S.rawAvg_add]
  congr 1
  funext x
  by_cases hx : S.Legal x <;> simp [hx, add_mul]

/-- The bad cross term is bounded above by the two bad energies. -/
theorem two_mul_rawBadInner_le (f g : S.RawVector) :
    2 * S.rawBadInner f g ≤
      S.rawBadEnergy f + S.rawBadEnergy g := by
  unfold rawBadInner rawBadEnergy
  have hpoint : ∀ x,
      2 * (if S.Legal x then 0 else f x * g x) ≤
        (if S.Legal x then 0 else (f x) ^ 2) +
          (if S.Legal x then 0 else (g x) ^ 2) := by
    intro x
    by_cases hx : S.Legal x
    · simp [hx]
    · simp only [hx, ↓reduceIte]
      nlinarith [sq_nonneg (f x - g x)]
  have havg := S.rawAvg_mono hpoint
  rw [S.rawAvg_smul] at havg
  rw [S.rawAvg_add] at havg
  simpa using havg

end SectorData
end IndependentMatchingBlockOccupancy
