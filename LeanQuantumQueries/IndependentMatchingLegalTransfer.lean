import LeanQuantumQueries.IndependentMatchingClippingEnergy

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

private theorem rawCard_posT :
    0 < (Fintype.card S.RawPlacement : ℝ) := by
  classical
  let x : S.RawPlacement := fun i =>
    ⟨(S.orbit_nonempty i).choose, (S.orbit_nonempty i).choose_spec⟩
  haveI : Nonempty S.RawPlacement := ⟨x⟩
  exact_mod_cast Fintype.card_pos

/-- Clear the denominator in a product-table average. -/
theorem rawCard_mul_rawAvgV (F : S.RawVector) :
    (Fintype.card S.RawPlacement : ℝ) * S.rawAvg F = ∑ x, F x := by
  unfold rawAvg
  field_simp [ne_of_gt S.rawCard_posT]

/-- Sum over the legal subtype is at most the corresponding nonnegative sum
over the whole raw table. -/
theorem sum_legal_le_sum_rawV (F : S.RawPlacement → ℝ)
    (hF : ∀ x, 0 ≤ F x) :
    (∑ x : S.Placement, F x.1) ≤ ∑ x : S.RawPlacement, F x := by
  classical
  let e : S.Placement ↪ S.RawPlacement :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hrewrite :
      (∑ x : S.Placement, F x.1) =
        ∑ y ∈ (Finset.univ.map e), F y := by
    rw [Finset.sum_map]
    rfl
  rw [hrewrite]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro x _ _
  exact hF x

/-- The legal energy is exactly the raw good numerator divided by the raw
placement count. -/
theorem rawGoodEnergyV_eq_totalEnergy_div_rawCard (f : S.RawVector) :
    S.rawGoodEnergyV f =
      S.totalEnergy (S.restrict f) /
        (Fintype.card S.RawPlacement : ℝ) := by
  classical
  unfold rawGoodEnergyV rawAvg totalEnergy restrict
  congr 1
  let e : S.Placement ↪ S.RawPlacement :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      (∑ x : S.Placement, (f x.1) ^ 2) =
        ∑ y ∈ (Finset.univ.map e), (f y) ^ 2 := by
    rw [Finset.sum_map]
    rfl
  rw [hmap]
  let L : Finset S.RawPlacement := Finset.univ.filter S.Legal
  have hL : Finset.univ.map e = L := by
    ext x
    simp [e, L]
  rw [hL]
  simp [L]

/-- A legal placement occupying `u` contributes to at least one coordinate
cylinder in the raw upper sum. -/
theorem legalOccupied_pointwise_leV (u : Fin B) (f : S.RawVector)
    (x : S.Placement) :
    (if S.Occupied u x then (f x.1) ^ 2 else 0) ≤
      ∑ i ∈ S.atUIndicesV u,
        S.rawAtU u i x.1 * (f x.1) ^ 2 := by
  classical
  by_cases hx : S.Occupied u x
  · rcases hx with ⟨i, hi⟩
    have hiU : i ∈ S.atUIndicesV u := by
      apply (S.mem_atUIndicesV_iff u i).2
      rw [← hi]
      exact (x.1 i).2
    simp only [hx, ↓reduceIte]
    have hterm :
        (f x.1) ^ 2 = S.rawAtU u i x.1 * (f x.1) ^ 2 := by
      simp [rawAtU, rawFiber, hi]
    rw [hterm]
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg
        (by simp [rawAtU, rawFiber]) (sq_nonneg _)) hiU
  · simp only [hx, ↓reduceIte]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by simp [rawAtU, rawFiber]) (sq_nonneg _)

/-- Legal occupied energy is at most the raw-table cardinality times the
normalized product upper sum. -/
theorem occupiedEnergy_restrict_le_rawCard_mul_upperV
    {u : Fin B} (c : S.OutsideCoeff u) :
    S.occupiedEnergy u (S.restrict (S.synth c.val)) ≤
      (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpperV c := by
  classical
  unfold occupiedEnergy
  have hlegal :
      (∑ x : S.Placement,
        if S.Occupied u x then (S.synth c.val x.1) ^ 2 else 0) ≤
      ∑ x : S.Placement,
        ∑ i ∈ S.atUIndicesV u,
          S.rawAtU u i x.1 * (S.synth c.val x.1) ^ 2 := by
    exact Finset.sum_le_sum fun x _ =>
      S.legalOccupied_pointwise_leV u (S.synth c.val) x
  have hraw :
      (∑ x : S.Placement,
        ∑ i ∈ S.atUIndicesV u,
          S.rawAtU u i x.1 * (S.synth c.val x.1) ^ 2) ≤
      ∑ x : S.RawPlacement,
        ∑ i ∈ S.atUIndicesV u,
          S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
    apply S.sum_legal_le_sum_rawV
    intro x
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by simp [rawAtU, rawFiber]) (sq_nonneg _)
  have havg :
      (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpperV c =
      ∑ x : S.RawPlacement,
        ∑ i ∈ S.atUIndicesV u,
          S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
    unfold rawOccupiedUpperV
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ S.atUIndicesV u,
          (Fintype.card S.RawPlacement : ℝ) *
            S.rawAvg (fun x =>
              S.rawAtU u i x * (S.synth c.val x) ^ 2) =
          ∑ i ∈ S.atUIndicesV u,
            ∑ x : S.RawPlacement,
              S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact S.rawCard_mul_rawAvgV _
      _ = ∑ x : S.RawPlacement,
          ∑ i ∈ S.atUIndicesV u,
            S.rawAtU u i x * (S.synth c.val x) ^ 2 := by
        rw [Finset.sum_comm]
  rw [havg]
  exact le_trans hlegal hraw

/-- Legal-table occupancy bound for a lift orthogonal to the explicit raw
common space. -/
theorem occupiedEnergy_restrict_bound_of_rawOrthogonalV
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsV q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (horth : S.RawCommonOrthogonal u (S.synth c.val)) :
    (q : ℝ) * S.occupiedEnergy u (S.restrict (S.synth c.val)) ≤
      704 * (t : ℝ) *
        S.totalEnergy (S.restrict (S.synth c.val)) := by
  have hocc := S.occupiedEnergy_restrict_le_rawCard_mul_upperV c
  have hprod := S.rawOccupiedUpperV_bound c H horth
  have hclip := S.rawNormSq_le_two_rawGoodEnergyV c.val H hlarge
  rw [S.rawGoodEnergyV_eq_totalEnergy_div_rawCard] at hclip
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hcard : 0 < (Fintype.card S.RawPlacement : ℝ) := S.rawCard_posT
  have ht : 0 ≤ (t : ℝ) := by positivity
  have htotal :
      0 ≤ S.totalEnergy (S.restrict (S.synth c.val)) := by
    unfold totalEnergy
    positivity
  have hupper0 : 0 ≤ S.rawOccupiedUpperV c := by
    unfold rawOccupiedUpperV rawAvg
    positivity
  have hnorm0 : 0 ≤ S.rawNormSq (S.synth c.val) := by
    unfold rawNormSq rawInner rawAvg
    positivity
  nlinarith

end SectorData
end IndependentMatchingBlockOccupancy
