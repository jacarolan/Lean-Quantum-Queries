import LeanQuantumQueries.IndependentMatchingCommon

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Indicator of the distinguished block inside one coordinate orbit. -/
def orbitIndicator (u : Fin B) (i : Fin d) :
    {a : Fin B // a ∈ S.orbit i} → ℝ :=
  fun a => if a.1 = u then 1 else 0

/-- The raw distinguished cylinder is a lifted orbit indicator. -/
theorem rawAtU_eq_lift_indicator (u : Fin B) (i : Fin d) :
    S.rawAtU u i = S.lift i (S.orbitIndicator u i) := by
  rfl

/-- The mean of a one-point orbit indicator. -/
theorem coordAvg_orbitIndicator (u : Fin B) (i : Fin d)
    (hui : u ∈ S.orbit i) :
    S.coordAvg i (S.orbitIndicator u i) =
      1 / ((S.orbit i).card : ℝ) := by
  classical
  let uu : {a : Fin B // a ∈ S.orbit i} := ⟨u, hui⟩
  unfold coordAvg orbitIndicator
  have hsum : (∑ a : {a : Fin B // a ∈ S.orbit i},
      if a.1 = u then (1 : ℝ) else 0) = 1 := by
    rw [Fintype.sum_eq_single uu]
    · simp [uu]
    · intro a ha
      have hne : a.1 ≠ u := by
        intro h
        apply ha
        exact Subtype.ext h
      simp [hne]
  rw [hsum]

/-- A supported outside coefficient has zero same-coordinate overlap with its
own distinguished cylinder. -/
theorem OutsideCoeff.rawInner_lift_rawAtU_self {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawInner (S.lift i (c.val i)) (S.rawAtU u i) = 0 := by
  rw [S.rawAtU_eq_lift_indicator]
  unfold rawInner
  rw [show (fun x => S.lift i (c.val i) x *
      S.lift i (S.orbitIndicator u i) x) =
      S.lift i (fun a => c.val i a * S.orbitIndicator u i a) by
        funext x
        rfl]
  rw [S.rawAvg_lift]
  unfold coordAvg orbitIndicator
  have hzero : (fun a : {a : Fin B // a ∈ S.orbit i} =>
      c.val i a * if a.1 = u then 1 else 0) = 0 := by
    funext a
    by_cases ha : a.1 = u
    · have hau : a = ⟨u, hui⟩ := Subtype.ext ha
      subst a
      simp [c.atU_eq_zero i hui]
    · simp [ha]
  rw [hzero]
  simp

/-- Distinct coordinates are independent under the product law. -/
theorem OutsideCoeff.rawInner_lift_rawAtU_ne {u : Fin B}
    (c : S.OutsideCoeff u) (i j : Fin d) (hji : j ≠ i)
    (hui : u ∈ S.orbit i) :
    S.rawInner (S.lift j (c.val j)) (S.rawAtU u i) =
      S.coordAvg j (c.val j) /
        ((S.orbit i).card : ℝ) := by
  rw [S.rawAtU_eq_lift_indicator]
  rw [S.rawInner_lift_lift j i hji,
    S.coordAvg_orbitIndicator u i hui]
  ring

/-- Inner product is additive in the second argument under subtraction. -/
theorem rawInner_sub_right (f g h : S.RawVector) :
    S.rawInner f (g - h) = S.rawInner f g - S.rawInner f h := by
  unfold rawInner rawAvg
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- Exact overlap of an additive outside vector with a distinguished
coordinate cylinder. -/
theorem OutsideCoeff.rawInner_synth_rawAtU {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawInner (S.synth c.val) (S.rawAtU u i) =
      (S.totalMean c.val - S.coordAvg i (c.val i)) /
        ((S.orbit i).card : ℝ) := by
  classical
  rw [show S.synth c.val = ∑ j, S.lift j (c.val j) by
    funext x
    simp [synth, lift]]
  rw [S.rawInner_sum_left]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [c.rawInner_lift_rawAtU_self i hui]
  simp only [zero_add]
  have hne : ∀ j ∈ (Finset.univ.erase i), j ≠ i := by
    intro j hj
    exact Finset.ne_of_mem_erase hj
  simp_rw [c.rawInner_lift_rawAtU_ne i _ (hne _ ‹_›) hui]
  rw [← Finset.sum_div]
  unfold totalMean
  have hmean :
      (∑ j ∈ Finset.univ.erase i, S.coordAvg j (c.val j)) =
        (∑ j, S.coordAvg j (c.val j)) - S.coordAvg i (c.val i) := by
    have h := Finset.sum_erase_add (fun j => S.coordAvg j (c.val j))
      (Finset.mem_univ i)
    linarith
  rw [hmean]

/-- The raw difference of two complete `u`-fibers is one of the explicit
common generators. -/
theorem rawAtUDifference_mem_common (u : Fin B) (i j : Fin d)
    (hi : S.Complete i) (hj : S.Complete j)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    S.rawAtU u i - S.rawAtU u j ∈ S.rawCommonSpace u := by
  apply Submodule.subset_span
  exact Or.inl ⟨i, j, hi, hj, hui, huj, rfl⟩

/-- A complete `u`-fiber is an explicit common generator when another
complete family avoids `u`. -/
theorem rawAtU_mem_common_of_avoiding (u : Fin B) (i h : Fin d)
    (hi : S.Complete i) (hh : S.Complete h)
    (hui : u ∈ S.orbit i) (huh : u ∉ S.orbit h) :
    S.rawAtU u i ∈ S.rawCommonSpace u := by
  apply Submodule.subset_span
  exact Or.inr ⟨i, h, hi, hh, hui, huh, rfl⟩

/-- Orthogonality to exact common differences forces the scaled mean defects
of two complete families to agree. -/
theorem OutsideCoeff.complete_scaled_defect_eq {u : Fin B}
    (c : S.OutsideCoeff u) (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (i j : Fin d) (hi : S.Complete i) (hj : S.Complete j)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    (S.totalMean c.val - S.coordAvg i (c.val i)) /
        ((S.orbit i).card : ℝ) =
      (S.totalMean c.val - S.coordAvg j (c.val j)) /
        ((S.orbit j).card : ℝ) := by
  have hzero := horth _ (S.rawAtUDifference_mem_common u i j hi hj hui huj)
  rw [S.rawInner_sub_right,
    c.rawInner_synth_rawAtU i hui,
    c.rawInner_synth_rawAtU j huj] at hzero
  linarith

/-- If a complete family avoids the distinguished block, every complete
family containing it has coordinate mean equal to the total mean. -/
theorem OutsideCoeff.complete_mean_eq_total_of_avoiding {u : Fin B}
    (c : S.OutsideCoeff u) (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (i h : Fin d) (hi : S.Complete i) (hh : S.Complete h)
    (hui : u ∈ S.orbit i) (huh : u ∉ S.orbit h) :
    S.coordAvg i (c.val i) = S.totalMean c.val := by
  have hzero := horth _ (S.rawAtU_mem_common_of_avoiding u i h hi hh hui huh)
  rw [c.rawInner_synth_rawAtU i hui] at hzero
  have hcard : ((S.orbit i).card : ℝ) ≠ 0 := by
    exact_mod_cast (S.orbit_nonempty i).card_ne_zero
  exact sub_eq_zero.mp (div_eq_zero_iff.mp hzero |>.resolve_right hcard)

end SectorData
end IndependentMatchingBlockOccupancy
