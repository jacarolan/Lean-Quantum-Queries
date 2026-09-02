import LeanQuantumQueries.IndependentMatchingCommon

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Indicator of `u` in one orbit. -/
def orbitIndicatorF (u : Fin B) (i : Fin d) :
    {a : Fin B // a ∈ S.orbit i} → ℝ :=
  fun a => if a.1 = u then 1 else 0

@[simp] theorem rawAtU_eq_lift_indicatorF (u : Fin B) (i : Fin d) :
    S.rawAtU u i = S.lift i (S.orbitIndicatorF u i) := rfl

/-- Mean of a one-point orbit indicator. -/
theorem coordAvg_orbitIndicatorF (u : Fin B) (i : Fin d)
    (hui : u ∈ S.orbit i) :
    S.coordAvg i (S.orbitIndicatorF u i) =
      1 / ((S.orbit i).card : ℝ) := by
  classical
  let uu : {a : Fin B // a ∈ S.orbit i} := ⟨u, hui⟩
  have hsum :
      (∑ a : {a : Fin B // a ∈ S.orbit i},
        if a.1 = u then (1 : ℝ) else 0) = 1 := by
    rw [Fintype.sum_eq_single uu]
    · simp [uu]
    · intro a ha
      have hne : a.1 ≠ u := by
        intro h
        apply ha
        exact Subtype.ext h
      simp [hne]
  unfold coordAvg orbitIndicatorF
  rw [hsum]

/-- Same-coordinate overlap with a distinguished cylinder vanishes. -/
theorem OutsideCoeff.rawInner_lift_rawAtU_selfF {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawInner (S.lift i (c.val i)) (S.rawAtU u i) = 0 := by
  rw [S.rawAtU_eq_lift_indicatorF]
  unfold rawInner
  rw [show
      (fun x => S.lift i (c.val i) x *
        S.lift i (S.orbitIndicatorF u i) x) =
      S.lift i (fun a => c.val i a * S.orbitIndicatorF u i a) by
        funext x
        rfl]
  rw [S.rawAvg_lift]
  unfold coordAvg orbitIndicatorF
  have hzero :
      (fun a : {a : Fin B // a ∈ S.orbit i} =>
        c.val i a * if a.1 = u then 1 else 0) = 0 := by
    funext a
    by_cases ha : a.1 = u
    · have hau : a = ⟨u, hui⟩ := Subtype.ext ha
      subst a
      rw [OutsideCoeff.atU_eq_zero (S := S) c i hui]
      simp
    · simp [ha]
  rw [hzero]
  simp

/-- Different coordinates factor under the product law. -/
theorem OutsideCoeff.rawInner_lift_rawAtU_neF {u : Fin B}
    (c : S.OutsideCoeff u) (i j : Fin d) (hji : j ≠ i)
    (hui : u ∈ S.orbit i) :
    S.rawInner (S.lift j (c.val j)) (S.rawAtU u i) =
      S.coordAvg j (c.val j) /
        ((S.orbit i).card : ℝ) := by
  rw [S.rawAtU_eq_lift_indicatorF]
  rw [S.rawInner_lift_lift j i (Ne.symm hji),
    S.coordAvg_orbitIndicatorF u i hui]
  ring

/-- Bilinearity in the second argument for subtraction. -/
theorem rawInner_sub_rightF (f g h : S.RawVector) :
    S.rawInner f (g - h) = S.rawInner f g - S.rawInner f h := by
  unfold rawInner rawAvg
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_div]

/-- Exact overlap of an additive outside vector with `x_i=u`. -/
theorem OutsideCoeff.rawInner_synth_rawAtUF {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawInner (S.synth c.val) (S.rawAtU u i) =
      (S.totalMean c.val - S.coordAvg i (c.val i)) /
        ((S.orbit i).card : ℝ) := by
  classical
  have hsynth : S.synth c.val = ∑ j, S.lift j (c.val j) := by
    funext x
    change (∑ j, c.val j (x j)) = ∑ j, c.val j (x j)
    rfl
  rw [hsynth, S.rawInner_sum_left]
  have hsplit :
      (∑ j, S.rawInner (S.lift j (c.val j)) (S.rawAtU u i)) =
        (∑ j ∈ (Finset.univ.erase i),
          S.rawInner (S.lift j (c.val j)) (S.rawAtU u i)) +
          S.rawInner (S.lift i (c.val i)) (S.rawAtU u i) := by
    exact Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => S.rawInner (S.lift j (c.val j)) (S.rawAtU u i))
      (a := i) (Finset.mem_univ i)
  rw [hsplit, OutsideCoeff.rawInner_lift_rawAtU_selfF (S := S) c i hui]
  simp only [add_zero]
  have hsum :
      (∑ j ∈ (Finset.univ.erase i),
        S.rawInner (S.lift j (c.val j)) (S.rawAtU u i)) =
      (∑ j ∈ (Finset.univ.erase i), S.coordAvg j (c.val j)) /
        ((S.orbit i).card : ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    exact OutsideCoeff.rawInner_lift_rawAtU_neF (S := S) c i j
      (Finset.ne_of_mem_erase hj) hui
  rw [hsum]
  unfold totalMean
  have herase :
      (∑ j ∈ (Finset.univ.erase i), S.coordAvg j (c.val j)) +
        S.coordAvg i (c.val i) =
      ∑ j, S.coordAvg j (c.val j) := by
    exact Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => S.coordAvg j (c.val j))
      (a := i) (Finset.mem_univ i)
  have hmean :
      (∑ j ∈ (Finset.univ.erase i), S.coordAvg j (c.val j)) =
        (∑ j, S.coordAvg j (c.val j)) - S.coordAvg i (c.val i) := by
    linarith
  rw [hmean]

/-- Complete-fiber differences are explicit common vectors. -/
theorem rawAtUDifference_mem_commonF (u : Fin B) (i j : Fin d)
    (hi : S.Complete i) (hj : S.Complete j)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    S.rawAtU u i - S.rawAtU u j ∈ S.rawCommonSpace u := by
  apply Submodule.subset_span
  exact Or.inl ⟨i, j, hi, hj, hui, huj, rfl⟩

/-- A complete fiber is common when another complete family avoids `u`. -/
theorem rawAtU_mem_common_of_avoidingF (u : Fin B) (i h : Fin d)
    (hi : S.Complete i) (hh : S.Complete h)
    (hui : u ∈ S.orbit i) (huh : u ∉ S.orbit h) :
    S.rawAtU u i ∈ S.rawCommonSpace u := by
  apply Submodule.subset_span
  exact Or.inr ⟨i, h, hi, hh, hui, huh, rfl⟩

/-- Raw common orthogonality equates complete-family scaled defects. -/
theorem OutsideCoeff.complete_scaled_defect_eqF {u : Fin B}
    (c : S.OutsideCoeff u)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (i j : Fin d) (hi : S.Complete i) (hj : S.Complete j)
    (hui : u ∈ S.orbit i) (huj : u ∈ S.orbit j) :
    (S.totalMean c.val - S.coordAvg i (c.val i)) /
        ((S.orbit i).card : ℝ) =
      (S.totalMean c.val - S.coordAvg j (c.val j)) /
        ((S.orbit j).card : ℝ) := by
  have hzero := horth _
    (S.rawAtUDifference_mem_commonF u i j hi hj hui huj)
  rw [S.rawInner_sub_rightF] at hzero
  have hi' := OutsideCoeff.rawInner_synth_rawAtUF (S := S) c i hui
  have hj' := OutsideCoeff.rawInner_synth_rawAtUF (S := S) c j huj
  linarith

/-- An avoiding complete family forces every containing complete row mean to
be the total mean. -/
theorem OutsideCoeff.complete_mean_eq_total_of_avoidingF {u : Fin B}
    (c : S.OutsideCoeff u)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (i h : Fin d) (hi : S.Complete i) (hh : S.Complete h)
    (hui : u ∈ S.orbit i) (huh : u ∉ S.orbit h) :
    S.coordAvg i (c.val i) = S.totalMean c.val := by
  have hzero := horth _
    (S.rawAtU_mem_common_of_avoidingF u i h hi hh hui huh)
  have hi' := OutsideCoeff.rawInner_synth_rawAtUF (S := S) c i hui
  rw [hi'] at hzero
  have hcard : ((S.orbit i).card : ℝ) ≠ 0 := by
    exact_mod_cast (S.orbit_nonempty i).card_ne_zero
  have hnum : S.totalMean c.val - S.coordAvg i (c.val i) = 0 := by
    exact (div_eq_zero_iff.mp hzero).resolve_right hcard
  linarith

end SectorData
end IndependentMatchingBlockOccupancy
