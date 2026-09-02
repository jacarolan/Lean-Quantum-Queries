import LeanQuantumQueries.IndependentMatchingMeansVerified

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Split a raw placement into coordinate `i` and all remaining coordinates. -/
noncomputable def splitAt (i : Fin d) :
    S.RawPlacement ≃
      ({a : Fin B // a ∈ S.orbit i} × S.Remaining i) where
  toFun x := (x i, fun j => x j.1)
  invFun p := S.insertAt i p.1 p.2
  left_inv := by
    intro x
    funext j
    by_cases hji : j = i
    · subst j
      exact S.insertAt_same i (x i) (fun k => x k.1)
    · exact S.insertAt_ne i j hji (x i) (fun k => x k.1)
  right_inv := by
    intro p
    apply Prod.ext
    · exact S.insertAt_same i p.1 p.2
    · funext j
      exact S.insertAt_ne i j.1 j.2 p.1 p.2

/-- Reindex a sum over raw placements by one coordinate and its complement. -/
theorem sum_splitAt (i : Fin d) (F : S.RawPlacement → ℝ) :
    (∑ x, F x) =
      ∑ a : {a : Fin B // a ∈ S.orbit i},
        ∑ y : S.Remaining i, F (S.insertAt i a y) := by
  classical
  have h := (S.splitAt i).symm.sum_comp F
  simpa [Fintype.sum_prod_type] using h

/-- A coefficient family with row `i` deleted. -/
def eraseRow (i : Fin d) (g : S.Coeff) : S.Coeff :=
  fun j a => if j = i then 0 else g j a

@[simp] theorem eraseRow_same (i : Fin d) (g : S.Coeff)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    S.eraseRow i g i a = 0 := by
  simp [eraseRow]

@[simp] theorem eraseRow_ne (i j : Fin d) (hji : j ≠ i)
    (g : S.Coeff) (a : {a : Fin B // a ∈ S.orbit j}) :
    S.eraseRow i g j a = g j a := by
  simp [eraseRow, hji]

/-- Deleting row `i` makes synthesis independent of coordinate `i`. -/
theorem synth_eraseRow_insertAt (i : Fin d) (g : S.Coeff)
    (a b : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i) :
    S.synth (S.eraseRow i g) (S.insertAt i a y) =
      S.synth (S.eraseRow i g) (S.insertAt i b y) := by
  classical
  unfold synth
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp
  · simp [eraseRow, hji, S.insertAt_ne i j hji]

/-- Synthesis of an outside-supported family agrees with row-deleted synthesis
on the cylinder `x_i=u`. -/
theorem OutsideCoeff.synth_eq_eraseRow_of_atU {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i)
    (x : S.RawPlacement) (hx : S.block x i = u) :
    S.synth c.val x = S.synth (S.eraseRow i c.val) x := by
  classical
  unfold synth
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    have hxi : x i = ⟨u, hui⟩ := by
      apply Subtype.ext
      exact hx
    rw [hxi, OutsideCoeff.atU_eq_zero (S := S) c i hui]
    simp
  · simp [eraseRow, hji]

/-- Exact averaging identity for a function independent of coordinate `i`. -/
theorem rawAvg_mul_indicator_of_insertAt_invariant
    (i : Fin d) (u : Fin B) (hui : u ∈ S.orbit i)
    (F : S.RawVector)
    (hF : ∀ (a b : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i),
      F (S.insertAt i a y) = F (S.insertAt i b y)) :
    S.rawAvg (fun x => S.rawAtU u i x * F x) =
      S.rawAvg F / ((S.orbit i).card : ℝ) := by
  classical
  let uu : {a : Fin B // a ∈ S.orbit i} := ⟨u, hui⟩
  have hcard : ((S.orbit i).card : ℝ) ≠ 0 := by
    exact_mod_cast (S.orbit_nonempty i).card_ne_zero
  unfold rawAvg rawAtU rawFiber block
  rw [S.sum_splitAt i]
  have hleft :
      (∑ a : {a : Fin B // a ∈ S.orbit i},
        ∑ y : S.Remaining i,
          (if (S.insertAt i a y i).1 = u then 1 else 0) *
            F (S.insertAt i a y)) =
        ∑ y : S.Remaining i, F (S.insertAt i uu y) := by
    rw [Fintype.sum_eq_single uu]
    · simp [uu]
    · intro a ha
      have hne : a.1 ≠ u := by
        intro hau
        apply ha
        exact Subtype.ext hau
      simp [hne]
  rw [hleft]
  rw [S.sum_splitAt i]
  have hright :
      (∑ a : {a : Fin B // a ∈ S.orbit i},
        ∑ y : S.Remaining i, F (S.insertAt i a y)) =
      ((S.orbit i).card : ℝ) *
        ∑ y : S.Remaining i, F (S.insertAt i uu y) := by
    calc
      (∑ a : {a : Fin B // a ∈ S.orbit i},
          ∑ y : S.Remaining i, F (S.insertAt i a y)) =
          ∑ _a : {a : Fin B // a ∈ S.orbit i},
            ∑ y : S.Remaining i, F (S.insertAt i uu y) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro y _
        exact hF a uu y
      _ = ((S.orbit i).card : ℝ) *
          ∑ y : S.Remaining i, F (S.insertAt i uu y) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  rw [hright]
  field_simp [hcard]

/-- Exact conditional second moment after fixing coordinate `i` to `u`. -/
theorem OutsideCoeff.rawAvg_atU_mul_synth_sq {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
      S.rawNormSq (S.synth (S.eraseRow i c.val)) /
        ((S.orbit i).card : ℝ) := by
  let F : S.RawVector := fun x =>
    (S.synth (S.eraseRow i c.val) x) ^ 2
  have hF : ∀ (a b : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i),
      F (S.insertAt i a y) = F (S.insertAt i b y) := by
    intro a b y
    unfold F
    rw [S.synth_eraseRow_insertAt i c.val a b y]
  have hcond := S.rawAvg_mul_indicator_of_insertAt_invariant
    i u hui F hF
  have hpoint :
      (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
        fun x => S.rawAtU u i x * F x := by
    funext x
    by_cases hx : S.block x i = u
    · rw [OutsideCoeff.synth_eq_eraseRow_of_atU (S := S) c i hui x hx]
    · simp [rawAtU, rawFiber, hx]
  rw [hpoint, hcond]
  rfl

/-- Deleting one row subtracts exactly its mean from the total mean. -/
theorem totalMean_eraseRow (i : Fin d) (g : S.Coeff) :
    S.totalMean (S.eraseRow i g) =
      S.totalMean g - S.coordAvg i (g i) := by
  classical
  unfold totalMean
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hsame : S.coordAvg i (S.eraseRow i g i) = 0 := by
    unfold coordAvg
    simp
  rw [hsame]
  have hne : ∀ j ∈ (Finset.univ.erase i), j ≠ i := by
    intro j hj
    exact Finset.ne_of_mem_erase hj
  simp_rw [show ∀ j ∈ (Finset.univ.erase i),
      S.coordAvg j (S.eraseRow i g j) = S.coordAvg j (g j) by
        intro j hj
        have hji := hne j hj
        congr 1
        funext a
        exact S.eraseRow_ne i j hji g a]
  ring

/-- Centered variance of the deleted row is zero. -/
theorem rawNormSq_lift_centered_eraseRow_same (i : Fin d) (g : S.Coeff) :
    S.rawNormSq
      (S.lift i (S.centered i (S.eraseRow i g i))) = 0 := by
  rw [S.rawNormSq_lift]
  unfold centered coordAvg
  simp

/-- Exact norm of the row-deleted additive vector. -/
theorem rawNormSq_synth_eraseRow (i : Fin d) (g : S.Coeff) :
    S.rawNormSq (S.synth (S.eraseRow i g)) =
      (S.totalMean g - S.coordAvg i (g i)) ^ 2 +
        ∑ j ∈ (Finset.univ.erase i),
          S.rawNormSq (S.lift j (S.centered j (g j))) := by
  classical
  rw [S.rawNormSq_synth, S.totalMean_eraseRow]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [S.rawNormSq_lift_centered_eraseRow_same]
  simp only [add_zero]
  apply congrArg (fun z =>
    (S.totalMean g - S.coordAvg i (g i)) ^ 2 + z)
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  congr 2
  funext a
  unfold centered
  rw [S.eraseRow_ne i j hji]
  congr 1
  unfold coordAvg
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [S.eraseRow_ne i j hji]

end SectorData
end IndependentMatchingBlockOccupancy
