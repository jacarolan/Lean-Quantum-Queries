import LeanQuantumQueries.IndependentMatchingMeansFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Split a raw placement into coordinate `i` and all other coordinates. -/
noncomputable def splitAtF (i : Fin d) :
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

/-- Reindex a raw-table sum by one coordinate and its complement. -/
theorem sum_splitAtF (i : Fin d) (F : S.RawPlacement → ℝ) :
    (∑ x, F x) =
      ∑ a : {a : Fin B // a ∈ S.orbit i},
        ∑ y : S.Remaining i, F (S.insertAt i a y) := by
  classical
  have h := (S.splitAtF i).symm.sum_comp F
  simpa [Fintype.sum_prod_type] using h.symm

/-- Delete one coefficient row. -/
def eraseRowF (i : Fin d) (g : S.Coeff) : S.Coeff :=
  fun j a => if j = i then 0 else g j a

@[simp] theorem eraseRowF_same (i : Fin d) (g : S.Coeff)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    S.eraseRowF i g i a = 0 := by
  simp [eraseRowF]

@[simp] theorem eraseRowF_ne (i j : Fin d) (hji : j ≠ i)
    (g : S.Coeff) (a : {a : Fin B // a ∈ S.orbit j}) :
    S.eraseRowF i g j a = g j a := by
  simp [eraseRowF, hji]

/-- Row-deleted synthesis does not depend on coordinate `i`. -/
theorem synth_eraseRowF_insertAt (i : Fin d) (g : S.Coeff)
    (a b : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i) :
    S.synth (S.eraseRowF i g) (S.insertAt i a y) =
      S.synth (S.eraseRowF i g) (S.insertAt i b y) := by
  classical
  unfold synth
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp
  · simp [eraseRowF, hji, S.insertAt_ne i j hji]

/-- On `x_i=u`, an outside-supported vector equals its row-deleted version. -/
theorem OutsideCoeff.synth_eq_eraseRowF_of_atU {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i)
    (x : S.RawPlacement) (hx : S.block x i = u) :
    S.synth c.val x = S.synth (S.eraseRowF i c.val) x := by
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
  · simp [eraseRowF, hji]

/-- Exact averaging identity for a function independent of coordinate `i`. -/
theorem rawAvg_mul_indicator_of_insertAt_invariantF
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
  rw [S.sum_splitAtF i]
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
  rw [S.sum_splitAtF i]
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

/-- Exact conditional second moment on the distinguished cylinder. -/
theorem OutsideCoeff.rawAvg_atU_mul_synth_sqF {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) (hui : u ∈ S.orbit i) :
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
      S.rawNormSq (S.synth (S.eraseRowF i c.val)) /
        ((S.orbit i).card : ℝ) := by
  let F : S.RawVector := fun x =>
    (S.synth (S.eraseRowF i c.val) x) ^ 2
  have hF : ∀ (a b : {a : Fin B // a ∈ S.orbit i}) (y : S.Remaining i),
      F (S.insertAt i a y) = F (S.insertAt i b y) := by
    intro a b y
    unfold F
    rw [S.synth_eraseRowF_insertAt i c.val a b y]
  have hcond := S.rawAvg_mul_indicator_of_insertAt_invariantF
    i u hui F hF
  have hpoint :
      (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
        fun x => S.rawAtU u i x * F x := by
    funext x
    by_cases hx : S.block x i = u
    · rw [OutsideCoeff.synth_eq_eraseRowF_of_atU (S := S) c i hui x hx]
    · simp [rawAtU, rawFiber, hx]
  rw [hpoint, hcond]
  rfl

/-- Deleting row `i` subtracts its mean from the total mean. -/
theorem totalMean_eraseRowF (i : Fin d) (g : S.Coeff) :
    S.totalMean (S.eraseRowF i g) =
      S.totalMean g - S.coordAvg i (g i) := by
  classical
  unfold totalMean
  have hleft :
      (∑ j, S.coordAvg j (S.eraseRowF i g j)) =
        (∑ j ∈ (Finset.univ.erase i),
          S.coordAvg j (S.eraseRowF i g j)) +
          S.coordAvg i (S.eraseRowF i g i) := by
    exact Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => S.coordAvg j (S.eraseRowF i g j))
      (a := i) (Finset.mem_univ i)
  have hright :
      (∑ j, S.coordAvg j (g j)) =
        (∑ j ∈ (Finset.univ.erase i), S.coordAvg j (g j)) +
          S.coordAvg i (g i) := by
    exact Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j => S.coordAvg j (g j))
      (a := i) (Finset.mem_univ i)
  rw [hleft, hright]
  have hsame : S.coordAvg i (S.eraseRowF i g i) = 0 := by
    unfold coordAvg
    simp
  rw [hsame]
  have hrest :
      (∑ j ∈ (Finset.univ.erase i),
        S.coordAvg j (S.eraseRowF i g j)) =
      ∑ j ∈ (Finset.univ.erase i), S.coordAvg j (g j) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    congr 1
    funext a
    exact S.eraseRowF_ne i j hji g a
  rw [hrest]
  ring

/-- The centered variance of the deleted row is zero. -/
theorem rawNormSq_lift_centered_eraseRowF_same
    (i : Fin d) (g : S.Coeff) :
    S.rawNormSq
      (S.lift i (S.centered i (S.eraseRowF i g i))) = 0 := by
  rw [S.rawNormSq_lift]
  unfold centered coordAvg
  simp

/-- Exact norm formula for row-deleted synthesis. -/
theorem rawNormSq_synth_eraseRowF (i : Fin d) (g : S.Coeff) :
    S.rawNormSq (S.synth (S.eraseRowF i g)) =
      (S.totalMean g - S.coordAvg i (g i)) ^ 2 +
        ∑ j ∈ (Finset.univ.erase i),
          S.rawNormSq (S.lift j (S.centered j (g j))) := by
  classical
  rw [S.rawNormSq_synth, S.totalMean_eraseRowF]
  have hsplit :
      (∑ j,
        S.rawNormSq
          (S.lift j (S.centered j (S.eraseRowF i g j)))) =
        (∑ j ∈ (Finset.univ.erase i),
          S.rawNormSq
            (S.lift j (S.centered j (S.eraseRowF i g j)))) +
          S.rawNormSq
            (S.lift i (S.centered i (S.eraseRowF i g i))) := by
    exact Finset.sum_erase_add
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun j =>
        S.rawNormSq (S.lift j (S.centered j (S.eraseRowF i g j))))
      (a := i) (Finset.mem_univ i)
  rw [hsplit, S.rawNormSq_lift_centered_eraseRowF_same]
  simp only [add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  congr 2
  funext a
  unfold centered
  rw [S.eraseRowF_ne i j hji]
  congr 1
  unfold coordAvg
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [S.eraseRowF_ne i j hji]

end SectorData
end IndependentMatchingBlockOccupancy
