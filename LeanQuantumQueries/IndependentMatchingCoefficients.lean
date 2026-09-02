import LeanQuantumQueries.IndependentMatchingIdeal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Values of coordinate `i` that can occur in an outside-rooted generator. -/
def allowedValues (u : Fin B) (i : Fin d) :
    Finset {a : Fin B // a ∈ S.orbit i} :=
  Finset.univ.filter fun a => a.1 ∈ S.compat i ∧ a.1 ≠ u

/-- Orbit values on which every outside coefficient must vanish. -/
def missingValues (u : Fin B) (i : Fin d) :
    Finset {a : Fin B // a ∈ S.orbit i} :=
  Finset.univ \ S.allowedValues u i

/-- Coefficients for a linear combination of all outside-rooted coordinate
fibers. -/
structure OutsideCoeff (u : Fin B) where
  val : ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ
  zero_of_not_allowed : ∀ i a, a ∉ S.allowedValues u i → val i a = 0

/-- Additive product-table vector synthesized from outside coefficients. -/
noncomputable def OutsideCoeff.synth {u : Fin B} (c : S.OutsideCoeff u) :
    S.RawVector := S.synth c.val

@[simp] theorem mem_allowedValues_iff (u : Fin B) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    a ∈ S.allowedValues u i ↔ a.1 ∈ S.compat i ∧ a.1 ≠ u := by
  simp [allowedValues]

@[simp] theorem mem_missingValues_iff (u : Fin B) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    a ∈ S.missingValues u i ↔
      ¬(a.1 ∈ S.compat i ∧ a.1 ≠ u) := by
  simp [missingValues]

/-- An outside coefficient vanishes at the distinguished block. -/
theorem OutsideCoeff.atU_eq_zero {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d) (hui : u ∈ S.orbit i) :
    c.val i ⟨u, hui⟩ = 0 := by
  apply c.zero_of_not_allowed
  simp [allowedValues]

/-- An outside coefficient vanishes on every missing orbit value. -/
theorem OutsideCoeff.eq_zero_of_mem_missing {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (ha : a ∈ S.missingValues u i) : c.val i a = 0 := by
  apply c.zero_of_not_allowed
  simpa [missingValues] using ha

/-- Squared norm of a lifted coordinate function is its coordinate average of
squares. -/
theorem rawNormSq_lift (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.rawNormSq (S.lift i g) = S.coordAvg i (fun a => (g a) ^ 2) := by
  unfold rawNormSq rawInner
  rw [show (fun x => S.lift i g x * S.lift i g x) =
      S.lift i (fun a => (g a) ^ 2) by
        funext x
        simp [lift, pow_two]]
  exact S.rawAvg_lift i _

/-- On a missing value, the centered coefficient equals minus its mean. -/
theorem OutsideCoeff.centered_eq_neg_mean_of_missing {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (ha : a ∈ S.missingValues u i) :
    S.centered i (c.val i) a = -S.coordAvg i (c.val i) := by
  have hz : c.val i a = 0 :=
    OutsideCoeff.eq_zero_of_mem_missing (S := S) c i a ha
  simp [centered, hz]

/-- Exact contribution of the missing values to the coordinate variance. -/
theorem OutsideCoeff.sum_missing_centered_sq {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) :
    (∑ a ∈ S.missingValues u i,
      (S.centered i (c.val i) a) ^ 2) =
      (S.missingValues u i).card * (S.coordAvg i (c.val i)) ^ 2 := by
  classical
  calc
    (∑ a ∈ S.missingValues u i,
        (S.centered i (c.val i) a) ^ 2) =
        ∑ _a ∈ S.missingValues u i, (S.coordAvg i (c.val i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [OutsideCoeff.centered_eq_neg_mean_of_missing (S := S) c i a ha]
      ring
    _ = (S.missingValues u i).card * (S.coordAvg i (c.val i)) ^ 2 := by
      simp

/-- The missing-value contribution is at most the full variance sum. -/
theorem OutsideCoeff.sum_missing_le_sum_all {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) :
    (∑ a ∈ S.missingValues u i,
      (S.centered i (c.val i) a) ^ 2) ≤
      ∑ a, (S.centered i (c.val i) a) ^ 2 := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro a _ _
  exact sq_nonneg _

/-- If at least one eighth of an orbit is missing, the squared coordinate mean
is at most eight times its variance. -/
theorem OutsideCoeff.mean_sq_le_eight_variance {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d)
    (hgap : (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (S.coordAvg i (c.val i)) ^ 2 ≤
      8 * S.rawNormSq (S.lift i (S.centered i (c.val i))) := by
  classical
  have hmiss := OutsideCoeff.sum_missing_le_sum_all (S := S) c i
  rw [OutsideCoeff.sum_missing_centered_sq (S := S) c i] at hmiss
  rw [S.rawNormSq_lift i]
  have hn : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  have hgapR : ((S.orbit i).card : ℝ) ≤
      8 * ((S.missingValues u i).card : ℝ) := by
    exact_mod_cast hgap
  have hmean : 0 ≤ (S.coordAvg i (c.val i)) ^ 2 := sq_nonneg _
  have hscaled :
      ((S.orbit i).card : ℝ) * (S.coordAvg i (c.val i)) ^ 2 ≤
        8 * ∑ a, (S.centered i (c.val i) a) ^ 2 := by
    nlinarith
  change (S.coordAvg i (c.val i)) ^ 2 ≤
    8 * ((∑ a, (S.centered i (c.val i) a) ^ 2) /
      ((S.orbit i).card : ℝ))
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hn).2
  simpa [mul_comm] using hscaled

end SectorData
end IndependentMatchingBlockOccupancy
