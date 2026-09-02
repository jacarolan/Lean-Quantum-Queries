import LeanQuantumQueries.IndependentMatchingMeans
import LeanQuantumQueries.IndependentMatchingArithmetic

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ}

/-- Numerical orbit bounds used by the product-table calculation.  The
incomplete-family gap is kept as a theorem parameter because it depends on
the distinguished block. -/
structure SectorBounds (S : SectorData d B) (q t : ℕ) : Prop where
  t_pos : 1 ≤ t
  coord_le : d ≤ t
  orbit_lower : ∀ i, q ≤ 8 * (S.orbit i).card
  orbit_upper : ∀ i, (S.orbit i).card ≤ q

/-- Complete rooting families whose orbit contains the distinguished block. -/
noncomputable def completeAtU (S : SectorData d B) (u : Fin B) :
    Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i => S.Complete i ∧ u ∈ S.orbit i

/-- Structurally incomplete rooting families. -/
noncomputable def incompleteIndices (S : SectorData d B) :
    Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i => ¬ S.Complete i

/-- Mean of the coefficient row belonging to one coordinate. -/
noncomputable def coefficientMean (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) : ℝ :=
  S.coordAvg i (c.val i)

/-- Variance contribution of one centered coordinate row. -/
noncomputable def coefficientVariance (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) : ℝ :=
  S.rawNormSq (S.lift i (S.centered i (c.val i)))

/-- Sum of all coordinate variances. -/
noncomputable def totalVariance (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) : ℝ :=
  ∑ i, S.coefficientVariance c i

@[simp] theorem mem_completeAtU_iff (S : SectorData d B)
    (u : Fin B) (i : Fin d) :
    i ∈ S.completeAtU u ↔ S.Complete i ∧ u ∈ S.orbit i := by
  classical
  simp [completeAtU]

@[simp] theorem mem_incompleteIndices_iff (S : SectorData d B)
    (i : Fin d) :
    i ∈ S.incompleteIndices ↔ ¬ S.Complete i := by
  classical
  simp [incompleteIndices]

/-- Every coordinate variance is nonnegative. -/
theorem coefficientVariance_nonneg (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) (i : Fin d) :
    0 ≤ S.coefficientVariance c i := by
  rw [coefficientVariance, S.rawNormSq_lift]
  unfold coordAvg
  have hcard : 0 < ((S.orbit i).card : ℝ) := by
    exact_mod_cast (S.orbit_nonempty i).card_pos
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) hcard.le

/-- The total variance is nonnegative. -/
theorem totalVariance_nonneg (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) : 0 ≤ S.totalVariance c := by
  classical
  apply Finset.sum_nonneg
  intro i _
  exact S.coefficientVariance_nonneg c i

/-- Exact norm decomposition using the coefficient means and variances. -/
theorem rawNormSq_synth_eq (S : SectorData d B) {u : Fin B}
    (c : S.OutsideCoeff u) :
    S.rawNormSq (S.synth c.val) =
      (S.totalMean c.val) ^ 2 + S.totalVariance c := by
  exact S.rawNormSq_synth c.val

/-- Number of complete-at-`u` coordinates is at most the number of coordinates. -/
theorem card_completeAtU_le (S : SectorData d B) (u : Fin B) :
    (S.completeAtU u).card ≤ d := by
  classical
  exact (S.completeAtU u).card_le_univ

/-- Number of incomplete coordinates is at most the number of coordinates. -/
theorem card_incomplete_le (S : SectorData d B) :
    S.incompleteIndices.card ≤ d := by
  classical
  exact S.incompleteIndices.card_le_univ

/-- The mean of every incomplete coefficient row is controlled by its
variance. -/
theorem incomplete_mean_sq_le (S : SectorData d B)
    {u : Fin B} (c : S.OutsideCoeff u)
    (i : Fin d)
    (hgapU : (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (S.coefficientMean c i) ^ 2 ≤
      8 * S.coefficientVariance c i := by
  exact OutsideCoeff.mean_sq_le_eight_variance (S := S) c i hgapU

/-- Cauchy--Schwarz plus the incomplete-family gap controls the sum of all
incomplete row means. -/
theorem incomplete_mean_sum_sq_le (S : SectorData d B)
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorBounds q t)
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (∑ i ∈ S.incompleteIndices, S.coefficientMean c i) ^ 2 ≤
      8 * (t : ℝ) * S.totalVariance c := by
  classical
  let I : Finset (Fin d) := S.incompleteIndices
  have hcs :
      (∑ i ∈ I, S.coefficientMean c i) ^ 2 ≤
        (I.card : ℝ) * ∑ i ∈ I, (S.coefficientMean c i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmean :
      (∑ i ∈ I, (S.coefficientMean c i) ^ 2) ≤
        8 * ∑ i ∈ I, S.coefficientVariance c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact S.incomplete_mean_sq_le c i
      (hgapU i ((S.mem_incompleteIndices_iff i).1 hi))
  have hvar :
      (∑ i ∈ I, S.coefficientVariance c i) ≤ S.totalVariance c := by
    unfold totalVariance
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact S.coefficientVariance_nonneg c i
  have hcardNat : I.card ≤ t :=
    le_trans S.card_incomplete_le H.coord_le
  have hcard : (I.card : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hcardNat
  have hMeanSqNonneg : 0 ≤ ∑ i ∈ I, (S.coefficientMean c i) ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hIvar : 0 ≤ ∑ i ∈ I, S.coefficientVariance c i := by
    apply Finset.sum_nonneg
    intro i _
    exact S.coefficientVariance_nonneg c i
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  have hV := S.totalVariance_nonneg c
  have hfinal :
      (∑ i ∈ I, S.coefficientMean c i) ^ 2 ≤
        8 * (t : ℝ) * S.totalVariance c := by
    nlinarith
  simpa [I] using hfinal

/-- Weighted contribution of means from complete rooting families. -/
theorem complete_weighted_mean_bound (S : SectorData d B)
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorBounds q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val))
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card) :
    (q : ℝ) * ∑ i ∈ S.completeAtU u,
        (S.coefficientMean c i) ^ 2 / ((S.orbit i).card : ℝ) ≤
      20000 * (t : ℝ) * S.rawNormSq (S.synth c.val) := by
  classical
  let C : Finset (Fin d) := S.completeAtU u
  let a := S.totalMean c.val
  let V := S.totalVariance c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hV0 : 0 ≤ V := S.totalVariance_nonneg c
  have hnorm : S.rawNormSq (S.synth c.val) = a ^ 2 + V :=
    S.rawNormSq_synth_eq c
  by_cases hav : ∃ h : Fin d, S.Complete h ∧ u ∉ S.orbit h
  · rcases hav with ⟨h, hh, huh⟩
    have hterm : ∀ i ∈ C,
        (q : ℝ) * ((S.coefficientMean c i) ^ 2 /
          ((S.orbit i).card : ℝ)) ≤ 8 * a ^ 2 := by
      intro i hiC
      have hi := (S.mem_completeAtU_iff u i).1 hiC
      have hmean := OutsideCoeff.complete_mean_eq_total_of_avoiding
        (S := S) c horth i h hi.1 hh hi.2 huh
      have hmean' : S.coefficientMean c i = a := by
        simpa [coefficientMean, a] using hmean
      have hmpos : 0 < ((S.orbit i).card : ℝ) := by
        exact_mod_cast (S.orbit_nonempty i).card_pos
      have hqR : (q : ℝ) ≤ 8 * ((S.orbit i).card : ℝ) := by
        exact_mod_cast H.orbit_lower i
      have hdiv : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 :=
        (div_le_iff₀ hmpos).2 hqR
      rw [hmean']
      calc
        (q : ℝ) * (a ^ 2 / ((S.orbit i).card : ℝ)) =
            ((q : ℝ) / ((S.orbit i).card : ℝ)) * a ^ 2 := by ring
        _ ≤ 8 * a ^ 2 :=
          mul_le_mul_of_nonneg_right hdiv (sq_nonneg _)
    have hsum :
        (q : ℝ) * ∑ i ∈ C,
            (S.coefficientMean c i) ^ 2 /
              ((S.orbit i).card : ℝ) ≤
          8 * (C.card : ℝ) * a ^ 2 := by
      rw [Finset.mul_sum]
      calc
        ∑ i ∈ C, (q : ℝ) *
            ((S.coefficientMean c i) ^ 2 /
              ((S.orbit i).card : ℝ)) ≤
            ∑ _i ∈ C, 8 * a ^ 2 :=
          Finset.sum_le_sum fun i hi => hterm i hi
        _ = 8 * (C.card : ℝ) * a ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    have hcardNat : C.card ≤ t :=
      le_trans (S.card_completeAtU_le u) H.coord_le
    have hcard : (C.card : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hcardNat
    have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
    rw [show S.completeAtU u = C by rfl, hnorm]
    nlinarith
  · have hcontains : ∀ i, S.Complete i → u ∈ S.orbit i := by
      intro i hi
      by_contra hui
      exact hav ⟨i, hi, hui⟩
    by_cases hCempty : C = ∅
    · have hCempty' : S.completeAtU u = ∅ := by
        simpa [C] using hCempty
      rw [hCempty', hnorm]
      simp only [Finset.sum_empty, mul_zero]
      positivity
    have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hCempty
    let i0 := hCne.choose
    have hi0C : i0 ∈ C := hCne.choose_spec
    have hi0 := (S.mem_completeAtU_iff u i0).1 hi0C
    let lam := (a - S.coefficientMean c i0) /
      ((S.orbit i0).card : ℝ)
    let I : Finset (Fin d) := S.incompleteIndices
    let b := ∑ i ∈ I, S.coefficientMean c i
    have hrel : ∀ i ∈ C,
        S.coefficientMean c i =
          a - ((S.orbit i).card : ℝ) * lam := by
      intro i hiC
      have hi := (S.mem_completeAtU_iff u i).1 hiC
      have hscaled := OutsideCoeff.complete_scaled_defect_eq
        (S := S) c horth i i0 hi.1 hi0.1 hi.2 hi0.2
      have hscaled' :
          (a - S.coefficientMean c i) / ((S.orbit i).card : ℝ) =
            (a - S.coefficientMean c i0) /
              ((S.orbit i0).card : ℝ) := by
        simpa [a, coefficientMean] using hscaled
      have hmi : ((S.orbit i).card : ℝ) ≠ 0 := by
        exact_mod_cast (S.orbit_nonempty i).card_ne_zero
      unfold lam
      have hnum :
          a - S.coefficientMean c i =
            ((S.orbit i).card : ℝ) *
              ((a - S.coefficientMean c i0) /
                ((S.orbit i0).card : ℝ)) := by
        calc
          a - S.coefficientMean c i =
              ((S.orbit i).card : ℝ) *
                ((a - S.coefficientMean c i) /
                  ((S.orbit i).card : ℝ)) := by
            field_simp [hmi]
          _ = ((S.orbit i).card : ℝ) *
                ((a - S.coefficientMean c i0) /
                  ((S.orbit i0).card : ℝ)) := by
            rw [hscaled']
      linarith
    have hpartition :
        (∑ i, S.coefficientMean c i) =
          (∑ i ∈ C, S.coefficientMean c i) + b := by
      have hCeq : C = Finset.univ.filter S.Complete := by
        ext i
        simp only [C, completeAtU, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · exact fun hi => hi.1
        · exact fun hi => ⟨hi, hcontains i hi⟩
      rw [hCeq]
      unfold b I incompleteIndices
      exact (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := S.Complete)
        (f := fun i => S.coefficientMean c i)).symm
    have hsumC :
        (∑ i ∈ C, S.coefficientMean c i) =
          (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
      calc
        (∑ i ∈ C, S.coefficientMean c i) =
            ∑ i ∈ C, (a - ((S.orbit i).card : ℝ) * lam) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrel i hi
        _ = (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
          rw [Finset.sum_sub_distrib, Finset.sum_const,
            Finset.sum_mul, nsmul_eq_mul]
    have heq :
        (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam =
          ((C.card : ℝ) - 1) * a + b := by
      have ha : a = ∑ i, S.coefficientMean c i := by
        rfl
      rw [ha, hpartition, hsumC]
      ring
    have hb : b ^ 2 ≤ 8 * (t : ℝ) * V := by
      exact S.incomplete_mean_sum_sq_le c H hgapU
    have hcardNat : C.card ≤ t :=
      le_trans (S.card_completeAtU_le u) H.coord_le
    have hcard : (C.card : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast hcardNat
    have hmpos : ∀ i ∈ C, 0 < ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hlower : ∀ i ∈ C,
        (q : ℝ) ≤ 8 * ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast H.orbit_lower i
    have hupper : ∀ i ∈ C,
        ((S.orbit i).card : ℝ) ≤ (q : ℝ) := by
      intro i _
      exact_mod_cast H.orbit_upper i
    have hmain := weighted_complete_mean_bound
      C (fun i => ((S.orbit i).card : ℝ))
      (fun i => S.coefficientMean c i)
      (q : ℝ) (t : ℝ) a b lam V ht hq0 hV0 hcard hmpos
      hlower hupper hrel heq hb
    rw [show S.completeAtU u = C by rfl, hnorm]
    exact hmain

end SectorData
end IndependentMatchingBlockOccupancy
