import LeanQuantumQueries.IndependentMatchingConditioningFinal
import LeanQuantumQueries.IndependentMatchingNumericsFinal
import LeanQuantumQueries.IndependentMatchingDefectArithmeticFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Incomplete row means are controlled by total row variance. -/
theorem incomplete_mean_sum_sq_leF
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t) :
    (∑ i ∈ S.incompleteIndicesF, S.rowMeanF c i) ^ 2 ≤
      8 * (t : ℝ) * S.totalVarianceF c := by
  classical
  let I := S.incompleteIndicesF
  have hcs := Finset.sq_sum_le_card_mul_sum_sq
    (s := I) (f := fun i => S.rowMeanF c i)
  have hrows :
      (∑ i ∈ I, (S.rowMeanF c i) ^ 2) ≤
        8 * ∑ i ∈ I, S.rowVarianceF c i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hinc : ¬ S.Complete i :=
      (S.mem_incompleteIndicesF_iff i).1 hi
    exact OutsideCoeff.mean_sq_le_eight_variance (S := S) c i
      (H.incomplete_gap u i hinc)
  have hvar := S.sum_rowVarianceF_le_total c I
  have hcardNat : I.card ≤ t := S.card_indexSetF_le_t H I
  have hcard : (I.card : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hcardNat
  have hlocal : 0 ≤ ∑ i ∈ I, S.rowVarianceF c i :=
    Finset.sum_nonneg fun i _ => S.rowVarianceF_nonneg c i
  have htotal := S.totalVarianceF_nonneg c
  have ht : 0 ≤ (t : ℝ) := by positivity
  nlinarith

/-- Defect contribution of incomplete coordinates containing `u`. -/
theorem incomplete_defect_boundF
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t) :
    (q : ℝ) * ∑ i ∈ S.incompleteAtUIndicesF u,
        (S.totalMean c.val - S.rowMeanF c i) ^ 2 /
          ((S.orbit i).card : ℝ) ≤
      144 * (t : ℝ) *
        ((S.totalMean c.val) ^ 2 + S.totalVarianceF c) := by
  classical
  let J := S.incompleteAtUIndicesF u
  let I := S.incompleteIndicesF
  let a := S.totalMean c.val
  let V := S.totalVarianceF c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hV : 0 ≤ V := S.totalVarianceF_nonneg c
  have hterm : ∀ i ∈ J,
      (q : ℝ) * ((a - S.rowMeanF c i) ^ 2 /
        ((S.orbit i).card : ℝ)) ≤
        16 * a ^ 2 + 16 * (S.rowMeanF c i) ^ 2 := by
    intro i hi
    have hmi : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hratio : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
      apply (div_le_iff₀ hmi).2
      exact_mod_cast H.orbit_lower i
    have hdef : (a - S.rowMeanF c i) ^ 2 ≤
        2 * a ^ 2 + 2 * (S.rowMeanF c i) ^ 2 := by
      nlinarith [sq_nonneg (a + S.rowMeanF c i)]
    calc
      (q : ℝ) * ((a - S.rowMeanF c i) ^ 2 /
          ((S.orbit i).card : ℝ)) =
          ((q : ℝ) / ((S.orbit i).card : ℝ)) *
            (a - S.rowMeanF c i) ^ 2 := by ring
      _ ≤ 8 * (a - S.rowMeanF c i) ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
      _ ≤ 8 * (2 * a ^ 2 + 2 * (S.rowMeanF c i) ^ 2) :=
        mul_le_mul_of_nonneg_left hdef (by norm_num)
      _ = 16 * a ^ 2 + 16 * (S.rowMeanF c i) ^ 2 := by ring
  have hsum :
      (q : ℝ) * ∑ i ∈ J,
          (a - S.rowMeanF c i) ^ 2 /
            ((S.orbit i).card : ℝ) ≤
        16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanF c i) ^ 2 := by
    rw [Finset.mul_sum]
    calc
      ∑ i ∈ J, (q : ℝ) *
          ((a - S.rowMeanF c i) ^ 2 /
            ((S.orbit i).card : ℝ)) ≤
          ∑ i ∈ J,
            (16 * a ^ 2 + 16 * (S.rowMeanF c i) ^ 2) :=
        Finset.sum_le_sum fun i hi => hterm i hi
      _ = 16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanF c i) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const,
          Finset.mul_sum, nsmul_eq_mul]
        ring
  have hJsubI : J ⊆ I := by
    intro i hi
    exact (S.mem_incompleteIndicesF_iff i).2
      ((S.mem_incompleteAtUIndicesF_iff u i).1 hi).1
  have hmeanJ :
      (∑ i ∈ J, (S.rowMeanF c i) ^ 2) ≤
        8 * S.totalVarianceF c := by
    have hsub :
        (∑ i ∈ J, (S.rowMeanF c i) ^ 2) ≤
          ∑ i ∈ I, (S.rowMeanF c i) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hJsubI
      intro i _ _
      exact sq_nonneg _
    have hrows :
        (∑ i ∈ I, (S.rowMeanF c i) ^ 2) ≤
          8 * ∑ i ∈ I, S.rowVarianceF c i := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hinc := (S.mem_incompleteIndicesF_iff i).1 hi
      exact OutsideCoeff.mean_sq_le_eight_variance (S := S) c i
        (H.incomplete_gap u i hinc)
    have hvar := S.sum_rowVarianceF_le_total c I
    have hlocal : 0 ≤ ∑ i ∈ I, S.rowVarianceF c i :=
      Finset.sum_nonneg fun i _ => S.rowVarianceF_nonneg c i
    nlinarith
  have hcardNat : J.card ≤ t := S.card_indexSetF_le_t H J
  have hcard : (J.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
  have ha0 : 0 ≤ a ^ 2 := sq_nonneg _
  have htarget :
      16 * (J.card : ℝ) * a ^ 2 +
          16 * ∑ i ∈ J, (S.rowMeanF c i) ^ 2 ≤
        144 * (t : ℝ) * (a ^ 2 + V) := by
    nlinarith
  exact le_trans hsum htarget

/-- Defect contribution of complete coordinates containing `u`. -/
theorem complete_defect_boundF
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val)) :
    (q : ℝ) * ∑ i ∈ S.completeAtUIndicesF u,
        (S.totalMean c.val - S.rowMeanF c i) ^ 2 /
          ((S.orbit i).card : ℝ) ≤
      200 * (t : ℝ) *
        ((S.totalMean c.val) ^ 2 + S.totalVarianceF c) := by
  classical
  let C := S.completeAtUIndicesF u
  let a := S.totalMean c.val
  let V := S.totalVarianceF c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hV : 0 ≤ V := S.totalVarianceF_nonneg c
  by_cases hav : ∃ h : Fin d, S.Complete h ∧ u ∉ S.orbit h
  · rcases hav with ⟨h, hh, huh⟩
    have hsumzero :
        (∑ i ∈ C,
          (a - S.rowMeanF c i) ^ 2 /
            ((S.orbit i).card : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := (S.mem_completeAtUIndicesF_iff u i).1 hi
      have hm := OutsideCoeff.complete_mean_eq_total_of_avoidingF
        (S := S) c horth i h hi'.1 hh hi'.2 huh
      have hz : a - S.rowMeanF c i = 0 := by
        simpa [a, rowMeanF] using sub_eq_zero.mpr hm.symm
      rw [hz]
      simp
    rw [hsumzero]
    positivity
  · have hcontains : ∀ i, S.Complete i → u ∈ S.orbit i := by
      intro i hi
      by_contra hui
      exact hav ⟨i, hi, hui⟩
    by_cases hCempty : C = ∅
    · subst C
      simp [ht, hV]
    have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hCempty
    let i0 : Fin d := hCne.choose
    have hi0C : i0 ∈ C := hCne.choose_spec
    have hi0 := (S.mem_completeAtUIndicesF_iff u i0).1 hi0C
    let lam : ℝ :=
      (a - S.rowMeanF c i0) / ((S.orbit i0).card : ℝ)
    let I := S.incompleteIndicesF
    let b : ℝ := ∑ i ∈ I, S.rowMeanF c i
    have hdef : ∀ i ∈ C,
        a - S.rowMeanF c i =
          ((S.orbit i).card : ℝ) * lam := by
      intro i hiC
      have hi := (S.mem_completeAtUIndicesF_iff u i).1 hiC
      have hscaled := OutsideCoeff.complete_scaled_defect_eqF
        (S := S) c horth i i0 hi.1 hi0.1 hi.2 hi0.2
      have hscaled' :
          (a - S.rowMeanF c i) / ((S.orbit i).card : ℝ) =
          (a - S.rowMeanF c i0) / ((S.orbit i0).card : ℝ) := by
        simpa [a, rowMeanF] using hscaled
      have hmi : ((S.orbit i).card : ℝ) ≠ 0 := by
        exact_mod_cast (S.orbit_nonempty i).card_ne_zero
      calc
        a - S.rowMeanF c i =
            ((S.orbit i).card : ℝ) *
              ((a - S.rowMeanF c i) /
                ((S.orbit i).card : ℝ)) := by
          field_simp [hmi]
        _ = ((S.orbit i).card : ℝ) *
              ((a - S.rowMeanF c i0) /
                ((S.orbit i0).card : ℝ)) := by
          rw [hscaled']
        _ = ((S.orbit i).card : ℝ) * lam := rfl
    have hCeq : C = Finset.univ.filter S.Complete := by
      ext i
      simp [C, completeAtUIndicesF, hcontains i]
    have hpartition :
        (∑ i, S.rowMeanF c i) =
          (∑ i ∈ C, S.rowMeanF c i) + b := by
      rw [hCeq]
      unfold b I incompleteIndicesF
      exact (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin d)))
        (p := S.Complete)
        (f := fun i => S.rowMeanF c i)).symm
    have hsumC :
        (∑ i ∈ C, S.rowMeanF c i) =
          (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
      calc
        (∑ i ∈ C, S.rowMeanF c i) =
            ∑ i ∈ C,
              (a - ((S.orbit i).card : ℝ) * lam) := by
          apply Finset.sum_congr rfl
          intro i hi
          linarith [hdef i hi]
        _ = (C.card : ℝ) * a -
            (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam := by
          rw [Finset.sum_sub_distrib, Finset.sum_const,
            Finset.sum_mul, nsmul_eq_mul]
          ring
    have haSum : a = ∑ i, S.rowMeanF c i := by
      unfold a rowMeanF totalMean
      rfl
    have heq :
        (∑ i ∈ C, ((S.orbit i).card : ℝ)) * lam =
          ((C.card : ℝ) - 1) * a + b := by
      rw [haSum, hpartition, hsumC]
      ring
    have hb : b ^ 2 ≤ 8 * (t : ℝ) * V := by
      exact S.incomplete_mean_sum_sq_leF c H
    have hcardNat : C.card ≤ t := S.card_indexSetF_le_t H C
    have hcard : (C.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
    have hmpos : ∀ i ∈ C, 0 < ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hlower : ∀ i ∈ C,
        (q : ℝ) ≤ 8 * ((S.orbit i).card : ℝ) := by
      intro i _
      exact_mod_cast H.orbit_lower i
    have harith := weighted_complete_defect_boundF
      C (fun i => ((S.orbit i).card : ℝ))
      (q : ℝ) (t : ℝ) a b lam V ht hq hV hcard hmpos hlower heq hb
    have hrewrite :
        (q : ℝ) * ∑ i ∈ C,
            (a - S.rowMeanF c i) ^ 2 /
              ((S.orbit i).card : ℝ) =
          (q : ℝ) * ∑ i ∈ C,
            ((((S.orbit i).card : ℝ) * lam) ^ 2 /
              ((S.orbit i).card : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdef i hi]
    rw [hrewrite]
    exact harith

/-- Contribution of all remaining-row variances. -/
theorem remaining_variance_boundF
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t) :
    (q : ℝ) * ∑ i ∈ S.atUIndicesF u,
        (∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
          ((S.orbit i).card : ℝ) ≤
      8 * (t : ℝ) * S.totalVarianceF c := by
  classical
  let U := S.atUIndicesF u
  let V := S.totalVarianceF c
  have hterm : ∀ i ∈ U,
      (q : ℝ) *
          ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ)) ≤ 8 * V := by
    intro i _
    have hmi : 0 < ((S.orbit i).card : ℝ) := by
      exact_mod_cast (S.orbit_nonempty i).card_pos
    have hratio : (q : ℝ) / ((S.orbit i).card : ℝ) ≤ 8 := by
      apply (div_le_iff₀ hmi).2
      exact_mod_cast H.orbit_lower i
    have hsum := S.sum_rowVarianceF_le_total c (Finset.univ.erase i)
    have hsum0 : 0 ≤
        ∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j :=
      Finset.sum_nonneg fun j _ => S.rowVarianceF_nonneg c j
    calc
      (q : ℝ) *
          ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ)) =
          ((q : ℝ) / ((S.orbit i).card : ℝ)) *
            (∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) := by ring
      _ ≤ 8 * (∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) :=
        mul_le_mul_of_nonneg_right hratio hsum0
      _ ≤ 8 * V := mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ U, (q : ℝ) *
        ((∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
          ((S.orbit i).card : ℝ)) ≤
        ∑ i ∈ U, 8 * V :=
      Finset.sum_le_sum fun i hi => hterm i hi
    _ = 8 * (U.card : ℝ) * V := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 8 * (t : ℝ) * V := by
      have hcardNat : U.card ≤ t := S.card_indexSetF_le_t H U
      have hcard : (U.card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcardNat
      have hV := S.totalVarianceF_nonneg c
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcard (by norm_num)) hV

/-- Product-table occupied upper sum. -/
theorem rawOccupiedUpperF_bound
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t)
    (horth : S.RawCommonOrthogonal u (S.synth c.val)) :
    (q : ℝ) * S.rawOccupiedUpperF c ≤
      352 * (t : ℝ) * S.rawNormSq (S.synth c.val) := by
  classical
  let U := S.atUIndicesF u
  let C := S.completeAtUIndicesF u
  let J := S.incompleteAtUIndicesF u
  let a := S.totalMean c.val
  let V := S.totalVarianceF c
  have hUCJ : U = C ∪ J := by
    ext i
    by_cases hi : S.Complete i <;>
      simp [U, C, J, atUIndicesF, completeAtUIndicesF,
        incompleteAtUIndicesF, hi]
  have hdisj : Disjoint C J := by
    refine Finset.disjoint_left.2 ?_
    intro i hiC hiJ
    have hc := (S.mem_completeAtUIndicesF_iff u i).1 hiC
    have hj := (S.mem_incompleteAtUIndicesF_iff u i).1 hiJ
    exact hj.1 hc.1
  have hCsubU : C ⊆ U := by
    intro i hi
    exact (S.mem_atUIndicesF_iff u i).2
      ((S.mem_completeAtUIndicesF_iff u i).1 hi).2
  have hJsubU : J ⊆ U := by
    intro i hi
    exact (S.mem_atUIndicesF_iff u i).2
      ((S.mem_incompleteAtUIndicesF_iff u i).1 hi).2
  have hformula : ∀ i, i ∈ U →
      S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) =
        ((a - S.rowMeanF c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ) := by
    intro i hiU
    have hui : u ∈ S.orbit i :=
      (S.mem_atUIndicesF_iff u i).1 hiU
    rw [OutsideCoeff.rawAvg_atU_mul_synth_sqF (S := S) c i hui,
      S.rawNormSq_synth_eraseRowF]
    rfl
  unfold rawOccupiedUpperF
  change (q : ℝ) * ∑ i ∈ U,
    S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2) ≤ _
  rw [hUCJ, Finset.sum_union hdisj]
  have hformulaC :
      (∑ i ∈ C,
        S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)) =
      ∑ i ∈ C,
        ((a - S.rowMeanF c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hformula i (hCsubU hi)
  have hformulaJ :
      (∑ i ∈ J,
        S.rawAvg (fun x => S.rawAtU u i x * (S.synth c.val x) ^ 2)) =
      ∑ i ∈ J,
        ((a - S.rowMeanF c i) ^ 2 +
          ∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hformula i (hJsubU hi)
  rw [hformulaC, hformulaJ]
  simp only [add_div, Finset.sum_add_distrib]
  have hC := S.complete_defect_boundF c H horth
  have hJ := S.incomplete_defect_boundF c H
  have hRem := S.remaining_variance_boundF c H
  have hRemSplit :
      (q : ℝ) *
        ((∑ i ∈ C,
          (∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ)) +
         (∑ i ∈ J,
          (∑ j ∈ (Finset.univ.erase i), S.rowVarianceF c j) /
            ((S.orbit i).card : ℝ))) ≤
        8 * (t : ℝ) * V := by
    rw [← Finset.sum_union hdisj, ← hUCJ]
    exact hRem
  have hnorm := S.rawNormSq_synth_eq_mean_varianceF c
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hnonneg : 0 ≤ a ^ 2 + V :=
    add_nonneg (sq_nonneg _) (S.totalVarianceF_nonneg c)
  rw [hnorm]
  nlinarith

end SectorData
end IndependentMatchingBlockOccupancy
