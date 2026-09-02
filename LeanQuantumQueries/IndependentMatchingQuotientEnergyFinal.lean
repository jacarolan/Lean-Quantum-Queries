import LeanQuantumQueries.IndependentMatchingProjectionFinal
import LeanQuantumQueries.IndependentMatchingLegalOccupancyFinal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Every raw outside vector has an outside-supported coefficient
representation. -/
theorem exists_outsideCoeff_of_mem_rawOutsideF
    (u : Fin B) {f : S.RawVector} (hf : f ∈ S.rawOutsideSpace u) :
    ∃ c : S.OutsideCoeff u, S.synth c.val = f := by
  rw [← S.map_outsideCoeff_eq_rawOutside u] at hf
  rcases hf with ⟨g, hg, hgf⟩
  exact ⟨{ val := g, zero_of_not_allowed := hg }, hgf⟩

/-- Raw squared norm is nonnegative. -/
theorem rawNormSq_nonnegF (f : S.RawVector) :
    0 ≤ S.rawNormSq f := by
  unfold rawNormSq rawInner rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => mul_self_nonneg _
  · positivity

/-- Good energy is at most total raw energy. -/
theorem rawGoodEnergyF_le_rawNormSq (f : S.RawVector) :
    S.rawGoodEnergyF f ≤ S.rawNormSq f := by
  have hsplit := S.rawNormSq_eq_good_add_badF f
  have hbad := S.rawBadEnergyF_nonneg f
  linarith

/-- Collision-smallness of a common component in an arbitrary additive
common-plus-orthogonal decomposition. -/
theorem common_part_energy_bound_auxF
    {q t : ℕ} {u : Fin B}
    (c p z : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t)
    (hdecomp : S.synth c.val = S.synth p.val + S.synth z.val)
    (hpcommon : S.synth p.val ∈ S.rawCommonSpace u)
    (hzorth : S.RawCommonOrthogonal u (S.synth z.val))
    (hquot : S.InOutsideQuotient u (S.restrict (S.synth c.val))) :
    (q : ℝ) * S.rawNormSq (S.synth p.val) ≤
      24 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth c.val) := by
  let P := S.synth p.val
  let Z := S.synth z.val
  let G := S.synth c.val
  let A := S.rawNormSq P
  let D := S.rawNormSq Z
  have hpinter := S.restrict_rawCommon_mem_inter u hpcommon
  rw [Submodule.mem_inf] at hpinter
  have hlegal : S.inner (S.restrict G) (S.restrict P) = 0 :=
    hquot.2 _ hpinter.1 hpinter.2
  have hgoodG : S.rawGoodInnerF G P = 0 :=
    S.rawGoodInnerF_eq_zero_of_inner_eq_zero G P hlegal
  have hGP : G = P + Z := hdecomp
  have hgoodSum :
      S.rawGoodInnerF P P + S.rawGoodInnerF Z P = 0 := by
    rw [hGP, S.rawGoodInnerF_add_left] at hgoodG
    exact hgoodG
  have hrawOrth : S.rawInner Z P = 0 := hzorth P hpcommon
  have hbadCross :
      S.rawGoodInnerF Z P + S.rawBadInnerF Z P = 0 := by
    rw [S.rawInner_eq_good_add_badF] at hrawOrth
    exact hrawOrth
  have hnormP :
      A = S.rawGoodEnergyF P + S.rawBadEnergyF P := by
    unfold A
    exact S.rawNormSq_eq_good_add_badF P
  rw [S.rawGoodInnerF_self] at hgoodSum
  have hcommonIdentity :
      A = S.rawBadEnergyF P + S.rawBadInnerF Z P := by
    linarith
  have hcross := S.two_mul_rawBadInnerF_le Z P
  have hbadP := S.rawBadEnergyF_bound p.val H
  have hbadZ := S.rawBadEnergyF_bound z.val H
  have hpyth : S.rawNormSq G = A + D := by
    unfold G A D P Z
    rw [hdecomp]
    unfold rawNormSq
    rw [S.rawInner_add_left, S.rawInner_add_right,
      S.rawInner_add_right]
    have horth' : S.rawInner (S.synth p.val) (S.synth z.val) = 0 := by
      unfold rawInner rawAvg at hrawOrth ⊢
      simpa [mul_comm] using hrawOrth
    rw [hrawOrth, horth']
    ring
  have hA : 0 ≤ A := S.rawNormSq_nonnegF P
  have hD : 0 ≤ D := S.rawNormSq_nonnegF Z
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hcrossScaled :
      (q : ℝ) * (2 * S.rawBadInnerF Z P) ≤
        (q : ℝ) *
          (S.rawBadEnergyF Z + S.rawBadEnergyF P) :=
    mul_le_mul_of_nonneg_left hcross hq
  have htwice :
      2 * ((q : ℝ) * A) ≤
        3 * ((q : ℝ) * S.rawBadEnergyF P) +
          (q : ℝ) * S.rawBadEnergyF Z := by
    have hid :
        2 * ((q : ℝ) * A) =
          2 * ((q : ℝ) * S.rawBadEnergyF P) +
            (q : ℝ) * (2 * S.rawBadInnerF Z P) := by
      rw [hcommonIdentity]
      ring
    rw [hid]
    calc
      2 * ((q : ℝ) * S.rawBadEnergyF P) +
          (q : ℝ) * (2 * S.rawBadInnerF Z P) ≤
          2 * ((q : ℝ) * S.rawBadEnergyF P) +
            (q : ℝ) *
              (S.rawBadEnergyF Z + S.rawBadEnergyF P) :=
        add_le_add_left hcrossScaled _
      _ = 3 * ((q : ℝ) * S.rawBadEnergyF P) +
          (q : ℝ) * S.rawBadEnergyF Z := by ring
  have hbadP3 :
      3 * ((q : ℝ) * S.rawBadEnergyF P) ≤
        3 * (16 * (t : ℝ) ^ 3 * A) :=
    mul_le_mul_of_nonneg_left hbadP (by norm_num)
  have hbadSum :
      3 * ((q : ℝ) * S.rawBadEnergyF P) +
          (q : ℝ) * S.rawBadEnergyF Z ≤
        3 * (16 * (t : ℝ) ^ 3 * A) +
          16 * (t : ℝ) ^ 3 * D :=
    add_le_add hbadP3 hbadZ
  have hqA :
      (q : ℝ) * A ≤ 24 * (t : ℝ) ^ 3 * (A + D) := by
    have ht3 : 0 ≤ (t : ℝ) ^ 3 := by positivity
    have hbound := le_trans htwice hbadSum
    nlinarith
  rw [← hpyth] at hqA
  exact hqA

/-- The orthogonally projected common component is collision-small. -/
theorem rawCommonPartF_energy_bound
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t)
    (hquot : S.InOutsideQuotient u (S.restrict (S.synth c.val))) :
    (q : ℝ) *
        S.rawNormSq (S.rawCommonPartF u (S.synth c.val)) ≤
      24 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth c.val) := by
  let G := S.synth c.val
  let P := S.rawCommonPartF u G
  let Z := S.rawCommonRemainderF u G
  have hpcommon : P ∈ S.rawCommonSpace u :=
    S.rawCommonPartF_mem u G
  have hpoutside : P ∈ S.rawOutsideSpace u :=
    (S.rawCommonSpace_le_inter u hpcommon).2
  have hGoutside : G ∈ S.rawOutsideSpace u :=
    S.synth_mem_rawOutside c.zero_of_not_allowed
  have hzoutside : Z ∈ S.rawOutsideSpace u := by
    unfold Z rawCommonRemainderF
    exact Submodule.sub_mem _ hGoutside hpoutside
  rcases S.exists_outsideCoeff_of_mem_rawOutsideF u hpoutside with
    ⟨p, hp⟩
  rcases S.exists_outsideCoeff_of_mem_rawOutsideF u hzoutside with
    ⟨z, hz⟩
  have hdecomp : S.synth c.val = S.synth p.val + S.synth z.val := by
    rw [hp, hz]
    exact (S.rawCommonPartF_add_remainder u G).symm
  have hpcommon' : S.synth p.val ∈ S.rawCommonSpace u := by
    rw [hp]
    exact hpcommon
  have hzorth : S.RawCommonOrthogonal u (S.synth z.val) := by
    rw [hz]
    exact S.rawCommonRemainderF_rawOrthogonal u G
  have haux := S.common_part_energy_bound_auxF c p z H hdecomp
    hpcommon' hzorth hquot
  rw [hp] at haux
  exact haux

/-- Sector-level legal quotient occupied-energy theorem. -/
theorem quotient_occupiedEnergy_boundF
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hquot : S.InOutsideQuotient u (S.restrict (S.synth c.val))) :
    (q : ℝ) *
        S.occupiedEnergy u (S.restrict (S.synth c.val)) ≤
      1504 * (t : ℝ) ^ 3 *
        S.totalEnergy (S.restrict (S.synth c.val)) := by
  let G := S.synth c.val
  let P := S.rawCommonPartF u G
  let Z := S.rawCommonRemainderF u G
  have hpcommon : P ∈ S.rawCommonSpace u :=
    S.rawCommonPartF_mem u G
  have hpoutside : P ∈ S.rawOutsideSpace u :=
    (S.rawCommonSpace_le_inter u hpcommon).2
  have hGoutside : G ∈ S.rawOutsideSpace u :=
    S.synth_mem_rawOutside c.zero_of_not_allowed
  have hzoutside : Z ∈ S.rawOutsideSpace u := by
    unfold Z rawCommonRemainderF
    exact Submodule.sub_mem _ hGoutside hpoutside
  rcases S.exists_outsideCoeff_of_mem_rawOutsideF u hzoutside with
    ⟨z, hz⟩
  have hzorth : S.RawCommonOrthogonal u (S.synth z.val) := by
    rw [hz]
    exact S.rawCommonRemainderF_rawOrthogonal u G
  have hGdecomp : G = P + Z :=
    (S.rawCommonPartF_add_remainder u G).symm
  have hrestrict : S.restrict G = S.restrict P + S.restrict Z := by
    rw [hGdecomp]
    rfl
  have hsubadd := S.occupiedEnergy_add_le_twoF u
    (S.restrict P) (S.restrict Z)
  rw [← hrestrict] at hsubadd
  have hpocc :
      S.occupiedEnergy u (S.restrict P) ≤
        (Fintype.card S.RawPlacement : ℝ) * S.rawNormSq P := by
    calc
      S.occupiedEnergy u (S.restrict P) ≤
          S.totalEnergy (S.restrict P) :=
        S.occupiedEnergy_le_totalEnergyF u _
      _ = (Fintype.card S.RawPlacement : ℝ) *
          S.rawGoodEnergyF P := by
        symm
        exact S.rawCard_mul_rawGoodEnergyF_eq_totalEnergy P
      _ ≤ (Fintype.card S.RawPlacement : ℝ) *
          S.rawNormSq P :=
        mul_le_mul_of_nonneg_left
          (S.rawGoodEnergyF_le_rawNormSq P) (by positivity)
  have hzocc :
      S.occupiedEnergy u (S.restrict Z) ≤
        (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpperF z := by
    rw [← hz]
    exact S.occupiedEnergy_restrict_le_rawCard_mul_upperF z
  have hpbound := S.rawCommonPartF_energy_bound c H hquot
  have hzprod := S.rawOccupiedUpperF_bound z H hzorth
  have hZleG : S.rawNormSq Z ≤ S.rawNormSq G := by
    have hpyth := S.rawNormSq_common_decompositionF u G
    have hp0 := S.rawNormSq_nonnegF P
    change S.rawNormSq (S.rawCommonRemainderF u G) ≤ S.rawNormSq G
    nlinarith
  have hzprodG :
      (q : ℝ) * S.rawOccupiedUpperF z ≤
        352 * (t : ℝ) * S.rawNormSq G := by
    have hzEq : S.synth z.val = Z := hz
    rw [hzEq] at hzprod
    exact le_trans hzprod
      (mul_le_mul_of_nonneg_left hZleG (by positivity))
  have hclip := S.rawNormSq_le_two_rawGoodEnergyF c.val H hlarge
  have hcardgood := S.rawCard_mul_rawGoodEnergyF_eq_totalEnergy G
  let R : ℝ := Fintype.card S.RawPlacement
  have hR : 0 ≤ R := by positivity
  have hq : 0 ≤ (q : ℝ) := by positivity
  have ht : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast H.t_pos
  have hoccScaled :
      (q : ℝ) * S.occupiedEnergy u (S.restrict G) ≤
        2 * R * ((q : ℝ) * S.rawNormSq P) +
          2 * R * ((q : ℝ) * S.rawOccupiedUpperF z) := by
    calc
      (q : ℝ) * S.occupiedEnergy u (S.restrict G) ≤
          (q : ℝ) *
            (2 * S.occupiedEnergy u (S.restrict P) +
              2 * S.occupiedEnergy u (S.restrict Z)) :=
        mul_le_mul_of_nonneg_left hsubadd hq
      _ ≤ (q : ℝ) *
            (2 * (R * S.rawNormSq P) +
              2 * (R * S.rawOccupiedUpperF z)) := by
        apply mul_le_mul_of_nonneg_left _ hq
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpocc (by norm_num))
          (mul_le_mul_of_nonneg_left hzocc (by norm_num))
      _ = 2 * R * ((q : ℝ) * S.rawNormSq P) +
          2 * R * ((q : ℝ) * S.rawOccupiedUpperF z) := by ring
  have hfirst :
      2 * R * ((q : ℝ) * S.rawNormSq P) ≤
        2 * R * (24 * (t : ℝ) ^ 3 * S.rawNormSq G) :=
    mul_le_mul_of_nonneg_left hpbound (mul_nonneg (by norm_num) hR)
  have hsecond :
      2 * R * ((q : ℝ) * S.rawOccupiedUpperF z) ≤
        2 * R * (352 * (t : ℝ) * S.rawNormSq G) :=
    mul_le_mul_of_nonneg_left hzprodG (mul_nonneg (by norm_num) hR)
  have hG0 := S.rawNormSq_nonnegF G
  have hrawStage :
      (q : ℝ) * S.occupiedEnergy u (S.restrict G) ≤
        752 * R * (t : ℝ) ^ 3 * S.rawNormSq G := by
    calc
      _ ≤ 2 * R * ((q : ℝ) * S.rawNormSq P) +
          2 * R * ((q : ℝ) * S.rawOccupiedUpperF z) := hoccScaled
      _ ≤ 2 * R * (24 * (t : ℝ) ^ 3 * S.rawNormSq G) +
          2 * R * (352 * (t : ℝ) * S.rawNormSq G) :=
        add_le_add hfirst hsecond
      _ ≤ 752 * R * (t : ℝ) ^ 3 * S.rawNormSq G := by
        have hRt : 0 ≤ R * S.rawNormSq G := mul_nonneg hR hG0
        nlinarith
  have hnear : R * S.rawNormSq G ≤
      2 * S.totalEnergy (S.restrict G) := by
    calc
      R * S.rawNormSq G ≤ R * (2 * S.rawGoodEnergyF G) :=
        mul_le_mul_of_nonneg_left hclip hR
      _ = 2 * (R * S.rawGoodEnergyF G) := by ring
      _ = 2 * S.totalEnergy (S.restrict G) := by
        rw [hcardgood]
  calc
    (q : ℝ) * S.occupiedEnergy u (S.restrict G) ≤
        752 * R * (t : ℝ) ^ 3 * S.rawNormSq G := hrawStage
    _ = 752 * (t : ℝ) ^ 3 * (R * S.rawNormSq G) := by ring
    _ ≤ 752 * (t : ℝ) ^ 3 *
        (2 * S.totalEnergy (S.restrict G)) :=
      mul_le_mul_of_nonneg_left hnear (by positivity)
    _ = 1504 * (t : ℝ) ^ 3 *
        S.totalEnergy (S.restrict G) := by ring

/-- Coefficient-free legal quotient statement. -/
theorem quotient_occupiedEnergy_bound_for_vectorF
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.SectorNumericsF q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    (q : ℝ) * S.occupiedEnergy u f ≤
      1504 * (t : ℝ) ^ 3 * S.totalEnergy f := by
  rcases S.exists_outsideCoeff_of_mem_outside u hf.1 with
    ⟨g, hg, hgf⟩
  let c : S.OutsideCoeff u :=
    { val := g
      zero_of_not_allowed := hg }
  have hquot : S.InOutsideQuotient u
      (S.restrict (S.synth c.val)) := by
    rw [hgf]
    exact hf
  have h := S.quotient_occupiedEnergy_boundF c H hlarge hquot
  rw [hgf] at h
  exact h

end SectorData
end IndependentMatchingBlockOccupancy
