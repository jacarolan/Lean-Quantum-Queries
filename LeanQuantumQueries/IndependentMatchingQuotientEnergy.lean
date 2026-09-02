import LeanQuantumQueries.IndependentMatchingEuclidean
import LeanQuantumQueries.IndependentMatchingLegalOccupancy

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Every raw outside-cylinder vector has an outside-supported coefficient
representation. -/
theorem exists_outsideCoeff_of_mem_rawOutside
    (u : Fin B) {f : S.RawVector} (hf : f ∈ S.rawOutsideSpace u) :
    ∃ c : S.OutsideCoeff u, S.synth c.val = f := by
  rw [← S.map_outsideCoeff_eq_rawOutside u] at hf
  rcases hf with ⟨g, hg, hgf⟩
  let c : S.OutsideCoeff u :=
    { val := g
      zero_of_not_allowed := hg }
  refine ⟨c, ?_⟩
  exact hgf

/-- Raw squared norm is nonnegative. -/
theorem rawNormSq_nonneg (f : S.RawVector) :
    0 ≤ S.rawNormSq f := by
  unfold rawNormSq rawInner rawAvg
  apply div_nonneg
  · exact Finset.sum_nonneg fun x _ => mul_self_nonneg _
  · positivity

/-- Raw good energy is at most total raw energy. -/
theorem rawGoodEnergy_le_rawNormSq (f : S.RawVector) :
    S.rawGoodEnergy f ≤ S.rawNormSq f := by
  have hsplit := S.rawNormSq_eq_good_add_bad f
  have hbad := S.rawBadEnergy_nonneg f
  linarith

/-- Abstract common-part estimate.  All vector hypotheses in this statement
are later supplied by the actual orthogonal projection. -/
theorem common_part_energy_bound_aux
    {q t : ℕ} {u : Fin B}
    (c p z : S.OutsideCoeff u)
    (H : S.SectorNumerics q t)
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
  have hgoodG : S.rawGoodInner G P = 0 :=
    S.rawGoodInner_eq_zero_of_inner_eq_zero G P hlegal
  have hGP : G = P + Z := hdecomp
  have hgoodSum :
      S.rawGoodInner P P + S.rawGoodInner Z P = 0 := by
    rw [hGP, S.rawGoodInner_add_left] at hgoodG
    exact hgoodG
  have hrawOrth : S.rawInner Z P = 0 := hzorth P hpcommon
  have hbadCross :
      S.rawGoodInner Z P + S.rawBadInner Z P = 0 := by
    rw [S.rawInner_eq_good_add_bad] at hrawOrth
    exact hrawOrth
  have hnormP :
      A = S.rawGoodEnergy P + S.rawBadEnergy P := by
    unfold A
    exact S.rawNormSq_eq_good_add_bad P
  have hcommonIdentity :
      A = S.rawBadEnergy P + S.rawBadInner Z P := by
    rw [S.rawGoodInner_self] at hgoodSum
    linarith
  have hcross := S.two_mul_rawBadInner_le Z P
  have hbadP := S.rawBadEnergy_bound p.val H
  have hbadZ := S.rawBadEnergy_bound z.val H
  have hpyth : S.rawNormSq G = A + D := by
    unfold G A D P Z
    rw [hdecomp]
    unfold rawNormSq
    rw [S.rawInner_add_left, S.rawInner_add_right,
      S.rawInner_add_right]
    have horth' : S.rawInner P Z = 0 := by
      unfold rawInner rawAvg at hrawOrth ⊢
      simpa [mul_comm] using hrawOrth
    rw [hrawOrth, horth']
    ring
  have hA : 0 ≤ A := S.rawNormSq_nonneg P
  have hD : 0 ≤ D := S.rawNormSq_nonneg Z
  have hbadP0 := S.rawBadEnergy_nonneg P
  have hbadZ0 := S.rawBadEnergy_nonneg Z
  have hq : 0 ≤ (q : ℝ) := by positivity
  have ht : 0 ≤ (t : ℝ) := by positivity
  nlinarith

/-- The actual projected common component is collision-small. -/
theorem rawCommonPart_energy_bound
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumerics q t)
    (hquot : S.InOutsideQuotient u (S.restrict (S.synth c.val))) :
    (q : ℝ) *
        S.rawNormSq (S.rawCommonPart u (S.synth c.val)) ≤
      24 * (t : ℝ) ^ 3 * S.rawNormSq (S.synth c.val) := by
  let G := S.synth c.val
  let P := S.rawCommonPart u G
  let Z := S.rawCommonRemainder u G
  have hpcommon : P ∈ S.rawCommonSpace u :=
    S.rawCommonPart_mem u G
  have hpoutside : P ∈ S.rawOutsideSpace u :=
    (S.rawCommonSpace_le_inter u hpcommon).2
  have hGoutside : G ∈ S.rawOutsideSpace u :=
    S.synth_mem_rawOutside c.zero_of_not_allowed
  have hzoutside : Z ∈ S.rawOutsideSpace u := by
    unfold Z rawCommonRemainder
    exact Submodule.sub_mem _ hGoutside hpoutside
  rcases S.exists_outsideCoeff_of_mem_rawOutside u hpoutside with
    ⟨p, hp⟩
  rcases S.exists_outsideCoeff_of_mem_rawOutside u hzoutside with
    ⟨z, hz⟩
  have hdecomp : S.synth c.val = S.synth p.val + S.synth z.val := by
    rw [hp, hz]
    exact (S.rawCommonPart_add_remainder u G).symm
  have hpcommon' : S.synth p.val ∈ S.rawCommonSpace u := by
    rw [hp]
    exact hpcommon
  have hzorth : S.RawCommonOrthogonal u (S.synth z.val) := by
    rw [hz]
    exact S.rawCommonRemainder_rawOrthogonal u G
  have haux := S.common_part_energy_bound_aux c p z H hdecomp
    hpcommon' hzorth hquot
  simpa [hp] using haux

/-- Pointwise restriction respects addition. -/
theorem restrict_add (f g : S.RawVector) :
    S.restrict (f + g) = S.restrict f + S.restrict g := by
  rfl

/-- The sector-level quotient occupancy estimate on the actual injective
placement table. -/
theorem quotient_occupiedEnergy_bound
    {q t : ℕ} {u : Fin B} (c : S.OutsideCoeff u)
    (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hquot : S.InOutsideQuotient u (S.restrict (S.synth c.val))) :
    (q : ℝ) *
        S.occupiedEnergy u (S.restrict (S.synth c.val)) ≤
      1504 * (t : ℝ) ^ 3 *
        S.totalEnergy (S.restrict (S.synth c.val)) := by
  let G := S.synth c.val
  let P := S.rawCommonPart u G
  let Z := S.rawCommonRemainder u G
  have hpcommon : P ∈ S.rawCommonSpace u :=
    S.rawCommonPart_mem u G
  have hpoutside : P ∈ S.rawOutsideSpace u :=
    (S.rawCommonSpace_le_inter u hpcommon).2
  have hGoutside : G ∈ S.rawOutsideSpace u :=
    S.synth_mem_rawOutside c.zero_of_not_allowed
  have hzoutside : Z ∈ S.rawOutsideSpace u := by
    unfold Z rawCommonRemainder
    exact Submodule.sub_mem _ hGoutside hpoutside
  rcases S.exists_outsideCoeff_of_mem_rawOutside u hzoutside with
    ⟨z, hz⟩
  have hzorth : S.RawCommonOrthogonal u (S.synth z.val) := by
    rw [hz]
    exact S.rawCommonRemainder_rawOrthogonal u G
  have hGdecomp : G = P + Z :=
    (S.rawCommonPart_add_remainder u G).symm
  have hrestrict : S.restrict G = S.restrict P + S.restrict Z := by
    rw [hGdecomp]
    rfl
  have hsubadd := S.occupiedEnergy_add_le_two u
    (S.restrict P) (S.restrict Z)
  rw [← hrestrict] at hsubadd
  have hpocc :
      S.occupiedEnergy u (S.restrict P) ≤
        (Fintype.card S.RawPlacement : ℝ) * S.rawNormSq P := by
    calc
      S.occupiedEnergy u (S.restrict P) ≤
          S.totalEnergy (S.restrict P) :=
        S.occupiedEnergy_le_totalEnergy u _
      _ = (Fintype.card S.RawPlacement : ℝ) *
          S.rawGoodEnergy P := by
        rw [S.rawCard_mul_rawGoodEnergy_eq_totalEnergy]
      _ ≤ (Fintype.card S.RawPlacement : ℝ) *
          S.rawNormSq P := by
        exact mul_le_mul_of_nonneg_left
          (S.rawGoodEnergy_le_rawNormSq P) (by positivity)
  have hzocc :
      S.occupiedEnergy u (S.restrict Z) ≤
        (Fintype.card S.RawPlacement : ℝ) * S.rawOccupiedUpper z := by
    rw [← hz]
    exact S.occupiedEnergy_restrict_le_rawCard_mul_upper z
  have hpbound := S.rawCommonPart_energy_bound c H hquot
  have hzprod := S.rawOccupiedUpper_bound z H hzorth
  have hZleG : S.rawNormSq Z ≤ S.rawNormSq G := by
    have hpyth := S.rawNormSq_common_decomposition u G
    have hp0 := S.rawNormSq_nonneg P
    simpa [P, Z] using (show
      S.rawNormSq (S.rawCommonRemainder u G) ≤ S.rawNormSq G by
        nlinarith)
  have hzprodG :
      (q : ℝ) * S.rawOccupiedUpper z ≤
        352 * (t : ℝ) * S.rawNormSq G := by
    rw [hz] at hZleG
    exact le_trans hzprod
      (mul_le_mul_of_nonneg_left hZleG (by positivity))
  have hclip := S.rawNormSq_le_two_rawGoodEnergy c.val H hlarge
  have hcardgood := S.rawCard_mul_rawGoodEnergy_eq_totalEnergy G
  have hcard : 0 ≤ (Fintype.card S.RawPlacement : ℝ) := by positivity
  have hq : 0 ≤ (q : ℝ) := by positivity
  have ht : (1 : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast H.t_pos
  have hG0 := S.rawNormSq_nonneg G
  have htotal0 : 0 ≤ S.totalEnergy (S.restrict G) := by
    unfold totalEnergy
    positivity
  nlinarith

/-- Every legal quotient vector admits the coefficient representation needed
by `quotient_occupiedEnergy_bound`. -/
theorem quotient_occupiedEnergy_bound_for_vector
    {q t : ℕ} {u : Fin B} {f : S.Vector}
    (H : S.SectorNumerics q t)
    (hlarge : 32 * t ^ 3 ≤ q)
    (hf : S.InOutsideQuotient u f) :
    (q : ℝ) * S.occupiedEnergy u f ≤
      1504 * (t : ℝ) ^ 3 * S.totalEnergy f := by
  rcases S.exists_outsideCoeff_of_mem_outside u hf.1 with
    ⟨g, hg, hgf⟩
  let c : S.OutsideCoeff u :=
    { val := g
      zero_of_not_allowed := hg }
  have hq' : S.InOutsideQuotient u
      (S.restrict (S.synth c.val)) := by
    rw [hgf]
    exact hf
  have h := S.quotient_occupiedEnergy_bound c H hlarge hq'
  simpa [hgf] using h

end SectorData
end IndependentMatchingBlockOccupancy
