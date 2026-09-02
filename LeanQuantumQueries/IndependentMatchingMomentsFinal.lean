import LeanQuantumQueries.IndependentMatchingProductThreeFinal
import LeanQuantumQueries.IndependentMatchingIdeal

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

private theorem remaining₂_nonemptyF (i j : Fin d) :
    Nonempty (S.Remaining₂ i j) := by
  classical
  refine ⟨fun k => ?_⟩
  exact ⟨(S.orbit_nonempty k.1).choose,
    (S.orbit_nonempty k.1).choose_spec⟩

private theorem remaining₃_nonemptyF (i j k : Fin d) :
    Nonempty (S.Remaining₃F i j k) := by
  classical
  refine ⟨fun l => ?_⟩
  exact ⟨(S.orbit_nonempty l.1).choose,
    (S.orbit_nonempty l.1).choose_spec⟩

private theorem remaining₂_card_ne_zeroF (i j : Fin d) :
    (Fintype.card (S.Remaining₂ i j) : ℝ) ≠ 0 := by
  haveI := S.remaining₂_nonemptyF i j
  exact_mod_cast Fintype.card_ne_zero

private theorem remaining₃_card_ne_zeroF (i j k : Fin d) :
    (Fintype.card (S.Remaining₃F i j k) : ℝ) ≠ 0 := by
  haveI := S.remaining₃_nonemptyF i j k
  exact_mod_cast Fintype.card_ne_zero

/-- Normalized expectation of a two-coordinate function. -/
theorem rawAvg_two_coordinatesF (i j : Fin d) (hji : j ≠ i)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} → ℝ) :
    S.rawAvg (fun x => F (x i) (x j)) =
      (∑ a, ∑ b, F a b) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card) := by
  unfold rawAvg
  rw [S.sum_two_coordinates i j hji F,
    S.card_rawPlacement₂ i j hji]
  rw [show
      (Fintype.card (S.Remaining₂ i j) : ℝ) *
          (S.orbit i).card * (S.orbit j).card =
        (Fintype.card (S.Remaining₂ i j) : ℝ) *
          (((S.orbit i).card : ℝ) * (S.orbit j).card) by ring]
  simpa using mul_div_mul_left
    (∑ a, ∑ b, F a b)
    (((S.orbit i).card : ℝ) * (S.orbit j).card)
    (S.remaining₂_card_ne_zeroF i j)

/-- Normalized expectation of a three-coordinate function. -/
theorem rawAvg_three_coordinatesF (i j k : Fin d)
    (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (F : {a : Fin B // a ∈ S.orbit i} →
      {b : Fin B // b ∈ S.orbit j} →
      {c : Fin B // c ∈ S.orbit k} → ℝ) :
    S.rawAvg (fun x => F (x i) (x j) (x k)) =
      (∑ a, ∑ b, ∑ c, F a b c) /
        (((S.orbit i).card : ℝ) * (S.orbit j).card *
          (S.orbit k).card) := by
  unfold rawAvg
  rw [S.sum_three_coordinatesF i j k hji hki hkj F,
    S.card_rawPlacement₃F i j k hji hki hkj]
  rw [show
      (Fintype.card (S.Remaining₃F i j k) : ℝ) *
          (S.orbit i).card * (S.orbit j).card * (S.orbit k).card =
        (Fintype.card (S.Remaining₃F i j k) : ℝ) *
          (((S.orbit i).card : ℝ) * (S.orbit j).card *
            (S.orbit k).card) by ring]
  simpa using mul_div_mul_left
    (∑ a, ∑ b, ∑ c, F a b c)
    (((S.orbit i).card : ℝ) * (S.orbit j).card *
      (S.orbit k).card)
    (S.remaining₃_card_ne_zeroF i j k)

end SectorData
end IndependentMatchingBlockOccupancy
