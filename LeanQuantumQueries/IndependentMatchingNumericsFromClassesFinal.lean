import LeanQuantumQueries.IndependentMatchingNumericsFinal

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Structural eligible-class facts supplied by the independent-matching block
construction.  `q` is the size of one full endpoint-type class. -/
structure EligibleClassWitnessF (q t : ℕ) : Prop where
  t_pos : 1 ≤ t
  coord_le : d ≤ t
  block_count_le : B ≤ 8 * q
  orbit_class : ∀ i, ∃ W : Finset (Fin B),
    W ⊆ S.orbit i ∧ q ≤ W.card
  missing_class : ∀ (u : Fin B) i, ¬ S.Complete i →
    ∃ W : Finset (Fin B),
      W ⊆ (S.missingValues u i).image Subtype.val ∧ q ≤ W.card

/-- The image of the orbit subtype under `Subtype.val` is the orbit itself. -/
theorem orbit_subtype_image_val (i : Fin d) :
    (Finset.univ : Finset {a : Fin B // a ∈ S.orbit i}).image Subtype.val =
      S.orbit i := by
  ext a
  simp

/-- The number of missing subtype values equals the number of their underlying
block names. -/
theorem card_missing_image_val (u : Fin B) (i : Fin d) :
    ((S.missingValues u i).image Subtype.val).card =
      (S.missingValues u i).card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- Every orbit is bounded by the total number of block names. -/
theorem orbit_card_le_block_count (i : Fin d) :
    (S.orbit i).card ≤ B := by
  simpa using Finset.card_le_univ (S.orbit i)

/-- Structural eligible-class witnesses imply all numerical hypotheses of the
finite-table clipping theorem, with scale parameter `8*q`. -/
theorem sectorNumericsF_of_eligibleClasses
    {q t : ℕ} (H : S.EligibleClassWitnessF q t) :
    S.SectorNumericsF (8 * q) t := by
  refine
    { t_pos := H.t_pos
      coord_le := H.coord_le
      orbit_lower := ?_
      incomplete_gap := ?_ }
  · intro i
    rcases H.orbit_class i with ⟨W, hWsub, hWcard⟩
    have hcard : W.card ≤ (S.orbit i).card :=
      Finset.card_le_card hWsub
    omega
  · intro u i hinc
    rcases H.missing_class u i hinc with ⟨W, hWsub, hWcard⟩
    have hmissingImage : W.card ≤
        ((S.missingValues u i).image Subtype.val).card :=
      Finset.card_le_card hWsub
    have hmissing : q ≤ (S.missingValues u i).card := by
      rw [S.card_missing_image_val u i] at hmissingImage
      omega
    have horbit : (S.orbit i).card ≤ 8 * q :=
      le_trans (S.orbit_card_le_block_count i) H.block_count_le
    omega

end SectorData
end IndependentMatchingBlockOccupancy
