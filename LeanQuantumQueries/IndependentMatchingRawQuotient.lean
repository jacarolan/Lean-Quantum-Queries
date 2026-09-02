import LeanQuantumQueries.IndependentMatchingRawOccupancyBound

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- Membership in the ideal product-table quotient: the raw outside span,
orthogonal to its intersection with the raw inside span. -/
def InRawOutsideQuotient (u : Fin B) (f : S.RawVector) : Prop :=
  f ∈ S.rawOutsideSpace u ∧
    ∀ g, g ∈ S.rawInsideSpace u → g ∈ S.rawOutsideSpace u →
      S.rawInner f g = 0

/-- Quotient orthogonality implies orthogonality to every explicit exact
common direction used by the coefficient calculation. -/
theorem rawCommonOrthogonal_of_inRawOutsideQuotient
    (u : Fin B) {f : S.RawVector}
    (hf : S.InRawOutsideQuotient u f) :
    S.RawCommonOrthogonal u f := by
  intro g hg
  have hg' := S.rawCommonSpace_le_inter u hg
  rw [Submodule.mem_inf] at hg'
  exact hf.2 g hg'.1 hg'.2

/-- Every vector in the raw outside-cylinder span has a supported additive
coefficient representation. -/
theorem exists_outsideCoeff_of_mem_rawOutside
    (u : Fin B) {f : S.RawVector}
    (hf : f ∈ S.rawOutsideSpace u) :
    ∃ c : S.OutsideCoeff u, S.synth c.val = f := by
  rw [← S.map_outsideCoeff_eq_rawOutside u] at hf
  rcases hf with ⟨g, hg, hgf⟩
  let c : S.OutsideCoeff u :=
    { val := g
      zero_of_not_allowed := by
        intro i a ha
        exact hg i a ha }
  refine ⟨c, ?_⟩
  change S.synthLinear g = f
  exact hgf

/-- End-to-end ideal product-table quotient occupancy estimate. -/
theorem q_mul_rawOccupiedEnergy_le_of_inRawOutsideQuotient
    {q t : ℕ} (u : Fin B) (f : S.RawVector)
    (H : S.SectorBounds q t)
    (hgapU : ∀ i, ¬ S.Complete i →
      (S.orbit i).card ≤ 8 * (S.missingValues u i).card)
    (hf : S.InRawOutsideQuotient u f) :
    (q : ℝ) * S.rawOccupiedEnergy u f ≤
      50000 * (t : ℝ) ^ 2 * S.rawNormSq f := by
  rcases S.exists_outsideCoeff_of_mem_rawOutside u hf.1 with ⟨c, hcf⟩
  have hquot : S.InRawOutsideQuotient u (S.synth c.val) := by
    rw [hcf]
    exact hf
  have horth := S.rawCommonOrthogonal_of_inRawOutsideQuotient u hquot
  have hbound := S.q_mul_rawOccupiedEnergy_synth_le c H horth hgapU
  simpa [hcf] using hbound

end SectorData
end IndependentMatchingBlockOccupancy
