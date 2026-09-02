import LeanQuantumQueries.IndependentMatchingCoefficients

open scoped BigOperators

namespace IndependentMatchingBlockOccupancy
namespace SectorData

variable {d B : ℕ} (S : SectorData d B)

/-- All additive coordinate coefficient families. -/
abbrev Coeff := ∀ i : Fin d, {a : Fin B // a ∈ S.orbit i} → ℝ

/-- The submodule of coefficient families supported on outside-rooted values. -/
noncomputable def outsideCoeffSpace (u : Fin B) : Submodule ℝ S.Coeff where
  carrier := {g | ∀ i a, a ∉ S.allowedValues u i → g i a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i a ha
    simp [hf i a ha, hg i a ha]
  smul_mem' := by
    intro c f hf i a ha
    simp [hf i a ha]

/-- Linear synthesis of additive coordinate coefficients on the product table. -/
noncomputable def synthLinear : S.Coeff →ₗ[ℝ] S.RawVector where
  toFun := S.synth
  map_add' := by
    intro f g
    funext x
    simp [synth, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    funext x
    simp [synth, Finset.mul_sum]

/-- Linear restriction from the product table to collision-free placements. -/
noncomputable def restrictionLinear : S.RawVector →ₗ[ℝ] S.Vector where
  toFun := S.restrict
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- Inside cylinder span before collision deletion. -/
noncomputable def rawInsideSpace (u : Fin B) : Submodule ℝ S.RawVector :=
  Submodule.span ℝ
    {f | ∃ i : Fin d, u ∈ S.compat i ∧ f = S.rawFiber i u}

/-- Outside cylinder span before collision deletion. -/
noncomputable def rawOutsideSpace (u : Fin B) : Submodule ℝ S.RawVector :=
  Submodule.span ℝ
    {f | ∃ (i : Fin d) (a : Fin B), a ∈ S.compat i ∧ a ≠ u ∧
      f = S.rawFiber i a}

/-- Every one-coordinate lift expands in the coordinate-fiber basis. -/
theorem lift_eq_sum_fibers (i : Fin d)
    (g : {a : Fin B // a ∈ S.orbit i} → ℝ) :
    S.lift i g = ∑ a, g a • S.rawFiber i a.1 := by
  classical
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_eq_single (x i)]
  · simp [lift, rawFiber, block]
  · intro a ha
    have hne : a.1 ≠ (x i).1 := by
      intro h
      apply ha
      exact Subtype.ext h
    simp [rawFiber, block, hne]

/-- Coefficients in `outsideCoeffSpace` synthesize into the raw outside span. -/
theorem synth_mem_rawOutside {u : Fin B} {g : S.Coeff}
    (hg : g ∈ S.outsideCoeffSpace u) :
    S.synth g ∈ S.rawOutsideSpace u := by
  classical
  rw [show S.synth g = ∑ i, S.lift i (g i) by
    funext x
    simp [synth, lift]]
  apply Submodule.sum_mem
  intro i _
  rw [S.lift_eq_sum_fibers i (g i)]
  apply Submodule.sum_mem
  intro a _
  by_cases ha : a ∈ S.allowedValues u i
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    have hallowed := (S.mem_allowedValues_iff u i a).1 ha
    exact ⟨i, a.1, hallowed.1, hallowed.2, rfl⟩
  · rw [hg i a ha]
    simp

/-- A delta coefficient family producing one prescribed outside cylinder. -/
noncomputable def deltaCoeff (u : Fin B) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) : S.Coeff :=
  fun j b => if _h : j = i then
    if b.1 = a.1 then 1 else 0
  else 0

/-- A delta family is supported on outside values when its chosen value is
compatible and not distinguished. -/
theorem deltaCoeff_mem_outside (u : Fin B) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i})
    (hcompat : a.1 ∈ S.compat i) (hne : a.1 ≠ u) :
    S.deltaCoeff u i a ∈ S.outsideCoeffSpace u := by
  intro j b hb
  unfold deltaCoeff
  split_ifs with hji hba
  · subst j
    have hallowed : b ∈ S.allowedValues u i := by
      apply (S.mem_allowedValues_iff u i b).2
      constructor
      · simpa [hba] using hcompat
      · simpa [hba] using hne
    exact (hb hallowed).elim
  · rfl
  · rfl

/-- The delta coefficient family synthesizes exactly one raw fiber. -/
theorem synth_deltaCoeff (u : Fin B) (i : Fin d)
    (a : {a : Fin B // a ∈ S.orbit i}) :
    S.synth (S.deltaCoeff u i a) = S.rawFiber i a.1 := by
  classical
  funext x
  unfold synth deltaCoeff rawFiber block
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The coefficient synthesis range is exactly the raw outside-cylinder span. -/
theorem map_outsideCoeff_eq_rawOutside (u : Fin B) :
    (S.outsideCoeffSpace u).map S.synthLinear = S.rawOutsideSpace u := by
  apply le_antisymm
  · rintro f ⟨g, hg, rfl⟩
    exact S.synth_mem_rawOutside hg
  · apply Submodule.span_le.2
    rintro f ⟨i, a, hcompat, hne, rfl⟩
    have horbit : a ∈ S.orbit i := S.compat_subset i hcompat
    let aa : {a : Fin B // a ∈ S.orbit i} := ⟨a, horbit⟩
    refine ⟨S.deltaCoeff u i aa,
      S.deltaCoeff_mem_outside u i aa hcompat hne, ?_⟩
    exact S.synth_deltaCoeff u i aa

/-- Restriction maps the raw inside span exactly onto the legal inside span. -/
theorem map_rawInside_eq_inside (u : Fin B) :
    (S.rawInsideSpace u).map S.restrictionLinear = S.insideSpace u := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.2
    apply Submodule.span_le.2
    rintro f ⟨i, hui, rfl⟩
    change S.fiber i u ∈ S.insideSpace u
    apply Submodule.subset_span
    exact ⟨i, hui, rfl⟩
  · apply Submodule.span_le.2
    rintro f ⟨i, hui, rfl⟩
    refine ⟨S.rawFiber i u, ?_, ?_⟩
    · apply Submodule.subset_span
      exact ⟨i, hui, rfl⟩
    · rfl

/-- Restriction maps the raw outside span exactly onto the legal outside span. -/
theorem map_rawOutside_eq_outside (u : Fin B) :
    (S.rawOutsideSpace u).map S.restrictionLinear = S.outsideSpace u := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.2
    apply Submodule.span_le.2
    rintro f ⟨i, a, hcompat, hne, rfl⟩
    change S.fiber i a ∈ S.outsideSpace u
    apply Submodule.subset_span
    exact ⟨i, a, hcompat, hne, rfl⟩
  · apply Submodule.span_le.2
    rintro f ⟨i, a, hcompat, hne, rfl⟩
    refine ⟨S.rawFiber i a, ?_, ?_⟩
    · apply Submodule.subset_span
      exact ⟨i, a, hcompat, hne, rfl⟩
    · rfl

/-- Every legal outside vector is the restriction of an additive product-table
vector with correctly supported coefficients. -/
theorem exists_outsideCoeff_of_mem_outside (u : Fin B) {f : S.Vector}
    (hf : f ∈ S.outsideSpace u) :
    ∃ g : S.Coeff, g ∈ S.outsideCoeffSpace u ∧
      S.restrict (S.synth g) = f := by
  rw [← S.map_rawOutside_eq_outside u] at hf
  rcases hf with ⟨r, hr, hrf⟩
  rw [← S.map_outsideCoeff_eq_rawOutside u] at hr
  rcases hr with ⟨g, hg, hgr⟩
  refine ⟨g, hg, ?_⟩
  change S.restrictionLinear (S.synthLinear g) = f
  rw [hgr, hrf]

end SectorData
end IndependentMatchingBlockOccupancy
