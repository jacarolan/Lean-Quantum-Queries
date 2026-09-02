import LeanQuantumQueries.IndependentMatchingNumericsFromClassesFinal

namespace IndependentMatchingBlockOccupancy

/-- Concrete type-level description of one independent-matching sector.
Each structural coordinate permits a nonempty collection of the eight endpoint
types; each endpoint type has exactly `q` block names. -/
structure TypedSectorInputF (d q : ℕ) where
  q_pos : 0 < q
  orbitTypes : Fin d → Finset (Fin 8)
  compatTypes : Fin d → Finset (Fin 8)
  compatTypes_subset : ∀ i, compatTypes i ⊆ orbitTypes i
  orbitTypes_nonempty : ∀ i, (orbitTypes i).Nonempty

namespace TypedSectorInputF

variable {d q : ℕ} (X : TypedSectorInputF d q)

/-- Canonical equivalence between endpoint type/block-number pairs and the
`8q` block names. -/
noncomputable def blockEquivF : Fin 8 × Fin q ≃ Fin (8 * q) :=
  finProdFinEquiv

/-- Blocks belonging to a set of endpoint types. -/
noncomputable def blocksOfTypesF (T : Finset (Fin 8)) :
    Finset (Fin (8 * q)) :=
  (T ×ˢ (Finset.univ : Finset (Fin q))).map X.blockEquivF.toEmbedding

/-- The finite-table sector induced by the typed description. -/
noncomputable def sectorDataF : SectorData d (8 * q) where
  orbit i := X.blocksOfTypesF (X.orbitTypes i)
  compat i := X.blocksOfTypesF (X.compatTypes i)
  compat_subset i := by
    apply Finset.map_mono
    exact Finset.product_mono (X.compatTypes_subset i) (by rfl)
  orbit_nonempty i := by
    classical
    rcases X.orbitTypes_nonempty i with ⟨r, hr⟩
    let s : Fin q := ⟨0, X.q_pos⟩
    refine ⟨X.blockEquivF (r, s), ?_⟩
    apply Finset.mem_map.2
    exact ⟨(r, s), by simp [hr], rfl⟩

/-- One complete endpoint type class. -/
noncomputable def typeClassF (r : Fin 8) : Finset (Fin (8 * q)) :=
  X.blocksOfTypesF {r}

/-- A type class has exactly `q` block names. -/
theorem card_typeClassF (r : Fin 8) :
    (X.typeClassF r).card = q := by
  classical
  unfold typeClassF blocksOfTypesF
  rw [Finset.card_map, Finset.card_product]
  simp

/-- Type-set inclusion induces block-set inclusion. -/
theorem blocksOfTypesF_mono {T U : Finset (Fin 8)} (hTU : T ⊆ U) :
    X.blocksOfTypesF T ⊆ X.blocksOfTypesF U := by
  unfold blocksOfTypesF
  apply Finset.map_mono
  exact Finset.product_mono hTU (by rfl)

/-- Membership of a block reveals the corresponding endpoint type and local
block number. -/
theorem mem_blocksOfTypesF_iff
    (T : Finset (Fin 8)) (b : Fin (8 * q)) :
    b ∈ X.blocksOfTypesF T ↔
      ∃ r : Fin 8, r ∈ T ∧
        ∃ s : Fin q, X.blockEquivF (r, s) = b := by
  classical
  unfold blocksOfTypesF
  constructor
  · intro hb
    rcases Finset.mem_map.1 hb with ⟨p, hp, rfl⟩
    exact ⟨p.1, (Finset.mem_product.1 hp).1, p.2, rfl⟩
  · rintro ⟨r, hr, s, rfl⟩
    apply Finset.mem_map.2
    exact ⟨(r, s), by simp [hr], rfl⟩

/-- Equality of endpoint type sets implies equality of their block sets. -/
theorem blocksOfTypesF_congr {T U : Finset (Fin 8)} (h : T = U) :
    X.blocksOfTypesF T = X.blocksOfTypesF U := by
  rw [h]

/-- If the induced compatible block set is not complete, an entire endpoint
type occurring in the orbit is absent from compatibility. -/
theorem exists_omitted_typeF (i : Fin d)
    (hinc : ¬ (X.sectorDataF).Complete i) :
    ∃ r : Fin 8, r ∈ X.orbitTypes i ∧ r ∉ X.compatTypes i := by
  classical
  have htypes : X.compatTypes i ≠ X.orbitTypes i := by
    intro h
    apply hinc
    unfold SectorData.Complete sectorDataF
    exact X.blocksOfTypesF_congr h
  by_contra hnone
  push_neg at hnone
  apply htypes
  apply Finset.Subset.antisymm (X.compatTypes_subset i)
  intro r hr
  by_contra hrc
  exact hnone r hr hrc

/-- A block in an omitted endpoint type belongs to the orbit but not to the
compatible set. -/
theorem omitted_type_block_membershipF
    (i : Fin d) (r : Fin 8)
    (hrOrbit : r ∈ X.orbitTypes i)
    (hrCompat : r ∉ X.compatTypes i)
    {b : Fin (8 * q)} (hb : b ∈ X.typeClassF r) :
    b ∈ (X.sectorDataF).orbit i ∧
      b ∉ (X.sectorDataF).compat i := by
  classical
  rcases (X.mem_blocksOfTypesF_iff {r} b).1 hb with
    ⟨r', hr', s, hbs⟩
  have hrr : r' = r := by simpa using hr'
  subst r'
  constructor
  · apply (X.mem_blocksOfTypesF_iff (X.orbitTypes i) b).2
    exact ⟨r, hrOrbit, s, hbs⟩
  · intro hbCompat
    rcases (X.mem_blocksOfTypesF_iff (X.compatTypes i) b).1 hbCompat with
      ⟨r', hr'Compat, s', hbs'⟩
    have hpairs : (r, s) = (r', s') := by
      apply X.blockEquivF.injective
      exact hbs.trans hbs'.symm
    have htype : r = r' := congrArg Prod.fst hpairs
    apply hrCompat
    simpa [htype] using hr'Compat

/-- Every omitted endpoint type is contained in the missing-value set for
all choices of distinguished block `u`. -/
theorem typeClassF_subset_missing_image
    (u : Fin (8 * q)) (i : Fin d) (r : Fin 8)
    (hrOrbit : r ∈ X.orbitTypes i)
    (hrCompat : r ∉ X.compatTypes i) :
    X.typeClassF r ⊆
      ((X.sectorDataF).missingValues u i).image Subtype.val := by
  classical
  intro b hb
  have hbmem := X.omitted_type_block_membershipF i r hrOrbit hrCompat hb
  let a : {a : Fin (8 * q) // a ∈ (X.sectorDataF).orbit i} :=
    ⟨b, hbmem.1⟩
  have haMissing : a ∈ (X.sectorDataF).missingValues u i := by
    apply ((X.sectorDataF).mem_missingValues_iff u i a).2
    intro hallowed
    exact hbmem.2 hallowed.1
  apply Finset.mem_image.2
  exact ⟨a, haMissing, rfl⟩

/-- The concrete eight-type sector supplies the structural eligible-class
witness used by the finite-table theorem. -/
theorem eligibleClassWitnessF
    {t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t) :
    (X.sectorDataF).EligibleClassWitnessF q t := by
  refine
    { t_pos := ht
      coord_le := hdt
      block_count_le := by rfl
      orbit_class := ?_
      missing_class := ?_ }
  · intro i
    rcases X.orbitTypes_nonempty i with ⟨r, hr⟩
    refine ⟨X.typeClassF r, ?_, ?_⟩
    · exact X.blocksOfTypesF_mono (by
        intro x hx
        simpa using ⟨hr, hx⟩)
    · rw [X.card_typeClassF]
  · intro u i hinc
    rcases X.exists_omitted_typeF i hinc with ⟨r, hrOrbit, hrCompat⟩
    refine ⟨X.typeClassF r,
      X.typeClassF_subset_missing_image u i r hrOrbit hrCompat, ?_⟩
    rw [X.card_typeClassF]

/-- All numerical facts follow automatically for the concrete sector. -/
theorem sectorNumericsF
    {t : ℕ} (ht : 1 ≤ t) (hdt : d ≤ t) :
    (X.sectorDataF).SectorNumericsF (8 * q) t :=
  (X.sectorDataF).sectorNumericsF_of_eligibleClasses
    (X.eligibleClassWitnessF ht hdt)

end TypedSectorInputF
end IndependentMatchingBlockOccupancy
