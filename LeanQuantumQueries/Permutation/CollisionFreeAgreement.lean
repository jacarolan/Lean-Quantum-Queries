import LeanQuantumQueries.Permutation.CollisionFreeMomentMatrix

/-!
# Agreement counts for collision-free permutation states

The overlap between two collision-free permutation states is the number of
`q`-subsets on which the two permutations agree.  This file proves that fact
by an explicit equivalence with their common size-`q` partial restrictions.  It
also counts permutations agreeing with a fixed permutation on two prescribed
subsets.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- Two permutations agree on a finite set of input positions. -/
def AgreesOnFinset
    (π σ : Equiv.Perm (Fin N)) (U : Finset (Fin N)) : Prop :=
  ∀ x ∈ U, π x = σ x

noncomputable instance
    (π σ : Equiv.Perm (Fin N)) (U : Finset (Fin N)) :
    Decidable (AgreesOnFinset π σ U) := Classical.propDecidable _

/-- Agreement on a `q`-subset. -/
def AgreesOn
    (π σ : Equiv.Perm (Fin N)) (S : QSubset N q) : Prop :=
  AgreesOnFinset π σ S.1

noncomputable instance
    (π σ : Equiv.Perm (Fin N)) (S : QSubset N q) :
    Decidable (AgreesOn π σ S) := Classical.propDecidable _

/-- Real-valued agreement indicator. -/
noncomputable def agreementIndicator
    (π σ : Equiv.Perm (Fin N)) (S : QSubset N q) : ℝ :=
  if AgreesOn π σ S then 1 else 0

/-- Common restrictions of `π` and `σ` are exactly their `q`-element agreement
subsets. -/
noncomputable def commonExtendedEquivAgreement
    (π σ : Equiv.Perm (Fin N)) :
    {f : PartialPerm N q // f.Extends π ∧ f.Extends σ} ≃
      {S : QSubset N q // AgreesOn π σ S} where
  toFun f := by
    refine ⟨⟨f.1.dom, f.1.card_dom⟩, ?_⟩
    intro x hx
    rcases (mem_dom_iff f.1 x).1 hx with ⟨y, hxy⟩
    exact (f.2.1 (x, y) hxy).trans (f.2.2 (x, y) hxy).symm
  invFun S := by
    refine ⟨partialOfSubset π S.1, partialOfSubset_extends π S.1, ?_⟩
    intro e he
    rcases e with ⟨x, y⟩
    have hmem := (mem_partialOfSubset_graph π S.1 x y).1 he
    have hagree := S.2 x hmem.1
    exact hagree.symm.trans hmem.2.symm
  left_inv f := by
    apply Subtype.ext
    exact partialOfSubset_dom π f.1 f.2.1
  right_inv S := by
    apply Subtype.ext
    simpa using dom_partialOfSubset π S.1

/-- Common size-`q` partial restrictions and agreement `q`-subsets have the
same cardinality. -/
theorem card_commonExtended_eq_card_agreement
    (π σ : Equiv.Perm (Fin N)) :
    Fintype.card {f : PartialPerm N q // f.Extends π ∧ f.Extends σ} =
      Fintype.card {S : QSubset N q // AgreesOn π σ S} :=
  Fintype.card_congr (commonExtendedEquivAgreement π σ)

/-- The Gram entry of the extension incidence matrix is the number of
agreement `q`-subsets. -/
theorem sum_extensionIncidence_mul_eq_agreement
    (π σ : Equiv.Perm (Fin N)) :
    ∑ f : PartialPerm N q,
        extensionIncidence N q π f * extensionIncidence N q σ f =
      ∑ S : QSubset N q, agreementIndicator π σ S := by
  classical
  calc
    (∑ f : PartialPerm N q,
        extensionIncidence N q π f * extensionIncidence N q σ f) =
      (Fintype.card
        {f : PartialPerm N q // f.Extends π ∧ f.Extends σ} : ℝ) := by
          rw [Fintype.card_subtype]
          rw [← Finset.sum_boole (R := ℝ)
            (fun f : PartialPerm N q => f.Extends π ∧ f.Extends σ) Finset.univ]
          apply Finset.sum_congr rfl
          intro f _
          by_cases hπ : f.Extends π <;> by_cases hσ : f.Extends σ <;>
            simp [extensionIncidence, hπ, hσ]
    _ = (Fintype.card
        {S : QSubset N q // AgreesOn π σ S} : ℝ) := by
          rw [card_commonExtended_eq_card_agreement π σ]
    _ = ∑ S : QSubset N q, agreementIndicator π σ S := by
          rw [Fintype.card_subtype]
          rw [← Finset.sum_boole (R := ℝ)
            (fun S : QSubset N q => AgreesOn π σ S) Finset.univ]
          apply Finset.sum_congr rfl
          intro S _
          simp [agreementIndicator]

/-- Restriction of `π` to an arbitrary finite set. -/
def partialOfFinset
    (π : Equiv.Perm (Fin N)) (U : Finset (Fin N)) :
    PartialPerm N U.card :=
  partialOfSubset π ⟨U, rfl⟩

/-- A permutation extends the restriction of `π` to `U` exactly when it
agrees with `π` throughout `U`. -/
theorem extends_partialOfFinset_iff
    (π σ : Equiv.Perm (Fin N)) (U : Finset (Fin N)) :
    (partialOfFinset π U).Extends σ ↔ AgreesOnFinset π σ U := by
  constructor
  · intro h x hx
    have hedge : (x, π x) ∈ (partialOfFinset π U).graph := by
      apply (mem_partialOfSubset_graph π ⟨U, rfl⟩ x (π x)).2
      exact ⟨hx, rfl⟩
    exact (h (x, π x) hedge).symm
  · intro h e he
    rcases e with ⟨x, y⟩
    have hmem := (mem_partialOfSubset_graph π ⟨U, rfl⟩ x y).1 he
    exact (h x hmem.1).symm.trans hmem.2.symm

/-- Permutations agreeing with `π` on `U` are exactly completions of the
partial restriction of `π` to `U`. -/
noncomputable def agreeingEquivCompletions
    (π : Equiv.Perm (Fin N)) (U : Finset (Fin N)) :
    {σ : Equiv.Perm (Fin N) // AgreesOnFinset π σ U} ≃
      {σ : Equiv.Perm (Fin N) // (partialOfFinset π U).Extends σ} where
  toFun σ := ⟨σ.1, (extends_partialOfFinset_iff π σ.1 U).2 σ.2⟩
  invFun σ := ⟨σ.1, (extends_partialOfFinset_iff π σ.1 U).1 σ.2⟩
  left_inv σ := by apply Subtype.ext; rfl
  right_inv σ := by apply Subtype.ext; rfl

/-- Exact number of permutations agreeing with `π` on an arbitrary finite
set. -/
theorem card_agreeing_on_finset
    (π : Equiv.Perm (Fin N)) (U : Finset (Fin N)) :
    Fintype.card {σ : Equiv.Perm (Fin N) // AgreesOnFinset π σ U} =
      Nat.factorial (N - U.card) := by
  classical
  calc
    Fintype.card {σ : Equiv.Perm (Fin N) // AgreesOnFinset π σ U} =
        Fintype.card
          {σ : Equiv.Perm (Fin N) // (partialOfFinset π U).Extends σ} :=
      Fintype.card_congr (agreeingEquivCompletions π U)
    _ = Nat.factorial (N - U.card) :=
      card_completions (partialOfFinset π U)

/-- Agreement on each of two subsets is agreement on their union. -/
theorem agreesOn_and_iff_union
    (π σ : Equiv.Perm (Fin N)) (S T : QSubset N q) :
    AgreesOn π σ S ∧ AgreesOn π σ T ↔
      AgreesOnFinset π σ (S.1 ∪ T.1) := by
  constructor
  · rintro ⟨hS, hT⟩ x hx
    rw [Finset.mem_union] at hx
    exact hx.elim (hS x) (hT x)
  · intro h
    exact ⟨fun x hx => h x (Finset.mem_union_left _ hx),
      fun x hx => h x (Finset.mem_union_right _ hx)⟩

/-- Exact agreement-indicator correlation for two prescribed `q`-subsets. -/
theorem sum_agreementIndicator_mul
    (π : Equiv.Perm (Fin N)) (S T : QSubset N q) :
    ∑ σ : Equiv.Perm (Fin N),
        agreementIndicator π σ S * agreementIndicator π σ T =
      (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin N),
        agreementIndicator π σ S * agreementIndicator π σ T) =
      (Fintype.card
        {σ : Equiv.Perm (Fin N) //
          AgreesOn π σ S ∧ AgreesOn π σ T} : ℝ) := by
          rw [Fintype.card_subtype]
          rw [← Finset.sum_boole (R := ℝ)
            (fun σ : Equiv.Perm (Fin N) =>
              AgreesOn π σ S ∧ AgreesOn π σ T) Finset.univ]
          apply Finset.sum_congr rfl
          intro σ _
          by_cases hS : AgreesOn π σ S <;> by_cases hT : AgreesOn π σ T <;>
            simp [agreementIndicator, hS, hT]
    _ = (Fintype.card
        {σ : Equiv.Perm (Fin N) //
          AgreesOnFinset π σ (S.1 ∪ T.1)} : ℝ) := by
          exact_mod_cast
            Fintype.card_congr
              (Equiv.subtypeEquivRight
                (fun σ => agreesOn_and_iff_union π σ S T))
    _ = (Nat.factorial (N - (S.1 ∪ T.1).card) : ℝ) := by
          rw [card_agreeing_on_finset]

end PartialPerm
end LeanQuantumQueries.Permutation
