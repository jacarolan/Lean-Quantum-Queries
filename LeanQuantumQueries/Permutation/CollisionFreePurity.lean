import LeanQuantumQueries.Permutation.CollisionFreeFlatness
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact purity of the collision-free random-permutation moment

The collision-free `q`-query state is indexed by `q`-subsets of the input
positions.  Its purity is obtained by grouping two such subsets according to
their intersection size.  This file carries out that calculation without
representation theory.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- A `q`-element subset of `Fin N`. -/
def QSubset (N q : ℕ) :=
  {s : Finset (Fin N) // s.card = q}

noncomputable instance (N q : ℕ) : Fintype (QSubset N q) := by
  classical
  unfold QSubset
  infer_instance

/-- There are `N.choose q` subsets of size `q`. -/
theorem card_qSubset (N q : ℕ) :
    Fintype.card (QSubset N q) = Nat.choose N q := by
  change Fintype.card {s : Finset (Fin N) // s.card = q} = Nat.choose N q
  simpa using (Fintype.card_finset_len (α := Fin N) q)

/-- The `q`-subsets meeting `S` in exactly `j` points. -/
def SubsetOverlap (S : QSubset N q) (j : ℕ) :=
  {T : QSubset N q // (S.1 ∩ T.1).card = j}

noncomputable instance (S : QSubset N q) (j : ℕ) :
    Fintype (SubsetOverlap S j) := by
  classical
  unfold SubsetOverlap
  infer_instance

/-- Code an overlap class by the shared part inside `S` and the fresh part
outside `S`. -/
def SubsetOverlapCode (S : QSubset N q) (j : ℕ) :=
  {A : Finset (Fin N) // A ⊆ S.1 ∧ A.card = j} ×
  {B : Finset (Fin N) // B ⊆ S.1ᶜ ∧ B.card = q - j}

noncomputable instance (S : QSubset N q) (j : ℕ) :
    Fintype (SubsetOverlapCode S j) := by
  classical
  unfold SubsetOverlapCode
  infer_instance

/-- Exact shared/fresh decomposition of a fixed-intersection class. -/
noncomputable def subsetOverlapEquivCode
    (S : QSubset N q) (j : ℕ) :
    SubsetOverlap S j ≃ SubsetOverlapCode S j where
  toFun T :=
    ⟨⟨S.1 ∩ T.1.1, Finset.inter_subset_left, T.2⟩,
      ⟨T.1.1 \ S.1,
        by
          intro x hx
          rw [Finset.mem_compl]
          exact (Finset.mem_sdiff.mp hx).2,
        by
          rw [Finset.card_sdiff, T.1.2]
          simpa [Finset.inter_comm] using
            congrArg (fun n => q - n) T.2⟩⟩
  invFun C := by
    let A := C.1.1
    let B := C.2.1
    have hjq : j ≤ q := by
      rw [← S.2, ← C.1.2.2]
      exact Finset.card_le_card C.1.2.1
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact (Finset.mem_compl.mp (C.2.2.1 hxB)) (C.1.2.1 hxA)
    have hcard : (A ∪ B).card = q := by
      rw [Finset.card_union_of_disjoint hdisj, C.1.2.2, C.2.2.2,
        Nat.add_sub_of_le hjq]
    have hinter : S.1 ∩ (A ∪ B) = A := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxS, hxA | hxB⟩
        · exact hxA
        · exact False.elim ((Finset.mem_compl.mp (C.2.2.1 hxB)) hxS)
      · intro hxA
        exact ⟨C.1.2.1 hxA, Or.inl hxA⟩
    exact ⟨⟨A ∪ B, hcard⟩, by rw [hinter, C.1.2.2]⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finset.ext
    intro x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv C := by
    apply Prod.ext
    · apply Subtype.ext
      apply Finset.ext
      intro x
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxS, hxA | hxB⟩
        · exact hxA
        · exact False.elim ((Finset.mem_compl.mp (C.2.2.1 hxB)) hxS)
      · intro hxA
        exact ⟨C.1.2.1 hxA, Or.inl hxA⟩
    · apply Subtype.ext
      apply Finset.ext
      intro x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxA | hxB, hxnotS⟩
        · exact False.elim (hxnotS (C.1.2.1 hxA))
        · exact hxB
      · intro hxB
        exact ⟨Or.inr hxB, Finset.mem_compl.mp (C.2.2.1 hxB)⟩

/-- Number of `j`-subsets of a fixed finite set. -/
theorem card_subsets_inside
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (j : ℕ) :
    Fintype.card {A : Finset α // A ⊆ S ∧ A.card = j} =
      Nat.choose S.card j := by
  classical
  rw [Fintype.card_subtype]
  have heq :
      ({A : Finset α | A ⊆ S ∧ A.card = j} : Finset _) =
        S.powersetCard j := by
    ext A
    simp [and_comm]
  rw [heq, Finset.card_powersetCard]

/-- Exact size of a fixed-intersection class. -/
theorem card_subsetOverlap
    (S : QSubset N q) (j : ℕ) :
    Fintype.card (SubsetOverlap S j) =
      Nat.choose q j * Nat.choose (N - q) (q - j) := by
  classical
  calc
    Fintype.card (SubsetOverlap S j) =
        Fintype.card (SubsetOverlapCode S j) :=
      Fintype.card_congr (subsetOverlapEquivCode S j)
    _ = Nat.choose q j * Nat.choose (N - q) (q - j) := by
      change Fintype.card
          ({A : Finset (Fin N) // A ⊆ S.1 ∧ A.card = j} ×
            {B : Finset (Fin N) // B ⊆ S.1ᶜ ∧ B.card = q - j}) = _
      rw [Fintype.card_prod, card_subsets_inside, card_subsets_inside,
        S.2, Finset.card_compl, S.2, Fintype.card_fin]

end PartialPerm
end LeanQuantumQueries.Permutation
