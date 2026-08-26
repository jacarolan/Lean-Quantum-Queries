import LeanQuantumQueries.Permutation.CollisionFreePurityClosed

/-!
# The collision kernel is the random-permutation joint moment

This file closes the combinatorial link between the exact partial-permutation
moment identity and the collision-free purity calculation.  A `q`-subset is
sent to the partial identity permutation on that subset.  The collision kernel
is exactly the joint extension moment of the two resulting partial
permutations.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- The diagonal embedding `x ↦ (x,x)`. -/
def diagonalEmbedding (N : ℕ) : Fin N ↪ Fin N × Fin N where
  toFun x := (x, x)
  inj' := by
    intro x y h
    exact congrArg Prod.fst h

/-- The partial identity permutation on a `q`-subset. -/
def identityPartial (S : QSubset N q) : PartialPerm N q := by
  refine ⟨S.1.map (diagonalEmbedding N), ?_⟩
  refine ⟨by simp [S.2], ?_, ?_⟩
  · intro x y₁ y₂ h₁ h₂
    rw [Finset.mem_map] at h₁ h₂
    rcases h₁ with ⟨a, ha, h₁eq⟩
    rcases h₂ with ⟨b, hb, h₂eq⟩
    have hax : a = x := congrArg Prod.fst h₁eq
    have hay₁ : a = y₁ := congrArg Prod.snd h₁eq
    have hbx : b = x := congrArg Prod.fst h₂eq
    have hby₂ : b = y₂ := congrArg Prod.snd h₂eq
    exact hay₁.symm.trans (hax.trans (hbx.symm.trans hby₂))
  · intro x₁ x₂ y h₁ h₂
    rw [Finset.mem_map] at h₁ h₂
    rcases h₁ with ⟨a, ha, h₁eq⟩
    rcases h₂ with ⟨b, hb, h₂eq⟩
    have hax₁ : a = x₁ := congrArg Prod.fst h₁eq
    have hay : a = y := congrArg Prod.snd h₁eq
    have hbx₂ : b = x₂ := congrArg Prod.fst h₂eq
    have hby : b = y := congrArg Prod.snd h₂eq
    exact hax₁.symm.trans (hay.trans (hby.symm.trans hbx₂))

@[simp] theorem mem_identityPartial_graph
    (S : QSubset N q) (x y : Fin N) :
    (x, y) ∈ (identityPartial S).graph ↔ x ∈ S.1 ∧ y = x := by
  constructor
  · intro h
    change (x, y) ∈ S.1.map (diagonalEmbedding N) at h
    rw [Finset.mem_map] at h
    rcases h with ⟨a, ha, heq⟩
    have hax : a = x := congrArg Prod.fst heq
    have hay : a = y := congrArg Prod.snd heq
    exact ⟨hax ▸ ha, hay.symm.trans hax⟩
  · rintro ⟨hx, hyx⟩
    change (x, y) ∈ S.1.map (diagonalEmbedding N)
    rw [Finset.mem_map]
    exact ⟨x, hx, by simpa [hyx]⟩

/-- Two partial identity permutations are always compatible. -/
theorem identityPartial_compatible
    (S T : QSubset N q) :
    (identityPartial S).Compatible (identityPartial T) := by
  constructor
  · intro x y₁ y₂ h₁ h₂
    have hy₁ := (mem_identityPartial_graph S x y₁).1 h₁ |>.2
    have hy₂ := (mem_identityPartial_graph T x y₂).1 h₂ |>.2
    exact hy₁.trans hy₂.symm
  · intro x₁ x₂ y h₁ h₂
    have hx₁ := (mem_identityPartial_graph S x₁ y).1 h₁ |>.2
    have hx₂ := (mem_identityPartial_graph T x₂ y).1 h₂ |>.2
    exact hx₁.symm.trans hx₂

/-- The union graph of two partial identities has the same cardinality as the
union of their underlying subsets. -/
theorem card_union_identityPartial
    (S T : QSubset N q) :
    ((identityPartial S).graph ∪ (identityPartial T).graph).card =
      (S.1 ∪ T.1).card := by
  change
    (S.1.map (diagonalEmbedding N) ∪
      T.1.map (diagonalEmbedding N)).card = (S.1 ∪ T.1).card
  rw [← Finset.map_union]
  simp

/-- The collision kernel used in the purity calculation is exactly the joint
moment of two partial identity permutations. -/
theorem collisionKernel_eq_jointMoment
    (S T : QSubset N q) :
    collisionKernel S T =
      (identityPartial S).jointMoment (identityPartial T) := by
  symm
  rw [(identityPartial S).jointMoment_of_compatible_eq_inv_descFactorial
    (identityPartial T) (identityPartial_compatible S T)]
  rw [card_union_identityPartial]
  rfl

/-- Consequently, the scalar called `collisionFreePurity` is literally the
normalized double sum of the exact random-permutation joint moments. -/
theorem collisionFreePurity_eq_jointMoment_average (N q : ℕ) :
    collisionFreePurity N q =
      (∑ S : QSubset N q,
        ∑ T : QSubset N q,
          (identityPartial S).jointMoment (identityPartial T)) /
        (Nat.choose N q : ℚ) ^ 2 := by
  unfold collisionFreePurity
  congr 1
  apply Fintype.sum_congr
  intro S
  apply Fintype.sum_congr
  intro T
  exact collisionKernel_eq_jointMoment S T

end PartialPerm
end LeanQuantumQueries.Permutation
