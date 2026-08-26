import LeanQuantumQueries.Permutation.JointMoment
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Representation-free flatness for collision-free permutation queries

This file develops the combinatorial and scalar spectral estimates used to
turn the exact joint-moment identity into the generic one-call distinguisher.
No representation theory is used.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

variable {N q : ℕ}

/-- Number of graph edges shared by two partial permutations. -/
def sharedCard (f g : PartialPerm N q) : ℕ :=
  (f.graph ∩ g.graph).card

@[simp] theorem sharedCard_self (f : PartialPerm N q) : f.sharedCard f = q := by
  simp [sharedCard, f.card_graph]

/-- The shared graph has at most `q` edges. -/
theorem sharedCard_le (f g : PartialPerm N q) : f.sharedCard g ≤ q := by
  rw [sharedCard, ← f.card_graph]
  exact Finset.card_le_card (Finset.inter_subset_left)

/-- The union size is determined by the number of shared edges. -/
theorem card_union_graph_eq (f g : PartialPerm N q) :
    (f.graph ∪ g.graph).card = 2 * q - f.sharedCard g := by
  have h := Finset.card_union_add_card_inter f.graph g.graph
  rw [f.card_graph, g.card_graph] at h
  omega

/-- Graphs with `q` edges, forgetting the partial-permutation constraints. -/
def GraphOfCard (N q : ℕ) :=
  {s : Finset (Fin N × Fin N) // s.card = q}

noncomputable instance (N q : ℕ) : Fintype (GraphOfCard N q) :=
  Fintype.ofFinite _

/-- Forgetting the uniqueness constraints is injective. -/
def graphEmbedding (N q : ℕ) : PartialPerm N q ↪ GraphOfCard N q where
  toFun f := ⟨f.graph, f.card_graph⟩
  inj' := by
    intro f g h
    apply Subtype.ext
    exact congrArg Subtype.val h

/-- A crude but useful upper bound on the number of size-`q` partial
permutations. -/
theorem card_partialPerm_le_choose (N q : ℕ) :
    Fintype.card (PartialPerm N q) ≤ Nat.choose (N * N) q := by
  calc
    Fintype.card (PartialPerm N q) ≤ Fintype.card (GraphOfCard N q) :=
      Fintype.card_le_of_injective (graphEmbedding N q) (graphEmbedding N q).injective
    _ = Nat.choose (N * N) q := by
      simpa [GraphOfCard, Fintype.card_prod] using
        (Fintype.card_finset_len (α := Fin N × Fin N) q)

/-- The class of compatible size-`q` partial permutations having exactly `j`
shared graph edges with `f`. -/
def CompatibleShared (f : PartialPerm N q) (j : ℕ) :=
  {g : PartialPerm N q // f.Compatible g ∧ f.sharedCard g = j}

noncomputable instance (f : PartialPerm N q) (j : ℕ) :
    Fintype (CompatibleShared f j) :=
  Fintype.ofFinite _

/-- The elementary code used to bound an overlap class: record the shared
edges and all remaining edges.  The second component deliberately forgets all
matching constraints. -/
def SharedFreshCode (f : PartialPerm N q) (j : ℕ) :=
  {s : Finset (Fin N × Fin N) // s ⊆ f.graph ∧ s.card = j} ×
  GraphOfCard N (q - j)

noncomputable instance (f : PartialPerm N q) (j : ℕ) :
    Fintype (SharedFreshCode f j) :=
  Fintype.ofFinite _

/-- Decompose a compatible graph into the part shared with `f` and the
remaining edges. -/
def sharedFreshCode (f : PartialPerm N q) (j : ℕ) :
    CompatibleShared f j → SharedFreshCode f j := fun g =>
  ⟨⟨f.graph ∩ g.1.graph, Finset.inter_subset_left,
      by simpa [sharedCard] using g.2.2.symm⟩,
    ⟨g.1.graph \ f.graph, by
      have hinter : (g.1.graph ∩ f.graph).card = j := by
        simpa [sharedCard, Finset.inter_comm] using g.2.2
      rw [Finset.card_sdiff]
      · rw [g.1.card_graph, hinter]
      · exact Finset.inter_subset_left⟩⟩

/-- The shared/fresh decomposition remembers the original graph. -/
theorem sharedFreshCode_injective (f : PartialPerm N q) (j : ℕ) :
    Function.Injective (sharedFreshCode f j) := by
  intro g₁ g₂ h
  have hs : f.graph ∩ g₁.1.graph = f.graph ∩ g₂.1.graph :=
    congrArg (fun z => z.1.1) h
  have ht : g₁.1.graph \ f.graph = g₂.1.graph \ f.graph :=
    congrArg (fun z => z.2.1) h
  apply Subtype.ext
  apply Subtype.ext
  ext e
  have hreconstruct (g : PartialPerm N q) :
      e ∈ g.graph ↔
        e ∈ f.graph ∩ g.graph ∨ e ∈ g.graph \ f.graph := by
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [hreconstruct g₁, hreconstruct g₂, hs, ht]

/-- Cardinality of the shared-edge part of the code. -/
theorem card_sharedCode (f : PartialPerm N q) (j : ℕ) :
    Fintype.card {s : Finset (Fin N × Fin N) // s ⊆ f.graph ∧ s.card = j} =
      Nat.choose q j := by
  classical
  rw [Fintype.card_subtype]
  have heq :
      ({s : Finset (Fin N × Fin N) | s ⊆ f.graph ∧ s.card = j} : Finset _) =
        f.graph.powersetCard j := by
    ext s
    simp [and_comm]
  rw [heq, Finset.card_powersetCard, f.card_graph]

/-- The number of compatible `g` with shared-edge count `j` is at most the
number of possible shared and fresh edge sets. -/
theorem card_compatibleShared_le
    (f : PartialPerm N q) (j : ℕ) :
    Fintype.card (CompatibleShared f j) ≤
      Nat.choose q j * Nat.choose (N * N) (q - j) := by
  calc
    Fintype.card (CompatibleShared f j) ≤
        Fintype.card (SharedFreshCode f j) :=
      Fintype.card_le_of_injective (sharedFreshCode f j)
        (sharedFreshCode_injective f j)
    _ = Nat.choose q j * Nat.choose (N * N) (q - j) := by
      simp [SharedFreshCode, GraphOfCard, card_sharedCode,
        Fintype.card_finset_len, Fintype.card_prod]

/-- The subexponential combinatorial factor appearing in the collision-free
purity bound. -/
def rookFactor (q : ℕ) : ℚ :=
  ∑ a in Finset.range (q + 1), (Nat.choose q a : ℚ) / Nat.factorial a

/-- A finite-family version of the spectral trimming estimate.  Interpreting
`lam i` as the eigenvalues of a density matrix, all eigenvalues above
`A * beta` carry total mass at most `1 / A`. -/
theorem spectral_trimming
    {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (beta A : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hpurity : ∑ i, (lam i) ^ 2 ≤ beta)
    (hbeta : 0 ≤ beta) (hA : 0 < A) :
    ∑ i with lam i > A * beta, lam i ≤ 1 / A := by
  have hAbeta : 0 ≤ A * beta := mul_nonneg hA.le hbeta
  calc
    ∑ i with lam i > A * beta, lam i
        ≤ ∑ i with lam i > A * beta, (lam i) ^ 2 / (A * beta) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : A * beta < lam i := by simpa using hi
          by_cases hb0 : beta = 0
          · subst beta
            simp at hi'
          · have hden : 0 < A * beta := mul_pos hA (lt_of_le_of_ne hbeta (Ne.symm hb0))
            rw [le_div_iff₀ hden]
            nlinarith [hlam i]
    _ ≤ beta / (A * beta) := by
          apply div_le_div_of_nonneg_right _ hAbeta
          exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
            (fun _ _ _ => (sq_nonneg _))).trans hpurity
    _ ≤ 1 / A := by
          by_cases hb0 : beta = 0
          · simp [hb0, hA.ne']
          · field_simp [hA.ne', hb0]

end PartialPerm
end LeanQuantumQueries.Permutation
