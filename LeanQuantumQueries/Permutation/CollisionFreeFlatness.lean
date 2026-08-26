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
  simpa [sharedCard, f.card_graph] using
    (Finset.card_le_card (Finset.inter_subset_left : f.graph ∩ g.graph ⊆ f.graph))

/-- The union size is determined by the number of shared edges. -/
theorem card_union_graph_eq (f g : PartialPerm N q) :
    (f.graph ∪ g.graph).card = 2 * q - f.sharedCard g := by
  have h := Finset.card_union_add_card_inter f.graph g.graph
  have hf := f.card_graph
  have hg := g.card_graph
  unfold sharedCard
  omega

/-- Graphs with `q` edges, forgetting the partial-permutation constraints. -/
def GraphOfCard (N q : ℕ) :=
  {s : Finset (Fin N × Fin N) // s.card = q}

noncomputable instance (N q : ℕ) : Fintype (GraphOfCard N q) := by
  classical
  unfold GraphOfCard
  infer_instance

/-- Exact cardinality of the ambient family of `q`-edge graphs. -/
theorem card_graphOfCard (N q : ℕ) :
    Fintype.card (GraphOfCard N q) = Nat.choose (N * N) q := by
  change Fintype.card
      {s : Finset (Fin N × Fin N) // s.card = q} = Nat.choose (N * N) q
  simpa using (Fintype.card_finset_len (α := Fin N × Fin N) q)

/-- Forgetting the uniqueness constraints is injective. -/
def graphEmbedding (N q : ℕ) : PartialPerm N q ↪ GraphOfCard N q where
  toFun f := ⟨f.graph, f.card_graph⟩
  inj' := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun z : GraphOfCard N q => z.1) h

/-- A crude but useful upper bound on the number of size-`q` partial
permutations. -/
theorem card_partialPerm_le_choose (N q : ℕ) :
    Fintype.card (PartialPerm N q) ≤ Nat.choose (N * N) q := by
  calc
    Fintype.card (PartialPerm N q) ≤ Fintype.card (GraphOfCard N q) :=
      Fintype.card_le_of_injective (graphEmbedding N q) (graphEmbedding N q).injective
    _ = Nat.choose (N * N) q := card_graphOfCard N q

/-- The class of compatible size-`q` partial permutations having exactly `j`
shared graph edges with `f`. -/
def CompatibleShared (f : PartialPerm N q) (j : ℕ) :=
  {g : PartialPerm N q // f.Compatible g ∧ f.sharedCard g = j}

noncomputable instance (f : PartialPerm N q) (j : ℕ) :
    Fintype (CompatibleShared f j) := by
  classical
  unfold CompatibleShared
  infer_instance

/-- The elementary code used to bound an overlap class: record the shared
edges and all remaining edges.  The second component deliberately forgets all
matching constraints. -/
def SharedFreshCode (f : PartialPerm N q) (j : ℕ) :=
  {s : Finset (Fin N × Fin N) // s ⊆ f.graph ∧ s.card = j} ×
  GraphOfCard N (q - j)

noncomputable instance (f : PartialPerm N q) (j : ℕ) :
    Fintype (SharedFreshCode f j) := by
  classical
  unfold SharedFreshCode
  infer_instance

/-- Decompose a compatible graph into the part shared with `f` and the
remaining edges. -/
def sharedFreshCode (f : PartialPerm N q) (j : ℕ) :
    CompatibleShared f j → SharedFreshCode f j := fun g =>
  ⟨⟨f.graph ∩ g.1.graph, Finset.inter_subset_left,
      by simpa [sharedCard] using g.2.2⟩,
    ⟨g.1.graph \ f.graph, by
      rw [Finset.card_sdiff, g.1.card_graph]
      simpa [sharedCard, Finset.inter_comm] using
        congrArg (fun n => q - n) g.2.2⟩⟩

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
  apply Finset.ext
  intro e
  change e ∈ g₁.1.graph ↔ e ∈ g₂.1.graph
  have hreconstruct (g : PartialPerm N q) :
      e ∈ g.graph ↔
        e ∈ f.graph ∩ g.graph ∨ e ∈ g.graph \ f.graph := by
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [hreconstruct g₁.1, hreconstruct g₂.1, hs, ht]

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
      change Fintype.card
          ({s : Finset (Fin N × Fin N) // s ⊆ f.graph ∧ s.card = j} ×
            GraphOfCard N (q - j)) = _
      rw [Fintype.card_prod, card_sharedCode, card_graphOfCard]

/-- The subexponential combinatorial factor appearing in the collision-free
purity bound. -/
def rookFactor (q : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (q + 1),
    (Nat.choose q a : ℚ) / Nat.factorial a

/-- A finite-family version of the spectral trimming estimate.  Interpreting
`lam i` as the eigenvalues of a density matrix, all eigenvalues above
`A * beta` carry total mass at most `1 / A`. -/
theorem spectral_trimming
    {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (beta A : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hpurity : ∑ i, (lam i) ^ 2 ≤ beta)
    (hbeta : 0 < beta) (hA : 0 < A) :
    ∑ i with lam i > A * beta, lam i ≤ 1 / A := by
  have hden : 0 < A * beta := mul_pos hA hbeta
  calc
    ∑ i with lam i > A * beta, lam i
        ≤ ∑ i with lam i > A * beta, (lam i) ^ 2 / (A * beta) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : A * beta < lam i := by simpa using hi
          rw [le_div_iff₀ hden]
          nlinarith [hlam i]
    _ = (∑ i with lam i > A * beta, (lam i) ^ 2) / (A * beta) := by
          rw [Finset.sum_div]
    _ ≤ beta / (A * beta) := by
          apply (div_le_div_iff_of_pos_right hden).2
          have hsub :
              (∑ i with lam i > A * beta, (lam i) ^ 2) ≤
                ∑ i, (lam i) ^ 2 := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _)
              (fun i _ _ => sq_nonneg (lam i))
          exact hsub.trans hpurity
    _ = 1 / A := by
          field_simp [hA.ne', hbeta.ne']

end PartialPerm
end LeanQuantumQueries.Permutation
