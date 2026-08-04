import Mathlib

namespace LeanQuantumQueries.Permutation

/-- An injective partial function `Fin N ⇀ Fin N` with exactly `r` graph edges. -/
structure PartialPerm (N r : ℕ) where
  graph : Finset (Fin N × Fin N)
  card_graph : graph.card = r
  left_unique : ∀ {x y₁ y₂}, (x, y₁) ∈ graph → (x, y₂) ∈ graph → y₁ = y₂
  right_unique : ∀ {x₁ x₂ y}, (x₁, y) ∈ graph → (x₂, y) ∈ graph → x₁ = x₂
  deriving DecidableEq

instance (N r : ℕ) : Fintype (PartialPerm N r) := Fintype.ofFinite _

namespace PartialPerm

variable {N r : ℕ}

/-- The domain of an injective partial permutation. -/
def dom (f : PartialPerm N r) : Finset (Fin N) := f.graph.image Prod.fst

/-- The image of an injective partial permutation. -/
def ran (f : PartialPerm N r) : Finset (Fin N) := f.graph.image Prod.snd

@[simp] theorem mem_dom_iff (f : PartialPerm N r) (x : Fin N) :
    x ∈ f.dom ↔ ∃ y, (x, y) ∈ f.graph := by
  simp [dom]

@[simp] theorem mem_ran_iff (f : PartialPerm N r) (y : Fin N) :
    y ∈ f.ran ↔ ∃ x, (x, y) ∈ f.graph := by
  simp [ran]

/-- A total permutation extends a partial permutation when it contains every graph edge. -/
def Extends (π : Equiv.Perm (Fin N)) (f : PartialPerm N r) : Prop :=
  ∀ e ∈ f.graph, π e.1 = e.2

instance (π : Equiv.Perm (Fin N)) (f : PartialPerm N r) : Decidable (Extends π f) :=
  inferInstance

@[simp] theorem card_graph (f : PartialPerm N r) : f.graph.card = r := f.card_graph

/-- The empty partial permutation. -/
def empty (N : ℕ) : PartialPerm N 0 where
  graph := ∅
  card_graph := by simp
  left_unique := by simp
  right_unique := by simp

@[simp] theorem empty_graph (N : ℕ) : (empty N).graph = ∅ := rfl

@[simp] theorem extends_empty (π : Equiv.Perm (Fin N)) : Extends π (empty N) := by
  simp [Extends]

/-- Add an edge whose domain and image are both unused. -/
def insert (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) : PartialPerm N (r + 1) where
  graph := insert (x, y) f.graph
  card_graph := by
    rw [Finset.card_insert_of_not_mem]
    · simpa [f.card_graph]
    · intro hxy
      exact hx ((mem_dom_iff f x).2 ⟨y, hxy⟩)
  left_unique := by
    intro x' y₁ y₂ h₁ h₂
    simp only [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · simpa using congrArg Prod.snd (h₁.trans h₂.symm)
    · subst h₁
      exact False.elim (hx ((mem_dom_iff f x).2 ⟨y₂, h₂⟩))
    · subst h₂
      exact False.elim (hx ((mem_dom_iff f x).2 ⟨y₁, h₁⟩))
    · exact f.left_unique h₁ h₂
  right_unique := by
    intro x₁ x₂ y' h₁ h₂
    simp only [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · simpa using congrArg Prod.fst (h₁.trans h₂.symm)
    · subst h₁
      exact False.elim (hy ((mem_ran_iff f y).2 ⟨x₂, h₂⟩))
    · subst h₂
      exact False.elim (hy ((mem_ran_iff f y).2 ⟨x₁, h₁⟩))
    · exact f.right_unique h₁ h₂

@[simp] theorem graph_insert (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) :
    (f.insert x y hx hy).graph = insert (x, y) f.graph := rfl

@[simp] theorem inserted_edge_mem (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) :
    (x, y) ∈ (f.insert x y hx hy).graph := by simp

@[simp] theorem old_edge_mem_insert_iff (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) (e : Fin N × Fin N) :
    e ∈ (f.insert x y hx hy).graph ↔ e = (x, y) ∨ e ∈ f.graph := by
  simp [insert]

/-- A partial permutation is compatible with another one if their union is still
left- and right-unique. -/
def Compatible (f : PartialPerm N r) {s : ℕ} (g : PartialPerm N s) : Prop :=
  (∀ {x y₁ y₂}, (x, y₁) ∈ f.graph → (x, y₂) ∈ g.graph → y₁ = y₂) ∧
  (∀ {x₁ x₂ y}, (x₁, y) ∈ f.graph → (x₂, y) ∈ g.graph → x₁ = x₂)

instance (f : PartialPerm N r) {s : ℕ} (g : PartialPerm N s) :
    Decidable (Compatible f g) := inferInstance

end PartialPerm

end LeanQuantumQueries.Permutation
