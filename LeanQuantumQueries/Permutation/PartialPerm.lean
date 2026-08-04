import Mathlib

namespace LeanQuantumQueries.Permutation

/-- Predicate saying that a finite graph is the graph of an injective partial
function with exactly `r` edges. -/
def IsPartialPermGraph (N r : ℕ) (g : Finset (Fin N × Fin N)) : Prop :=
  g.card = r ∧
  (∀ {x y₁ y₂}, (x, y₁) ∈ g → (x, y₂) ∈ g → y₁ = y₂) ∧
  (∀ {x₁ x₂ y}, (x₁, y) ∈ g → (x₂, y) ∈ g → x₁ = x₂)

/-- An injective partial function `Fin N ⇀ Fin N` with exactly `r` graph edges. -/
def PartialPerm (N r : ℕ) :=
  {g : Finset (Fin N × Fin N) // IsPartialPermGraph N r g}

deriving instance DecidableEq for PartialPerm

noncomputable instance (N r : ℕ) : Fintype (PartialPerm N r) :=
  Fintype.ofFinite _

namespace PartialPerm

variable {N r : ℕ}

/-- The graph of a partial permutation. -/
def graph (f : PartialPerm N r) : Finset (Fin N × Fin N) := f.1

@[simp] theorem card_graph (f : PartialPerm N r) : f.graph.card = r := f.2.1

/-- Left uniqueness of the graph. -/
theorem left_unique (f : PartialPerm N r) {x y₁ y₂ : Fin N}
    (h₁ : (x, y₁) ∈ f.graph) (h₂ : (x, y₂) ∈ f.graph) : y₁ = y₂ :=
  f.2.2.1 h₁ h₂

/-- Right uniqueness of the graph. -/
theorem right_unique (f : PartialPerm N r) {x₁ x₂ y : Fin N}
    (h₁ : (x₁, y) ∈ f.graph) (h₂ : (x₂, y) ∈ f.graph) : x₁ = x₂ :=
  f.2.2.2 h₁ h₂

/-- The domain of an injective partial permutation. -/
def dom (f : PartialPerm N r) : Finset (Fin N) := f.graph.image Prod.fst

/-- The image of an injective partial permutation. -/
def ran (f : PartialPerm N r) : Finset (Fin N) := f.graph.image Prod.snd

@[simp] theorem mem_dom_iff (f : PartialPerm N r) (x : Fin N) :
    x ∈ f.dom ↔ ∃ y, (x, y) ∈ f.graph := by
  simp [dom, graph]

@[simp] theorem mem_ran_iff (f : PartialPerm N r) (y : Fin N) :
    y ∈ f.ran ↔ ∃ x, (x, y) ∈ f.graph := by
  simp [ran, graph]

/-- A total permutation extends a partial permutation when it contains every graph edge. -/
def Extends (π : Equiv.Perm (Fin N)) (f : PartialPerm N r) : Prop :=
  ∀ e ∈ f.graph, π e.1 = e.2

noncomputable instance (π : Equiv.Perm (Fin N)) (f : PartialPerm N r) :
    Decidable (Extends π f) := Classical.propDecidable _

/-- The empty partial permutation. -/
def empty (N : ℕ) : PartialPerm N 0 :=
  ⟨∅, by simp [IsPartialPermGraph]⟩

@[simp] theorem empty_graph (N : ℕ) : (empty N).graph = ∅ := rfl

@[simp] theorem extends_empty (π : Equiv.Perm (Fin N)) : Extends π (empty N) := by
  simp [Extends]

/-- Add an edge whose domain and image are both unused. -/
def extend (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) : PartialPerm N (r + 1) := by
  refine ⟨Finset.insert (x, y) f.graph, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem]
    · simpa [f.card_graph]
    · intro hxy
      exact hx ((mem_dom_iff f x).2 ⟨y, hxy⟩)
  · intro x' y₁ y₂ h₁ h₂
    simp only [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · simpa using congrArg Prod.snd (h₁.trans h₂.symm)
    · have hxy : x' = x ∧ y₁ = y := Prod.mk.inj h₁
      subst x'
      subst y₁
      exact False.elim (hx ((mem_dom_iff f x).2 ⟨y₂, h₂⟩))
    · have hxy : x' = x ∧ y₂ = y := Prod.mk.inj h₂
      subst x'
      subst y₂
      exact False.elim (hx ((mem_dom_iff f x).2 ⟨y₁, h₁⟩))
    · exact f.left_unique h₁ h₂
  · intro x₁ x₂ y' h₁ h₂
    simp only [Finset.mem_insert] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · simpa using congrArg Prod.fst (h₁.trans h₂.symm)
    · have hxy : x₁ = x ∧ y' = y := Prod.mk.inj h₁
      subst x₁
      subst y'
      exact False.elim (hy ((mem_ran_iff f y).2 ⟨x₂, h₂⟩))
    · have hxy : x₂ = x ∧ y' = y := Prod.mk.inj h₂
      subst x₂
      subst y'
      exact False.elim (hy ((mem_ran_iff f y).2 ⟨x₁, h₁⟩))
    · exact f.right_unique h₁ h₂

@[simp] theorem graph_extend (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) :
    (f.extend x y hx hy).graph = Finset.insert (x, y) f.graph := rfl

@[simp] theorem inserted_edge_mem (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) :
    (x, y) ∈ (f.extend x y hx hy).graph := by simp

@[simp] theorem edge_mem_extend_iff (f : PartialPerm N r) (x y : Fin N)
    (hx : x ∉ f.dom) (hy : y ∉ f.ran) (e : Fin N × Fin N) :
    e ∈ (f.extend x y hx hy).graph ↔ e = (x, y) ∨ e ∈ f.graph := by
  simp [extend]

/-- A partial permutation is compatible with another one if their union is still
left- and right-unique. -/
def Compatible (f : PartialPerm N r) {s : ℕ} (g : PartialPerm N s) : Prop :=
  (∀ {x y₁ y₂}, (x, y₁) ∈ f.graph → (x, y₂) ∈ g.graph → y₁ = y₂) ∧
  (∀ {x₁ x₂ y}, (x₁, y) ∈ f.graph → (x₂, y) ∈ g.graph → x₁ = x₂)

noncomputable instance (f : PartialPerm N r) {s : ℕ} (g : PartialPerm N s) :
    Decidable (Compatible f g) := Classical.propDecidable _

end PartialPerm

end LeanQuantumQueries.Permutation
