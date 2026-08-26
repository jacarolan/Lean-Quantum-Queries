import LeanQuantumQueries.Permutation.OverlapFactorBound

/-!
# From collision-free purity to a flat spectral sector

This is the final representation-free spectral step used by the one-call
attack.  If `lam` is the list of eigenvalues of the collision-free moment
state, then the exact purity calculation bounds `∑ i, lam i ^ 2`.  Removing
all eigenvalues larger than `A` times this purity loses at most `1 / A` of the
trace, while every retained eigenvalue obeys the desired flatness bound.
-/

namespace LeanQuantumQueries.Permutation
namespace PartialPerm

open scoped BigOperators

/-- The exact collision-free purity, viewed as a real number. -/
noncomputable def collisionFreeBeta (N q : ℕ) : ℝ :=
  (Nat.factorial q : ℝ) * (overlapFactor q : ℝ) /
    (N.descFactorial q : ℝ) ^ 2

/-- An explicit upper bound on the collision-free purity. -/
noncomputable def collisionFreeBetaUpper (N q : ℕ) : ℝ :=
  (Nat.factorial q : ℝ) *
      (2 * (3 : ℝ) ^ q / (2 : ℝ) ^ q) /
    (N.descFactorial q : ℝ) ^ 2

/-- The exact rational purity calculation agrees with `collisionFreeBeta`. -/
theorem collisionFreePurity_real_eq_beta
    {N q : ℕ} (h2qN : 2 * q ≤ N) :
    (collisionFreePurity N q : ℝ) = collisionFreeBeta N q := by
  rw [collisionFreePurity_eq h2qN]
  simp [collisionFreeBeta]

/-- The exact collision-free purity is strictly positive. -/
theorem collisionFreeBeta_pos
    {N q : ℕ} (h2qN : 2 * q ≤ N) :
    0 < collisionFreeBeta N q := by
  have hqN : q ≤ N := by omega
  have hoverlap : (0 : ℝ) < (overlapFactor q : ℝ) := by
    exact_mod_cast overlapFactor_pos q
  have hdesc : (0 : ℝ) < (N.descFactorial q : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hqN)
  unfold collisionFreeBeta
  positivity

/-- The exact purity is at most the explicit elementary bound. -/
theorem collisionFreeBeta_le_upper
    {N q : ℕ} (h2qN : 2 * q ≤ N) :
    collisionFreeBeta N q ≤ collisionFreeBetaUpper N q := by
  have hqN : q ≤ N := by omega
  have hoverlap :
      (overlapFactor q : ℝ) ≤
        2 * (3 : ℝ) ^ q / (2 : ℝ) ^ q := by
    exact_mod_cast overlapFactor_le q
  have hdesc : (0 : ℝ) < (N.descFactorial q : ℝ) := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hqN)
  unfold collisionFreeBeta collisionFreeBetaUpper
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hdesc)).2
  exact mul_le_mul_of_nonneg_left hoverlap (by positivity)

/-- The explicit upper bound is strictly positive. -/
theorem collisionFreeBetaUpper_pos
    {N q : ℕ} (h2qN : 2 * q ≤ N) :
    0 < collisionFreeBetaUpper N q :=
  (collisionFreeBeta_pos h2qN).trans_le
    (collisionFreeBeta_le_upper h2qN)

/-- Indices whose eigenvalue is below the spectral cutoff. -/
noncomputable def flatIndices
    {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (beta A : ℝ) : Finset ι :=
  Finset.univ.filter fun i => lam i ≤ A * beta

@[simp] theorem mem_flatIndices
    {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (beta A : ℝ) (i : ι) :
    i ∈ flatIndices lam beta A ↔ lam i ≤ A * beta := by
  classical
  simp [flatIndices]

/-- Purity-to-flatness theorem.  For a probability spectrum of purity at most
`beta`, the cutoff at `A * beta` retains trace at least `1 - 1 / A` and caps
every retained eigenvalue by `A * beta`. -/
theorem flat_sector_of_purity
    {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (beta A : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (htrace : ∑ i, lam i = 1)
    (hpurity : ∑ i, (lam i) ^ 2 ≤ beta)
    (hbeta : 0 < beta) (hA : 0 < A) :
    1 - 1 / A ≤ ∑ i in flatIndices lam beta A, lam i ∧
      ∀ i ∈ flatIndices lam beta A, lam i ≤ A * beta := by
  classical
  have hhigh :
      ∑ i with lam i > A * beta, lam i ≤ 1 / A :=
    spectral_trimming lam beta A hlam hpurity hbeta hA
  have hsplit :
      (∑ i with lam i > A * beta, lam i) +
          (∑ i in flatIndices lam beta A, lam i) = 1 := by
    calc
      (∑ i with lam i > A * beta, lam i) +
          (∑ i in flatIndices lam beta A, lam i) =
        ∑ i, lam i := by
          simpa [flatIndices, not_lt] using
            (Finset.sum_filter_add_sum_filter_not
              (s := (Finset.univ : Finset ι)) lam
              (fun i => lam i > A * beta))
      _ = 1 := htrace
  constructor
  · linarith
  · intro i hi
    exact (mem_flatIndices lam beta A i).1 hi

/-- Exact final flat-sector theorem for the collision-free
random-permutation moment. -/
theorem collisionFree_flat_sector
    {ι : Type*} [Fintype ι]
    {N q : ℕ}
    (lam : ι → ℝ) (A : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (htrace : ∑ i, lam i = 1)
    (hpurity : ∑ i, (lam i) ^ 2 = collisionFreeBeta N q)
    (h2qN : 2 * q ≤ N) (hA : 0 < A) :
    1 - 1 / A ≤
        ∑ i in flatIndices lam (collisionFreeBeta N q) A, lam i ∧
      ∀ i ∈ flatIndices lam (collisionFreeBeta N q) A,
        lam i ≤ A * collisionFreeBeta N q := by
  apply flat_sector_of_purity
    lam (collisionFreeBeta N q) A hlam htrace hpurity.le
    (collisionFreeBeta_pos h2qN) hA

/-- Explicit quantitative version used in the attack.  It retains trace at
least `1 - 1/A`, and every retained eigenvalue is at most

`A * q! * (2 * 3^q / 2^q) / (N.descFactorial q)^2`.
-/
theorem collisionFree_flat_sector_explicit
    {ι : Type*} [Fintype ι]
    {N q : ℕ}
    (lam : ι → ℝ) (A : ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (htrace : ∑ i, lam i = 1)
    (hpurity : ∑ i, (lam i) ^ 2 = collisionFreeBeta N q)
    (h2qN : 2 * q ≤ N) (hA : 0 < A) :
    1 - 1 / A ≤
        ∑ i in flatIndices lam (collisionFreeBetaUpper N q) A, lam i ∧
      ∀ i ∈ flatIndices lam (collisionFreeBetaUpper N q) A,
        lam i ≤ A * collisionFreeBetaUpper N q := by
  apply flat_sector_of_purity
    lam (collisionFreeBetaUpper N q) A hlam htrace
    (hpurity.le.trans (collisionFreeBeta_le_upper h2qN))
    (collisionFreeBetaUpper_pos h2qN) hA

end PartialPerm
end LeanQuantumQueries.Permutation
