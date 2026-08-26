import LeanQuantumQueries.Permutation.CollisionKernelMoment
import LeanQuantumQueries.Permutation.CollisionFreeSpectralCutoff

/-!
# Representation-free flatness chain for the one-call permutation attack

The imported modules provide the complete mathematical chain:

1. exact joint moments of partial-permutation extension indicators;
2. identification of the collision kernel with those joint moments;
3. exact evaluation of the collision-free moment purity;
4. an explicit exponential upper bound on that purity;
5. spectral truncation producing a high-mass sector with bounded eigenvalues.

The final theorem is
`PartialPerm.collisionFree_flat_sector_explicit`.
-/
