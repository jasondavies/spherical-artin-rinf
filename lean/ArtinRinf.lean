-- Abstract layers (no sorry, no axioms beyond Lean's standard three)
import ArtinRinf.Reidemeister
import ArtinRinf.FreeAbelian
import ArtinRinf.PermMatrix
import ArtinRinf.Criterion
-- Artin groups, the map f : A → ℤ^T ⋊ Perm T, P^ab as a permutation module
import ArtinRinf.ArtinGroup
import ArtinRinf.Aff
import ArtinRinf.Pure
-- Finite certificates
import ArtinRinf.Certificate
import ArtinRinf.OutCert
-- The six exceptional types
import ArtinRinf.BT
import ArtinRinf.Types.H3
import ArtinRinf.Types.H3Out
import ArtinRinf.Types.F4Out
import ArtinRinf.Types.F4
import ArtinRinf.Types.H4
import ArtinRinf.Types.E6
import ArtinRinf.Types.E7
import ArtinRinf.Types.E8
-- Franzsen–Howlett route (alternative Artin-group proof): theorems without `hOut`
import ArtinRinf.FH
import ArtinRinf.Types.H3FH
import ArtinRinf.Types.F4FH
import ArtinRinf.Types.H4FH
import ArtinRinf.Types.E6FH
import ArtinRinf.Types.E7FH
import ArtinRinf.Types.E8FH
-- Type D₅ (the signed-pair constituent)
import ArtinRinf.CoxD5
import ArtinRinf.Types.D5
import ArtinRinf.Types.D5FH

-- The concrete I₂(5) affine extension and its exact Reidemeister count.
import ArtinRinf.Dihedral5.Generators
