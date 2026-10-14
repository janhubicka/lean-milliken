import Milliken.GeneralTree.IntrinsicFinite
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

/-!
# ATR-facing general-tree Milliken library

For the only maintained downstream client (the three-uniform ATR theorem),
the canonical API is the unconditional heterogeneous Halpern–Läuchli /
Milliken development over pruned, locally finite rooted trees.

The historical fixed-alphabet homogeneous implementation is deliberately
not re-exported here. Imports are kept transitively minimal by CI.
-/
