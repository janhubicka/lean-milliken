import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional
import Milliken.GeneralTree.Vector
import Milliken.GeneralTree.Published

/-!
# ATR-facing general-tree Milliken library

For the only maintained downstream client (the three-uniform ATR theorem),
the canonical API is the unconditional heterogeneous Halpern–Läuchli /
Milliken development over pruned, locally finite rooted trees.

The historical fixed-alphabet homogeneous implementation is deliberately
not re-exported here. It can be removed when a reachability check confirms
there are no remaining dependencies from ATR or the unrestricted library.
-/
