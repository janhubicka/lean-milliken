import Milliken.GeneralTree.ProtectedRealization
import Milliken.GeneralTree.Galvin
import Milliken.GeneralTree.BaireColours
import Milliken.GeneralTree.IntrinsicFinite
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

/-!
# Milliken: Ramsey theory of strong subtrees

This library proves the unrestricted Milliken theorem for pruned, locally
finitely branching rooted trees and exports the complete supporting
Halpern–Läuchli and Ramsey-space interfaces. It also provides the
finite-approximation, protected-stem, Galvin and Baire-colouring corollaries.

The umbrella import exposes the public theorems, while individual
`Milliken.GeneralTree.*` modules allow finer-grained imports.
Internal proof modules do not impose any application-specific assumptions.
-/
