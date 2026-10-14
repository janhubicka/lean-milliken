# Using the Milliken Lean library

This is a reusable Lean 4 formalisation of strong-subtree Ramsey theory,
not an application-specific verification. The primary mathematical model
is an arbitrary **pruned, rooted, locally finitely branching tree**:
the immediate-successor set of each node is finite and nonempty, but
there need not be a global bound on branching degree.

## Install and import

Add a pinned revision of the library to your project's `lakefile.toml`:

```toml
[[require]]
name = "milliken"
git = "https://github.com/janhubicka/lean-milliken"
rev = "<a-tested-commit-SHA>"
```

Use `import Milliken` for the supported public theorem collection,
or import a narrower `Milliken.GeneralTree.*` module when useful.
The dependency's `lean-toolchain` and `lakefile.toml` fix the required
Lean and Mathlib versions. A downstream project should use compatible
Mathlib revisions and verify its own `lake build`.

## Main mathematical endpoints

```lean
import Milliken

open Milliken
open Milliken.GeneralTree

-- Todorčević's topological Ramsey-space theorem (full Baire formulation).
#check GeneralTree.generalMilliken_unconditional

-- Product Halpern–Läuchli and the one-step boundary instance.
#check GeneralTree.heterogeneousHDHL_unconditional
#check GeneralTree.generalProductHL_unconditional
#check GeneralTree.boundaryProductHL_unconditional

-- Original-style finite colouring for *realised* finite approximations.
#check GeneralTree.milliken1979_general_unconditional

-- A prescribed finite strong stem is kept during colouring.
#check GeneralTree.millikenFixedStemFiniteColouring_general
#check GeneralTree.millikenFixedStemMonochromatic_general

-- Baire-measurable colourings of infinite strong trees, and Galvin's
-- avoidance/hitting alternative for finite approximation families.
#check GeneralTree.millikenFiniteBaireColouring
#check GeneralTree.galvinAlternative_realized

-- Geometric realisation of a finite approximation preserving a stem.
#check GeneralTree.exists_refinement_realising_with_stem

-- Generic finite-colouring facts usable in *any* topological Ramsey space.
#check RamseySpace.finiteBaireColouring
#check RamseySpace.finiteApproximationColouring
#check RamseySpace.ApproximationSystem.isOpen_approxColourFibre
```

For example, the complete topological theorem has no hypotheses other
than its `AmbientTree`:

```lean
import Milliken

example (U : Milliken.AmbientTree) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := Milliken.GeneralTree.generalApproximationSystem U) :=
  Milliken.GeneralTree.generalMilliken_unconditional U
```

A strong subtree does not have to contain the ambient root. Its
selected **source** levels form a strictly increasing sequence of
ambient heights. Every ambient child cone is represented exactly once
at the next selected source level; a merely meet-preserving subset
is not strong enough.

## Reusable geometry and proof components

| Import | What it provides |
| --- | --- |
| `Milliken.AmbientTree` | Locally finite, pruned rooted ambient trees and rank lemmas |
| `Milliken.GeneralTree` | Strong-subtree carrier, selected levels, refinement and finite approximation types |
| `Milliken.GeneralTree.Published` | Source-facing `S_∞`, `S_k`, `r_k` and maximal-level `bookLeFin` |
| `Milliken.GeneralTree.UnconditionalHLAPI` | Arbitrary-tree product HL, boundary HL and one-step pigeonhole |
| `Milliken.GeneralTree.FixedStemUnconditional` | Protected-initial-part colourings |
| `Milliken.GeneralTree.ProtectedRealization` | Relative finite strong-tree extension with a fixed prefix |
| `Milliken.GeneralTree.Galvin` | Open-family avoidance/hitting |
| `Milliken.GeneralTree.BaireColours` | Finite Baire-fibre colouring of infinite strong trees |
| `Milliken.GeneralTree.IntrinsicFinite` | Intrinsic finite strong-tree witnesses, their finite frontier geometry, and forward map from realised approximations |
| `Milliken.FiniteColourRamseySpace` | Generic Baire/fixed-height finite-colouring lemmas |

The combinatorial proof itself includes a universal heterogeneous
high-density Halpern–Läuchli induction, full selected-source-level
compression, a common-root wedge, complement-obstruction transport,
finite frontier grafting, published A.1–A.4 and the Abstract Ellentuck
theorem. The [proof architecture](Proof-architecture.md) and
[auxiliary lemma guide](Geometry-and-auxiliary-lemmas.md) give mathematical
explanations and exact Lean declaration locations.

## Theorem scope and open interfaces

- `generalMilliken_unconditional` really concludes the full textbook
  topological Ramsey property: all Baire-property sets are Ramsey and
  all meagre sets are Ramsey null.
- `FiniteApprox U k` carries a proof that its carrier is the initial
  part of some infinite strong tree. The exact identification with **all
  intrinsic** finite strong trees still needs the reverse
  finite-to-infinite completion theorem; do not silently claim this.
- A synchronized **vector** finite-strong-subtree colouring is a distinct
  theorem from product HL for level-tuples. The declarations
  `HasVectorMillikenFiniteColourProperty` and
  `HasVectorFixedStemColourProperty` presently state target properties,
  not established results.
- The Baire-colouring corollary does not automatically include the
  additional Souslin-measurable regularity assertion without its
  separate topological bridge.

These qualifications are tracked in the
[published source crosswalk](Published-statements.md) and
[proof-audit tracker](../audits/AUDIT_TRACKER_2026.md).

## Verification and downstream integration

The GitHub Actions workflow checks `lake build`, all-source
integrity, import reachability, and the designated theorem
`#print axioms` reports. Only Lean's standard classical/propositional
axioms are permitted; source admissions and local axioms are rejected.

For any new application, add a small Lean file importing
`Milliken` or a narrower module, state the **actual theorem** to be
used, and ensure it compiles at the exact pinned library revision.
The library's own CI does not certify propositions newly introduced
by downstream applications. Application-specific encoding, coding
equivalences and interpretation of finite structures must be checked
in those projects, rather than inserted as compatibility APIs here.

## References

- S. Todorčević, *Introduction to Ramsey Spaces* (2010),
  Chapters 3, 5 and 6.
- K. R. Milliken, *A Ramsey theorem for trees*, *Journal of
  Combinatorial Theory A* **26** (1979), 215–237.
