# lean-milliken

A reusable Lean 4 library for **Milliken's theorem on strong subtrees**
of arbitrary rooted, pruned, locally finitely branching trees. The number
of immediate successors may vary by node and need not have a global
bound. The formalisation follows Todorčević's *Introduction to Ramsey
Spaces* (Chapters 3, 5 and 6), including the heterogeneous
Halpern–Läuchli induction, the exact A.1–A.4 Ramsey-space interface,
and the Abstract Ellentuck theorem.

**[Read the GitHub Wiki](https://github.com/janhubicka/lean-milliken/wiki)**
for a mathematical proof guide, the published-statement crosswalk,
auxiliary lemmas, adversarial audit records, and a practical
[guide for using the library](docs/wiki/Using-the-library.md).

## Lean quick start

Pin a tested Git revision of this library in your Lake package and import
`Milliken` for the public theorems:

```lean
import Milliken

#check Milliken.AmbientTree
#check Milliken.GeneralTree.StrongSubtree
#check Milliken.GeneralTree.generalApproximationSystem
#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.heterogeneousHDHL_unconditional
#check Milliken.GeneralTree.generalProductHL_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.milliken1979_general_unconditional
#check Milliken.GeneralTree.millikenFixedStemMonochromatic_general
#check Milliken.GeneralTree.millikenFiniteBaireColouring
#check Milliken.GeneralTree.galvinAlternative_realized
#check Milliken.GeneralTree.exists_refinement_realising_with_stem

-- Results about arbitrary topological Ramsey spaces:
#check RamseySpace.finiteBaireColouring
#check RamseySpace.finiteApproximationColouring
#check RamseySpace.ApproximationSystem.isOpen_approxColourFibre
```

The central theorem has the type

```lean
example (U : Milliken.AmbientTree) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := Milliken.GeneralTree.generalApproximationSystem U) :=
  Milliken.GeneralTree.generalMilliken_unconditional U
```

This is the **full topological Ramsey conclusion**: sets with the
Baire property are Ramsey and meagre sets are Ramsey null, with the
published basic-neighbourhood interpretation.

For smaller imports, use `Milliken.GeneralTree.UnconditionalHLAPI`,
`FixedStemUnconditional`, `ProtectedRealization`, `Galvin`,
`BaireColours` or the individual geometric modules.

## Mathematical conventions

A strong subtree may begin above the ambient root. Its selected
source levels form a strictly increasing sequence of ambient
heights. At each successive selected level **every immediate
ambient-child cone** is represented exactly once. The explicit
predecessor condition prohibits extraneous disconnected selected
nodes. `r n T` keeps the first `n` selected *source* levels; `r 0 T`
is empty.

The arbitrary-tree Ramsey-space proof uses Todorčević's literal
maximal-level finitisation `bookLeFin` (6.3), not a carrier-only
approximation order.

## Precise theorem scope

The unconditional finite-colouring theorem
`milliken1979_general_unconditional` currently colours
`FiniteApprox U k`, whose objects carry evidence of **infinite
realisability**. The distinct intrinsic finite-tree representation
has been formalised, but the reverse completion/equivalence still
requires proof before claiming exact quantifier identity with the
original 1979 formulation.

Synchronized product Halpern–Läuchli colours tuples of *nodes on
common levels*. A finite **vector of entire strong subtrees** is a
different colouring problem: the properties in
`GeneralTree.Vector` are separately specified, not proved by the
scalar theorem alone. The Baire-colouring theorem does not assert
a Souslin-measurability bridge without the requisite topological
regularity result.

See [Published statements](docs/wiki/Published-statements.md) for
checked theorems, consequences and open source-equivalence issues.

## Reproducible verification

GitHub Actions builds the complete library and runs a
kernel-axiom audit of designated theorem endpoints, scans the
source for `sorry` and locally declared axioms, and verifies
the module dependency graph.

```bash
lake update
lake exe cache get
lake build
python3 scripts/audit_module_reachability.py
python3 scripts/audit_dependency_graph.py
python3 scripts/audit_source_integrity.py
python3 scripts/audit_public_library.py
```

The theorem/axiom report is produced and checked exactly as in
[`.github/workflows/lean.yml`](.github/workflows/lean.yml).
Only standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`) are accepted.

## Sources

- S. Todorčević, *Introduction to Ramsey Spaces*, Princeton
  University Press, 2010, Chapters 3, 5 and 6.
  [Book PDF](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf).
- K. R. Milliken, “A Ramsey theorem for trees,” *Journal of
  Combinatorial Theory A* **26** (1979), 215–237.
  [DOI](https://doi.org/10.1016/0097-3165(79)90101-8).
