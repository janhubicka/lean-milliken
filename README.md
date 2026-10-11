# lean-milliken

Lean 4 formalization of Milliken's strong-tree theorem, organized around
Todorčević's *Introduction to Ramsey Spaces*, Chapters 3 and 6.

## Main theorem

The repository now proves Milliken's theorem with no Halpern--Läuchli
hypothesis left as an argument.

The public endpoints are:

```lean
Milliken.Chapter6.milliken
Milliken.Chapter6.milliken_onBasicNeighborhoods
```

For every finite nonempty branching alphabet `ι`, the first theorem proves
that the strong-subtree space is a topological Ramsey space; the second gives
the literal basic-neighborhood formulation.

The proof path is:

1. the verified infinite Hales--Jewett subspace theorem from
   `janhubicka/lean-successors`;
2. a product-alphabet bridge yielding strong-subtree Halpern--Läuchli;
3. Todorčević Chapter 6: A.1--A.4 for the strong-tree approximation space;
4. metric closedness;
5. the Abstract Ellentuck theorem from
   `janhubicka/lean-ramsey-space-todorcevic`.

The conditional Chapter 6 endpoints are retained as:

```lean
Milliken.Chapter6.milliken_of_strongSubtreeHL
Milliken.Chapter6.milliken_onBasicNeighborhoods_of_strongSubtreeHL
```

The Hales--Jewett bridge itself is:

```lean
Milliken.HalpernLauchli.HalesJewettBridge.strongSubtreeHL
```

## Application API (homogeneous ambient trees)

Use `import Milliken.Applications` rather than importing the proof files.

```lean
import Milliken.Applications

#check Milliken.Applications.todorcevic62_homogeneous
#check Milliken.Applications.millikenFiniteColouring
#check Milliken.Applications.millikenFixedStemFiniteColouring
#check Milliken.Applications.exists_refinement_realising
#check Milliken.Applications.milliken1979_homogeneous
#check Milliken.Applications.millikenFixedStem1979_homogeneous
```

- `millikenFiniteColouring k colour`: an infinite strong embedding `B`
  on which every height-`k` approximation of a refinement has the same colour.
- `millikenFixedStemFiniteColouring n k A colour`: a refinement
  `B ≤ A` with `r_n(B) = r_n(A)`, homogeneous for the height-`k`
  approximations of all further refinements retaining that same stem.
  Source level `n` is not necessarily ambient level `n`.
- `millikenFixedStem1979_homogeneous ell k h A colour`: the direct\n  `Str_{ell,k}`-style consequence with `ell ≤ k`, colour all finite\n  height-`k` strong subtrees contained in `B` and having `r_ell(A)`\n  as their initial approximation.\n- `milliken1979_homogeneous k colour`: the direct finite-tree formulation:
  *every* height-`k` realised finite strong subtree with its carrier
  contained in `B` has the same colour. The bridge from carrier inclusion
  is proved by `exists_refinement_realising`.
- `todor...62_homogeneous`: Todorčević Theorem 6.2 in the homogeneous
  case, on all basic Ellentuck neighbourhoods.

**Scope warning.** These are unconditional theorems only for
`List ι` with a fixed finite, nonempty branching alphabet.
The library defines `AmbientTree` and `GeneralTree.StrongSubtree` with
exact (str1)–(str2), and the unproved *property definition*
`GeneralTree.HasMillikenFiniteColourProperty`. It has **not yet proved** Milliken
for arbitrary pruned, finitely branching rooted trees with unbounded degrees,
as in Todorčević 6.2 and Milliken's 1979 abstract. Nor does the current
application API prove a synchronized finite-vector-strong-subtree
version for several trees. These two transports are needed for the
three-coordinate variable-branching type trees in `3-uniform-diaries`.

See [published-statement crosswalk](docs/PUBLISHED_STATEMENTS.md) and
[referee audit checklist](docs/REFEREE_AUDITS.md). Both distinguish
completed Lean results from unproved generalizations.

## Verified Chapter 6 route

The checked Chapter 6 path contains:

1. strong embeddings and finite approximations (A.1);
2. the finite carrier/factorization order (A.2);
3. finite-stem extension and the depth-boundary splice (A.3);
4. Todorčević's Lemma 6.1 from strong-subtree Halpern--Läuchli, followed by
   the lift from the canonical stem to arbitrary depth (A.4);
5. metric closedness of the strong-tree space;
6. assembly through Abstract Ellentuck.

## Chapter 3 / Halpern--Läuchli reconstruction

The repository also contains a separate reconstruction of Todorčević's
Chapter 3 density proof.  This is no longer a dependency of the final
Milliken theorem, but is kept as an independent formalization project.

Checked components include:

- the density and level-matrix language;
- Lemma 3.5 and the asymmetric formulation;
- stabilization/section machinery and its closedness fusion limit;
- the minimal-`D` argument in Lemma 3.15;
- explicit tail normalization and nested matrix refinement for the implicit
  step around equation (3);
- the normalized Lemma 3.15;
- the increasing `(n_p,X_p)` tower and Lemma 3.16;
- the stabilized reduced successor induction step;
- compactness for the reduced dichotomy;
- finite level-block coding and the obstruction supplied by highly dense
  sets.

The remaining source-faithful Chapter 3 item is the final Remark 3.8
level-change upgrade from the reduced dichotomy to the full highly-dense
formulation.  This does **not** block the main Milliken theorem, because the
verified Hales--Jewett bridge supplies strong-subtree Halpern--Läuchli
directly.

## CI and proof audit

The project is pinned to fixed revisions of Mathlib,
`lean-ramsey-space-todorcevic`, and `lean-successors`.  CI runs the full
`lake build` and a transitive `#print axioms` audit for:

- the Hales--Jewett to Halpern--Läuchli bridge;
- `Milliken.Chapter6.milliken`;
- `Milliken.Chapter6.milliken_onBasicNeighborhoods`.

The audit rejects `sorryAx` and any axioms beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.
