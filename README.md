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
