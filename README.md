# lean-milliken

Lean 4 formalization of Milliken's strong-tree theorem following
Todorčević's *Introduction to Ramsey Spaces*, Chapters 3 and 6.

## Verified Chapter 6 route

The requested proof of Milliken from the strong-subtree
Halpern--Läuchli theorem is formalized end to end.

The main theorem is:

```lean
Milliken.Chapter6.milliken_of_strongSubtreeHL
```

For a finite nonempty branching alphabet `ι`, it takes

```lean
HalpernLauchli.StrongSubtreeHL ι
```

as the Chapter 3 input and proves that the strong-subtree space is a
topological Ramsey space.  The final step invokes the Abstract Ellentuck
theorem from
`janhubicka/lean-ramsey-space-todorcevic`.

The checked Chapter 6 path contains:

1. strong embeddings and finite approximations (A.1);
2. the finite carrier/factorization order (A.2);
3. finite-stem extension and the depth-boundary splice (A.3);
4. Todorčević's Lemma 6.1 from strong-subtree Halpern--Läuchli, followed by
   the lift from the canonical stem to arbitrary depth (A.4);
5. metric closedness of the strong-tree space;
6. assembly through Abstract Ellentuck.

There are no `sorry`, `admit`, or additional axioms in this route.

## Chapter 3 / Halpern--Läuchli development

The repository also develops a self-contained formalization of the Chapter 3
proof rather than treating Halpern--Läuchli as a permanent axiom.

Currently checked:

- the density and level-matrix language;
- Lemma 3.5 and the asymmetric formulation;
- the stabilization/section machinery;
- the minimal-`D` argument in Lemma 3.15;
- an explicit tail normalization needed to make the printed equation (3)
  machine-valid;
- the nested matrix-refinement construction;
- the completed normalized Lemma 3.15;
- the increasing `(n_p,X_p)` tower used in Lemma 3.16.

The remaining Chapter 3 input is the finitary Halpern--Läuchli dichotomy
(Theorem 3.9) used in Lemma 3.16, followed by the final HDHL induction step.

## CI

The Lean toolchain and GitHub Actions setup follow
`janhubicka/lean-ramsey-space-todorcevic`.  The project is pinned to the
same Mathlib revision and CI runs `lake build`.
