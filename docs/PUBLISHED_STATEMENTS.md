# Published Milliken statements and Lean API

The relevant source is Stevo Todorčević, *Introduction to Ramsey Spaces*
(Princeton University Press, 2010), §6.1, pp. 135–137, and K. R. Milliken,
*A Ramsey theorem for trees*, *J. Combin. Theory Ser. A* **26** (1979),
215–237, DOI: [10.1016/0097-3165(79)90101-8](https://doi.org/10.1016/0097-3165(79)90101-8).

## Mathematical crosswalk

| Published item | Hypotheses/conclusion | Checked Lean implementations | Further applications |
| --- | --- | --- | --- |
| Todorčević, (str1)–(str2), p. 135 | For each level of the subtree every **ambient immediate successor** has exactly one extension at the next selected level; subtree may start below the ambient root. | `StrongEmbedding.branch`, `branch_reflect`, `level_witness`; the root image is unconstrained. | A composition/transport theorem linking the new `GeneralTree.StrongSubtree` to the abstract Ramsey space. |
| §6.1, (6.1)–(6.2) | `r_n(T)` is the first `n` **source** levels, including the empty approximation. | `StrongTreeSpace.Approx`, `approx`, `approx_surjective`. | Express restriction for variable branching without a fixed source alphabet. |
| §6.1, (6.3) | Finitisation using both carrier inclusion and last-level inclusion. | `bookLeFin` records (6.3), while `leFin` is a proof-oriented carrier relation; see `FiniteApprox.lean`. | **Counterexample recorded:** `r_1(id) ≤fin r_2(id)` for `leFin`, but not for `bookLeFin`. Prove equivalence of induced *depth/neighbourhood* notions, not of the relations. |
| Todorčević, Lemma 6.1 | Fixed finite stem, homogeneous one-step extensions under a refinement. | `pigeonhole_of_strongSubtreeHL_and_refine` and `Chapter6.milliken_onBasicNeighborhoods`. | General-tree and synchronized vector versions. |
| Todorčević, Theorem 6.2 | Full topological Ramsey space for **every** pruned, finitely branching rooted tree of height omega. | `Applications.todorcevic62_homogeneous` (homogeneous), **`GeneralTree.generalMilliken_unconditional`** (arbitrary locally finite degrees, proved in PR #138). | Separate synchronized-vector finite-subtree theorem for three-uniform applications. |
| Todorčević, Corollary 6.5; Milliken (1979) | A finite coloring of all strongly embedded finite height-`k` subtrees is monochromatic within one infinite strong subtree. | `Applications.milliken1979_homogeneous` and **`GeneralTree.milliken1979_general_unconditional`**, using `exists_refinement_realising_general`. | Published `k > 0`; Lean allows `k = 0`. Independent vector strengthening remains open. |
| Todorčević, Corollary 6.6 | Finite-height witness `m` for given `k,l,n>0`. | Not currently exported. | Formal compactness derivation from Corollary 6.5, with careful level indexing. |
| Manuscript `Str_{ell,k}(T)` | Fix `ell` source levels and color height-`k` **finite** strong subtrees below an infinite refinement, for `0 ≤ ell ≤ k`. | `Applications.millikenFixedStemFiniteColouring ell k A colour` for homogeneous trees, with quantification over infinite realizers. | The exact finite `Str_{ell,k}` predicate is exported by `Applications.millikenFixedStem1979_homogeneous` using `truncateApprox`; identify its transport and transport to synchronized variable-branching *vector* trees. |

## Public imports

`import Milliken.Applications` exports the checked application theorems
without importing the unrelated Chapter 3 reconstruction via `Milliken.lean`.
The internal module `Milliken.MillikenTheorem` exports the topological
Ramsey-space result and its conditional Halpern–Läuchli variants.

The library's `StrongTreeSpace.le` means canonical strong factorization
(`X = B ∘ Z`). `StrongTreeSpace.le_iff_range_subset` proves it is
equivalent to range inclusion in the homogeneous nonempty-alphabet case.

## Important distinction for 3-uniform-diaries

A common-level strong-subtree Halpern–Läuchli theorem for three coordinates
only homogenizes *level vectors*; it does not by itself colour all
finite **vector strong subtrees**. In particular, running the
one-tree theorem in the product alphabet does not directly yield a
coordinatewise independent vector strong-subtree theorem.

Moreover, the manuscript's `T₀` and `T₁` have finite yet unbounded
level-dependent branching, whereas `StrongEmbedding ι` uses one fixed
finite alphabet. Two distinct extensions remain:

1. **Completed:** The arbitrary-degree `GeneralTree.StrongSubtree`
   theorem is connected to the finite-boundary/Abstract Ellentuck
   development by `HeterogeneousUniversalMilliken`; no homogeneous
   alphabet or uniform bound on degree is assumed.
2. **Still needed for some applications:** A synchronized-vector theorem
   with one common selected level sequence, a fixed-prefix
   `Str_{ell,k}` interface, per-coordinate strongness and compatibility
   with the diary manuscript's canonical maps.

Thus the unrestricted **single-tree** theorem is proved; it is not yet
the full vector theorem required for every type-respecting application.

## Sources

- [Todorčević, Chapter 6](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf#page=144) (PDF, printed pp. 135–137).
- [Milliken, 1979, DOI](https://doi.org/10.1016/0097-3165(79)90101-8).


### Local finiteness versus globally fixed branching

The induction in `HalpernLauchli/FinalInduction.lean` processes the
finite immediate-successor set by iteration. The universal heterogeneous HDHL induction now formalises the same
reasoning for genuinely different finite successor sets, including
node-dependent unbounded finite degrees. The homogeneous
`Node ι = List ι` development is retained as an independent theorem.

The new `GeneralTree` definitions separate these two levels of
generality. `StrongSubtree.successor_unique` is quantified over
`x ⋖ y` in the arbitrary ambient tree `U`, and the finite-approximation
property is stated for every `U : AmbientTree` as a *Prop*, not
as an unproved theorem. `predecessor_exists` rules out ghost nodes
which otherwise defeat equivalence with published regular subtrees.


### Existing increasing-branching development on PR #3

The separate [`remark38-level-change` branch](https://github.com/janhubicka/lean-milliken/pull/3)
already contains:

- `SelectedLevelTree.Selection` and `Child`: the selected-level
  compression of `List ι`, with finitely many children whose number
  can grow with the chosen level gaps.
- `childFinite`, `child_nonempty`, `truncate`, and
  `exists_child_below`.
- `SelectedLevelInduction.hdhl_one` and
  `hdhl_of_all_selected`, connecting the *assumed* selected-level
  HDHL property back to the usual one.

Thus the variable-degree *geometry* is indeed already in the repository,
and merged into `main`. PR #3 by itself did not prove all-dimensional
selected-level HDHL or node-dependent branching; these were later
completed by PRs #123–#138. The first CI
failure was localized to `SelectedLevelCone` and received the
namespace-notation repair in commit
[`e37b0fd`](https://github.com/janhubicka/lean-milliken/commit/e37b0fdd64cdf310835377fefb496919a6e6efd0).
The broader source-level compression, wedge construction and
unconditional arbitrary-tree induction are now checked, so this old
development note is retained only for historical context.
