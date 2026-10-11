# Published Milliken statements and Lean API

The relevant source is Stevo Todorčević, *Introduction to Ramsey Spaces*
(Princeton University Press, 2010), §6.1, pp. 135–137, and K. R. Milliken,
*A Ramsey theorem for trees*, *J. Combin. Theory Ser. A* **26** (1979),
215–237, DOI: [10.1016/0097-3165(79)90101-8](https://doi.org/10.1016/0097-3165(79)90101-8).

## Mathematical crosswalk

| Published item | Hypotheses/conclusion | Checked homogeneous implementation | Remaining obligations |
| --- | --- | --- | --- |
| Todorčević, (str1)–(str2), p. 135 | For each level of the subtree every **ambient immediate successor** has exactly one extension at the next selected level; subtree may start below the ambient root. | `StrongEmbedding.branch`, `branch_reflect`, `level_witness`; the root image is unconstrained. | A composition/transport theorem linking the new `GeneralTree.StrongSubtree` to the abstract Ramsey space. |
| §6.1, (6.1)–(6.2) | `r_n(T)` is the first `n` **source** levels, including the empty approximation. | `StrongTreeSpace.Approx`, `approx`, `approx_surjective`. | Express restriction for variable branching without a fixed source alphabet. |
| §6.1, (6.3) | Finitisation using both carrier inclusion and last-level inclusion. | `bookLeFin` records (6.3), while `leFin` is a proof-oriented carrier relation; see `FiniteApprox.lean`. | Audit and prove equivalence of *relevant* depth/neighbourhood notions; do not claim definitional equality. |
| Todorčević, Lemma 6.1 | Fixed finite stem, homogeneous one-step extensions under a refinement. | `pigeonhole_of_strongSubtreeHL_and_refine` and `Chapter6.milliken_onBasicNeighborhoods`. | General-tree and synchronized vector versions. |
| Todorčević, Theorem 6.2 | Full topological Ramsey space for **every** pruned, finitely branching rooted tree of height omega. | `Applications.todorcevic62_homogeneous`, specializing to full finite-alphabet trees. | **NOT YET PROVED:** `GeneralTree.HasMillikenFiniteColourProperty U`, including unbounded finite degrees. `GeneralTree.StrongSubtree` now expresses (str1)–(str2) for arbitrary `AmbientTree`. |
| Todorčević, Corollary 6.5; Milliken (1979) | A finite coloring of all strongly embedded finite height-`k` subtrees is monochromatic within one infinite strong subtree. | `Applications.milliken1979_homogeneous`. The carrier-to-refinement lemma `exists_refinement_realising` is essential here. | Arbitrary ambient tree; note published `k > 0`, while the Lean result also permits `k = 0`. |
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

1. Connect the arbitrary-degree `GeneralTree.StrongSubtree` statement to the
   existing finite-boundary induction. In `FinalInduction.lean` the finitely
   many children are processed individually; this is the correct local
   argument, but the checked `StrongSubtreeHL ι` still uses a fixed `ι`.
2. A vector theorem with one common selected level sequence, with a
   fixed-prefix `Str_{ell,k}` interface, preserving per-coordinate
   strongness and compatibility with the manuscript's canonical maps.

Until both exist, the auxiliary type-respecting theorem is **not** fully
discharged by the published single-tree API.

## Sources

- [Todorčević, Chapter 6](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf#page=144) (PDF, printed pp. 135–137).
- [Milliken, 1979, DOI](https://doi.org/10.1016/0097-3165(79)90101-8).
