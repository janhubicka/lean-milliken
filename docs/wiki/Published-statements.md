# Published statements: a source-to-Lean crosswalk

**Source:** Stevo Todorčević, *Introduction to Ramsey Spaces* (2010), §6.1–6.2 (printed pp. 135–141); [book PDF](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf). The preceding strong-tree Halpern–Läuchli machinery is in §3.1–3.2. Other source: K. R. Milliken, *A Ramsey theorem for trees*, *J. Combinatorial Theory A* **26** (1979), 215–237, [DOI](https://doi.org/10.1016/0097-3165(79)90101-8). **Source-access limitation:** only the 1979 publisher's abstract, not every page of the original proof, has been inspected.

The crosswalk is maintained against the current public `Milliken.GeneralTree` interfaces. Individual audit findings retain the tested commit identifiers so they remain reproducible when modules are reorganised.

## What “formalised” means here

- **Exact source-facing theorem:** Lean conclusion matches the main printed proposition at the level of strong-tree topological Ramsey spaces (up to standard mathematical equivalences), and its arguments contain no unproved HL hypotheses.
- **Directly formalised conditional reduction:** a Lean theorem proves the implication from a named hypothesis to the source conclusion; the premise must be discharged separately.
- **Realised-form theorem:** quantifies over `FiniteApprox U k`, whose `realised` witness proves that its carrier is a prefix of *some* infinite strong subtree. It is not yet an intrinsic `S_k(U)` interface without that witness.
- **Not exported:** even if the proof seems an elementary consequence of a proved theorem, there is no dedicated kernel-checked statement corresponding to this numbered item.

## §3.1–3.2: input to Milliken

| Published source | Mathematical content | Checked declaration(s) / limitations |
| --- | --- | --- |
| Theorem 3.2 (strong-subtree Halpern–Läuchli) | Monochromatic synchronized products of selected levels of finite families of strong trees | `GeneralTree.generalProductHL_unconditional` in `GeneralTree/UnconditionalHLAPI.lean`; arbitrary pruned locally finite ambient tree, not only fixed alphabets |
| Remark 3.8 / selected-level density reduction | Choose cofinal source indices excluding restricted somewhere-dense complementary matrices | `heterogeneousRemark38Levels`, `heterogeneous_no_restricted_compl_of_highlyDense` in `GeneralTree/HeterogeneousRemark38.lean` |
| Lemmas 3.15, 3.16 (HL density induction) | Negative somewhere-density argument and positive last-coordinate sections | `heterogeneousLemma315_tailNormalize`, `heterogeneousLemma316` in correspondingly named `GeneralTree/HeterogeneousLemma*Proof.lean` files; transported to possibly nonisomorphic locally finite coordinate trees |
| Full higher-dimensional density theorem | Every highly dense colour class contains an appropriately dense product matrix | `GeneralTree.universalHeterogeneousHDHL` and `heterogeneousHDHL_unconditional` in `GeneralTree/HeterogeneousUniversalMilliken.lean` |

**Nuance:** source §3 uses level products, not products of finite strong-subtree *objects*. These are different theorems. `GeneralTree.HasVectorMillikenFiniteColourProperty` in `GeneralTree/Vector.lean` is still only a definition.

## §6.1: strong-tree space

| Printed item | Source statement | Lean witness | Verdict |
| --- | --- | --- | --- |
| (str1)–(str2), p. 135 | Regular strong subtree; every immediate **ambient** successor of a selected-level node has a **unique** descendant on the next selected level | `GeneralTree.StrongSubtree`, `StrongSubtree.sourceLevel`, `AmbientTree.children` | **Matches operational strongness.** Formal representation adds `predecessor_exists` explicitly to ban later-level “ghosts”; intrinsic-to-formal equivalence still deserves a standalone theorem |
| (6.1) | `r_n(T)=T\restriction n` truncates to the first `n` selected **source levels** | `GeneralTree.r`, `StrongSubtree.initialPart` | **Checked** |
| (6.2) | Finite approximations to infinite strong trees | `SInfinity`, `SFinite`, `FiniteApprox`, `r` | **Checked for realised approximations.** Intrinsic finite strong subtrees not separately identified |
| (6.3) | `a ≤fin b` iff both empty or `a⊆b` and maximal levels `a(max)⊆b(max)` | `GeneralTree.bookLeFin`, `generalBookFinitization` | **Literal book order checked** via `LowerFinite`, `OrderRealization`, `PrefixFinitization` |
| A.1–A.3 | Separation/coherence, finite order, extension/amalgamation | `generalApproximationSystem`, `generalBookFinitization`, `generalAmalgamation_nonempty`, `generalAmalgamation_refine` | **Checked**, arbitrary locally finite ambient |
| (6.4)–(6.7) | Actual finite successor-boundary cones, tuple coding of one-step extensions, pullback of colours | `GeneralTree/BoundaryTupleHL.lean`, `BoundaryIndex.lean`, `BoundaryBijection.lean`, `BoundaryCones.lean` | **Checked in the canonical A.4 reduction** |
| (6.8) | Graft synchronized monochromatic successor-cone trees onto fixed stem | `StrongSubtree.boundaryGraftStrong`, `boundaryGraftStrong_approx`, `boundaryGraftStrong_sourceLevel_at` in `BoundaryGraftStrong.lean` | **Checked**, including zero-length stem |
| Lemma 6.1 | Canonical one-step pigeonhole for **arbitrary subset** `O ⊆ S_{n+1}(U)` in every basic set `[n,T]` | `canonicalPigeonhole_of_boundaryProductHL` (`BoundaryTupleHL.lean`) plus `boundaryProductHL_unconditional` (`UnconditionalHLAPI.lean`) | **Unconditional through separate proved HL endpoint** |
| A.4 | All published depths and finite stems, not merely canonical root stem | `generalPigeonhole_of_canonical` (`CanonicalPigeonhole.lean`); `generalPigeonhole_unconditional` | **Checked**, uses protected A.3 |
| Topological closedness | Approximation code image closed in product of discrete finite approximation spaces | `generalIsTychonoffClosed`, `generalIsMetricallyClosed` (`GeneralClosed.lean`) | **Checked** |
| Theorem 6.2 (Milliken) | For every pruned locally finitely branching rooted tree of height `ω`, infinite strong trees form a topological Ramsey space | `generalMilliken_unconditional` (`HeterogeneousUniversalMilliken.lean`) | **Unconditional and checked**. It has the literal basic-neighbourhood `IsTopologicalRamseySpaceTextbook` conclusion, via `RamseySpace.abstractEllentuck_textbook` |

The **old** homogeneous `StrongTreeSpace.leFin` was a different order (height and carrier inclusion); its `bookLeFin` was a separate published comparison interface. This distinction **does not undermine** the present arbitrary-tree result, which constructs A.2 using `GeneralTree.bookLeFin` itself. Do not confuse the old homogeneous documentation with the unrestricted proof.

## §6.1: numbered corollaries

| Item | Published conclusion | Lean status / next bridge |
| --- | --- | --- |
| Corollary 6.3 (Ellentuck) | The usual infinite-subset space on `ω` is Ramsey | The abstract Ellentuck dependency has its own example; **not a separate specialization from general-tree theorem exported here** |
| Corollary 6.4 | Any finite *Souslin-measurable* colouring of `S∞(U)` is homogeneous on `S∞(T)` for a strong `T` | **Lean-checked and merged #149:** `millikenFiniteBaireColouring` for finite *Baire-measurable* colouring; Souslin-to-Baire regularity bridge still outstanding |
| Corollary 6.5 | Colour all **intrinsic** finite strong trees of height `k>0`; get monochromatic `S_k(T)` | `milliken1979_general_unconditional` proves the realised approximation version; **intrinsic finite-extension equivalence is outstanding** |
| Corollary 6.6 | For `k,l,n>0`, a finite height bound `m` works for `l`-colourings of `S_k(U\restriction m)` | **Not exported**; requires finite-tree formulation and the book's compactness/diagonal argument (equations (6.9)–(6.11)) |
| Corollary 6.7 | For each family of finite strong trees, obtain an infinite `T` that avoids the family or meets it along every further infinite branch | **Lean-checked and merged #150:** `galvinAlternative_realized` for arbitrary families of realised finite approximations; intrinsic-completion bridge still outstanding |
| Corollary 6.8 | Colour a family of finite strong trees without strict initial-part comparisons; obtain monochromatic intersection after refinement | **Not exported**; iterate Corollary 6.7 |
| Corollary 6.9 (Galvin) | For a family of finite subsets of `ℕ`, find infinite `B` which avoids the family or meets it on every infinite subset by an initial segment | **Not exported in the Milliken library**; `U=(ω,<)` specialization |
| Corollary 6.10 (Nash–Williams) | Initial-segment-antichain family of nonempty finite subsets becomes monochromatic on an infinite subset | **Not exported in the Milliken library**; `U=(ω,<)` specialization |

The book's printed text of Corollary 6.9 contains an evident `B⊆ℱ` typo when `ℱ` is a family of finite sets; its stated intended conclusion and proof use an infinite subset of `ℕ`. Record such source typos rather than hard-coding them into Lean.

## §6.2: embedding-type applications (not just the strong-tree Ramsey core)

The published **Definition 6.11** defines an embedding-type relation `Em` on arbitrary subsets of a downward-closed tree via a bijection of their meet closures preserving ancestor relation, relative level comparisons, membership and branch labels. The **strong subtree envelope** `C_A(U)` comprises finite strong trees covering `A^∧`.

| Item | Source meaning | Lean status |
| --- | --- | --- |
| Definition 6.11, (6.12)–(6.15) | Meet closure, embedding type, finite-height strong envelope | General tree has order, greatest common ancestors and finite approximations, but **this named embedding-type/envelope construction is not yet supplied as an exported standalone application** |
| Lemma 6.12 | For `A Em B`, if their strong envelopes intersect then `A=B` | **Not exported**; vital uniqueness for colour transfer |
| Theorem 6.13 | For arbitrary `A⊆U`, finite Souslin-measurable colouring of `[A]_Em` becomes monochromatic after a strong refinement | **Not exported**; requires the envelope uniqueness and a colouring measurable-transfer theorem |
| Corollary 6.14 | Finite-`A` embedding-type colouring, no Souslin assumption needed | **Not exported**; an important reusable embedding-type corollary requiring an additional finite-envelope interpretation |
| Further §6.2 statements | Relaxed embedding types, degree-preserving trees, Devlin-type applications | **Out of current Milliken-core scope**. These must not be claimed automatically validated |

The phrase *all related statements* is therefore interpreted as **full coverage in this crosswalk**, with explicit non-formalised labels, not a fictitious claim that every later consequence in Chapter 6 has been Lean-checked.

### The rest of §6.2: Theorem 6.15 and Corollaries 6.16–6.18

The source's §6.2 continues beyond Corollary 6.14. These four
statements have been checked against the *printed* book, pp. 141–143:

| Printed item | Exact mathematical character | Status in lean-milliken |
| --- | --- | --- |
| **Theorem 6.15** | Finite **Souslin-measurable** colouring of the relaxed embedding class `[A]_{Eb}`, under a degree-dominance condition on `U`; obtain a **degree-preserving** subtree with a monochromatic class | **Not formalised.** The published argument uses Theorem 6.13 followed by a carefully chosen degree-preserving thinning. |
| **Corollary 6.16** | Finite Souslin-measurable colouring of *all infinite chains* of a pruned finitely branching `U`; obtain a degree-preserving subtree whose chains are monochromatic | **Not exported.** |
| **Corollary 6.17 (Stern)** | Finite Souslin-measurable colouring of infinite chains of the binary tree; obtain a **perfect** subtree whose chains are monochromatic | **Not exported.** |
| **Corollary 6.18 (Silver)** | Finite Souslin-measurable colouring of infinite subsets of `ℕ`; obtain an infinite homogeneous subset | **Not exported here** (this is a classical application, not an additional axiom needed for Milliken). |

In particular, a **degree-preserving** subtree in Theorem 6.15 is
not automatically the same as a **strong** subtree; the source uses
the weaker target on purpose. These are applications requiring further
embedding-type formalisation, not prerequisites of the already proved
Theorem 6.2.

**Source-location verification:** [Todorčević's book, Chapter 6, printed
pp. 135–143](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf);
the statements of 6.7–6.10 occur on printed p. 138, those of 6.11–6.14
on pp. 139–141, and 6.15–6.18 on pp. 142–143.

## Original 1979 theorem

Publisher's abstract: for a rooted infinite-height tree, with a **nonempty finite** immediate-successor set at each node, any finite colouring of height-`n` **strongly embedded finite subtrees**, `n>0`, is monochromatic inside some infinite strong subtree. Source: [journal entry](https://www.sciencedirect.com/science/article/pii/0097316579901018).

- **Matching assumptions:** `AmbientTree` requires nonempty finite child sets at every node and a `RootedTree` whose predecessors form finite chains. Thus no global degree bound or fixed branching alphabet.
- **Matching combinatorial proof:** `milliken1979_general_unconditional` supplies `S` and one colour for all `FiniteApprox U n` whose carrier lies in `S`. Its derivation is from topological Milliken using `exists_refinement_realising_general`.
- **Still required for exact published quantifier domain:** define *intrinsic* height-`n` finite strong tree with no realiser field, prove every one extends to infinite `StrongSubtree U` (and conversely), transport colours through this equivalence. The existing extension lemma only **relocates a realised finite prefix into another infinite tree**.
- The library also permits `n=0`, where its approximation is the empty set. This is a harmless extension, but not part of the published positive-`n` statement.
- Because the publisher's full 1979 paper has not been compared page by page, do not claim identity of every auxiliary lemma or proof-ordering from the original article.

## Fixed stems and synchronized-vector generalizations

`GeneralTree.millikenFixedStemFiniteColouring_general` and `millikenFixedStemMonochromatic_general` give verified **infinite-refinement** statements preserving the first `ell` source levels. No `ell ≤ k` premise is needed to state these infinite-approximation colourings. The intrinsic **finite-tree anchored** `Str_{ell,k}` formulation *does* need `ell ≤ k` and an exact finite-to-infinite restriction lemma.

`GeneralTree.HasVectorMillikenFiniteColourProperty` and `HasVectorFixedStemColourProperty` are declarations of *desired propositions*, **not proofs**. A synchronization of **levels** in heterogeneous product HL is not sufficient to identify separately chosen coordinatewise finite strong-subtree **shapes**. In particular applications, a *scalar root-gluing correspondence* may reduce a vector colouring to an ambient scalar-tree colouring, but the encoding and finite realisation equivalence must be established independently. Such application data are not assumptions of the Milliken library.

## Quick validation recipe

```lean
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

#check Milliken.GeneralTree.universalHeterogeneousHDHL
#check Milliken.GeneralTree.heterogeneousHDHL_unconditional
#check Milliken.GeneralTree.generalProductHL_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.generalPigeonhole_unconditional
#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.milliken1979_general_unconditional
#check Milliken.GeneralTree.millikenFixedStemMonochromatic_general
```

Check **full theorem types and axiom lists**, not merely whether these names resolve. Consult `scripts/CheckMilliken.lean`, `scripts/check-axiom-log.py`, `docs/audits/AUDIT_TRACKER_2026.md`.
