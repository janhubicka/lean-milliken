# Referee audit protocol and current findings

This is a *review dossier*, not a claim that independent external
referees have already signed off. Any unchecked items need genuinely
independent review. Distinct referee briefs are intentionally
non-overlapping to prevent the same assumption passing unnoticed.

## Referee A — Todorčević source fidelity (independent review requested)

Read *Introduction to Ramsey Spaces*, Chapter 6, especially (str1)–(str2),
(6.1)–(6.3), Lemma 6.1 and Theorem 6.2, independently of the Lean code.
Check the following:

- [ ] The ambient tree is arbitrary, rooted, finitely branching, height
      omega, without terminal nodes; identify every place the repository
      silently specializes to homogeneous `List ι`.
- [ ] Rooted does **not** require the strong subtree to share the ambient
      root: an arbitrary initial cone is allowed.
- [ ] Every immediate **ambient** successor is represented exactly once at
      the next chosen subtree level; neither weak subtree nor merely
      meet-preserving embedding suffices.
- [ ] Levels are synchronized across all children within a single strong
      subtree; `r_n` fixes source levels.
- [ ] Verify the carrier+maximal-level finitization (6.3) against the
      proof-oriented `leFin`; establish the precise comparison needed.
- [ ] Verify whether Chapter 6's topological Ramsey conclusion is preserved
      by the application aliases without a hidden Borel/analytic restriction.

**Audit finding:** The public 6.2 alias proves only the homogeneous case.
`AmbientTree` currently has no theorem parametrized by `U`. This is
a major **scope limitation**, explicitly documented, not silently fixed.

**Audit finding:** The library has two finitizations: `bookLeFin`
follows (6.3) and `leFin` uses height+carrier inclusion. Their relation
needs a focused mathematical review, even if the internal A.1–A.4 proof
is Lean-checked with `leFin`.

Status: **external signoff outstanding**.

## Referee B — original Milliken (1979) and finite colors

Independently reconstruct the statement from the original
*J. Combin. Theory A* 26 (1979), pp. 215–237 (also the published abstract).
Audit `Applications.milliken1979_homogeneous`.

- [ ] `k>0` is the published parameter, while allowing `k=0` is harmless.
- [ ] Check that `StrongTreeSpace.Approx` represents all finite strong
      subtrees, not merely a privileged list of restrictions of `B`.
- [ ] Check finite-carrier inclusion `approxCarrier a ⊆ range B`
      corresponds exactly to a finite strong subtree of `B`.
- [ ] Critically review `exists_refinement_realising` for the empty
      approximation, non-root-preserving subtrees, and skipped levels.
- [ ] Check the extension construction handles finite stems with a root
      below the ambient root and respects *every* labelled branch.
- [ ] Compare `Corollary 6.6` to the finite-height witness needed in
      applications; this has not yet been formalized in the library.

**Audit finding:** The direct original-style theorem no longer colours
only refinements `X`: it quantifies over *every* finite approximation
whose carrier lies inside the chosen tree, using the existing stem-extension
theorem. This eliminates a common hidden quantifier mismatch.

**Audit finding:** Variable branching remains out of scope. A fixed
finite alphabet does not cover trees with unbounded finite degrees.

Status: **external signoff outstanding**.

## Referee C — application and Lean integrity

Review integration into `lean-3-uniform-diaries`, especially the
`T₀,T₁,T₂` synchronized type trees and auxiliary-type maps.

- [ ] Validate `ell≤k` and the precise `Str_{ell,k}` fixed-prefix
      quantification, including `ell=0` and `k=1`.
- [ ] Never infer a *finite-vector*-subtree theorem from the existing
      **level-product** Halpern–Läuchli endpoint without a proof.
- [ ] No bound on the branching of the manuscript's `T₀,T₁` is silently
      assumed. Each level can be finite while degrees are unbounded.
- [ ] Validate composition, pullback, and strong completion in the relative
      target, including canonical-map compatibility.
- [ ] Check application endpoints with `#print axioms` recursively,
      reject `sorryAx`/new axioms, and inspect GitHub Actions results.
- [ ] Use a smoke-test module in a downstream Lake project with a pinned
      revision of `lean-milliken`, not only in-repository checking.

**Audit finding:** The synchronized three-coordinate Halpern–Läuchli
endpoint has common levels, but this is not a proof of anchored
vector Milliken for finite strong-subtree shapes.

Status: **external signoff outstanding**.

## Signoff protocol

Each independent referee should append their name/review link,
the tested commit SHA, all critical counterexamples, and a clear
PASS / PASS WITH QUALIFICATIONS / FAIL verdict **only after examining
the sources and Lean declarations independently**. This file currently
records initial audit findings and the work needed for actual signoff.


## Internal adversarial check: absent predecessors (2026-10-11)

A first pass over the abstract arbitrary-degree carrier representation
found a real trap in a *proposed definition*, before any proof was exported.
Simply requiring a common selected-level sequence, a least root, and
(str2)'s unique next-level extension would still permit **ghost nodes**
on later selected levels which descend from the root but not from a
node on the immediately preceding selected level.

Example: in the full binary tree, use ambient selected levels
0, 2, 3, ... . At ambient level 2 choose `00` and `10` as
representatives above the two children of the root. At level 3,
choose all their mandatory extensions and also `010`,
which has no predecessor in the selected level-2 nodes.
The one-way successor condition alone would allow this ghost branch
to continue forever even though it is not part of the intended
regular strong subtree.

**Resolution in this branch:** add
`GeneralTree.StrongSubtree.predecessor_exists`, requiring every
member of source level `n+1` to have an ancestor in source level `n`.
This is needed to encode the *regular rooted subtree* prerequisite
of Todorčević (str1)–(str2). The formal general-theorem proof remains
open. Referee A should independently verify the strengthened equivalence.
