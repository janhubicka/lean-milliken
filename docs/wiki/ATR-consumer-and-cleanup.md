# The only downstream consumer: three-uniform diaries

**Maintenance policy (14 October 2026):** `janhubicka/lean-3-uniform-diaries` is the **only** supported client of `janhubicka/lean-milliken`. Obsolete fixed-alphabet compatibility APIs can be removed even if this means changing ATR imports or theorem names. API simplicity and theorem fidelity matter more than preserving unused historical wrappers.

## Supported public path

For the unrestricted strong-tree theorems, use:

```lean
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.millikenFixedStemMonochromatic_general
```

A scalar strong tree of variable local degree is genuinely supported. Avoid recreating a large constant alphabet to encode the diary's locally variable branching, or importing removed homogeneous `Milliken.MillikenTheorem`, `Milliken.Applications` and the legacy `HalesJewettBridge`.

## Migration branches and test order

1. [Milliken PR #144](https://github.com/janhubicka/lean-milliken/pull/144) removes 81 historical proof modules (~0.5 MB) and retains the generic finite-colour result as `Milliken.FiniteColourRamseySpace`. Its source-index enumerator was moved to `GeneralTree.IncreasingEnumeration`.
2. The initial candidate `1f42273ee3d492f395087bb4c4b90cc47edfdd65` compiled Lean, but the graph linter found a redundant `GeneralTree.Vector` umbrella import. Removing it produced `d2df3a15511c92f2bb4640a966c05aaae46147ab`; [complete upstream CI passed](https://github.com/janhubicka/lean-milliken/actions/runs/38587255692).
3. [ATR PR #395](https://github.com/janhubicka/lean-3-uniform-diaries/pull/395) drops the unused homogeneous wrappers `MillikenDependency`, `MillikenAnchoredFiniteColour` and `MillikenThreeCoordinateHL`, and retains an ATR-local **generic** finite-colouring adapter in `ThreeUniformDiaries/MillikenFiniteColour.lean`.
4. The ATR `lakefile.toml` should pin **the green upstream SHA** `d2df3a15511c92f2bb4640a966c05aaae46147ab`. Do not merge ATR until its newest-run GitHub Actions has passed on that pin.
5. Merge Milliken #144 before ATR #395, and check the merge commits' CIs if merges cause any additional changes. After a future upstream commit, update the pinned ATR hash deliberately instead of relying on a branch name.

## Real dependency versus obsolete aliases

In the baseline ATR:
- `ThreeUniformDiaries/MillikenDependency.lean` imported `Milliken.MillikenTheorem` only to re-export an unused homogeneous result.
- `ThreeUniformDiaries/MillikenAnchoredFiniteColour.lean` wrapped a homogeneous anchored finite-colour theorem.
- `ThreeUniformDiaries/MillikenThreeCoordinateHL.lean` wrapped a homogeneous level-product HL lemma; it was **not** a finite-vector subtree theorem.
- `ThreeUniformDiaries/MillikenFiniteColour.lean` mixed generic Ramsey-space finite-colouring facts with the old homogeneous application. The supported version retains just the generic adapter, importing `Milliken.FiniteColourRamseySpace`.
- `ThreeUniformDiaries/ATRGeneralMilliken.lean` and `ATRScalarMillikenTransfer.lean` use `GeneralTree` and checked Abstract Ellentuck to apply a protected finite-colouring theorem. They still contain historically written conditional API variants; these can be shortened further once direct unconditional callers are established.

The restored compile should be audited for *actual* direct transitive dependencies, not simply for no appearance of an old name in an unused comment.

## An essential mathematical distinction

The ATR proof involves three coordinate type trees `T₀,T₁,T₂`, with synchronized levels and in some cases **unbounded finite** branching. Three logically different assertions appear:

1. **Heterogeneous product Halpern–Läuchli:** colours tuples consisting of one node from each of several level sets. The library proves this unconditionally.
2. **Scalar Milliken:** colours finite **scalar** strong subtrees of one ambient tree. The general library proves the infinite-realiser approximation version, with strong finite stems.
3. **Synchronized vector Milliken:** colours tuples of **whole finite strong subtrees** in the individual coordinates, all using one common level map. The declaration `HasVectorMillikenFiniteColourProperty` currently states this as a **target**, not an established theorem.

One possible verified route from (2) to the diary is to glue the three coordinate trees under one new root and prove that scalar refinements/approximations *exactly* encode the required vector finite pictures. This is not accomplished by writing down a `TypedVectorSubset` alone. The ATR code has an explicit `ATRScalarRealization` structure with `decodeApprox`, `decodeInfinite` and a substantive **realize** field; an application theorem assuming a value of this structure is valid, but one must construct that value for the concrete diary model to discharge the condition.

The cleanup preserves the geometric and HL modules needed for that future construction. It eliminates only unsupported fixed-alphabet historical implementation.

## Consumer acceptance checklist

- [x] Identify actual old homogeneous imports and remove unused wrappers in the migration PR.
- [x] Prove updated general-tree upstream compiles with kernel/source/import audits.
- [ ] Complete ATR CI at the **exact** trimmed upstream pin on the latest ATR head.
- [ ] Confirm the diary's final named Ramsey endpoint does not still require an unspecified `ATRScalarRealization` or an unproved vector-theorem parameter unless correctly labelled conditional.
- [ ] Clean stale comments referring to heterogeneous HL as unproved (it now has `boundaryProductHL_unconditional`).
- [ ] Remove transitional conditional theorem aliases only when no longer part of either the approved proof structure or ATR consumer imports.
- [ ] Re-run both workflows after merger and update this page with final merge commit hashes.

See [Published statements](Published-statements.md) and [Audit tracker](../audits/AUDIT_TRACKER_2026.md).
