# lean-milliken

Lean 4 formalization of the Halpern--Läuchli and Milliken tree theorems,
following Chapters 3 and 6 of Stevo Todorčević's *Introduction to Ramsey Spaces*.

The intended proof architecture is:

1. rooted finitely-branching trees and strong subtrees;
2. the strong-subtree Halpern--Läuchli theorem;
3. Todorčević's Ramsey space \((\mathcal S_\infty(U),\subseteq,r)\);
4. verification of A.1--A.4, with A.4 supplied by Halpern--Läuchli;
5. Milliken's theorem as an application of the Abstract Ellentuck theorem from
   `janhubicka/lean-ramsey-space-todorcevic`.

The repository is intentionally organized so that the tree/level-product
combinatorics can be reused independently of the Ramsey-space wrapper.
