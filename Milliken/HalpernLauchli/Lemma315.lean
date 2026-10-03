import Milliken.HalpernLauchli.Sections
import Milliken.HalpernLauchli.Asymmetric

/-!
# The logical shell of Lemma 3.15

For fixed P and k, call y bad at scale n if some n-dense level matrix M
has P_y ∩ M failing k-density.  If the conclusion of Lemma 3.15 fails,
then at every n the good part of X cannot itself be somewhere cone-dense.
This is the first reduction in Todorčević's proof; the later minimal-D
argument uses only the resulting bad sets.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A last-coordinate node is bad at scale n when some level n-dense
matrix has a non-k-dense intersection with its section. -/
def BadSectionAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (y : Node ι) : Prop :=
  ∃ M : Matrix ι d,
    M.LevelDenseAt n ∧
      ¬ ProductDenseAt (lastSection P y ∩ M.carrier) k

/-- A level matrix avoiding one section while remaining dense above a fixed
front-coordinate vector.  This is the witness appearing in (1)--(3) of the
proof of Lemma 3.15. -/
def SectionAvoidAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (y : Node ι) (base : Fin d → Node ι) (n : ℕ) : Prop :=
  ∃ M : Matrix ι d, ∃ l : ℕ,
    M.OnLevel l ∧
    M.DenseAbove base n ∧
    M.carrier ⊆ (lastSection P y)ᶜ

theorem sectionAvoidAt_of_le [Nonempty ι] {d : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {y : Node ι} {base : Fin d → Node ι}
    {m n : ℕ} (hmn : m ≤ n)
    (h : SectionAvoidAt P y base n) :
    SectionAvoidAt P y base m := by
  rcases h with ⟨M, l, hlevel, hdense, hsub⟩
  exact ⟨M, l, hlevel, M.denseAbove_of_le hmn hdense, hsub⟩

/-- Failure of k-density inside an n-dense level matrix exposes a single
level-k vector above which a level matrix misses the entire section. -/
theorem badSectionAt_has_avoidWitness [Nonempty ι] {d k n : ℕ}
    {P : Set (Fin (d + 1) → Node ι)} {y : Node ι}
    (hkn : k < n)
    (hbad : BadSectionAt P k n y) :
    ∃ x : LevelVector ι d k,
      SectionAvoidAt P y x.1 n := by
  rcases hbad with ⟨M, ⟨l, hlevel, hdense⟩, hfail⟩
  rcases exists_bad_levelVector (lastSection P y) M hfail with
    ⟨x, hxsub⟩
  have hbase : ∀ i, (x.1 i).length < n := by
    intro i
    rw [x.2 i]
    exact hkn
  let N : Matrix ι d := M.restrictAbove x.1
  refine ⟨x, N, l, ?_, ?_, ?_⟩
  · dsimp [N]
    exact M.restrictAbove_onLevel hlevel
  · dsimp [N]
    exact M.restrictAbove_denseAbove x.1 hdense hbase
  · dsimp [N]
    exact hxsub

/-- Badness itself is downward monotone in the density level. -/
theorem badSectionAt_of_le [Nonempty ι] {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)} {y : Node ι}
    {m n : ℕ} (hmn : m ≤ n)
    (hbad : BadSectionAt P k n y) :
    BadSectionAt P k m y := by
  rcases hbad with ⟨M, hM, hfail⟩
  exact ⟨M, M.levelDenseAt_of_le hmn hM, hfail⟩

/-- A finite family of level-k vectors which covers all sufficiently deep
bad-section witnesses on a somewhere-dense set.  The explicit density root
is retained because the minimal-D argument repeatedly passes to deeper
cones. -/
structure AvoidCover [Finite ι] [Nonempty ι] {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) (X : Set (Node ι)) where
  D : Finset (LevelVector ι d k)
  n0 : ℕ
  Y : Set (Node ι)
  root : Node ι
  Y_subset : Y ⊆ X
  Y_dense : ConeDense Y root
  cover :
    ∀ n, n0 ≤ n →
      ∀ y ∈ Y, BadSectionAt P k n y →
        ∃ x ∈ D, SectionAvoidAt P y x.1 n

theorem exists_avoidCover [Finite ι] [Nonempty ι] {d k : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    {X : Set (Node ι)} (hX : SomewhereConeDense X) :
    Nonempty (AvoidCover P k X) := by
  classical
  letI : Finite (LevelVector ι d k) := finite_levelVector d k
  letI : Fintype (LevelVector ι d k) := Fintype.ofFinite _
  rcases hX with ⟨root, hroot⟩
  refine ⟨{
    D := Finset.univ
    n0 := k + 1
    Y := X
    root := root
    Y_subset := fun _ h => h
    Y_dense := hroot
    cover := ?_
  }⟩
  intro n hn y hy hbad
  have hkn : k < n := by omega
  rcases badSectionAt_has_avoidWitness hkn hbad with ⟨x, hx⟩
  exact ⟨x, Finset.mem_univ _, hx⟩

/-- Choose a cover with a minimum number of level-k vectors. -/
theorem exists_minimalAvoidCover [Finite ι] [Nonempty ι] {d k : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    {X : Set (Node ι)} (hX : SomewhereConeDense X) :
    ∃ C : AvoidCover P k X,
      ∀ C' : AvoidCover P k X, C.D.card ≤ C'.D.card := by
  classical
  let C0 : AvoidCover P k X :=
    Classical.choice (exists_avoidCover P hX)
  let p : ℕ → Prop :=
    fun m => ∃ C : AvoidCover P k X, C.D.card = m
  have hp : ∃ m, p m :=
    ⟨C0.D.card, C0, rfl⟩
  let m : ℕ := Nat.find hp
  rcases Nat.find_spec hp with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro C'
  rw [hC]
  by_contra hle
  have hlt : C'.D.card < m := Nat.lt_of_not_ge hle
  exact (Nat.find_min hp hlt) ⟨C', rfl⟩

/-- The set \(Y_n(\vec x)\) from the proof of Lemma 3.15:
bad nodes of \(Y\) for which the fixed vector \(\vec x\) itself supplies
an avoiding matrix. -/
def avoidWitnessSet {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (Y : Set (Node ι))
    (x : LevelVector ι d k) : Set (Node ι) :=
  {y | y ∈ Y ∧ BadSectionAt P k n y ∧
    SectionAvoidAt P y x.1 n}

/-- The minimal-\(D\) argument in the proof of Lemma 3.15.

Once an avoiding cover uses as few level-\(k\) vectors as possible, every
vector which remains in \(D\) must occur densely often: otherwise pass to a
deeper cone disjoint from its witness set and remove that vector from \(D\).
The new cover starts at \(\max(n_0,n)\), so downward monotonicity of both
badness and avoidance rules out the removed vector at every later scale. -/
theorem avoidWitnessSet_coneDense_of_minimal
    [Finite ι] [Nonempty ι] {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {X : Set (Node ι)}
    (C : AvoidCover P k X)
    (hmin : ∀ C' : AvoidCover P k X, C.D.card ≤ C'.D.card)
    {x : LevelVector ι d k} (hxD : x ∈ C.D)
    (n : ℕ) :
    ConeDense (avoidWitnessSet P k n C.Y x) C.root := by
  classical
  let N := max C.n0 n
  have hmain :
      ConeDense (avoidWitnessSet P k N C.Y x) C.root := by
    by_contra hnot
    rw [not_coneDense_iff] at hnot
    rcases hnot with ⟨u, hru, hu⟩
    let Y' : Set (Node ι) := restrictCone C.Y u
    have hY'dense : ConeDense Y' u := by
      dsimp [Y']
      exact coneDense_restrictCone C.Y_dense hru
    let C' : AvoidCover P k X := {
      D := C.D.erase x
      n0 := N
      Y := Y'
      root := u
      Y_subset := by
        intro y hy
        exact C.Y_subset hy.1
      Y_dense := hY'dense
      cover := by
        intro m hm y hyY' hbad
        have hmC : C.n0 ≤ m := by
          exact (Nat.le_max_left C.n0 n).trans hm
        rcases C.cover m hmC y hyY'.1 hbad with
          ⟨z, hzD, hzAvoid⟩
        have hzx : z ≠ x := by
          intro hzx
          subst z
          have hNm : N ≤ m := hm
          have hnN : n ≤ N := Nat.le_max_right _ _
          have hnM : n ≤ m := hnN.trans hNm
          have hbadn : BadSectionAt P k n y :=
            badSectionAt_of_le hnM hbad
          have havoidn : SectionAvoidAt P y x.1 n :=
            sectionAvoidAt_of_le hnM hzAvoid
          have hyW :
              y ∈ avoidWitnessSet P k N C.Y x := by
            refine ⟨hyY'.1, ?_, ?_⟩
            · exact badSectionAt_of_le hNm hbad
            · exact sectionAvoidAt_of_le hNm hzAvoid
          exact hu y hyW hyY'.2
        exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hzD⟩, hzAvoid⟩
    have hcard :
        C'.D.card < C.D.card := by
      dsimp [C']
      simpa [Finset.card_erase_of_mem hxD]
    exact (not_lt_of_ge (hmin C')) hcard
  by_cases hn : n ≤ N
  · intro u hru
    rcases hmain hru with ⟨y, hyW, huy⟩
    refine ⟨y, ?_, huy⟩
    rcases hyW with ⟨hyY, hbadN, havoidN⟩
    exact ⟨hyY, badSectionAt_of_le hn hbadN,
      sectionAvoidAt_of_le hn havoidN⟩
  · exact (hn (Nat.le_max_right _ _)).elim

/-- In the failure case of Lemma 3.15 a minimal avoiding cover cannot have
empty \(D\). -/
theorem minimalAvoidCover_D_nonempty
    [Finite ι] [Nonempty ι] {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {X : Set (Node ι)}
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set (Node ι),
        Y ⊆ X ∧ SomewhereConeDense Y ∧ SectionsGoodAt P k n Y)
    (C : AvoidCover P k X) :
    C.D.Nonempty := by
  classical
  have hsome : SomewhereConeDense C.Y :=
    ⟨C.root, C.Y_dense⟩
  rcases exists_bad_in_somewhere_of_no_uniform
      P k X hfail C.n0 C.Y C.Y_subset hsome with
    ⟨y, hyY, hbad⟩
  rcases C.cover C.n0 le_rfl y hyY hbad with
    ⟨x, hxD, hxAvoid⟩
  exact ⟨x, hxD⟩

/-- Bad nodes restricted to a prescribed set X. -/
def badSectionSet {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (X : Set (Node ι)) : Set (Node ι) :=
  X ∩ {y | BadSectionAt P k n y}

/-- The desired uniform conclusion at fixed n on Y. -/
def SectionsGoodAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (Y : Set (Node ι)) : Prop :=
  ∀ y ∈ Y, ∀ M : Matrix ι d,
    M.LevelDenseAt n →
      ProductDenseAt (lastSection P y ∩ M.carrier) k

theorem sectionsGoodAt_iff_no_bad {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (Y : Set (Node ι)) :
    SectionsGoodAt P k n Y ↔
      ∀ y ∈ Y, ¬ BadSectionAt P k n y := by
  constructor
  · intro h y hy hbad
    rcases hbad with ⟨M, hM, hfail⟩
    exact hfail (h y hy M hM)
  · intro h y hy M hM
    by_contra hfail
    exact h y hy ⟨M, hM, hfail⟩

/-- If no n,Y satisfy the conclusion of Lemma 3.15, then for each n the
good part of X is not somewhere cone-dense. -/
theorem good_complement_not_somewhere_of_no_uniform {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) (X : Set (Node ι))
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set (Node ι),
        Y ⊆ X ∧ SomewhereConeDense Y ∧ SectionsGoodAt P k n Y) :
    ∀ n : ℕ,
      ¬ SomewhereConeDense
        (X \ badSectionSet P k n X) := by
  intro n hsome
  let Y : Set (Node ι) := X \ badSectionSet P k n X
  have hYX : Y ⊆ X := by
    intro y hy
    exact hy.1
  have hgood : SectionsGoodAt P k n Y := by
    rw [sectionsGoodAt_iff_no_bad]
    intro y hyY hbad
    exact hyY.2 ⟨hyY.1, hbad⟩
  exact hfail ⟨n, Y, hYX, hsome, hgood⟩

/-- Equivalently, under failure of the uniform conclusion every somewhere
dense subset of X contains a bad node at every scale. -/
theorem exists_bad_in_somewhere_of_no_uniform {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) (X : Set (Node ι))
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set (Node ι),
        Y ⊆ X ∧ SomewhereConeDense Y ∧ SectionsGoodAt P k n Y)
    (n : ℕ) {Y : Set (Node ι)}
    (hYX : Y ⊆ X) (hY : SomewhereConeDense Y) :
    ∃ y ∈ Y, BadSectionAt P k n y := by
  by_contra hnone
  push Not at hnone
  have hsub :
      Y ⊆ X \ badSectionSet P k n X := by
    intro y hy
    refine ⟨hYX hy, ?_⟩
    intro hybad
    exact hnone y hy hybad.2
  have hsome :
      SomewhereConeDense (X \ badSectionSet P k n X) :=
    somewhereConeDense_mono hsub hY
  exact good_complement_not_somewhere_of_no_uniform P k X hfail n hsome

end HalpernLauchli
end Milliken
