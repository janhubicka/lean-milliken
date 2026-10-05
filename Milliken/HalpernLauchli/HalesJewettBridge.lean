import Milliken.BranchEmbedding
import Milliken.HalpernLauchli.Statement
import SuccessorTree.HalesJewett.AlphabetInduction
import SuccessorTree.HalesJewett.Composition

/-!
# Halpern--Läuchli from the verified infinite Hales--Jewett subspace theorem

A common-level tuple of `d` words over `ι` is one word over the product
alphabet `Fin d → ι`, read column by column.  The infinite-dimensional
Hales--Jewett theorem formalized in `lean-successors` gives a homogeneous
subspace over this product alphabet.

Projecting that subspace to each coordinate gives strong embeddings of
`ι^{<ω}`.  Their block lengths are identical, hence they have one common
level set, and Hales--Jewett homogeneity is exactly homogeneity of all level
products.  This yields the strong-subtree Halpern--Läuchli theorem needed by
Chapter 6 without any additional axiom.
-/

namespace Milliken
namespace HalpernLauchli

universe u v

open SuccessorTree
open SuccessorTree.HalesJewett

namespace HalesJewettBridge

/-- Total output length contributed by the next `n` blocks of a subspace,
starting with block `i`. -/
def blockSpan (W : Subspace α) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, n + 1 =>
      1 + (W.blocks i).tail.length + blockSpan W (i + 1) n

@[simp] theorem blockSpan_zero (W : Subspace α) (i : ℕ) :
    blockSpan W i 0 = 0 := rfl

@[simp] theorem blockSpan_succ (W : Subspace α) (i n : ℕ) :
    blockSpan W i (n + 1) =
      1 + (W.blocks i).tail.length +
        blockSpan W (i + 1) n := rfl

/-- Adding one source letter at the right adds precisely the next block. -/
theorem blockSpan_succ_right
    (W : Subspace α) (i n : ℕ) :
    blockSpan W i (n + 1) =
      blockSpan W i n +
        (1 + (W.blocks (i + n)).tail.length) := by
  induction n generalizing i with
  | zero =>
      simp [blockSpan]
  | succ n ih =>
      calc
        blockSpan W i ((n + 1) + 1) =
            1 + (W.blocks i).tail.length +
              blockSpan W (i + 1) (n + 1) := rfl
        _ =
            1 + (W.blocks i).tail.length +
              (blockSpan W (i + 1) n +
                (1 + (W.blocks (i + 1 + n)).tail.length)) := by
              rw [ih (i := i + 1)]
        _ =
            (1 + (W.blocks i).tail.length +
              blockSpan W (i + 1) n) +
                (1 + (W.blocks (i + (n + 1))).tail.length) := by
              have hidx : i + 1 + n = i + (n + 1) := by omega
              rw [hidx]
              omega
        _ =
            blockSpan W i (n + 1) +
              (1 + (W.blocks (i + (n + 1))).tail.length) := rfl

/-- Common target level of the subspace evaluation on source level `n`. -/
def levels (W : Subspace α) (n : ℕ) : ℕ :=
  W.head.length + blockSpan W 0 n

/-- Evaluation from a block offset has the expected block-span length. -/
theorem evalFrom_length
    (W : Subspace α) (i : ℕ) (s : List α) :
    (W.evalFrom i s).length = blockSpan W i s.length := by
  induction s generalizing i with
  | nil =>
      rfl
  | cons a s ih =>
      simp only [Subspace.evalFrom, List.length_append,
        List.length_cons, blockSpan_succ]
      rw [ih (i := i + 1)]
      simp [LeftVariableWord.eval, evalWord]

/-- Evaluation length depends only on source length. -/
theorem eval_length
    (W : Subspace α) (s : List α) :
    (W.eval s).length = levels W s.length := by
  simp [Subspace.eval, levels, evalFrom_length]

/-- Subspace levels are strictly increasing. -/
theorem levels_strictMono (W : Subspace α) :
    StrictMono (levels W) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [levels, levels, blockSpan_succ_right]
  omega

/-- Evaluation respects source concatenation, with the tail starting at the
next unused variable block. -/
theorem eval_append
    (W : Subspace α) (s t : List α) :
    W.eval (s ++ t) =
      W.eval s ++ W.evalFrom s.length t := by
  unfold Subspace.eval
  rw [Subspace.evalFrom_append]
  simp [List.append_assoc]

/-- Subspace evaluation preserves the labelled immediate branch relation. -/
theorem eval_branch
    (W : Subspace α) (s : List α) (a : α) :
    (child (W.eval s) a).IsPrefix
      (W.eval (child s a)) := by
  rw [show child s a = s ++ [a] by rfl, eval_append]
  refine ⟨evalWord a (W.blocks s.length).tail, ?_⟩
  simp [child, Subspace.evalFrom, LeftVariableWord.eval,
    List.append_assoc]

/-- Every Hales--Jewett subspace is canonically a strong tree embedding. -/
noncomputable def strongEmbedding (W : Subspace α) :
    StrongEmbedding α :=
  StrongEmbedding.ofBranchLevels
    W.eval
    (levels W)
    (levels_strictMono W)
    (eval_length W)
    (eval_branch W)

/-- Map constants of a line symbol while preserving the parameter. -/
def mapLineSymbol (f : α → β) : LineSymbol α → LineSymbol β
  | .const a => .const (f a)
  | .parameter => .parameter

/-- Mapping commutes with evaluation of a line word. -/
theorem map_evalWord
    (f : α → β) (a : α) (w : List (LineSymbol α)) :
    (evalWord a w).map f =
      evalWord (f a) (w.map (mapLineSymbol f)) := by
  induction w with
  | nil =>
      rfl
  | cons x w ih =>
      cases x with
      | const b =>
          change
            f b :: (evalWord a w).map f =
              f b :: evalWord (f a) (w.map (mapLineSymbol f))
          exact congrArg (List.cons (f b)) ih
      | parameter =>
          change
            f a :: (evalWord a w).map f =
              f a :: evalWord (f a) (w.map (mapLineSymbol f))
          exact congrArg (List.cons (f a)) ih

/-- Coordinatewise image of one left-variable block. -/
def mapBlock (f : α → β)
    (B : LeftVariableWord α) :
    LeftVariableWord β :=
  ⟨B.tail.map (mapLineSymbol f)⟩

theorem mapBlock_eval
    (f : α → β)
    (B : LeftVariableWord α) (a : α) :
    (B.eval a).map f = (mapBlock f B).eval (f a) := by
  change
    f a :: (evalWord a B.tail).map f =
      f a :: evalWord (f a) (B.tail.map (mapLineSymbol f))
  exact congrArg (List.cons (f a))
    (map_evalWord f a B.tail)

/-- Map every constant of a subspace. -/
def mapSubspace (f : α → β) (W : Subspace α) :
    Subspace β where
  head := W.head.map f
  blocks := fun n => mapBlock f (W.blocks n)

theorem mapSubspace_evalFrom
    (f : α → β) (W : Subspace α)
    (i : ℕ) (s : List α) :
    (W.evalFrom i s).map f =
      (mapSubspace f W).evalFrom i (s.map f) := by
  induction s generalizing i with
  | nil =>
      rfl
  | cons a s ih =>
      simp only [Subspace.evalFrom, List.map_append, List.map_cons]
      rw [mapBlock_eval, ih (i := i + 1)]
      rfl

theorem mapSubspace_eval
    (f : α → β) (W : Subspace α)
    (s : List α) :
    (W.eval s).map f =
      (mapSubspace f W).eval (s.map f) := by
  simp [Subspace.eval, mapSubspace, mapSubspace_evalFrom,
    List.map_append]

theorem blockSpan_mapSubspace
    (f : α → β) (W : Subspace α)
    (i n : ℕ) :
    blockSpan (mapSubspace f W) i n =
      blockSpan W i n := by
  induction n generalizing i with
  | zero =>
      rfl
  | succ n ih =>
      change
        1 + ((mapSubspace f W).blocks i).tail.length +
              blockSpan (mapSubspace f W) (i + 1) n =
          1 + (W.blocks i).tail.length +
              blockSpan W (i + 1) n
      have htail :
          ((mapSubspace f W).blocks i).tail.length =
            (W.blocks i).tail.length := by
        simp [mapSubspace, mapBlock]
      rw [htail, ih (i := i + 1)]

theorem levels_mapSubspace
    (f : α → β) (W : Subspace α)
    (n : ℕ) :
    levels (mapSubspace f W) n = levels W n := by
  change
    (W.head.map f).length + blockSpan (mapSubspace f W) 0 n =
      W.head.length + blockSpan W 0 n
  rw [List.length_map, blockSpan_mapSubspace]

/-- Read coordinate `i` of every letter in a product-alphabet word. -/
def column {d : ℕ}
    (i : Fin d) (u : List (Fin d → α)) : List α :=
  u.map (fun a => a i)

/-- Turn a common-level tuple of coordinate words into its column word over
the product alphabet. -/
noncomputable def packLevelTuple
    {d n : ℕ}
    (x : Fin d → List α)
    (hx : ∀ i, (x i).length = n) :
    List (Fin d → α) :=
  List.ofFn fun j : Fin n =>
    fun i =>
      (x i).get
        ⟨j.1, by simpa [hx i] using j.2⟩

@[simp] theorem packLevelTuple_length
    {d n : ℕ}
    (x : Fin d → List α)
    (hx : ∀ i, (x i).length = n) :
    (packLevelTuple x hx).length = n := by
  simp [packLevelTuple]

/-- Packing and then reading a coordinate recovers the original word. -/
theorem column_packLevelTuple
    {d n : ℕ}
    (x : Fin d → List α)
    (hx : ∀ i, (x i).length = n)
    (i : Fin d) :
    column i (packLevelTuple x hx) = x i := by
  apply List.ext_get
  · simp [column, packLevelTuple, hx i]
  · intro j hj₁ hj₂
    simp [column, packLevelTuple]

/-- Project one product-alphabet Hales--Jewett subspace to coordinate `i`. -/
def coordinateSubspace
    {d : ℕ}
    (W : Subspace (Fin d → α))
    (i : Fin d) :
    Subspace α :=
  mapSubspace (fun a => a i) W

/-- Evaluation of a coordinate projection is the corresponding coordinate
of the product-alphabet evaluation. -/
theorem coordinateSubspace_eval
    {d : ℕ}
    (W : Subspace (Fin d → α))
    (i : Fin d)
    (u : List (Fin d → α)) :
    (coordinateSubspace W i).eval (column i u) =
      column i (W.eval u) := by
  exact (mapSubspace_eval (fun a => a i) W u).symm

/-- Infinite Hales--Jewett on the product alphabet gives strong-subtree
Halpern--Läuchli in every finite dimension. -/
theorem strongSubtreeHL
    (ι : Type u) [Finite ι] [Nonempty ι] :
    StrongSubtreeHL ι := by
  intro d colors hcolors c
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let A := Fin d → ι
  let colour : List A → Fin colors :=
    fun u => c (fun i => column i u)
  rcases omegaRamsey_of_allStarHJ
      (allStarHJ_finite A) colour with
    ⟨W, hW⟩
  let F : Fin d → StrongEmbedding ι :=
    fun i => strongEmbedding (coordinateSubspace W i)
  let L : ℕ → ℕ := levels W
  have hcommon : HasCommonLevels F L := by
    refine ⟨levels_strictMono W, ?_⟩
    intro i s
    change
      ((coordinateSubspace W i).eval s).length =
        levels W s.length
    rw [eval_length, levels_mapSubspace]
  let color : Fin colors := colour (W.eval [])
  refine ⟨color, L, F, hcommon, ?_⟩
  intro n x hx
  let u : List A := packLevelTuple x hx
  have hproj :
      ∀ i, (F i).toFun (x i) =
        column i (W.eval u) := by
    intro i
    dsimp [F, strongEmbedding]
    change
      (coordinateSubspace W i).eval (x i) =
        column i (W.eval u)
    rw [← column_packLevelTuple x hx i]
    exact coordinateSubspace_eval W i u
  change c (fun i => (F i).toFun (x i)) = color
  have hhom := hW u []
  change
    c (fun i => column i (W.eval u)) =
      c (fun i => column i (W.eval [])) at hhom
  simpa [hproj, color, colour] using hhom

end HalesJewettBridge
end HalpernLauchli
end Milliken
