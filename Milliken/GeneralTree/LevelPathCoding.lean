import Milliken.GeneralTree.LevelAlphabet
import Milliken.AmbientChild

/-!
# Coding finite paths with rank-dependent alphabets

Each rank has a finite alphabet covering all ambient immediate child
cones, even when the degrees are unbounded across ranks. The path
evaluator is a surjection on every cone, and strictly increases rank.
This is structural preparation for heterogeneous Halpern--Läuchli,
not a proof of that theorem.
-/

namespace Milliken
namespace GeneralTree

noncomputable def childFromLabel (U : AmbientTree) (x : U) (a : ℕ) : U :=
  (childAlphabetMap U x
    ⟨a % levelBranchBound U (U.level x),
      Nat.mod_lt a (levelBranchBound_pos U (U.level x))⟩).1

theorem childFromLabel_covBy (U : AmbientTree) (x : U) (a : ℕ) :
    x ⋖ childFromLabel U x a :=
  (childAlphabetMap U x
    ⟨a % levelBranchBound U (U.level x),
      Nat.mod_lt a (levelBranchBound_pos U (U.level x))⟩).2

theorem exists_childFromLabel (U : AmbientTree)
    {x y : U} (hxy : x ⋖ y) :
    ∃ a : ℕ, childFromLabel U x a = y := by
  obtain ⟨a, ha⟩ := exists_label_of_child U hxy
  refine ⟨a.1, ?_⟩
  change (childAlphabetMap U x
    ⟨a.1 % levelBranchBound U (U.level x),
      Nat.mod_lt a.1 (levelBranchBound_pos U (U.level x))⟩).1 = y
  have hind :
      (⟨a.1 % levelBranchBound U (U.level x),
        Nat.mod_lt a.1 (levelBranchBound_pos U (U.level x))⟩ :
          LevelAlphabet U (U.level x)) = a := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt a.2
  rw [hind]
  exact ha

noncomputable def evalPath (U : AmbientTree) : U → List ℕ → U
  | x, [] => x
  | x, a :: as => evalPath U (childFromLabel U x a) as

@[simp] theorem evalPath_nil (U : AmbientTree) (x : U) :
    evalPath U x [] = x := rfl

@[simp] theorem evalPath_cons (U : AmbientTree) (x : U)
    (a : ℕ) (as : List ℕ) :
    evalPath U x (a :: as) =
      evalPath U (childFromLabel U x a) as := rfl

theorem evalPath_append (U : AmbientTree) (x : U)
    (as bs : List ℕ) :
    evalPath U x (as ++ bs) =
      evalPath U (evalPath U x as) bs := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      change
        evalPath U (childFromLabel U x a) (as ++ bs) =
          evalPath U (evalPath U (childFromLabel U x a) as) bs
      exact ih (childFromLabel U x a)

theorem evalPath_level (U : AmbientTree) (x : U) (as : List ℕ) :
    U.level (evalPath U x as) = U.level x + as.length := by
  induction as generalizing x with
  | nil => simp [evalPath]
  | cons a as ih =>
      change
        U.level (evalPath U (childFromLabel U x a) as) =
          U.level x + (as.length + 1)
      rw [ih (childFromLabel U x a)]
      have hstep := U.level_covBy (childFromLabel_covBy U x a)
      omega

end GeneralTree
end Milliken
