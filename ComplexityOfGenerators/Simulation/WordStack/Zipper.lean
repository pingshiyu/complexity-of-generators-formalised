import ComplexityOfGenerators.Simulation.WordStack.Words

/-! Tape cursors represented by two word stacks. Read-only movement clamps at
both endpoints; work-tape movement supplies a blank beyond the stored region. -/

namespace ComplexityOfGenerators.Simulation.WordStack

structure Zipper (A : Type) where
  left : List A
  right : List A
  deriving DecidableEq

namespace Zipper

variable {A : Type}

def word (z : Zipper A) : List A := z.left.reverse ++ z.right
def position (z : Zipper A) : ℕ := z.left.length
def read (z : Zipper A) : Option A := z.right.head?

def clampedMove (z : Zipper A) : Move → Zipper A
  | .stay => z
  | .left => match z.left with | [] => z | a :: xs => ⟨xs, a :: z.right⟩
  | .right => match z.right with | [] => z | a :: xs => ⟨a :: z.left, xs⟩

theorem read_eq (z : Zipper A) : z.read = z.word[z.position]? := by
  simp only [read, word, position, List.getElem?_append, List.length_reverse, lt_self_iff_false,
    ite_eq_right, Nat.sub_self]
  cases z.right <;> rfl

theorem clampedMove_word (z : Zipper A) (direction : Move) : (z.clampedMove direction).word = z.word := by
  cases direction <;> cases z with
  | mk left right =>
    cases left <;> cases right <;> simp [clampedMove, word, List.reverse_cons, List.append_assoc]

theorem clampedMove_position (z : Zipper A) (direction : Move) :
    (z.clampedMove direction).position = direction.onInput z.word.length z.position := by
  cases direction <;> cases z with
  | mk left right =>
    cases left <;> cases right <;> simp [clampedMove, word, position, Move.onInput]

def workMove (blank : A) (z : Zipper A) : Move → Zipper A
  | .stay => z
  | .left => ⟨z.left.tail, z.left.head?.getD blank :: z.right⟩
  | .right => ⟨z.right.head?.getD blank :: z.left, z.right.tail⟩

def write (a : A) (z : Zipper A) : Zipper A := ⟨z.left, a :: z.right.tail⟩

end Zipper

namespace Command

variable {S O : Type} {k : ℕ}

def moveOne (src dst : Fin k) (fallback : Option S) : Command S O k :=
  .branch src fun o => match o.1 with
    | some a => (pop src).seq (push dst a)
    | none => match fallback with | none => .skip | some a => push dst a

def movedOne (src dst : Fin k) (fallback : Option S) (m : Memory S O k) : Memory S O k :=
  match m.store src with
  | a :: rest => (m.set src rest).set dst (a :: m.store dst)
  | [] => match fallback with | none => m | some a => m.set dst (a :: m.store dst)

theorem moveOne_runs (src dst : Fin k) (different : src ≠ dst) (fallback : Option S)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ t ≤ 4, (moveOne src dst fallback).Runs n bits m t (.done (movedOne src dst fallback m)) := by
  cases word_eq : m.store src with
  | nil =>
    cases fallback with
    | none =>
      refine ⟨1, by omega, ?_⟩
      apply Runs.branch m src _ 0 _
      simpa [observe, movedOne, word_eq] using Runs.skip m
    | some a =>
      refine ⟨2, by omega, ?_⟩
      apply Runs.branch m src _ 1 _
      simpa [observe, movedOne, word_eq] using push_runs dst a bits m bounded
  | cons a rest =>
    have first := pop_runs src bits m bounded
    simp only [word_eq, List.tail_cons] at first
    have last := push_runs dst a bits (m.set src rest) bounded
    simp only [Memory.set_there _ _ different.symm] at last
    refine ⟨4, by omega, ?_⟩
    apply Runs.branch m src _ 3 _
    simpa only [observe, word_eq, List.head?_cons, movedOne] using
      Runs.seq _ _ _ _ 1 1 _ first last

def moveRead (left right : Fin k) : Move → Command S O k
  | .stay => .skip
  | .left => moveOne left right none
  | .right => moveOne right left none

def movedRead (left right : Fin k) (direction : Move) (m : Memory S O k) : Memory S O k :=
  match direction with
  | .stay => m
  | .left => movedOne left right none m
  | .right => movedOne right left none m

theorem moveRead_runs (left right : Fin k) (different : left ≠ right) (direction : Move)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ t ≤ 4, (moveRead left right direction).Runs n bits m t (.done (movedRead left right direction m)) := by
  cases direction with
  | stay => exact ⟨0, by omega, Runs.skip m⟩
  | left => exact moveOne_runs left right different none bits m bounded
  | right => exact moveOne_runs right left different.symm none bits m bounded

theorem movedRead_stacks (left right : Fin k) (different : left ≠ right) (direction : Move)
    (m : Memory S O k) :
    let z : Zipper S := ⟨m.store left, m.store right⟩
    movedRead left right direction m =
      (m.set left (z.clampedMove direction).left).set right (z.clampedMove direction).right := by
  cases direction <;> cases hl : m.store left <;> cases hr : m.store right <;>
    simp only [movedRead, movedOne, hl, hr, Zipper.clampedMove]
  all_goals
    apply Configuration.ext <;> try rfl
    funext j
    by_cases hleft : j = left <;> by_cases hright : j = right <;>
      simp_all [Memory.set, Function.update_apply]

def moveWork (left right : Fin k) (blank : S) : Move → Command S O k
  | .stay => .skip
  | .left => moveOne left right (some blank)
  | .right => moveOne right left (some blank)

def movedWork (left right : Fin k) (blank : S) (direction : Move) (m : Memory S O k) : Memory S O k :=
  match direction with
  | .stay => m
  | .left => movedOne left right (some blank) m
  | .right => movedOne right left (some blank) m

theorem moveWork_runs (left right : Fin k) (different : left ≠ right) (blank : S) (direction : Move)
    {n : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ n) :
    ∃ t ≤ 4, (moveWork left right blank direction).Runs n bits m t (.done (movedWork left right blank direction m)) := by
  cases direction with
  | stay => exact ⟨0, by omega, Runs.skip m⟩
  | left => exact moveOne_runs left right different (some blank) bits m bounded
  | right => exact moveOne_runs right left different.symm (some blank) bits m bounded

theorem movedWork_stacks (left right : Fin k) (different : left ≠ right) (blank : S) (direction : Move)
    (m : Memory S O k) :
    let z : Zipper S := ⟨m.store left, m.store right⟩
    movedWork left right blank direction m =
      (m.set left (z.workMove blank direction).left).set right (z.workMove blank direction).right := by
  cases direction <;> cases hl : m.store left <;> cases hr : m.store right <;>
    simp only [movedWork, movedOne, hl, hr, Zipper.workMove, List.head?_nil, List.head?_cons,
      List.tail_nil, List.tail_cons, Option.getD_none, Option.getD_some]
  all_goals
    apply Configuration.ext <;> try rfl
    funext j
    by_cases hleft : j = left <;> by_cases hright : j = right <;>
      simp_all [Memory.set, Function.update_apply]

def writeHead (dst : Fin k) (a : S) : Command S O k := (pop dst).seq (push dst a)

theorem writeHead_runs (dst : Fin k) (a : S) {n : ℕ} (bits : BitString) (m : Memory S O k)
    (bounded : m.indexHead ≤ n) :
    (writeHead dst a).Runs n bits m 3 (.done (m.set dst (a :: (m.store dst).tail))) := by
  have last := push_runs dst a bits (m.set dst (m.store dst).tail) bounded
  simp only [Memory.set_here, Memory.set_twice] at last
  exact Runs.seq _ _ _ _ 1 1 _ (pop_runs dst bits m bounded) last

end Command
end ComplexityOfGenerators.Simulation.WordStack
