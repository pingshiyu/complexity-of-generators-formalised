import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

/-! A unary-position one-hot word builder. Four owned stacks contain the
size clock, position countdown, pending marker, and reversed output. -/
namespace ComplexityOfGenerators.Simulation.WordStack.OneHot
variable {S O : Type} {k : ℕ}
abbrev Layout (k : ℕ) := Fin 4 ↪ Fin k

def setup (slots : Layout k) (encode : Bool → S) : Routine S O k :=
  (Routine.clear (slots 2)).seq (Routine.ofLocal (Local.push (slots 2) (encode true)))

def step (slots : Layout k) (encode : Bool → S) : Routine S O k :=
  Routine.branch (slots 1) (fun head => if head.isNone then
    Routine.branch (slots 2) (fun pending => if pending.isNone then
      Routine.ofLocal (Local.push (slots 3) (encode false)) else
      (Routine.clear (slots 2)).seq (Routine.ofLocal (Local.push (slots 3) (encode true))))
    else (Routine.ofLocal (Local.pop (slots 1))).seq
      (Routine.ofLocal (Local.push (slots 3) (encode false))))

theorem step_frame (slots : Layout k) (encode : Bool → S) (j : Fin k)
    (position : j ≠ slots 1) (pending : j ≠ slots 2) (output : j ≠ slots 3) :
    (step (O := O) slots encode).Fixes j := by
  apply Routine.Fixes.branch
  intro head
  split
  · apply Routine.Fixes.branch
    intro mark
    split
    · exact Routine.fixes_push _ _ _ output
    · exact (Routine.fixes_clear _ _ pending).seq (Routine.fixes_push _ _ _ output)
  · exact (Routine.fixes_pop _ _ position).seq (Routine.fixes_push _ _ _ output)

def routine (slots : Layout k) (encode : Bool → S) : Routine S O k :=
  (setup slots encode).seq
    (Routine.iterate (slots 0) (step slots encode)
      (step_frame slots encode (slots 0) (by simp) (by simp) (by simp)))

def bit (slots : Layout k) (s : Local.Store S k) : Bool :=
  (s (slots 1)).head?.isNone && (s (slots 2)).head?.isSome

theorem setup_eval (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (setup (O := O) slots encode).eval s = Function.update s (slots 2) [encode true] := by
  simp [setup, Routine.seq, Routine.clear, Routine.ofLocal, Local.eval_push]

theorem step_eval (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (step (O := O) slots encode).eval s =
      Function.update (Function.update (Function.update s (slots 1) (s (slots 1)).tail)
        (slots 2) (if (s (slots 1)).head?.isNone then [] else s (slots 2)))
        (slots 3) (encode (bit slots s) :: s (slots 3)) := by
  have posSelf : Function.update s (slots 1) (s (slots 1)) = s := Function.update_eq_self _ _
  cases position : s (slots 1) with
  | nil =>
    have posEmpty : Function.update s (slots 1) [] = s := by simpa only [position] using posSelf
    cases pending : s (slots 2) with
    | nil =>
      have markEmpty : Function.update s (slots 2) [] = s := by
        simpa only [pending] using (Function.update_eq_self (slots 2) s)
      simp [step, bit, Routine.branch, position, pending, Routine.ofLocal, Local.eval_push, posEmpty, markEmpty]
    | cons a rest =>
      simp [step, bit, Routine.branch, position, pending, Routine.seq, Routine.clear, Routine.ofLocal,
        Local.eval_push, posEmpty]
  | cons a rest =>
    have markSelf : Function.update (Function.update s (slots 1) rest) (slots 2) (s (slots 2)) =
        Function.update s (slots 1) rest := by
      simpa using (Function.update_eq_self (slots 2) (Function.update s (slots 1) rest))
    simp [step, bit, Routine.branch, position, Routine.seq, Routine.ofLocal, Local.eval_pop, Local.eval_push, markSelf]

theorem routine_frame (slots : Layout k) (encode : Bool → S) (j : Fin k)
    (outside : ∀ i, j ≠ slots i) : (routine (O := O) slots encode).Fixes j := by
  apply Routine.Fixes.seq
  · intro s
    simp [setup_eval, outside]
  · exact Routine.iterate_frame (slots 0) (step slots encode) _ j (outside 0)
      (step_frame slots encode j (outside 1) (outside 2) (outside 3))

theorem routine_randomFree (slots : Layout k) (encode : Bool → S) :
    Command.RandomFree (routine (O := O) slots encode).command := by
  apply (Routine.randomFree_seq _ _).mpr
  constructor
  · simp [setup]
  · apply Routine.randomFree_iterate
    simp only [step, Routine.randomFree_branch]
    intro head
    split
    · simp only [Routine.randomFree_branch]
      intro mark
      split <;> simp
    · simp

end ComplexityOfGenerators.Simulation.WordStack.OneHot
