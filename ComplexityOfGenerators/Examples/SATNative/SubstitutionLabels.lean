import ComplexityOfGenerators.Examples.SATNative.SubstitutionTransform

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

def tailSetup {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 3 22 9 (by decide) (by decide) (by decide) id).seq (Routine.ofLocal (Local.pop 22))

theorem tailSetup_eval {O : Type} (s : Store) :
    (tailSetup (O := O)).eval s = Function.update (Function.update s 9 []) 22 (s 3).tail := by
  simp only [tailSetup, Routine.seq, Routine.assign_eval, Routine.ofLocal, Local.eval_pop]
  funext j
  by_cases a : j = 9 <;> by_cases b : j = 22 <;> simp [a, b]

noncomputable def checkLabel {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  tailSetup.seq (Routine.branch 22 fun tail => if tail.isSome then Routine.clear 6 else bodyTransform bit)

noncomputable def selectLabel {O : Type} : Routine Symbol O 32 :=
  Routine.branch 10 fun active => if active.isSome then
    Routine.branch 3 fun head => match head with
    | some .zero => checkLabel false
    | some .one => checkLabel true
    | _ => Routine.clear 6
  else Routine.branch 3 fun head => if head.isSome then Routine.clear 6 else bodyTransform false

def validLabel (active : ℕ) (label : List Symbol) : Bool :=
  if active = 0 then label.isEmpty else (labelValue label).isSome

attribute [local irreducible] bodyTransform tailSetup

theorem tailSetup_represents {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state ((tailSetup (O := O)).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  simp [tailSetup_eval, Represents, word, cap, count, valid, inside, seen]

@[simp] theorem verdict_clear {O : Type} (s : Store) : NativeEvaluation.verdict ((Routine.clear (O := O) 6).eval s) = false := by
  simp [NativeEvaluation.verdict, Routine.clear]

theorem checkLabel_verdict {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    NativeEvaluation.verdict ((checkLabel (O := O) bit).eval s) =
      if (s 3).tail.isEmpty then NativeBody.accepts ((NativeBody.step capacity active)^[(s 16).length] state) else false := by
  have prepared := tailSetup_represents (O := O) capacity active state s represented
  have signal := bodyTransform_verdict (O := O) bit capacity active state ((tailSetup (O := O)).eval s) prepared
  have clock : (tailSetup (O := O)).eval s 16 = s 16 := by simp [tailSetup_eval]
  have tail : (tailSetup (O := O)).eval s 22 = (s 3).tail := by simp [tailSetup_eval]
  rw [clock] at signal
  cases remaining : (s 3).tail with
  | nil => simpa [checkLabel, Routine.seq, Routine.branch, tail, remaining] using signal
  | cons head rest => simp [checkLabel, Routine.seq, Routine.branch, tail, remaining]

theorem selectLabel_verdict {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    NativeEvaluation.verdict ((selectLabel (O := O)).eval s) =
      if validLabel active (s 3) then NativeBody.accepts ((NativeBody.step capacity active)^[(s 16).length] state) else false := by
  have count := represented.2.2.1
  have no := checkLabel_verdict (O := O) false capacity active state s represented
  have yes := checkLabel_verdict (O := O) true capacity active state s represented
  have base := bodyTransform_verdict (O := O) false capacity active state s represented
  cases active with
  | zero =>
    cases label : s 3 with
    | nil => simpa [selectLabel, Routine.branch, count, label, validLabel] using base
    | cons head rest => simp [selectLabel, Routine.branch, count, label, validLabel]
  | succ active =>
    cases label : s 3 with
    | nil => simp [selectLabel, Routine.branch, count, label, validLabel, labelValue, List.replicate_succ]
    | cons head rest =>
      cases head <;> cases rest <;>
        simp [selectLabel, Routine.branch, count, label, validLabel, labelValue, List.replicate_succ,
          no, yes]

@[simp] theorem tailSetup_randomFree {O : Type} : Command.RandomFree (tailSetup (O := O)).command := by simp [tailSetup]

@[simp] theorem checkLabel_randomFree {O : Type} (bit : Bool) : Command.RandomFree (checkLabel (O := O) bit).command := by
  simp only [checkLabel, Routine.randomFree_seq, tailSetup_randomFree, true_and, Routine.randomFree_branch]
  intro head
  by_cases present : head.isSome <;> simp [present]

@[simp] theorem selectLabel_randomFree {O : Type} : Command.RandomFree (selectLabel (O := O)).command := by
  simp only [selectLabel, Routine.randomFree_branch]
  intro active
  by_cases present : active.isSome
  · simp only [present, ite_true, Routine.randomFree_branch]
    intro head
    cases head with | none => simp | some symbol => cases symbol <;> simp
  · simp only [present, Bool.false_eq_true, ite_false, Routine.randomFree_branch]
    intro head
    by_cases presentLabel : head.isSome <;> simp [presentLabel]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
