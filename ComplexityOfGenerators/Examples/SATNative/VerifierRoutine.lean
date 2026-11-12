import ComplexityOfGenerators.Examples.SATNative.VerifierReady
import ComplexityOfGenerators.Examples.SATNative.EvaluationLoopBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody
open NativeAssignment

set_option backward.isDefEq.respectTransparency true

noncomputable def evaluationChoice {O : Type} : Routine Symbol O 32 :=
  Routine.branch 27 fun valid => if valid.isSome then evaluationRoutine else Routine.clear 6

noncomputable def verifier {O : Type} : Routine Symbol O 32 := prepareEvaluation.seq evaluationChoice

attribute [local irreducible] prepareEvaluation evaluationChoice evaluationRoutine

theorem verifier_eval {O : Type} (s : Store) :
    (verifier (O := O)).eval s = (evaluationChoice (O := O)).eval ((prepareEvaluation (O := O)).eval s) := by
  simp only [verifier, Routine.seq]

def verdict (s : Store) : Bool := (s 2).isEmpty && !(s 17).head?.isSome && (s 6).head?.isSome

theorem verdict_of_represents (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) :
    verdict s = accepts state := by
  rcases represented.1 with ⟨word, _, _, valid, inside, _⟩
  rw [verdict, word, valid, inside]
  cases mark : state.parserState.inside <;> cases good : state.parserState.valid <;>
    simp [accepts, NativeBody.accepts, mark, good]

set_option maxHeartbeats 800000 in
theorem verifier_decides {O : Type} (s : Store) :
    verdict ((verifier (O := O)).eval s) = verifies (s 2) (s 3) := by
  rw [verifier_eval]
  let ready := (prepareEvaluation (O := O)).eval s
  have properties := prepareEvaluation_properties (O := O) s
  dsimp only at properties
  rcases properties with ⟨represented, clock, valid⟩
  by_cases good : (s 3).length = (NativeHeader.parsedState (s 2)).count ∧ Binary (s 3)
  · have flag : ready 27 = [.one] := by simpa only [if_pos good] using valid
    have evaluated := evaluationRoutine_represents (O := O) _ _ _ _ ready represented
    rw [clock] at evaluated
    have result := verdict_of_represents _ _ _ _ _ evaluated
    change verdict ((evaluationChoice (O := O)).eval ready) = _
    simp only [evaluationChoice, Routine.branch, flag, List.head?_cons, Option.isSome_some, ite_true]
    simpa only [verifies, if_pos good, finalState, readyState] using result
  · have flag : ready 27 = [] := by simpa only [if_neg good] using valid
    change verdict ((evaluationChoice (O := O)).eval ready) = _
    simp [evaluationChoice, Routine.branch, flag, Routine.clear, verdict, verifies, good]

@[simp] theorem evaluationChoice_randomFree {O : Type} : Command.RandomFree (evaluationChoice (O := O)).command := by
  simp only [evaluationChoice, Routine.randomFree_branch]
  intro valid
  by_cases present : valid.isSome <;> simp [present]

@[simp] theorem prepareEvaluation_randomFree {O : Type} : Command.RandomFree (prepareEvaluation (O := O)).command := by
  simp [prepareEvaluation, NativeParser.bodySetup]

@[simp] theorem verifier_randomFree {O : Type} : Command.RandomFree (verifier (O := O)).command := by simp [verifier]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
