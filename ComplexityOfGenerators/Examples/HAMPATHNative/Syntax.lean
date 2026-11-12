import ComplexityOfGenerators.Examples.HAMPATHNative.Parser
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def syntaxWord (word : List Symbol) : List Unit := if wellFormed word then [()] else []

def prepare : Routine Symbol Unit 32 := Routine.transfer 0 2 (by decide) id

def finish : Command Symbol Unit 32 :=
  .branch 6 fun valid => if valid.1.isSome then
    .branch 12 fun seen => if seen.1.isSome then
      .branch 2 fun remaining => if remaining.1.isSome then .skip else Command.emitFixed 0 [()]
    else .skip
  else .skip

def syntaxCommand : Command Symbol Unit 32 := prepare.command.seq (parser.command.seq finish)

def syntaxProgram := syntaxCommand.program 0

noncomputable def syntaxMachine : Machine Symbol Unit Unit :=
  InputBank.machine syntaxProgram 0 1 id (fun _ => .bit false)

def loaded (word : List Symbol) (auxiliary : List Unit) : Memory Symbol Unit 32 :=
  ⟨(), 0, 0, [], Function.update (Function.update (fun _ => []) 0 word.reverse) 1
    (auxiliary.reverse.map (fun _ => .bit false))⟩

def prepared (word : List Symbol) (auxiliary : List Unit) : Memory Symbol Unit 32 :=
  {loaded word auxiliary with store := prepare.eval (loaded word auxiliary).store}

theorem prepared_word (word : List Symbol) (auxiliary : List Unit) :
    (prepared word auxiliary).store 2 = word := by simp [prepared, prepare, loaded, Routine.transfer]

theorem prepared_sizes (word : List Symbol) (auxiliary : List Unit) :
    ∀ j, ((prepared word auxiliary).store j).length ≤ word.length + auxiliary.length := by
  intro j
  by_cases source : j = 0 <;> by_cases input : j = 2 <;> by_cases aux : j = 1 <;>
    simp [prepared, loaded, prepare, Routine.transfer, source, input, aux] <;> omega

theorem finish_runs (bits : BitString) (m : Memory Symbol Unit 32) (index : m.indexHead = 0) :
    ∃ ticks ≤ 5, finish.Runs 0 bits m ticks
      (.done {m with output := m.output ++
        (if ((m.store 6).head?.isSome && (m.store 12).head?.isSome && (m.store 2).isEmpty) then [()] else [])}) := by
  cases valid : m.store 6 with
  | nil =>
      refine ⟨1, by omega, ?_⟩
      apply Command.Runs.branch m 6 _ 0 _
      simp [finish, observe, valid]
      exact Command.Runs.skip m
  | cons v rest =>
      cases seen : m.store 12 with
      | nil =>
          refine ⟨2, by omega, ?_⟩
          apply Command.Runs.branch m 6 _ 1 _
          simp only [finish, observe, valid, List.head?_cons, Option.isSome_some, ite_true]
          apply Command.Runs.branch m 12 _ 0 _
          simp [observe, seen]
          exact Command.Runs.skip m
      | cons s restSeen =>
          cases remaining : m.store 2 with
          | nil =>
              refine ⟨5, by omega, ?_⟩
              apply Command.Runs.branch m 6 _ 4 _
              simp only [finish, observe, valid, List.head?_cons, Option.isSome_some, ite_true]
              apply Command.Runs.branch m 12 _ 3 _
              simp only [observe, seen, List.head?_cons, Option.isSome_some, ite_true]
              apply Command.Runs.branch m 2 _ 2 _
              simp only [observe, remaining, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
              simpa [valid, seen, remaining] using Command.emitFixed_runs (0 : Fin 32) [()] bits m (by omega)
          | cons r restRemaining =>
              refine ⟨3, by omega, ?_⟩
              apply Command.Runs.branch m 6 _ 2 _
              simp only [finish, observe, valid, List.head?_cons, Option.isSome_some, ite_true]
              apply Command.Runs.branch m 12 _ 1 _
              simp only [observe, seen, List.head?_cons, Option.isSome_some, ite_true]
              apply Command.Runs.branch m 2 _ 0 _
              simp [observe, remaining, valid, seen]
              exact Command.Runs.skip m

theorem finish_randomFree : Command.RandomFree finish := by
  unfold finish
  apply Command.RandomFree.branch
  intro valid
  split_ifs
  · apply Command.RandomFree.branch
    intro seen
    split_ifs
    · apply Command.RandomFree.branch
      intro remaining
      split_ifs
      · exact .skip
      · exact Command.randomFree_emitFixed _ _
    · exact .skip
  · exact .skip

theorem parser_randomFree {O : Type} : Command.RandomFree (parser (O := O)).command := by
  simp [parser, header, headerExtract, headerSetup, headerClock, rows, rowRoutine, rowPrepare, rowFinish,
    cells, startPrepare, starts]

theorem syntaxProgram_noRandom : InputBank.NoRandom syntaxProgram := by
  apply Command.RandomFree.noRandom
  simp [syntaxCommand, prepare, parser_randomFree, finish_randomFree]

theorem syntaxMachine_deterministic : syntaxMachine.Deterministic :=
  InputBank.machine_deterministic syntaxProgram 0 1 id (fun _ => .bit false) syntaxProgram_noRandom

end ComplexityOfGenerators.Examples.HAMPATH.Native
