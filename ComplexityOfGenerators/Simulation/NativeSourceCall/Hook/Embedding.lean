import ComplexityOfGenerators.Simulation.RoutineComposition
import ComplexityOfGenerators.Foundations.ExecutionRegions

/-! Native finite-control embeddings over a common physical work alphabet.
Only nonterminal instructions need agree, so accepting routine endpoints may
be hooked to a continuation rather than terminating the combined machine. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.RoutineEmbedding
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} [Finite I] [Finite A] [Finite O] {symbols : ℕ}
    (R S : Routine I A O symbols)

def instruction (f : Fin R.states → Fin S.states) : Instruction O R.states symbols → Instruction O S.states symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (f no) (f yes)
  | .step next write work input auxiliary index emit => .step (f next) write work input auxiliary index emit

def nonterminal : Instruction O R.states symbols → Prop
  | .accept | .reject => False
  | .readRandom _ _ | .step _ _ _ _ _ _ _ => True

def configuration (f : Fin R.states → Fin S.states) (c : Configuration R.machine) : Configuration S.machine :=
  ⟨f c.state,c.inputHead,c.auxiliaryHead,c.indexHead,c.randomHead,c.workHead,c.work,c.visited,c.output⟩

theorem next (f : Fin R.states → Fin S.states)
    (table : ∀ state input auxiliary index raw,
      nonterminal R (R.transition state input auxiliary index raw) →
        S.transition (f state) input auxiliary index raw = instruction R S f (R.transition state input auxiliary index raw))
    (data : InputData I A) (bits : BitString) (c d : Configuration R.machine)
    (edge : R.machine.next data bits c=.running d) :
    S.machine.next data bits (configuration R S f c)=.running (configuration R S f d) := by
  cases action : R.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [Machine.next,Routine.machine,action] at edge
  | reject => simp [Machine.next,Routine.machine,action] at edge
  | readRandom no yes =>
      have targetTable := table c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead<data.index then some () else none) (c.work c.workHead) (by simp [action,nonterminal])
      rw [action] at targetTable
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next,Routine.machine,action,lookup] at edge
      | some bit =>
          simp only [Machine.next,Routine.machine,action,lookup,RunState.running.injEq] at edge
          subst d
          simp only [Machine.next,Routine.machine,configuration,targetTable,instruction,lookup]
          cases bit <;> rfl
  | step state write work input auxiliary index emit =>
      have targetTable := table c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead<data.index then some () else none) (c.work c.workHead) (by simp [action,nonterminal])
      rw [action] at targetTable
      simp only [Machine.next,Routine.machine,action,RunState.running.injEq] at edge
      subst d
      simp only [Machine.next,Routine.machine,configuration,targetTable,instruction]
      cases write <;> cases emit <;> rfl

theorem steps (f : Fin R.states → Fin S.states)
    (table : ∀ state input auxiliary index raw,
      nonterminal R (R.transition state input auxiliary index raw) →
        S.transition (f state) input auxiliary index raw = instruction R S f (R.transition state input auxiliary index raw))
    (data : InputData I A) (bits : BitString) {c d : Configuration R.machine} {ticks : ℕ}
    (path : R.machine.Steps data bits c ticks d) :
    S.machine.Steps data bits (configuration R S f c) ticks (configuration R S f d) := by
  induction path with
  | refl => exact .refl
  | tail path edge ih => exact ih.tail (next R S f table data bits _ _ edge)

/-- Missing random input remains a real terminal observation in the target,
even when accepting observations have been replaced with continuation hooks. -/
theorem exhausted (f : Fin R.states → Fin S.states)
    (table : ∀ state input auxiliary index raw,
      nonterminal R (R.transition state input auxiliary index raw) →
        S.transition (f state) input auxiliary index raw = instruction R S f (R.transition state input auxiliary index raw))
    (data : InputData I A) (bits : BitString) (c : Configuration R.machine)
    (terminal : R.machine.observe data bits c=.halted .exhausted) :
    S.machine.observe data bits (configuration R S f c)=.halted .exhausted := by
  cases action : R.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [Machine.observe,Routine.machine,action] at terminal
  | reject => simp [Machine.observe,Routine.machine,action] at terminal
  | step state write work input auxiliary index emit => simp [Machine.observe,Routine.machine,action] at terminal
  | readRandom no yes =>
      have targetTable := table c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead<data.index then some () else none) (c.work c.workHead) (by simp [action,nonterminal])
      rw [action] at targetTable
      have missing : ¬c.randomHead<bits.length := by
        intro available
        simp [Machine.observe,Routine.machine,action,available] at terminal
      simp only [Machine.observe,Routine.machine,configuration,targetTable,instruction,missing,↓reduceIte]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.RoutineEmbedding
