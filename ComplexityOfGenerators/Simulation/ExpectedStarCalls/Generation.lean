import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Emission

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

noncomputable def generatingCommand (decode : β → StarPaths.Symbol) : Command (Cell (β := β) P) α 80 :=
  (command P decode).seq (emit P)

def BufferedResult (parts : List ℕ) : Result (Cell (β := β) P) α 80 → Prop
  | .exhausted => True
  | .done after => after.indexHead = 0 ∧ after.output = [] ∧ ∃ factors : List (List α),
      List.Forall₂ (fun j word => word ∈ P.layer j) parts factors ∧
        (after.store 70).filterMap (outputLetter P) = factors.flatten.reverse

def GeneratedResult (parts : List ℕ) : Result (Cell (β := β) P) α 80 → Prop
  | .exhausted => True
  | .done after => ∃ factors : List (List α), List.Forall₂ (fun j word => word ∈ P.layer j) parts factors ∧
      after.output = factors.flatten

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem command_runs_total (inputIndex : ℕ) (parts : List ℕ) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (indices : ∀ j ∈ parts, j ≤ inputIndex) :
    ∃ ticks result, (command P decode).Runs inputIndex bits m ticks result ∧ BufferedResult P parts result := by
  let ready : Memory (Cell (β := β) P) α 80 := {m with store := (Routine.clear (O := α) 70).eval m.store}
  have readyPath : ready.store 31 = pathWord P encode parts := by simpa [ready, Routine.clear] using path
  obtain ⟨first, _, firstRun⟩ := (Routine.clear (O := α) 70).runs (n := inputIndex) bits m (by omega)
  obtain ⟨rest, result, restRun, post⟩ := loop_runs_total P encode decode retract inputIndex parts bits ready origin empty readyPath indices
  refine ⟨first+1+rest, result, Command.Runs.seq _ _ _ _ _ _ _ firstRun restRun, ?_⟩
  cases result with
  | exhausted => trivial
  | done next =>
      obtain ⟨factors, language, buffer⟩ := post.factors
      exact ⟨post.origin.trans origin, post.output, factors, language, by simpa [ready, Routine.clear] using buffer⟩

include retract in
theorem generating_runs_total (inputIndex : ℕ) (parts : List ℕ) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (indices : ∀ j ∈ parts, j ≤ inputIndex) :
    ∃ ticks result, (generatingCommand P decode).Runs inputIndex bits m ticks result ∧ GeneratedResult P parts result := by
  obtain ⟨first, result, firstRun, post⟩ := command_runs_total P encode decode retract inputIndex parts bits m origin empty path indices
  cases result with
  | exhausted => exact ⟨first, .exhausted, Command.Runs.seq_absent _ _ _ _ firstRun, trivial⟩
  | done after =>
      obtain ⟨afterOrigin, afterEmpty, factors, language, buffer⟩ := post
      obtain ⟨last, _, next, lastRun, output, _, _⟩ := emit_runs P inputIndex bits after (by rw [afterOrigin]; omega)
      refine ⟨first+1+last, .done next, Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun, factors, language, ?_⟩
      rw [output, afterEmpty, buffer, List.nil_append, List.reverse_reverse]

include retract in
theorem generating_runs_trace (inputIndex ceiling budget : ℕ) (parts : List ℕ) (records : List (Record α))
    (bits : BitString) (m : Memory (Cell (β := β) P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (sizes : StoreBound m.store budget)
    (indices : ∀ j ∈ parts, j ≤ inputIndex)
    (fits : budget+parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex ≤ ceiling)
    (trace : Trace P bits m.randomHead parts records) :
    ∃ ticks ≤ 2*(blocks records+1)*coefficient P inputIndex ceiling,
      ∃ next, (generatingCommand P decode).Runs inputIndex bits m ticks (.done next) ∧
        next.output = words records ∧ next.indexHead = 0 ∧ next.randomHead = m.randomHead+consumed P parts records := by
  obtain ⟨first, firstCost, after, firstRun, afterOrigin, afterHead, afterEmpty, buffer, sizesAfter⟩ :=
    command_runs_trace P encode decode retract inputIndex ceiling budget parts records bits m origin empty path sizes indices fits trace
  obtain ⟨last, lastCost, next, lastRun, output, nextOrigin, nextHead⟩ := emit_runs P inputIndex bits after (by rw [afterOrigin]; omega)
  refine ⟨first+1+last, ?_, next, Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun, ?_, nextOrigin.trans afterOrigin,
    nextHead.trans afterHead⟩
  · have bounded : StoreBound after.store ceiling := sizesAfter.mono fits
    have raw := bounded 70
    have scratch := bounded 74
    have charge : 1+last ≤ coefficient P inputIndex ceiling := by unfold coefficient; omega
    have extra : coefficient P inputIndex ceiling ≤ (blocks records+1)*coefficient P inputIndex ceiling := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (coefficient P inputIndex ceiling) (by omega : 1 ≤ blocks records+1)
    calc
      first+1+last ≤ (blocks records+1)*coefficient P inputIndex ceiling+coefficient P inputIndex ceiling := by omega
      _ ≤ (blocks records+1)*coefficient P inputIndex ceiling+(blocks records+1)*coefficient P inputIndex ceiling := Nat.add_le_add_left extra _
      _ = 2*(blocks records+1)*coefficient P inputIndex ceiling := by ring
  · rw [output, afterEmpty, buffer, List.nil_append, List.reverse_reverse]

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
