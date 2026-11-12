import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Views
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

/-- Exact fixed-bank interface immediately before one source-call event. -/
structure EventReady (j : ℕ) (parts : List ℕ) (m : Memory (Cell M) Unit 80) : Prop where
  origin : m.indexHead=0
  path : m.store 31=pathWord M parts
  exported : m.store 71=List.replicate (j-1) (factorSymbol M)
  eventRegister : m.store 0=[]

def afterFactor (m : Memory (Cell M) Unit 80) : Memory (Cell M) Unit 80 :=
  {m with store := (prepareFactor M).eval m.store}

def afterEvent (m : Memory (Cell M) Unit 80) : Memory (Cell M) Unit 80 :=
  {m with output := m.output++[()]}

theorem event_runs (n : ℕ) (bits : BitString) (m : Memory (Cell M) Unit 80) (origin : m.indexHead=0) :
    (event M).Runs n bits m 1 (.done (afterEvent M m)) := by
  have run := Command.Runs.act (n := n) (bits := bits) m (0 : Fin 80) .stay .stay (some ())
  have memory : Program.changeMemory (0 : Fin 80) n .stay .stay (some ()) m = afterEvent M m := by
    apply Configuration.ext <;> try rfl
    · simp [Program.changeMemory,Move.onInput,origin,afterEvent]
    · simp [Program.changeMemory,Action.apply,afterEvent]
  simpa only [event,memory] using run

theorem prepareFactor_runs (n : ℕ) (bits : BitString) (m : Memory (Cell M) Unit 80)
    (budget j : ℕ) (parts : List ℕ) (origin : m.indexHead=0)
    (path : m.store 31=pathWord M (j::parts)) (zero : m.store 0=[])
    (sizes : StoreBound m.store budget) :
    ∃ ticks≤12*(budget+1),
      (prepareFactor M).command.Runs n bits m ticks (.done (afterFactor M m)) ∧
      EventReady M j parts (afterFactor M m) ∧
      StoreBound (afterFactor M m).store budget := by
  obtain ⟨ticks,bound,run⟩ := (prepareFactor M).runs bits m (by omega)
  have fields := prepareFactor_fields M m.store j parts path
  have frame := prepareFactor_frame M m.store 0 (by decide) (by decide)
  refine ⟨ticks,bound.trans (prepareFactor_cost_le M m.store budget j parts sizes path),run,
    ⟨origin,fields.1,fields.2,frame.trans zero⟩,prepareFactor_bound M m.store budget sizes⟩

theorem call_runs (n : ℕ) (bits : BitString) (m : Memory (Cell M) Unit 80)
    (budget j : ℕ) (parts : List ℕ) (origin : m.indexHead=0)
    (path : m.store 31=pathWord M (j::parts)) (zero : m.store 0=[])
    (sizes : StoreBound m.store budget) :
    ∃ ticks≤14*(budget+1),
      (call M).Runs n bits m ticks (.done (afterEvent M (afterFactor M m))) ∧
      EventReady M j parts (afterFactor M m) ∧
      StoreBound (afterFactor M m).store budget := by
  obtain ⟨ticks,bound,run,ready,afterBound⟩ :=
    prepareFactor_runs M n bits m budget j parts origin path zero sizes
  refine ⟨ticks+1+1,by omega,?_,ready,afterBound⟩
  exact Command.Runs.seq _ _ _ _ _ _ _ run (event_runs M n bits _ ready.origin)

@[simp] theorem prepareFactor_randomFree : Command.RandomFree (prepareFactor M).command := by
  simp [prepareFactor,parseFactor]

@[simp] theorem events_randomFree : Command.RandomFree (events M) := by
  simp [events,loop,call,event]

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
