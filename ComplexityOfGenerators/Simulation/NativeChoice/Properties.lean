import ComplexityOfGenerators.Simulation.NativeChoice.Execution
import ComplexityOfGenerators.Generators

namespace ComplexityOfGenerators.Simulation.NativeChoice
noncomputable section
variable {E O : Type} [Fintype E] (family : E → Machine Unit Bool O)

/-- All branches share one transition table; selection changes only its finite
initial control. This is the callback interface for native source calls. -/
theorem machine_with_initial (initial event : E) :
    {machine family initial with initial:=start family event}=machine family event := rfl

theorem run_halted_iff (event : E) (data : InputData Unit Bool) (bits : BitString)
    (ticks : ℕ) (result : Outcome O) :
    (machine family event).run data bits ticks=.halted result ↔
      (family event).run data bits ticks=.halted result := by
  rw [run]
  cases (family event).run data bits ticks <;> simp [runState]

theorem produces_iff (event : E) (data : InputData Unit Bool) (bits : BitString) (word : List O) :
    (machine family event).Produces data bits word ↔ (family event).Produces data bits word := by
  simp only [Machine.Produces,run_halted_iff]

theorem halting (event : E) (data : InputData Unit Bool)
    (source : (family event).HaltingTransducer data) : (machine family event).HaltingTransducer data := by
  constructor
  · intro bits
    obtain ⟨ticks,result,run⟩ := source.1 bits
    exact ⟨ticks,result,(run_halted_iff family event data bits ticks result).mpr run⟩
  · intro bits ticks rejected
    exact source.2 bits ticks ((run_halted_iff family event data bits ticks .rejected).mp rejected)

end
end ComplexityOfGenerators.Simulation.NativeChoice
