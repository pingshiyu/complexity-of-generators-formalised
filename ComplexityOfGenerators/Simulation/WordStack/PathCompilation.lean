import ComplexityOfGenerators.Simulation.WordStack.Compiler
import ComplexityOfGenerators.Simulation.WordStack.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.PathCompilation

namespace ComplexityOfGenerators.Simulation.WordStack.Program
open TransducerBank
variable {Q S O : Type} {k : ℕ} (P : Program Q S O k)

theorem steps_compiled {n : ℕ} {bits : BitString} {start finish : Configuration Q S O k} {t : ℕ}
    (path : P.Steps n bits start t finish) (bounded : start.indexHead≤n) :
    ∃ ticks≤2*t, P.bank.Steps (generatorData n) bits (P.encoded start) ticks (P.encoded finish) := by
  induction path with
  | refl source => exact ⟨0,by omega,.refl _⟩
  | random source no yes bit t finish table lookup rest ih =>
      obtain ⟨ticks,bound,tail⟩ := ih bounded
      have instruction := P.encoded_instruction n source
      rw [table] at instruction
      refine ⟨ticks+1,by omega,?_⟩
      apply TapeBank.Steps.random _ _ _ bit ticks _ instruction lookup
      simpa only [P.encoded_choose,apply_ite Phase.ready] using tail
  | step source next action index emit t finish table rest ih =>
      obtain ⟨s,cost,first⟩ := P.step_compiled bounded table (bits := bits)
      obtain ⟨ticks,bound,tail⟩ := ih (index.onInput_le _ _ bounded)
      exact ⟨s+ticks,by omega,first.trans P.bank tail⟩

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable [Fintype Q] [Fintype S] [Fintype O]

theorem steps_native {n : ℕ} {bits : BitString} {source finish : Configuration Q S O k} {t : ℕ}
    (path : P.Steps n bits source t finish) (r : ℕ) (negative : Fin k→Bool)
    (start : ComplexityOfGenerators.Configuration P.machine)
    (ready : BankReady P.bank (P.encoded source) negative start)
    (bounded : P.bank.Bounded (generatorData n) r (P.encoded source)) :
    ∃ ticks next sides, BankReady P.bank (P.encoded finish) sides next ∧
      P.machine.Steps (generatorData n) bits start ticks next := by
  obtain ⟨ticks,_,bankPath⟩ := P.steps_compiled path bounded.index
  exact bank_steps_path P.bank bankPath r negative start ready bounded

end
end ComplexityOfGenerators.Simulation.WordStack.Program
