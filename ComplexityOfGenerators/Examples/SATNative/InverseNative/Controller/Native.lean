import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Execution
import ComplexityOfGenerators.Examples.InverseInputBounds
import ComplexityOfGenerators.Proofs.GeneratorCriteria

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform parse NativeSubstitution.prepareStream

def data (n : ℕ) (target label : List Symbol) : InputData Symbol Symbol := ⟨target,label,n⟩

def seed : PolynomialBound := ⟨1,1,by decide⟩

@[simp] theorem seed_eq (n : ℕ) : seed n = n+1 := by simp [seed,PolynomialBound.eval]

theorem value_oversized {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString)
    (oversized : n < (formula.encode capacity active).length ∨ n < label.length) :
    value n (formula.encode capacity active) label bits = none := by
  cases produced : value n (formula.encode capacity active) label bits with
  | none => rfl
  | some word =>
      have member := value_sound bound formula valid satisfiable n label bits word produced
      rw [PaddedCNF.inverse_empty_of_oversized_input n _ label oversized] at member
      exact False.elim member

theorem loaded_eq (n : ℕ) (target label : List Symbol) :
    InputBank.loadedMemory (0 : Fin 35) 1 (id : Symbol → Symbol) (id : Symbol → Symbol) (data n target label) =
      loaded target label := by
  simp [InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore,data,loaded]

/-- Every finite tape has an actual native execution, including all empty
fibres and arbitrarily oversized ordinary or auxiliary inputs. -/
theorem machine_execution {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString) :
    ∃ ticks, machine.run (data n (formula.encode capacity active) label) bits ticks =
      .halted (valueOutcome (value n (formula.encode capacity active) label bits)) := by
  by_cases oversized : n < (formula.encode capacity active).length ∨ n < label.length
  · obtain ⟨ticks,_,run⟩ := InputBank.Capped.controller_oversized_run program 0 1 (id : Symbol → Symbol) id
      (data n (formula.encode capacity active) label) bits oversized
    refine ⟨ticks,?_⟩
    simpa only [machine,value_oversized bound formula valid satisfiable n label bits oversized,valueOutcome] using run
  · have targetBound : (formula.encode capacity active).length ≤ n := by omega
    have labelBound : label.length ≤ n := by omega
    obtain ⟨ticks,_,result,run,outcome⟩ := command_runs_canonical bound formula valid n label bits
    have execution := Program.Evaluates.executes _ (run.compiled 0 (Nat.zero_le _))
    change program.Executes n bits ((loaded (formula.encode capacity active) label).at program.initial) ticks result.outcome at execution
    rw [← loaded_eq n (formula.encode capacity active) label] at execution
    obtain ⟨nativeTicks,_,native⟩ := InputBank.Capped.run_controller_compiled program 0 1 id id (by decide)
      (data n (formula.encode capacity active) label) bits targetBound labelBound ticks result.outcome execution
    refine ⟨nativeTicks,?_⟩
    simpa only [machine,outcome] using native

theorem machine_accepts_iff_value {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString) :
    machine.Accepts (data n (formula.encode capacity active) label) bits ↔
      (value n (formula.encode capacity active) label bits).isSome := by
  obtain ⟨ticks,run⟩ := machine_execution bound formula valid satisfiable n label bits
  cases produced : value n (formula.encode capacity active) label bits with
  | none =>
      constructor
      · rintro ⟨word,otherTicks,accepts⟩
        have same := machine.halted_outcome_unique _ bits ticks otherTicks _ _ run accepts
        simp [produced,valueOutcome] at same
      · intro impossible; cases impossible
  | some word =>
      constructor
      · intro _; rfl
      · intro _; exact ⟨word,ticks,by simpa only [produced,valueOutcome] using run⟩

theorem machine_language {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) :
    machine.generatedLanguage (data n (formula.encode capacity active) label) =
      selfReduction.inverseFibre n (formula.encode capacity active) label := by
  ext word
  constructor
  · rintro ⟨bits,_,ticks,accepts⟩
    obtain ⟨referenceTicks,reference⟩ := machine_execution bound formula valid satisfiable n label bits
    have same := machine.halted_outcome_unique _ bits referenceTicks ticks _ _ reference accepts
    cases produced : value n (formula.encode capacity active) label bits with
    | none => simp [produced,valueOutcome] at same
    | some candidate =>
        have equal : candidate = word := by simpa only [produced,valueOutcome,Outcome.accepted.injEq] using same
        exact value_sound bound formula valid satisfiable n label bits word (by simpa only [equal] using produced)
  · intro member
    obtain ⟨bits,length,produced⟩ := value_complete bound formula valid satisfiable n label word member
    obtain ⟨ticks,run⟩ := machine_execution bound formula valid satisfiable n label bits
    refine ⟨bits,?_,ticks,?_⟩
    · intro empty
      rw [empty,List.length_nil] at length
      omega
    · simpa only [produced,valueOutcome] using run

theorem machine_halting {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) : machine.HaltingTransducer (data n (formula.encode capacity active) label) := by
  constructor
  · intro bits
    obtain ⟨ticks,run⟩ := machine_execution bound formula valid satisfiable n label bits
    exact ⟨ticks,_,run⟩
  · intro bits ticks rejects
    obtain ⟨referenceTicks,reference⟩ := machine_execution bound formula valid satisfiable n label bits
    have same := machine.halted_outcome_unique _ bits referenceTicks ticks _ _ reference rejects
    cases produced : value n (formula.encode capacity active) label bits <;> simp [produced,valueOutcome] at same

theorem full_trial {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString) (length : bits.length = seed n) :
    machine.Accepts (data n (formula.encode capacity active) label) bits ↔
      (machine.generatedLanguage (data n (formula.encode capacity active) label)).Nonempty := by
  rw [machine_accepts_iff_value bound formula valid satisfiable,machine_language bound formula valid satisfiable]
  exact value_full bound formula valid satisfiable n label bits (by rw [length,seed_eq]; omega)

theorem machine_generator {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) : machine.IsGenerator (data n (formula.encode capacity active) label) :=
  machine.isGenerator_of_full_trials _ (seed n) (machine_halting bound formula valid satisfiable n label)
    (full_trial bound formula valid satisfiable n label)

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
