import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Execution
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Generability
import ComplexityOfGenerators.Proofs.GeneratorCriteria

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def data (n : ℕ) (target label : List Symbol) : InputData Symbol Symbol := ⟨target,label,n⟩

theorem value_oversized (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : BitString)
    (oversized : n<(graph.encode start).length ∨ n<label.length) :
    value graph start n label bits=none := by
  cases produced : value graph start n label bits with
  | none => rfl
  | some word =>
      have supported := value_sound graph start n member label bits word produced
      rw [HAMPATH.inverse_empty_of_oversized_input n _ label oversized] at supported
      exact False.elim supported

theorem loaded_eq (n : ℕ) (target label : List Symbol) :
    InputBank.loadedMemory (0 : Fin 64) 1 (id : Symbol→Symbol) (id : Symbol→Symbol) (data n target label)=
      loaded target label := by
  simp [InputBank.loadedMemory,InputBank.auxiliaryStore,InputBank.inputStore,data,loaded]

theorem machine_execution (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : BitString) :
    ∃ ticks, machine.run (data n (graph.encode start) label) bits ticks=
      .halted (valueOutcome (value graph start n label bits)) := by
  by_cases oversized : n<(graph.encode start).length ∨ n<label.length
  · obtain ⟨ticks,_,run⟩ := InputBank.Capped.controller_oversized_run program 0 1 (id : Symbol→Symbol) id
      (data n (graph.encode start) label) bits oversized
    refine ⟨ticks,?_⟩
    simpa only [machine,value_oversized graph start n member label bits oversized,valueOutcome] using run
  · have targetBound : (graph.encode start).length≤n := by omega
    have labelBound : label.length≤n := by omega
    obtain ⟨ticks,_,result,run,outcome⟩ := command_runs graph start n label bits member.start_bound
    have execution := Program.Evaluates.executes _ (run.compiled 63 (Nat.zero_le _))
    change program.Executes n bits ((loaded (graph.encode start) label).at program.initial) ticks result.outcome at execution
    rw [← loaded_eq n (graph.encode start) label] at execution
    obtain ⟨nativeTicks,_,native⟩ := InputBank.Capped.run_controller_compiled program 0 1 id id (by decide)
      (data n (graph.encode start) label) bits targetBound labelBound ticks result.outcome execution
    refine ⟨nativeTicks,?_⟩
    simpa only [machine,outcome] using native

theorem machine_accepts_iff_value (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : BitString) :
    machine.Accepts (data n (graph.encode start) label) bits ↔ (value graph start n label bits).isSome := by
  obtain ⟨ticks,run⟩ := machine_execution graph start n member label bits
  cases produced : value graph start n label bits with
  | none =>
      constructor
      · rintro ⟨word,otherTicks,accepts⟩
        have same := machine.halted_outcome_unique _ bits ticks otherTicks _ _ run accepts
        simp [produced,valueOutcome] at same
      · intro impossible
        cases impossible
  | some word =>
      constructor
      · intro _
        rfl
      · intro _
        exact ⟨word,ticks,by simpa only [produced,valueOutcome] using run⟩

theorem machine_language (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) :
    machine.generatedLanguage (data n (graph.encode start) label)=
      selfReduction.inverseFibre n (graph.encode start) label := by
  ext word
  constructor
  · rintro ⟨bits,_,ticks,accepts⟩
    obtain ⟨referenceTicks,reference⟩ := machine_execution graph start n member label bits
    have same := machine.halted_outcome_unique _ bits referenceTicks ticks _ _ reference accepts
    cases produced : value graph start n label bits with
    | none => simp [produced,valueOutcome] at same
    | some candidate =>
        have equal : candidate=word := by simpa only [produced,valueOutcome,Outcome.accepted.injEq] using same
        exact value_sound graph start n member label bits word (by simpa only [equal] using produced)
  · intro supported
    obtain ⟨bits,length,produced⟩ := value_complete_seed graph start n member label word supported
    obtain ⟨ticks,run⟩ := machine_execution graph start n member label bits
    refine ⟨bits,?_,ticks,?_⟩
    · intro empty
      rw [empty,List.length_nil,seed_eq] at length
      omega
    · simpa only [produced,valueOutcome] using run

theorem machine_halting (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) : machine.HaltingTransducer (data n (graph.encode start) label) := by
  constructor
  · intro bits
    obtain ⟨ticks,run⟩ := machine_execution graph start n member label bits
    exact ⟨ticks,_,run⟩
  · intro bits ticks rejects
    obtain ⟨referenceTicks,reference⟩ := machine_execution graph start n member label bits
    have same := machine.halted_outcome_unique _ bits referenceTicks ticks _ _ reference rejects
    cases produced : value graph start n label bits <;> simp [produced,valueOutcome] at same

theorem full_trial (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) (bits : BitString) (length : bits.length=seed n) :
    machine.Accepts (data n (graph.encode start) label) bits ↔
      (machine.generatedLanguage (data n (graph.encode start) label)).Nonempty := by
  rw [machine_accepts_iff_value graph start n member,machine_language graph start n member]
  exact value_full graph start n member label bits length

theorem machine_generator (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start)
    (label : List Symbol) : machine.IsGenerator (data n (graph.encode start) label) :=
  machine.isGenerator_of_full_trials _ (seed n) (machine_halting graph start n member label)
    (full_trial graph start n member label)

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
