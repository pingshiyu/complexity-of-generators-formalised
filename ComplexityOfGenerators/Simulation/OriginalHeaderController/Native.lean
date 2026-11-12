import ComplexityOfGenerators.Simulation.OriginalHeaderController.Execution
import ComplexityOfGenerators.Simulation.WordStack.UnaryExport
import ComplexityOfGenerators.Proofs.FixedBlockRetryCriteria

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound) (operation : Operation)

def program : Program (command selector width clock operation).Control (Cell selector) Event 35 :=
  (command selector width clock operation).program 0

noncomputable def alphabetFintype : Fintype (Cell selector) := inferInstance
attribute [irreducible] alphabetFintype
noncomputable def controlFintype : Fintype (command selector width clock operation).Control := by
  letI := alphabetFintype selector
  exact Command.controlFintype (command selector width clock operation)
attribute [irreducible] controlFintype
noncomputable def machine : Machine Unit Bool Event := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  exact (program selector width clock operation).machine

def parameter (e : Event) (raw : Option (Fin (machine selector width clock operation).symbols)) : Bool := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  exact if e.2 then false else unaryExport (program selector width clock operation).bank 23 raw

theorem parameter_memory :
    letI := alphabetFintype selector
    letI := controlFintype selector width clock operation
    ∀(e : Event) (j : ℕ) (store : Store selector) (heads : Fin 35→Option ℤ)
      (memory : ℤ→Option (Fin (machine selector width clock operation).symbols)),
      allowed e j→store 23=List.replicate (j-1) (unitSymbol selector)→
      BankMemory (program selector width clock operation).bank (fun i=>tape (store i)) heads memory→
      ∀position : ℕ,parameter selector width clock operation e (memory position)=decide (position<j) := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  intro e j store heads memory allowedJ exported represented position
  by_cases zero : j=0
  · subst j
    have flag : e.2=true := allowedJ
    simp [parameter,flag]
  · have flag : e.2=false := by simpa only [allowed,zero,decide_false] using allowedJ
    simp only [parameter,flag,Bool.false_eq_true,ite_false]
    exact unaryExport_memory (program selector width clock operation).bank 23 store heads memory j
      (unitSymbol selector) (by omega) exported represented position

theorem compile_run {n ticks : ℕ} {bits : BitString} {result : Outcome Event}
    (execution : (program selector width clock operation).Executes n bits
      (program selector width clock operation).initialConfiguration ticks result) :
    ∃nativeTicks≤1+(2*ticks+1)*(4*ticks+4),
      (machine selector width clock operation).run (generatorData n) bits nativeTicks=.halted result := by
  letI := alphabetFintype selector
  letI := controlFintype selector width clock operation
  exact (program selector width clock operation).run_compiled execution

theorem machine_runs_success (n failures : ℕ) (bits : BitString)
    (header : List Bool) (requests : List Request) (choice : Choice operation n header requests)
    (enough : (failures+1)*width n≤bits.length)
    (failed : ∀ k<failures,reference selector clock n ((bits.drop (k*width n)).take (width n))=none)
    (accepted : reference selector clock n ((bits.drop (failures*width n)).take (width n))=some header) :
    ∃ticks≤25*(primitiveCoefficient selector width clock n)^2*(failures+1)^2,
      (machine selector width clock operation).run (generatorData n) bits ticks=
        .halted (.accepted ((eventList requests).map Prod.fst)) := by
  obtain ⟨stackTicks,bound,next,run,output,_,_⟩ := command_runs_success selector width clock operation n 0 failures bits
    header requests choice (by simpa using enough) (by simpa using failed) (by simpa using accepted)
  obtain ⟨ticks,compiler,native⟩ := compile_run selector width clock operation (run.executes 0)
  have budget := Machine.retry_compiler_cost_le stackTicks (primitiveCoefficient selector width clock n) failures
    ((primitiveCoefficient selector width clock).positive n) bound
  exact ⟨ticks,compiler.trans budget,by simpa only [Result.outcome,output] using native⟩

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
