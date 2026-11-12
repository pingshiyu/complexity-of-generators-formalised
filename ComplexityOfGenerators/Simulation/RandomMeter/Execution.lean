import ComplexityOfGenerators.Simulation.RandomMeter.Basic
import ComplexityOfGenerators.Foundations.ExecutionPaths

namespace ComplexityOfGenerators.Simulation.RandomMeter
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

theorem random_path (data : InputData I A) (c : Configuration M)
    (no yes : Fin M.states) (action : M.transition c.state data.input[c.inputHead]?
      data.auxiliary[c.auxiliaryHead]? (if c.indexHead<data.index then some () else none)
      (c.work c.workHead)=.readRandom no yes)
    (lead : BitString) (bit : Bool) (tail : BitString) :
    (raw M).Steps data (lead++bit::tail) (configuration M c lead.length) 1
      (configuration M {c with state:=if bit then yes else no,randomHead:=0} (lead.length+1)) := by
  apply Machine.Steps.tail (.refl)
  have lookup : (lead++bit::tail)[lead.length]?=some bit := by simp
  simp only [Machine.next,raw,configuration,Equiv.symm_apply_apply,action,direct,lookup]
  cases bit <;> rfl

theorem ordinary_path (data : InputData I A) (c : Configuration M)
    (next : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead)=
      .step next write work input auxiliary index emit)
    (lead : BitString) (bit : Bool) (tail : BitString) :
    (raw M).Steps data (lead++bit::tail) (configuration M c lead.length) 2
      (configuration M (M.stepConfiguration data c next write work input auxiliary index emit) (lead.length+1)) := by
  let middle := configuration M c (lead.length+1) true
  have lookup : (lead++bit::tail)[lead.length]?=some bit := by simp
  have ignored : (raw M).next data (lead++bit::tail) (configuration M c lead.length)=.running middle := by
    simp only [Machine.next,raw,configuration,Equiv.symm_apply_apply,action,lookup]
    cases bit <;> rfl
  have executed : (raw M).next data (lead++bit::tail) middle=.running
      (configuration M (M.stepConfiguration data c next write work input auxiliary index emit) (lead.length+1)) := by
    simp only [Machine.next,raw,middle,configuration,Equiv.symm_apply_apply,action,direct]
    cases write <;> cases emit <;> rfl
  exact (Machine.Steps.tail (.refl) ignored).tail executed

/-- Every finite random tape provides a linear native execution budget. -/
theorem runFrom_value (data : InputData I A) (c : Configuration M)
    (lead bits : BitString) :
    ∃ ticks,ticks≤2*bits.length ∧
      (raw M).runFrom data (lead++bits) (configuration M c lead.length) ticks=
        .halted (value M data c bits) := by
  induction bits generalizing c lead with
  | nil =>
      refine ⟨0,by simp,?_⟩
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) <;>
        simp [Machine.runFrom,Machine.observe,raw,configuration,action,direct,value]
  | cons bit tail ih =>
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | accept => exact ⟨0,by omega,by simp [Machine.runFrom,Machine.observe,raw,configuration,action,direct,value]⟩
      | reject => exact ⟨0,by omega,by simp [Machine.runFrom,Machine.observe,raw,configuration,action,direct,value]⟩
      | readRandom no yes =>
          let finish : Configuration M := {c with state:=if bit then yes else no,randomHead:=0}
          obtain ⟨ticks,bound,run⟩ := ih finish (lead++[bit])
          have tailRun : (raw M).runFrom data (lead++bit::tail)
              (configuration M finish (lead.length+1)) ticks=.halted (value M data finish tail) := by
            simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using run
          have path := random_path M data c no yes action lead bit tail
          refine ⟨1+ticks,by simp only [List.length_cons];omega,?_⟩
          rw [(raw M).runFrom_add data (lead++bit::tail) _ _ 1 path.runFrom ticks]
          simpa only [value,action] using tailRun
      | step next write work input auxiliary index emit =>
          let finish := M.stepConfiguration data c next write work input auxiliary index emit
          obtain ⟨ticks,bound,run⟩ := ih finish (lead++[bit])
          have tailRun : (raw M).runFrom data (lead++bit::tail)
              (configuration M finish (lead.length+1)) ticks=.halted (value M data finish tail) := by
            simpa only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] using run
          have path := ordinary_path M data c next write work input auxiliary index emit action lead bit tail
          refine ⟨2+ticks,by simp only [List.length_cons];omega,?_⟩
          rw [(raw M).runFrom_add data (lead++bit::tail) _ _ 2 path.runFrom ticks]
          simpa only [value,action] using tailRun

theorem raw_run (data : InputData I A) (bits : BitString) :
    (raw M).run data bits (2*bits.length)=.halted (value M data M.initialConfiguration bits) := by
  obtain ⟨ticks,bound,run⟩ := runFrom_value M data M.initialConfiguration [] bits
  simp only [List.nil_append,List.length_nil,configuration_initial,Machine.runFrom_initial] at run
  have padded := (raw M).run_halted_add data bits ticks _ run (2*bits.length-ticks)
  simpa only [Nat.add_sub_of_le bound] using padded

theorem run (data : InputData I A) (bits : BitString) :
    (machine M).run data bits (3*bits.length)=
      .halted (rejectDrainOutcome (value M data M.initialConfiguration bits)) := by
  have execution := rejectDrain_run_halted (raw M) data bits (2*bits.length) _ (raw_run M data bits)
  simpa only [machine,show 2*bits.length+bits.length=3*bits.length by omega] using execution

end
end ComplexityOfGenerators.Simulation.RandomMeter
