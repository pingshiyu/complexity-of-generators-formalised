import ComplexityOfGenerators.Simulation.BoundedHeaderCertification.Basic

namespace ComplexityOfGenerators.Simulation.BoundedHeaderCertification
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem phase_fixes22 (tag : Bool) (seed clock : PolynomialBound) : (phase M tag seed clock).Fixes 22 := by
  intro s
  have trialFrame := ConcatenationGenerator.sourceTrial_fixes_outer M M M Symbol.left
    (UnionGenerator.leftDecode M M) (fun _ => .left .unit) (fun _ => .left .unit)
    (UnionGenerator.leftBit M M) seed clock 22 (by decide)
  have trial22 : (UnionGenerator.leftTrial M M seed clock).eval
      ((BoundedMachinePhase.prepare M).eval s) 22=(BoundedMachinePhase.prepare M).eval s 22 :=
    trialFrame _
  have prepared := BoundedMachinePhase.prepare_fixes22 M s
  change (finish M tag).eval ((UnionGenerator.leftTrial M M seed clock).eval
    ((BoundedMachinePhase.prepare M).eval s)) 22=s 22
  unfold finish
  simp only [Routine.branch]
  split <;> simp [Routine.seq,header_eval,flag_eval,Routine.clear,trial22,prepared]

theorem phase_correct (tag : Bool) (seed clock : PolynomialBound) :
    FixedBlockRetry.PhaseCorrect (Symbol.unit : Cell M) Symbol.bit (decode M)
      seed (phase M tag seed clock) (value M tag clock) := by
  intro n block s length _ master random
  let r := (prepare M).eval s
  have ri : r 11=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have ra : r 12=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have re : r 14=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have rn : (r 13).length=n := by simpa [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using master
  have rr : r 17=block.map Symbol.bit := by simpa [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using random
  obtain ⟨status,output,state,payload,native⟩ :=
    BoundedSource.sourceTrial_result (O := α) Symbol.unit Symbol.bit M Symbol.left (UnionGenerator.leftDecode M M)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit M M) (fun _ => rfl)
      seed clock r (generatorData n) block
      (by simp [ri,generatorData]) (by simp [ra,generatorData]) rn rr re
  change ∀ word,(status=.accepted ∧ output.reverse=word) ↔
    M.run (generatorData n) (block.take (seed n)) (clock n)=.halted (.accepted word) at native
  have whole : block.take (seed n)=block := by rw [←length,List.take_length]
  rw [whole] at native
  let t := (trial M seed clock).eval r
  change t 0=[.left (.state status)] at state
  have tm : (t 22).length=n := by
    have fixed := ConcatenationGenerator.sourceTrial_fixes_outer M M M Symbol.left
      (UnionGenerator.leftDecode M M) (fun _ => .left .unit) (fun _ => .left .unit)
      (UnionGenerator.leftBit M M) seed clock 22 (by decide) r
    change t 22=r 22 at fixed
    rw [fixed]
    exact (congrArg List.length (BoundedMachinePhase.prepare_fixes22 M s)).trans master
  have sourceValue : UnionGenerator.sourceValue M clock n block =
      (if status=.accepted then some output.reverse else none) := by
    apply Option.ext
    intro word
    rw [UnionGenerator.sourceValue_eq_some,←native]
    by_cases accepted : status=.accepted <;> simp [accepted]
  change ((finish M tag).eval t 32=FixedBlockRetry.flagWord Symbol.unit (value M tag clock n block).isSome ∧
    ∀ word,value M tag clock n block=some word → ((finish M tag).eval t 31).filterMap (decode M)=word)
  simp only [value,sourceValue]
  cases status <;>
    simp [finish,Routine.branch,Routine.seq,state,header_eval,flag_eval,Routine.clear,
      FixedBlockRetry.flagWord,UnionGenerator.flagWord,tm,decode,List.filterMap_replicate]

end
end ComplexityOfGenerators.Simulation.BoundedHeaderCertification
