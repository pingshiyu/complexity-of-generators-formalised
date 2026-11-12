import ComplexityOfGenerators.Simulation.BoundedHeaderCertification.Views

namespace ComplexityOfGenerators.Simulation.BoundedHeaderCertification
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem header_bound (tag : Bool) (s : Store M) (cap : ℕ) (sizes : StoreBound s cap)
    (index : (s 22).length+1≤cap) :
    StoreBound ((header M tag).eval s) cap ∧ (header M tag).cost s≤20*cap+5 := by
  constructor
  · rw [header_eval]
    exact (sizes.clear 33).update 31 _ (by simpa using index)
  · have a:=sizes 22
    have b:=sizes 31
    have c:=sizes 33
    simp only [header,Routine.seq,Routine.assign_cost,Routine.ofLocal,Local.push,Local.ticks]
    omega

theorem finish_bound (tag : Bool) (s : Store M) (cap : ℕ) (sizes : StoreBound s cap)
    (index : (s 22).length+1≤cap) :
    StoreBound ((finish M tag).eval s) cap ∧ (finish M tag).cost s≤30*cap+12 := by
  unfold finish
  simp only [Routine.branch]
  split
  · obtain ⟨headerSize,headerCost⟩ := header_bound M tag s cap sizes index
    obtain ⟨flagSize,flagCost⟩ := UnionGenerator.flag_bound M M 32 true _ cap headerSize (by omega)
    exact ⟨flagSize,by simp only [Routine.seq,flag,Routine.mapOutput]; omega⟩
  · obtain ⟨flagSize,flagCost⟩ := UnionGenerator.flag_bound M M 32 false _ cap (sizes.clear 31) (by omega)
    exact ⟨flagSize,by simp only [Routine.seq,Routine.clear,flag,Routine.mapOutput]; have:=sizes 31; omega⟩

theorem phase_bound (tag : Bool) (seed clock : PolynomialBound) :
    FixedBlockRetry.PhaseBound Symbol.bit seed (BoundedMachinePhase.cap seed clock)
      (BoundedMachinePhase.time M seed clock) (phase M tag seed clock) := by
  intro n block s length _ master random sizes
  let r := (prepare M).eval s
  have lower := BoundedMachinePhase.cap_lower seed clock n
  obtain ⟨rSize,rCost⟩ := BoundedMachinePhase.prepare_bound M s _ sizes
  have ri : r 11=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have ra : r 12=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have re : r 14=[] := by simp [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have rn : (r 13).length=n := by simpa [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using master
  have rr : r 17=block.map Symbol.bit := by simpa [r,prepare,Routine.mapOutput,BoundedMachinePhase.prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using random
  obtain ⟨sourceSize,_,sourceCost⟩ :=
    BoundedSource.sourceTrial_bound (O := α) Symbol.unit Symbol.bit M Symbol.left (UnionGenerator.leftDecode M M)
      (fun _=>rfl) (fun _=>.left .unit) (fun _=>.left .unit) (UnionGenerator.leftBit M M) (fun _=>rfl)
      seed clock r (generatorData n) block
      (by simp [ri,generatorData]) (by simp [ra,generatorData]) rn rr re _ rSize
      (by simpa [generatorData] using (by omega : n+1≤BoundedMachinePhase.cap seed clock n))
      (by simpa [generatorData] using (by omega : seed n≤BoundedMachinePhase.cap seed clock n))
      (by simpa [generatorData] using (by omega : clock n+1≤BoundedMachinePhase.cap seed clock n))
      (by simpa [generatorData] using (by omega : 1+n+seed n+3*(clock n+1)≤BoundedMachinePhase.cap seed clock n))
  have sourceMaster : ((trial M seed clock).eval r 22).length=n := by
    have fixed := ConcatenationGenerator.sourceTrial_fixes_outer M M M Symbol.left
      (UnionGenerator.leftDecode M M) (fun _=>.left .unit) (fun _=>.left .unit)
      (UnionGenerator.leftBit M M) seed clock 22 (by decide) r
    change (trial M seed clock).eval r 22=r 22 at fixed
    rw [fixed]
    exact (congrArg List.length (BoundedMachinePhase.prepare_fixes22 M s)).trans master
  obtain ⟨finalSize,finalCost⟩ := finish_bound M tag _ _ sourceSize (by
    change ((trial M seed clock).eval r 22).length+1≤_
    rw [sourceMaster]
    omega)
  refine ⟨finalSize,?_⟩
  apply le_trans _ (BoundedMachinePhase.time_lower M seed clock n)
  change (UnionGenerator.leftTrial M M seed clock).cost r≤_ at sourceCost
  change (finish M tag).cost ((UnionGenerator.leftTrial M M seed clock).eval r)≤_ at finalCost
  change (BoundedMachinePhase.prepare M).cost s+1+((UnionGenerator.leftTrial M M seed clock).cost r+1+
    (finish M tag).cost ((UnionGenerator.leftTrial M M seed clock).eval r))≤_
  simp only [generatorData,Nat.add_mul,Nat.mul_add] at sourceCost ⊢
  omega

end
end ComplexityOfGenerators.Simulation.BoundedHeaderCertification
