import ComplexityOfGenerators.Simulation.BoundedMachinePhase.Basic

/-! The actual bounded source routine stores only encoded output letters.
This strengthens the filtered-output specification where a later controller
must parse the stored word as a header. -/
namespace ComplexityOfGenerators.Simulation.BoundedMachinePhase
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def Canonical (s : Store M) : Prop := ∃ word : List α,s 31=word.map Symbol.letter

theorem Canonical.eq_of_filterMap {s : Store M} (canonical : Canonical M s) (word : List α)
    (decoded : (s 31).filterMap (UnionGenerator.outputLetter M M)=word) : s 31=word.map Symbol.letter := by
  obtain ⟨source,equal⟩ := canonical
  have same : source=word := by
    simpa only [equal,List.filterMap_map,UnionGenerator.outputLetter,Function.comp_def,List.filterMap_some] using decoded
  exact same ▸ equal

theorem phase_canonical (seed clock : PolynomialBound) (n : ℕ) (block : BitString) (s : Store M)
    (_length : block.length=seed n) (_index : (s 13).length=n) (master : (s 22).length=n)
    (random : s 17=block.map Symbol.bit) : Canonical M ((phase M seed clock).eval s) := by
  let r := (prepare M).eval s
  have ri : r 11=[] := by simp [r,prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have ra : r 12=[] := by simp [r,prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have re : r 14=[] := by simp [r,prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval]
  have rn : (r 13).length=n := by
    simpa [r,prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using master
  have rr : r 17=block.map Symbol.bit := by
    simpa [r,prepare,Routine.seq,Routine.assign_eval,Routine.clearMany_eval] using random
  obtain ⟨status,output,state,payload,_⟩ :=
    BoundedSource.sourceTrial_result (O := α) Symbol.unit Symbol.bit M Symbol.left (UnionGenerator.leftDecode M M)
      (fun _ => rfl) (fun _ => .left .unit) (fun _ => .left .unit) (UnionGenerator.leftBit M M) (fun _ => rfl)
      seed clock r (generatorData n) block
      (by simp [ri,generatorData]) (by simp [ra,generatorData]) rn rr re
  let t := (UnionGenerator.leftTrial M M seed clock).eval r
  change t 0=[.left (.state status)] at state
  change t 10=output.map (fun a => Symbol.left (Source.Cell.output a)) at payload
  change ∃ word : List α,((finish M).eval t) 31=word.map Symbol.letter
  cases status with
  | accepted =>
    exact ⟨output.reverse,by simp [finish,Routine.branch,Routine.seq,state,payload,
        UnionGenerator.takeOutput_eval,UnionGenerator.flag_eval,UnionGenerator.leftOutput,
        List.map_reverse,List.map_map,Function.comp_def]⟩
  | live q => exact ⟨[],by simp [finish,Routine.branch,Routine.seq,state,Routine.clear,UnionGenerator.flag_eval]⟩
  | rejected => exact ⟨[],by simp [finish,Routine.branch,Routine.seq,state,Routine.clear,UnionGenerator.flag_eval]⟩
  | exhausted => exact ⟨[],by simp [finish,Routine.branch,Routine.seq,state,Routine.clear,UnionGenerator.flag_eval]⟩

end
end ComplexityOfGenerators.Simulation.BoundedMachinePhase
