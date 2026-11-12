import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.NativeSplit
import ComplexityOfGenerators.Simulation.WordStack.ExhaustedCompilation

namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

/-- Every finite tape either exhausts before any call event, or selects a
concrete certified composition and enters the deterministic event suffix. -/
theorem machine_split_total (n : ℕ) (bits : BitString) :
    (∃ ticks last,
      (machine M p).Steps (generatorData n) bits (machine M p).initialConfiguration ticks last ∧
      last.output=[] ∧ (machine M p).observe (generatorData n) bits last=.halted .exhausted) ∨
    ∃ parts : List ℕ, parts.sum=n ∧ (∀ j∈parts,0<j) ∧ ExpectedStarGenerator.PathHit M p n ∧
      ∃ prefixTicks tailTicks tailStart last,
        (machine M p).Steps (generatorData n) bits (machine M p).initialConfiguration prefixTicks tailStart ∧
        tailStart.output=[] ∧
        (machine M p).NativeEventTrace (parameter M p) allowed (generatorData n) bits
          (parts.map (fun j=>((),j))) tailStart last ∧
        (machine M p).Steps (generatorData n) bits tailStart tailTicks last ∧
        last.randomHead=tailStart.randomHead ∧
        (machine M p).observe (generatorData n) bits last=.halted (.accepted (List.replicate parts.length ())) := by
  letI := alphabetFintype M
  letI := controlFintype M p
  obtain ⟨_,_,bootRun⟩ := boot_runs M n 0 bits
  obtain ⟨pathTicks,result,retryRun,post⟩ := pathRetry_runs_total M p n 0 bits
  cases result with
  | exhausted =>
      have pureRun := prelude_of_exhausted M p bootRun retryRun
      have execution := pureRun.compiled 0 (by simp [initialMemory])
      let A := (prelude M p).program 0
      let T := (events M).program 0
      let C := program M p
      have embedded : A.Embeds C Sum.inl := A.sequence_left T
      exact Or.inl (WordStack.Program.Executes.exhausted_native_of_embeds A C execution
        ((prelude_outputFree M p).noEmit 0) Sum.inl embedded rfl)
  | done after =>
      obtain ⟨origin,empty,sizes,parts,total,positive,path,hit⟩ := post
      obtain ⟨prefixTicks,tailTicks,tailStart,last,head,headEmpty,_,trace,tail,stable,terminal⟩ :=
        machine_split_selected M p n parts bits pathTicks after retryRun origin empty path sizes positive
      exact Or.inr ⟨parts,total,positive,hit,prefixTicks,tailTicks,tailStart,last,head,headEmpty,
        trace,tail,stable,terminal⟩

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
