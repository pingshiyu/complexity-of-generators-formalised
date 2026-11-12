import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Selection

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

 theorem forced_stop (n : ℕ) (bits : BitString) (word : Word α) (consumed : ℕ)
    (within : word.length≤n) (finished : ¬(0<Fintype.card α ∧ word.length<n)) :
    (bank B fallback).RegionSteps (generatorData n) bits n
      (configuration B fallback word consumed word.length .guess) (1+(word.length+1))
      (configuration B fallback word consumed 0 (.fetch B.initial)) := by
  have table : (bank B fallback).instruction (generatorData n)
      (configuration B fallback word consumed word.length .guess)=
      .step .guessRewind (wordTape B word word.length) .stay .stay .stay .stay none := by
    by_cases alphabet : 0<Fintype.card α
    · have endWord : ¬word.length<n := fun live=>finished ⟨alphabet,live⟩
      simp [TapeBank.instruction,configuration,bank,generatorData,alphabet,endWord]
    · simp [TapeBank.instruction,configuration,bank,generatorData,alphabet]
  exact (go_last B fallback n bits word consumed word.length .guess .guessRewind within rfl table).trans _
    (rewind_region B fallback n bits word consumed word.length within)

 theorem guess_runs_aux (remaining n : ℕ) (bits : BitString) (word : Word α) (consumed : ℕ)
    (within : word.length≤n) (available : consumed≤bits.length) (capacity : word.length+remaining=n) :
    ∃ ticks,ticks≤(Fintype.card α+5)*(remaining+1)+word.length ∧
      (Exhausts B fallback n bits (configuration B fallback word consumed word.length .guess) ticks ∨
        ∃ generated nextConsumed,generated.length≤n ∧ consumed≤nextConsumed ∧ nextConsumed≤bits.length ∧
          (bank B fallback).RegionSteps (generatorData n) bits n
            (configuration B fallback word consumed word.length .guess) ticks
            (configuration B fallback generated nextConsumed 0 (.fetch B.initial))) := by
  induction remaining generalizing word consumed with
  | zero =>
      refine ⟨1+(word.length+1),by nlinarith,Or.inr ⟨word,consumed,within,le_rfl,available,?_⟩⟩
      exact forced_stop B fallback n bits word consumed within (by omega)
  | succ remaining ih =>
      by_cases alphabet : 0<Fintype.card α
      · have live : word.length<n := by omega
        let firstSymbol : Fin (Fintype.card α) := ⟨0,alphabet⟩
        have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback word consumed word.length .guess)=
            .readRandom .guessRewind (.symbol firstSymbol) := by
          simp [TapeBank.instruction,configuration,bank,generatorData,alphabet,live,firstSymbol]
        cases lookup : bits[consumed]? with
        | none =>
            refine ⟨0,by omega,Or.inl ⟨_,.refl _ (bounded B fallback n word consumed word.length _ within),?_⟩⟩
            exact .exhausted _ _ _ table lookup
        | some bit =>
            have nextAvailable : consumed+1≤bits.length := by
              have bound := (List.getElem?_eq_some_iff.mp lookup).1
              omega
            cases bit with
            | false =>
                have first := random_step B fallback n bits word consumed word.length .guess .guessRewind
                  (.symbol firstSymbol) false within table lookup
                have back := rewind_region B fallback n bits word (consumed+1) word.length within
                refine ⟨1+(word.length+1),by nlinarith,Or.inr ⟨word,consumed+1,within,by omega,nextAvailable,?_⟩⟩
                exact first.trans _ back
            | true =>
                have first := random_step B fallback n bits word consumed word.length .guess .guessRewind
                  (.symbol firstSymbol) true within table lookup
                obtain ⟨selectedTicks,selectedCost,result⟩ :=
                  select_runs B fallback n bits word (consumed+1) firstSymbol within nextAvailable
                have selectedBound : selectedTicks≤Fintype.card α := by simpa [firstSymbol] using selectedCost
                rcases result with failure | ⟨chosen,afterChoice,lowerChoice,upperChoice,selection⟩
                · refine ⟨1+selectedTicks,?_,Or.inl (failure.prepend B fallback first)⟩
                  nlinarith
                · have writing := write_letter B fallback n bits word afterChoice chosen live
                  obtain ⟨afterTicks,afterCost,afterResult⟩ := ih (word++[letter chosen]) afterChoice
                    (by simp;omega) upperChoice (by simp;omega)
                  have before := (first.trans _ selection).trans _ writing
                  refine ⟨1+selectedTicks+1+afterTicks,?_,?_⟩
                  · simp only [List.length_append,List.length_singleton,Nat.mul_add,Nat.mul_one] at afterCost ⊢
                    omega
                  · rcases afterResult with failure | ⟨generated,nextConsumed,lengthBound,lower,upper,path⟩
                    · apply Or.inl
                      apply Exhausts.prepend B fallback _ before
                      simpa only [List.length_append,List.length_singleton] using failure
                    · refine Or.inr ⟨generated,nextConsumed,lengthBound,by omega,upper,?_⟩
                      exact before.trans _ (by simpa only [List.length_append,List.length_singleton] using path)
      · refine ⟨1+(word.length+1),by nlinarith,Or.inr ⟨word,consumed,within,le_rfl,available,?_⟩⟩
        exact forced_stop B fallback n bits word consumed within (by simp [alphabet])

/-- Every finite proposal either exhausts or reaches a fresh source with a
real candidate word of length at most the generator index. -/
theorem runs (n : ℕ) (bits : BitString) :
    ∃ ticks,ticks≤(Fintype.card α+10)*(n+1) ∧
      (Exhausts B fallback n bits {(bank B fallback).initialConfiguration with state:=.guess} ticks ∨
        ∃ word consumed,word.length≤n ∧ consumed≤bits.length ∧
          (bank B fallback).RegionSteps (generatorData n) bits n
            {(bank B fallback).initialConfiguration with state:=.guess} ticks
            (UpToGeneration.configuration B fallback word consumed B.initialConfiguration)) := by
  obtain ⟨ticks,cost,result⟩ := guess_runs_aux B fallback n n bits [] 0 (by simp) (by omega) (by simp)
  refine ⟨ticks,?_,?_⟩
  · simp only [List.length_nil,Nat.add_zero] at cost
    exact cost.trans (Nat.mul_le_mul_right _ (by omega))
  · rw [initial_configuration]
    rcases result with failure | ⟨word,consumed,lengthBound,lower,upper,path⟩
    · exact Or.inl failure
    · exact Or.inr ⟨word,consumed,lengthBound,upper,by simpa only [source_configuration,List.length_nil] using path⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
