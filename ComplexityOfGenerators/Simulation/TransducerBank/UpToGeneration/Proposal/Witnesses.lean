import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.SelectionWitnesses
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Runs

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

 theorem witness_aux (n : ℕ) (front target : Word α) (capacity : front.length+target.length≤n) :
    ∃ coins ticks,∀ prefixBits suffix,
      (bank B fallback).RegionSteps (generatorData n) (prefixBits++coins++suffix) n
        (configuration B fallback front prefixBits.length front.length .guess) ticks
        (configuration B fallback (front++target) (prefixBits.length+coins.length) 0 (.fetch B.initial)) := by
  induction target generalizing front with
  | nil =>
      have within : front.length≤n := by simpa using capacity
      by_cases active : 0<Fintype.card α ∧ front.length<n
      · let firstSymbol : Fin (Fintype.card α) := ⟨0,active.1⟩
        refine ⟨[false],1+(front.length+1),?_⟩
        intro prefixBits suffix
        have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback front prefixBits.length front.length .guess)=
            .readRandom .guessRewind (.symbol firstSymbol) := by
          simp [TapeBank.instruction,configuration,bank,generatorData,active.1,active.2,firstSymbol]
        have first := random_step B fallback n (prefixBits++[false]++suffix) front prefixBits.length front.length
          .guess .guessRewind (.symbol firstSymbol) false within table (by simp [List.append_assoc])
        have rest := rewind_region B fallback n (prefixBits++[false]++suffix) front (prefixBits.length+1) front.length within
        simpa using first.trans _ rest
      · refine ⟨[],1+(front.length+1),?_⟩
        intro prefixBits suffix
        simpa using forced_stop B fallback n (prefixBits++suffix) front prefixBits.length within active
  | cons value target ih =>
      have within : front.length≤n := by simp only [List.length_cons] at capacity;omega
      have live : front.length<n := by simp only [List.length_cons] at capacity;omega
      have alphabet : 0<Fintype.card α := Fintype.card_pos_iff.mpr ⟨value⟩
      let firstSymbol : Fin (Fintype.card α) := ⟨0,alphabet⟩
      let chosen : Fin (Fintype.card α) := (Fintype.equivFin α) value
      have chosenLetter : letter chosen=value := by simp [chosen,letter]
      obtain ⟨symbolCoins,symbolTicks,choose⟩ := select_witness B fallback n front within value
      obtain ⟨tailCoins,tailTicks,support⟩ := ih (front++[value]) (by simp only [List.length_append,List.length_cons,List.length_nil] at capacity ⊢;omega)
      refine ⟨true::(symbolCoins++tailCoins),1+symbolTicks+1+tailTicks,?_⟩
      intro prefixBits suffix
      let allBits := prefixBits++(true::(symbolCoins++tailCoins))++suffix
      have table : (bank B fallback).instruction (generatorData n)
          (configuration B fallback front prefixBits.length front.length .guess)=
          .readRandom .guessRewind (.symbol firstSymbol) := by
        simp [TapeBank.instruction,configuration,bank,generatorData,alphabet,live,firstSymbol]
      have first := random_step B fallback n allBits front prefixBits.length front.length
        .guess .guessRewind (.symbol firstSymbol) true within table (by simp [allBits,List.append_assoc])
      have selected : (bank B fallback).RegionSteps (generatorData n) allBits n
          (configuration B fallback front (prefixBits.length+1) front.length (.symbol firstSymbol)) symbolTicks
          (configuration B fallback front (prefixBits.length+1+symbolCoins.length) front.length (.writeLetter chosen)) := by
        simpa [allBits,List.append_assoc,firstSymbol,chosen] using choose (prefixBits++[true]) (tailCoins++suffix)
      have written := write_letter B fallback n allBits front (prefixBits.length+1+symbolCoins.length) chosen live
      rw [chosenLetter] at written
      have rest : (bank B fallback).RegionSteps (generatorData n) allBits n
          (configuration B fallback (front++[value]) (prefixBits.length+1+symbolCoins.length) (front.length+1) .guess)
          tailTicks
          (configuration B fallback (front++value::target) (prefixBits.length+(true::(symbolCoins++tailCoins)).length) 0 (.fetch B.initial)) := by
        simpa [allBits,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using support (prefixBits++[true]++symbolCoins) suffix
      exact ((first.trans _ selected).trans _ written).trans _ rest

/-- Every word of length at most n has a finite proposal prefix, with any
further source choices left unread at the fresh-source handoff. -/
theorem complete (n : ℕ) (word : Word α) (within : word.length≤n) :
    ∃ coins ticks,∀ suffix,
      (bank B fallback).RegionSteps (generatorData n) (coins++suffix) n
        {(bank B fallback).initialConfiguration with state:=.guess} ticks
        (UpToGeneration.configuration B fallback word coins.length B.initialConfiguration) := by
  obtain ⟨coins,ticks,support⟩ := witness_aux B fallback n [] word (by simpa using within)
  refine ⟨coins,ticks,?_⟩
  intro suffix
  rw [initial_configuration]
  simpa only [List.nil_append,List.length_nil,Nat.zero_add,source_configuration] using support [] suffix

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
