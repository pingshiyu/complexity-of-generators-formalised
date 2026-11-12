import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Selection

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

 theorem select_witness_aux (distance n : ℕ) (word : Word α) (within : word.length≤n)
    (target position : Fin (Fintype.card α)) (reaches : position.val+distance=target.val) :
    ∃ coins ticks,∀ prefixBits suffix,
      (bank B fallback).RegionSteps (generatorData n) (prefixBits++coins++suffix) n
        (configuration B fallback word prefixBits.length word.length (.symbol position)) ticks
        (configuration B fallback word (prefixBits.length+coins.length) word.length (.writeLetter target)) := by
  induction distance generalizing position with
  | zero =>
      have same : position=target := Fin.ext (by omega)
      subst position
      by_cases more : target.val+1<Fintype.card α
      · let next : Fin (Fintype.card α) := ⟨target.val+1,more⟩
        refine ⟨[false],1,?_⟩
        intro prefixBits suffix
        have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback word prefixBits.length word.length (.symbol target))=
            .readRandom (.writeLetter target) (.symbol next) := by
          simp [TapeBank.instruction,configuration,bank,more,next]
        have path := random_step B fallback n (prefixBits++[false]++suffix) word prefixBits.length word.length
          (.symbol target) (.writeLetter target) (.symbol next) false within table (by simp [List.append_assoc])
        simpa using path
      · refine ⟨[],1,?_⟩
        intro prefixBits suffix
        have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback word prefixBits.length word.length (.symbol target))=
            .step (.writeLetter target) (wordTape B word word.length) .stay .stay .stay .stay none := by
          simp [TapeBank.instruction,configuration,bank,more]
        simpa only [List.append_nil,List.nil_append,List.length_nil,Nat.add_zero] using go_last B fallback n (prefixBits++suffix) word prefixBits.length word.length
          (.symbol target) (.writeLetter target) within rfl table
  | succ distance ih =>
      have more : position.val+1<Fintype.card α := by omega
      let next : Fin (Fintype.card α) := ⟨position.val+1,more⟩
      obtain ⟨coins,ticks,support⟩ := ih next (by dsimp [next];omega)
      refine ⟨true::coins,1+ticks,?_⟩
      intro prefixBits suffix
      have table : (bank B fallback).instruction (generatorData n)
          (configuration B fallback word prefixBits.length word.length (.symbol position))=
          .readRandom (.writeLetter position) (.symbol next) := by
        simp [TapeBank.instruction,configuration,bank,more,next]
      have first := random_step B fallback n (prefixBits++(true::coins)++suffix) word prefixBits.length word.length
        (.symbol position) (.writeLetter position) (.symbol next) true within table (by simp [List.append_assoc])
      have rest := support (prefixBits++[true]) suffix
      have rest' : (bank B fallback).RegionSteps (generatorData n) (prefixBits++(true::coins)++suffix) n
          (configuration B fallback word (prefixBits.length+1) word.length (.symbol next)) ticks
          (configuration B fallback word (prefixBits.length+(true::coins).length) word.length (.writeLetter target)) := by
        simpa [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using rest
      exact first.trans _ rest'

/-- Every alphabet symbol has a finite selector witness, independent of all
coins before and after this bounded selection. -/
theorem select_witness (n : ℕ) (word : Word α) (within : word.length≤n) (value : α) :
    ∃ coins ticks,∀ prefixBits suffix,
      (bank B fallback).RegionSteps (generatorData n) (prefixBits++coins++suffix) n
        (configuration B fallback word prefixBits.length word.length
          (.symbol ⟨0,Fintype.card_pos_iff.mpr ⟨value⟩⟩)) ticks
        (configuration B fallback word (prefixBits.length+coins.length) word.length
          (.writeLetter ((Fintype.equivFin α) value))) :=
  select_witness_aux B fallback ((Fintype.equivFin α) value).val n word within
    ((Fintype.equivFin α) value) ⟨0,Fintype.card_pos_iff.mpr ⟨value⟩⟩ (by simp)

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
