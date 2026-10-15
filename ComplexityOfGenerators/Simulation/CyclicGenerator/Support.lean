import ComplexityOfGenerators.Simulation.CyclicGenerator.Advance
import ComplexityOfGenerators.Simulation.CyclicGenerator.Compiled

/-! Every accepted word can be selected by a finite seed. Earlier accepted
candidates are declined, rejected candidates consume no randomness, and the
target is selected with a final false bit. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem candidate_support (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (target : List α) (targetLength : target.length = n) (accepts : D.Accepts (decisionData target) [])
    (word : List α) (length : word.length = n) (before : wordRank word ≤ wordRank target)
    (seen : Bool) (position : ℕ) (positionBound : position ≤ n) (front : BitString) :
    ∃ tail : BitString, false ∈ tail ∧
      (bank D).RegionRun (generatorData n) (front ++ tail) (radius n s)
        (candidateConfig D word seen front.length position) (.accepted target) := by
  generalize distance_eq : wordRank target - wordRank word = distance
  induction distance generalizing word seen position front with
  | zero =>
      have same : word = target := wordRank_injective_of_length (length.trans targetLength.symm) (by omega)
      subst word
      refine ⟨[false], by simp, ?_⟩
      have run := select_candidate D deterministic target seen front.length position s (front ++ [false])
        (by omega) (halts target targetLength) (space target targetLength) accepts (by simp)
      simpa only [targetLength] using run
  | succ distance ih =>
      have strict : wordRank word < wordRank target := by omega
      obtain ⟨overflow, rank⟩ := incrementWord_before first least word target
        (length.trans targetLength.symm) strict
      let next := incrementWord first word
      have nextLength : next.word.length = n := (incrementWord_length first word).trans length
      have nextBefore : wordRank next.word ≤ wordRank target := by dsimp [next]; omega
      have nextPosition : next.position ≤ n := by have := incrementWord_cost first word; dsimp [next]; omega
      have nextDistance : wordRank target - wordRank next.word = distance := by dsimp [next]; omega
      by_cases currentAccepts : D.Accepts (decisionData word) []
      · obtain ⟨tail, stop, run⟩ := ih next.word nextLength nextBefore true next.position nextPosition
          (front ++ [true]) nextDistance
        refine ⟨true :: tail, by simp [stop], ?_⟩
        obtain ⟨ticks, skip⟩ := skip_declined_candidate D first least deterministic word seen front.length
          position s (front ++ true :: tail) (by omega) (halts word length) (space word length)
          currentAccepts (by simp) overflow
        rw [length] at skip
        have run' : (bank D).RegionRun (generatorData n) (front ++ true :: tail) (radius n s)
            (candidateConfig D next.word true (front.length + 1) next.position) (.accepted target) := by
          simpa [List.append_assoc] using run
        exact run'.prepend (bank D) skip
      · obtain ⟨tail, stop, run⟩ := ih next.word nextLength nextBefore seen next.position nextPosition
          front nextDistance
        refine ⟨tail, stop, ?_⟩
        obtain ⟨ticks, skip⟩ := skip_rejected_candidate D first least deterministic word seen front.length
          position s (front ++ tail) (by omega) (halts word length) (space word length) currentAccepts overflow
        rw [length] at skip
        exact run.prepend (bank D) skip

theorem machine_output_complete (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (word : List α) (length : word.length = n) (accepts : D.Accepts (decisionData word) []) :
    word ∈ (machine D).generatedLanguage (generatorData n) := by
  obtain ⟨bits, stop, run⟩ := candidate_support D first least deterministic n s halts space word length accepts
    (List.replicate n first) (by simp) (by simp [wordRank_replicate first least]) false n le_rfl []
  simp only [List.nil_append, List.length_nil] at run
  have load := ((load_initial D first least n bits).inRegion (bank D) 0
    ((bank D).initial_bounded (generatorData n))).mono (bank D)
      (show 0 + (n + 1) ≤ radius n s by unfold radius; omega)
  have whole := run.prepend (bank D) load
  obtain ⟨ready, related, boot, region⟩ := TransducerBank.bank_loaded_inRegion (bank D)
    (generatorData n) bits (radius n s)
  obtain ⟨ticks, finish, path, terminal, _⟩ := whole.compile (bank D) (fun _ => false) ready related region
  refine ⟨bits, ?_, 1 + ticks, ?_⟩
  · intro empty
    simp [empty] at stop
  · have wholePath : (machine D).Steps (generatorData n) bits (machine D).initialConfiguration
        (1 + ticks) finish := boot.trans (machine D) path
    have observed : (machine D).observe (generatorData n) bits finish = .halted (.accepted word) := terminal
    simpa [Machine.runFrom_initial, observed] using wholePath.runFrom (machine D)

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
