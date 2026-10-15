import ComplexityOfGenerators.Simulation.CyclicGenerator.DecisionInterface
import ComplexityOfGenerators.Simulation.CyclicGenerator.Selection
import ComplexityOfGenerators.Simulation.CyclicGenerator.CounterOrder
import ComplexityOfGenerators.Simulation.CyclicGenerator.Load

/-! A common polynomial region for the cyclic generator's routines. It is
independent of the number of candidates, decisions, and declined offers. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem restart_inRegion (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (source : Configuration D) (geometry : D.TapeGeometry source)
    (input : source.inputHead ≤ word.length) (space : source.visited.card ≤ s) :
    ∃ ticks, (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      {decisionConfig D word seen random source with state := .eraseLeft seen} ticks
      {candidateConfig D word seen random 0 with state := .increment seen} := by
  obtain ⟨ticks, cost, path⟩ := restart_steps D word seen random s bits source geometry input space
  have bound := decisionConfig_bounded D word seen random s source input
    (show source.workHead.natAbs ≤ s by have := geometry.workHead_bound D; omega)
  exact ⟨ticks, (path.inRegion (bank D) (word.length + s) (bound.with_state (bank D) _)).mono (bank D) (by unfold radius; omega)⟩

theorem select_word_inRegion (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (source : Configuration D) (input : source.inputHead ≤ word.length) (work : source.workHead.natAbs ≤ s)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) (coin : bits[random]? = some false) :
    (bank D).RegionRun (generatorData word.length) bits (radius word.length s)
      (decisionConfig D word seen random source) (.accepted word) :=
  ((select_word D word seen random bits source accepts coin).inRegion (bank D)
    (decisionConfig_bounded D word seen random s source input work)).mono (bank D) (by unfold radius; omega)

theorem reject_word_inRegion (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (source : Configuration D) (input : source.inputHead ≤ word.length) (work : source.workHead.natAbs ≤ s)
    (rejects : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .reject) :
    (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      (decisionConfig D word seen random source) 1
      {decisionConfig D word seen random source with state := .eraseLeft seen} :=
  ((reject_word D word seen random bits source rejects).inRegion (bank D) (word.length + s)
    (decisionConfig_bounded D word seen random s source input work)).mono (bank D) (by unfold radius; omega)

theorem decline_word_inRegion (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (source : Configuration D) (input : source.inputHead ≤ word.length) (work : source.workHead.natAbs ≤ s)
    (accepts : D.transition source.state word[source.inputHead]? none none
      (source.work source.workHead) = .accept) (coin : bits[random]? = some true) :
    (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      (decisionConfig D word seen random source) 1
      {decisionConfig D word true (random + 1) source with state := .eraseLeft true} :=
  ((decline_word D word seen random bits source accepts coin).inRegion (bank D) (word.length + s)
    (decisionConfig_bounded D word seen random s source input work)).mono (bank D) (by unfold radius; omega)

theorem increment_inRegion (first : α) (least : firstLetter = some first)
    (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString) :
    let result := incrementWord first word
    (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      {candidateConfig D word seen random 0 with state := .increment seen}
      (result.position + if result.overflow then 0 else 1)
      {candidateConfig D result.word seen random result.position with
        state := if result.overflow then .increment seen else .wordStart seen} := by
  have cost := incrementWord_cost first word
  exact ((increment_candidate D first least word seen random bits).inRegion (bank D) word.length
    ((candidate_bounded D word seen random 0 (Nat.zero_le _)).with_state (bank D) _)).mono (bank D) (by unfold radius; omega)

/-- Exhaustion may consume arbitrarily many random bits but moves no work
head. Thus its space bound has no dependence on the length of the seed. -/
theorem drain_inRegion (n r : ℕ) (bits : BitString) (fuel : ℕ) (c : Config D)
    (table : (bank D).instruction (generatorData n) c = .readRandom .drain .drain)
    (bound : (bank D).Bounded (generatorData n) r c) (remaining : bits.length ≤ c.randomHead + fuel) :
    (bank D).RegionRun (generatorData n) bits r c .exhausted := by
  induction fuel generalizing c with
  | zero =>
      exact ⟨0, c, .refl c bound, .exhausted c .drain .drain table (List.getElem?_eq_none (by omega))⟩
  | succ fuel ih =>
      cases lookup : bits[c.randomHead]? with
      | none => exact ⟨0, c, .refl c bound, .exhausted c .drain .drain table lookup⟩
      | some bit =>
          let d := TransducerBank.TapeBank.choose c (Phase.drain : State D)
          have bounded : (bank D).Bounded (generatorData n) r d :=
            ⟨bound.input, bound.auxiliary, bound.index, bound.head⟩
          have rest := ih d (by simp [TransducerBank.TapeBank.instruction, d,
            TransducerBank.TapeBank.choose, bank, transition]) bounded (by
              change bits.length ≤ c.randomHead + 1 + fuel; omega)
          apply rest.prepend (bank D)
          exact .random c .drain .drain bit 0 d bound table lookup (by simpa using
            (TransducerBank.TapeBank.RegionSteps.refl d bounded (bits := bits)))

theorem empty_pass_inRegion (word : List α) (random s : ℕ) (bits : BitString) :
    (bank D).RegionRun (generatorData word.length) bits (radius word.length s)
      {candidateConfig D word false random word.length with state := .increment false} .exhausted := by
  apply drain_inRegion D _ _ bits bits.length
  · simp [TransducerBank.TapeBank.instruction, bank, select, transition, candidateConfig]
  · exact ((candidate_bounded D word false random word.length le_rfl).with_state (bank D) _).mono
      (bank D) (show word.length ≤ radius word.length s by unfold radius; omega)
  · change bits.length ≤ random + bits.length
    omega

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
