import ComplexityOfGenerators.Simulation.CyclicGenerator.RoutineSpace

/-! Advance between consecutive candidates within one enumeration pass. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem increment_no_overflow (first : α) (least : firstLetter = some first)
    (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (overflow : (incrementWord first word).overflow = false) :
    (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      {candidateConfig D word seen random 0 with state := .increment seen}
      ((incrementWord first word).position + 1)
      (candidateConfig D (incrementWord first word).word seen random (incrementWord first word).position) := by
  simpa [overflow, candidateConfig] using increment_inRegion D first least word seen random s bits

theorem skip_rejected_candidate (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (word : List α) (seen : Bool) (random position s : ℕ)
    (bits : BitString) (positionBound : position ≤ word.length)
    (halts : D.Halts (decisionData word) []) (space : D.SpaceBound (decisionData word) s)
    (rejects : ¬D.Accepts (decisionData word) []) (overflow : (incrementWord first word).overflow = false) :
    ∃ ticks, (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      (candidateConfig D word seen random position) ticks
      (candidateConfig D (incrementWord first word).word seen random (incrementWord first word).position) := by
  obtain ⟨ticks, terminal, test, geometry, visited, input, action, answer⟩ :=
    candidate_decision D deterministic word seen random position s bits positionBound halts space
  have rejected := action.resolve_left (fun accepted => rejects (answer.mp accepted))
  have work : terminal.workHead.natAbs ≤ s := by have := geometry.workHead_bound D; omega
  have reject := reject_word_inRegion D word seen random s bits terminal input work rejected
  obtain ⟨_, cleanup⟩ := restart_inRegion D word seen random s bits terminal geometry input visited
  exact ⟨_, ((test.trans (bank D) reject).trans (bank D) cleanup).trans (bank D)
    (increment_no_overflow D first least word seen random s bits overflow)⟩

theorem skip_declined_candidate (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (word : List α) (seen : Bool) (random position s : ℕ)
    (bits : BitString) (positionBound : position ≤ word.length)
    (halts : D.Halts (decisionData word) []) (space : D.SpaceBound (decisionData word) s)
    (accepts : D.Accepts (decisionData word) []) (coin : bits[random]? = some true)
    (overflow : (incrementWord first word).overflow = false) :
    ∃ ticks, (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      (candidateConfig D word seen random position) ticks
      (candidateConfig D (incrementWord first word).word true (random + 1) (incrementWord first word).position) := by
  obtain ⟨ticks, terminal, test, geometry, visited, input, _, answer⟩ :=
    candidate_decision D deterministic word seen random position s bits positionBound halts space
  have work : terminal.workHead.natAbs ≤ s := by have := geometry.workHead_bound D; omega
  have decline := decline_word_inRegion D word seen random s bits terminal input work (answer.mpr accepts) coin
  obtain ⟨_, cleanup⟩ := restart_inRegion D word true (random + 1) s bits terminal geometry input visited
  exact ⟨_, ((test.trans (bank D) decline).trans (bank D) cleanup).trans (bank D)
    (increment_no_overflow D first least word true (random + 1) s bits overflow)⟩

theorem select_candidate (deterministic : D.Deterministic)
    (word : List α) (seen : Bool) (random position s : ℕ) (bits : BitString)
    (positionBound : position ≤ word.length)
    (halts : D.Halts (decisionData word) []) (space : D.SpaceBound (decisionData word) s)
    (accepts : D.Accepts (decisionData word) []) (coin : bits[random]? = some false) :
    (bank D).RegionRun (generatorData word.length) bits (radius word.length s)
      (candidateConfig D word seen random position) (.accepted word) := by
  obtain ⟨ticks, terminal, test, geometry, visited, input, _, answer⟩ :=
    candidate_decision D deterministic word seen random position s bits positionBound halts space
  have work : terminal.workHead.natAbs ≤ s := by have := geometry.workHead_bound D; omega
  exact (select_word_inRegion D word seen random s bits terminal input work (answer.mpr accepts) coin).prepend
    (bank D) test

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
