import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Canonical

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] normalize canonicalPrepare

theorem normalize_bound (reg : Fin 35) (a : reg ≠ 33) (b : reg ≠ 34) (map : Cell M → Cell M)
    (s : Store M) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((normalize M reg a b map).eval s) budget ∧
      (normalize M reg a b map).cost s ≤ 40*(budget+1) := by
  constructor
  · rw [normalize_eval]
    exact ((sizes.clear 33).update reg _ (by simpa using sizes reg)).clear 34
  · have source := sizes reg
    have target := sizes 34
    have scratch := sizes 33
    simp [normalize,WordStack.Routine.seq,WordStack.Routine.assign_cost,
      WordStack.Routine.assign_eval,WordStack.Routine.clear,a,b,b.symm,a.symm]
    omega

theorem canonicalPrepare_bound (s : Store M) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((canonicalPrepare M).eval s) budget ∧ (canonicalPrepare M).cost s ≤ 250*(budget+1) := by
  let cleared := (WordStack.Routine.clearMany (S := Cell M) (O := α) StarPaths.owned).eval s
  let first := (normalize M 17 (by decide) (by decide) (fun value => encodePath M (projectPath M value))).eval cleared
  let second := (normalize M 25 (by decide) (by decide) (fun value => encodePath M (projectPath M value))).eval first
  have clearedBound : StoreBound cleared budget := sizes.clearMany StarPaths.owned
  have clearCost := WordStack.Routine.clearMany_cost (O := α) StarPaths.owned s budget (fun j _ => sizes j)
  have length : StarPaths.owned.length = 32 := by decide
  rw [length] at clearCost
  obtain ⟨firstSize,firstCost⟩ := normalize_bound M 17 (by decide) (by decide) _ cleared budget clearedBound
  obtain ⟨secondSize,secondCost⟩ := normalize_bound M 25 (by decide) (by decide) _ first budget firstSize
  obtain ⟨finalSize,finalCost⟩ := normalize_bound M 22 (by decide) (by decide) (fun _ => unitSymbol M) second budget secondSize
  constructor
  · unfold canonicalPrepare
    exact finalSize
  · unfold canonicalPrepare
    change (WordStack.Routine.clearMany (O := α) StarPaths.owned).cost s+1+
      ((normalize M 17 _ _ _).cost cleared+1+((normalize M 25 _ _ _).cost first+1+
        (normalize M 22 _ _ _).cost second)) ≤ _
    omega

end ComplexityOfGenerators.Simulation.CertifiedStarPhase
