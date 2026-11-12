import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Canonical

namespace ComplexityOfGenerators.Simulation.CertifiedStarPhase
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

def mappedCommand : Command (Cell M) α 35 :=
  (StarPaths.pathRoutine (O := α)).command.mapSymbols (encodePath M) (projectPath M)

/-- A total native routine, rather than a conditional assumed embedding.
Its actual prefix establishes the canonical alphabet invariant on all stores. -/
def pathStage : Step M where
  command := (canonicalPrepare M).command.seq (mappedCommand M)
  eval := fun s => Local.mapStore (encodePath M) ((StarPaths.pathRoutine (O := α)).eval (pathInput M s))
  cost := fun s => (canonicalPrepare M).cost s+1+(StarPaths.pathRoutine (O := α)).cost (pathInput M s)
  runs bits ambient index := by
    obtain ⟨firstTicks,firstBound,firstRun⟩ := (canonicalPrepare M).runs bits ambient index
    let initial : Memory StarPaths.Symbol α 35 :=
      ⟨(),ambient.indexHead,ambient.randomHead,ambient.output,pathInput M ambient.store⟩
    obtain ⟨lastTicks,lastBound,lastRun⟩ := (StarPaths.pathRoutine (O := α)).runs bits initial index
    have mappedRun := lastRun.mapSymbols (encodePath M) (projectPath M) (project_encode M)
    have initialEq : initial.mapSymbols (encodePath M) =
        {ambient with store := (canonicalPrepare M).eval ambient.store} := by
      apply Configuration.ext <;> try rfl
      exact (canonicalPrepare_eval M ambient.store).symm
    have finalEq : Memory.mapSymbols (encodePath M)
        ({initial with store := (StarPaths.pathRoutine (O := α)).eval initial.store} : Memory StarPaths.Symbol α 35) =
        {ambient with store := Local.mapStore (encodePath M) ((StarPaths.pathRoutine (O := α)).eval (pathInput M ambient.store))} := by
      apply Configuration.ext <;> rfl
    change (mappedCommand M).Runs _ bits (initial.mapSymbols (encodePath M)) lastTicks
      (.done (Memory.mapSymbols (encodePath M)
        ({initial with store := (StarPaths.pathRoutine (O := α)).eval initial.store} : Memory StarPaths.Symbol α 35))) at mappedRun
    rw [initialEq,finalEq] at mappedRun
    refine ⟨firstTicks+1+lastTicks,?_,?_⟩
    · exact Nat.add_le_add (Nat.add_le_add_right firstBound 1) lastBound
    · exact Command.Runs.seq _ _ _ _ _ _ _ firstRun mappedRun

theorem pathInput_master (s : Store M) : (pathInput M s 22).length = (s 22).length := by simp [pathInput]

theorem pathStage_frame (s : Store M) : ((pathStage M).eval s 22).length = (s 22).length := by
  change (((StarPaths.pathRoutine (O := α)).eval (pathInput M s) 22).map (encodePath M)).length = (s 22).length
  rw [List.length_map]
  rw [StarPaths.pathRoutine_frame 22 (by simp)]
  exact pathInput_master M s

/-- On the prepared certification cache and supplied bit word, the mapped
native path selector has exactly the small-alphabet selector's semantics. -/
theorem pathStage_value (flags bits : List Bool) (s : Store M) (n : ℕ)
    (source : s 25 = StarCertification.cacheWord M flags) (coins : s 17 = bits.map (bitSymbol M))
    (size : (s 22).length = n) :
    (pathStage M).eval s 31 = (StarPaths.held (StarPaths.selected flags n bits)).map (encodePath M) ∧
      (pathStage M).eval s 32 = (StarPaths.flagWord (StarPaths.selected flags n bits).isSome).map (encodePath M) := by
  have sourceInput : pathInput M s 25 = StarPaths.flagsWord flags := by
    simp [pathInput,source,StarCertification.cacheWord,StarCertification.flagSymbol,StarPaths.flagsWord,
      List.map_map,Function.comp_def,projectPath]
  have coinsInput : pathInput M s 17 = bits.map StarPaths.coinSymbol := by
    simp [pathInput,coins,bitSymbol,encodePath,List.map_map,Function.comp_def,projectPath]
  have sizeInput : (pathInput M s 22).length = n := (pathInput_master M s).trans size
  have result := StarPaths.pathRoutine_value (O := α) flags bits n (pathInput M s) sourceInput coinsInput sizeInput
  exact ⟨congrArg (List.map (encodePath M)) result.1,congrArg (List.map (encodePath M)) result.2⟩

end ComplexityOfGenerators.Simulation.CertifiedStarPhase
