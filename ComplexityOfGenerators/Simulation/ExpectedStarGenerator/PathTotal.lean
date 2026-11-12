import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.PathRetry
import ComplexityOfGenerators.Simulation.FixedBlockRetry.ValueProperties

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

def PathResult (n : ℕ) : Result (Cell M P) α 80 → Prop
  | .exhausted => True
  | .done after => after.indexHead = 0 ∧ after.output = [] ∧ (after.store 22).length = n ∧
      StoreBound after.store (CertifiedStarPhase.cap p n) ∧ ∃ parts : List ℕ,
        parts.sum = n ∧ (∀ j ∈ parts, 0 < j) ∧
        after.store 31 = ExpectedStarCalls.pathWord P (CertifiedStarPhase.encodePath M) parts

/-- A concrete complete coin block certifying some positive composition. -/
def PathHit (n : ℕ) : Prop := ∃ block : BitString,
  block.length=StarCertification.width p n ∧ ∃ payload,
    CertifiedStarPhase.value M p n block=some payload

theorem pathRetry_runs_total_with_hit (n : ℕ) (bits : BitString) (m : Memory (Cell M P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = [])
    (owned : ∀ i, m.store (outerSlots i) = (outerStore M n i).map Sum.inl)
    (sizes : StoreBound m.store (CertifiedStarPhase.cap p n)) :
    ∃ ticks result, (pathRetry M p P).Runs n bits m ticks result ∧ PathResult M p P n result ∧
      (match result with | .exhausted => True | .done _ => PathHit M p n) := by
  let start := startMemory M P n m
  let count := (bits.length-m.randomHead)/StarCertification.width p n
  obtain ⟨ticks, _, result, run, selected, finished, canonical, nextOrigin⟩ :=
    FixedBlockRetry.loop_runs_at_index_with_post
      (CertifiedStarPhase.unitSymbol M) (CertifiedStarPhase.bitSymbol M) (StarCertification.width p)
      (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p) (CertifiedStarPhase.routine M p)
      (CertifiedStarPhase.decodePath M) (CertifiedStarPhase.value M p)
      (CertifiedStarPhase.phase_correct M p) (CertifiedStarPhase.phase_bound M p) (CertifiedStarPhase.routine_frame M p)
      (Canonical M) (phase_canonical M p) (restored_canonical M)
      n count n bits start (startMemory_state M p P n m origin empty)
      (by simp [start, startMemory, outerStore]) le_rfl (outer_indexBudget p n) (outer_widthBudget p n) rfl
  have lifted := pathRetry_lift M p P owned run
  cases result with
  | exhausted => exact ⟨ticks, .exhausted, lifted, trivial, trivial⟩
  | done inner =>
      have state : FixedBlockRetry.State n (CertifiedStarPhase.cap p n) inner := finished.1
      have hit : FixedBlockRetry.scan (StarCertification.width p n) (CertifiedStarPhase.value M p n)
          count (bits.drop m.randomHead) = some ((inner.store 31).filterMap (CertifiedStarPhase.decodePath M)) := selected.symm
      obtain ⟨k, inside, source⟩ := FixedBlockRetry.scan_sound _ _ _ _ _ hit
      have budget : count*StarCertification.width p n≤bits.length-m.randomHead := Nat.div_mul_le_self _ _
      have blockBudget : (k+1)*StarCertification.width p n≤bits.length-m.randomHead :=
        (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt inside)).trans budget
      have remaining : StarCertification.width p n≤bits.length-m.randomHead-k*StarCertification.width p n := by
        simp only [Nat.add_mul,Nat.one_mul] at blockBudget
        omega
      have rawHit : PathHit M p n := by
        refine ⟨((bits.drop m.randomHead).drop (k*StarCertification.width p n)).take (StarCertification.width p n),
          ?_,_,source⟩
        simp only [List.length_take,List.length_drop]
        exact Nat.min_eq_left remaining
      obtain ⟨parts, valid, word⟩ := CertifiedStarPhase.value_sound M p n _ _ source
      have raw : inner.store 31 = (StarPaths.payload parts).map (CertifiedStarPhase.encodePath M) := by
        change ((inner.store 31).filterMap (CertifiedStarPhase.decodePath M)).map (CertifiedStarPhase.encodePath M) = inner.store 31 at canonical
        rw [word] at canonical
        exact canonical.symm
      let after := Memory.patch outerSlots (inner.mapSymbols Sum.inl) m
      have low (i : Fin 35) : after.store (outerSlots i) = (inner.store i).map Sum.inl := by
        simp [after, Memory.patch, Memory.mapSymbols, Local.mapStore]
      refine ⟨ticks, .done after, lifted, ?_, rawHit⟩
      refine ⟨nextOrigin.trans origin, state.output, ?_, ?_, parts, valid.1,
        fun j member => (valid.2 j member).1, ?_⟩
      · change (after.store (outerSlots 22)).length = _
        rw [low, List.length_map]
        exact state.master
      · intro k
        by_cases selected : ∃ i, outerSlots i = k
        · obtain ⟨i, rfl⟩ := selected
          rw [low, List.length_map]
          exact state.sizes i
        · have outside : ∀ i, k ≠ outerSlots i := by intro i same; exact selected ⟨i, same.symm⟩
          rw [show after.store k = m.store k from Memory.patchStore_outside outerSlots _ _ k outside]
          exact sizes k
      · change after.store (outerSlots 31) = _
        rw [low, raw]
        simp [ExpectedStarCalls.pathWord, ExpectedStarCalls.pathSymbol, List.map_map, Function.comp_def]

/-- The original interface is retained for clients that only need the path. -/
theorem pathRetry_runs_total (n : ℕ) (bits : BitString) (m : Memory (Cell M P) α 80)
    (origin : m.indexHead=0) (empty : m.output=[])
    (owned : ∀ i, m.store (outerSlots i)=(outerStore M n i).map Sum.inl)
    (sizes : StoreBound m.store (CertifiedStarPhase.cap p n)) :
    ∃ ticks result, (pathRetry M p P).Runs n bits m ticks result ∧ PathResult M p P n result := by
  obtain ⟨ticks,result,run,post,_⟩ := pathRetry_runs_total_with_hit M p P n bits m origin empty owned sizes
  exact ⟨ticks,result,run,post⟩

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
