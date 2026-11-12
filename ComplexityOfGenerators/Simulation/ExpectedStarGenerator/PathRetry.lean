import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Initialization

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

def Canonical (s : Local.Store (Outer M) 35) : Prop :=
  ((s 31).filterMap (CertifiedStarPhase.decodePath M)).map (CertifiedStarPhase.encodePath M) = s 31

theorem phase_canonical (n : ℕ) (block : BitString) (s : Local.Store (Outer M) 35)
    (_length : block.length = StarCertification.width p n) (_index : (s 13).length = n)
    (master : (s 22).length = n) (coins : s 17 = block.map (CertifiedStarPhase.bitSymbol M)) :
    Canonical M ((CertifiedStarPhase.routine M p).eval s) := by
  unfold Canonical
  rw [CertifiedStarPhase.routine_output M p n block s coins master]
  simp [List.filterMap_map, Function.comp_def]

theorem restored_canonical (s : Local.Store (Outer M) 35) (canonical : Canonical M s) :
    Canonical M ((FixedBlockRetry.restoreIndex (O := α) (CertifiedStarPhase.unitSymbol M)).eval s) := by
  simpa only [Canonical, FixedBlockRetry.restoreIndex, Routine.assign_eval,
    Function.update_of_ne (by decide : (31 : Fin 35) ≠ 13), Function.update_of_ne (by decide : (31 : Fin 35) ≠ 33)] using canonical

def startMemory (n : ℕ) (m : Memory (Cell M P) α 80) : Memory (Outer M) α 35 :=
  ⟨(), m.indexHead, m.randomHead, m.output, outerStore M n⟩

theorem outerStore_bound (n : ℕ) : StoreBound (outerStore M n) n := by
  intro i
  by_cases first : i = 13 <;> by_cases second : i = 22 <;> simp [outerStore, first, second]

theorem startMemory_state (n : ℕ) (m : Memory (Cell M P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = []) :
    FixedBlockRetry.State n (CertifiedStarPhase.cap p n) (startMemory M P n m) := by
  refine ⟨by simp [startMemory, origin], ?_, ?_, empty, ?_⟩
  · simp [startMemory, outerStore]
  · simp [startMemory, outerStore]
  · exact (outerStore_bound M n).mono (by have := outer_indexBudget p n; omega)

theorem pathRetry_lift {n ticks : ℕ} {bits : BitString} {m : Memory (Cell M P) α 80}
    {result : Result (Outer M) α 35}
    (owned : ∀ i, m.store (outerSlots i) = (outerStore M n i).map Sum.inl)
    (run : (FixedBlockRetry.retryLoop (CertifiedStarPhase.unitSymbol M) (CertifiedStarPhase.bitSymbol M)
      (StarCertification.width p) (CertifiedStarPhase.routine M p)).Runs n bits (startMemory M P n m) ticks result) :
    (pathRetry M p P).Runs n bits m ticks ((result.mapSymbols Sum.inl).patch outerSlots m) := by
  have mapped := run.mapSymbols (Sum.inl : Outer M → Cell M P) (outerDecode M P) (by intro symbol; rfl)
  have lifted := mapped.rename outerSlots m
  have initialEq : Memory.patch outerSlots ((startMemory M P n m).mapSymbols Sum.inl) m = m := by
    apply Memory.patch_eq
    apply Configuration.ext <;> try rfl
    funext i
    exact owned i
  rwa [initialEq] at lifted

def pathCallBudget (n : ℕ) : ℕ := FixedBlockRetry.attemptBudget (StarCertification.width p)
  (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p) n+2

theorem pathRetry_runs_success (n failures : ℕ) (parts : List ℕ) (bits : BitString)
    (m : Memory (Cell M P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (owned : ∀ i, m.store (outerSlots i) = (outerStore M n i).map Sum.inl)
    (sizes : StoreBound m.store (CertifiedStarPhase.cap p n))
    (enough : m.randomHead+(failures+1)*StarCertification.width p n ≤ bits.length)
    (failed : ∀ k < failures, CertifiedStarPhase.value M p n
      ((bits.drop (m.randomHead+k*StarCertification.width p n)).take (StarCertification.width p n)) = none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (m.randomHead+failures*StarCertification.width p n)).take (StarCertification.width p n)) = some (StarPaths.payload parts)) :
    ∃ ticks ≤ (failures+1)*pathCallBudget M p n, ∃ next,
      (pathRetry M p P).Runs n bits m ticks (.done next) ∧ next.indexHead = 0 ∧
      next.randomHead = m.randomHead+(failures+1)*StarCertification.width p n ∧ next.output = [] ∧
      next.store 31 = ExpectedStarCalls.pathWord P (CertifiedStarPhase.encodePath M) parts ∧
      (next.store 22).length = n ∧ StoreBound next.store (CertifiedStarPhase.cap p n) := by
  let start := startMemory M P n m
  obtain ⟨ticks, cost, inner, run, state, innerOrigin, innerHead, canonical, _, payload⟩ :=
    FixedBlockRetry.loop_runs_success_at_index_with_post
      (CertifiedStarPhase.unitSymbol M) (CertifiedStarPhase.bitSymbol M) (StarCertification.width p)
      (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p) (CertifiedStarPhase.routine M p)
      (CertifiedStarPhase.decodePath M) (CertifiedStarPhase.value M p)
      (CertifiedStarPhase.phase_correct M p) (CertifiedStarPhase.phase_bound M p) (CertifiedStarPhase.routine_frame M p)
      (Canonical M) (phase_canonical M p) (restored_canonical M)
      n failures n bits start (startMemory_state M p P n m origin empty)
      (by simp [start, startMemory, outerStore]) le_rfl (outer_indexBudget p n) (outer_widthBudget p n)
      enough failed (StarPaths.payload parts) success
  let next := Memory.patch outerSlots (inner.mapSymbols Sum.inl) m
  have lifted := pathRetry_lift M p P owned run
  have raw : inner.store 31 = (StarPaths.payload parts).map (CertifiedStarPhase.encodePath M) := by
    change ((inner.store 31).filterMap (CertifiedStarPhase.decodePath M)).map (CertifiedStarPhase.encodePath M) = inner.store 31 at canonical
    rw [payload] at canonical
    exact canonical.symm
  have low (i : Fin 35) : next.store (outerSlots i) = (inner.store i).map Sum.inl := by
    simp [next, Memory.patch, Memory.mapSymbols, Local.mapStore]
  refine ⟨ticks, cost, next, lifted, innerOrigin.trans origin, innerHead, state.output, ?_, ?_, ?_⟩
  · change next.store (outerSlots 31) = _
    rw [low, raw]
    simp [ExpectedStarCalls.pathWord, ExpectedStarCalls.pathSymbol, List.map_map, Function.comp_def]
  · change (next.store (outerSlots 22)).length = _
    rw [low, List.length_map]
    exact state.master
  · intro k
    by_cases selected : ∃ i, outerSlots i = k
    · obtain ⟨i, rfl⟩ := selected
      rw [low, List.length_map]
      exact state.sizes i
    · have outside : ∀ i, k ≠ outerSlots i := by intro i same; exact selected ⟨i, same.symm⟩
      rw [show next.store k = m.store k from Memory.patchStore_outside outerSlots _ _ k outside]
      exact sizes k

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
