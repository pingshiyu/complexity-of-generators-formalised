import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Parameters

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] CertifiedStarPhase.routine StarCertification.routine StarPaths.pathRoutine
  ExpectedStarCalls.generatingCommand pathRetry
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

theorem ready_bound (n random : ℕ) : StoreBound (readyMemory M P n random).store n := by
  intro k
  by_cases first : k = 13 <;> by_cases second : k = 22 <;> simp [readyMemory, readyStore, first, second]

/-- One outer path retry followed by the actual sequential inner phase
retries. All physical output is delayed until their final common emission. -/
theorem command_runs_trace (n random failures : ℕ) (parts : List ℕ) (records : List (ExpectedStarCalls.Record α))
    (bits : BitString) (total : parts.sum = n) (positive : ∀ j ∈ parts, 0 < j)
    (enough : random+(failures+1)*StarCertification.width p n ≤ bits.length)
    (failed : ∀ k < failures, CertifiedStarPhase.value M p n
      ((bits.drop (random+k*StarCertification.width p n)).take (StarCertification.width p n)) = none)
    (success : CertifiedStarPhase.value M p n
      ((bits.drop (random+failures*StarCertification.width p n)).take (StarCertification.width p n)) = some (StarPaths.payload parts))
    (trace : ExpectedStarCalls.Trace P bits (random+(failures+1)*StarCertification.width p n) parts records) :
    ∃ ticks ≤ primitiveCoefficient M p P n*(failures+1+ExpectedStarCalls.blocks records+1),
      ∃ next, (command M p P).Runs n bits (initialMemory M P random) ticks (.done next) ∧
        next.output = ExpectedStarCalls.words records ∧ next.indexHead = 0 ∧
        next.randomHead = random+(failures+1)*StarCertification.width p n+ExpectedStarCalls.consumed P parts records := by
  unfold command
  obtain ⟨first, firstCost, firstRun⟩ := boot_runs M P n random bits
  have readySize : StoreBound (readyMemory M P n random).store (CertifiedStarPhase.cap p n) :=
    (ready_bound M P n random).mono (by have := outer_indexBudget p n; omega)
  obtain ⟨second, secondCost, after, secondRun, afterOrigin, afterHead, afterEmpty, afterPath, _, afterSize⟩ :=
    pathRetry_runs_success M p P n failures parts bits (readyMemory M P n random) rfl rfl
      (ready_owned M P n random) readySize enough failed success
  have indices (j : ℕ) (member : j ∈ parts) : j ≤ n := (part_le_sum parts j member).trans_eq total
  have count : parts.length ≤ n := (positive_length_le_sum parts positive).trans_eq total
  have fits : CertifiedStarPhase.cap p n+parts.length*BoundedMachinePhase.cap P.seed P.clock n ≤ workspace p P n :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ count) _).trans (workspace_lower p P n)
  have actualTrace : ExpectedStarCalls.Trace P bits after.randomHead parts records := by rw [afterHead]; exact trace
  obtain ⟨last, lastCost, next, lastRun, output, origin, nextHead⟩ := ExpectedStarCalls.generating_runs_trace P
    (CertifiedStarPhase.encodePath M) (CertifiedStarPhase.projectPath M) (CertifiedStarPhase.project_encode M)
    n (workspace p P n) (CertifiedStarPhase.cap p n) parts records bits after afterOrigin afterEmpty afterPath afterSize indices fits actualTrace
  have lower := primitiveCoefficient_lower M p P n
  have outerPositive : 1 ≤ failures+1 := by omega
  have prefixCharge : first+1+(second+1) ≤ (failures+1)*(100*(n+1)+pathCallBudget M p n+2) := by
    have overhead : 100*(n+1)+2 ≤ (failures+1)*(100*(n+1)+2) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (100*(n+1)+2) outerPositive
    calc
      first+1+(second+1) ≤ (failures+1)*pathCallBudget M p n+(100*(n+1)+2) := by omega
      _ ≤ (failures+1)*pathCallBudget M p n+(failures+1)*(100*(n+1)+2) := Nat.add_le_add_left overhead _
      _ = (failures+1)*(100*(n+1)+pathCallBudget M p n+2) := by ring
  have prefixCeiling : first+1+(second+1) ≤ (failures+1)*primitiveCoefficient M p P n :=
    prefixCharge.trans (Nat.mul_le_mul_left _ (by omega))
  have tailCeiling : last ≤ (ExpectedStarCalls.blocks records+1)*primitiveCoefficient M p P n := by
    apply lastCost.trans
    calc
      2*(ExpectedStarCalls.blocks records+1)*ExpectedStarCalls.coefficient P n (workspace p P n) =
          (ExpectedStarCalls.blocks records+1)*(2*ExpectedStarCalls.coefficient P n (workspace p P n)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  refine ⟨first+1+(second+1+last), ?_, next, Command.Runs.seq _ _ _ _ _ _ _ firstRun
    (Command.Runs.seq _ _ _ _ _ _ _ secondRun lastRun), output, origin, ?_⟩
  · nlinarith only [prefixCeiling, tailCeiling]
  · rw [nextHead, afterHead]
    rfl

noncomputable def program : Program (command M p P).Control (Cell M P) α 80 := (command M p P).program 0

/-- Keep the finite alphabet/control enumerations shared by every native
compiler bridge. Re-synthesizing these dictionaries can unfold the whole
composite command during definitional equality. -/
noncomputable def alphabetFintype : Fintype (Cell M P) := inferInstance

attribute [irreducible] alphabetFintype

noncomputable def controlFintype : Fintype (command M p P).Control := by
  letI := alphabetFintype M P
  exact Command.controlFintype (command M p P)

attribute [irreducible] controlFintype

noncomputable def machine : Machine Unit Bool α := by
  letI := alphabetFintype M P
  letI := controlFintype M p P
  exact (program M p P).machine

theorem compile_run {n ticks : ℕ} {bits : BitString} {result : Outcome α}
    (execution : (program M p P).Executes n bits (program M p P).initialConfiguration ticks result) :
    ∃ nativeTicks ≤ 1+(2*ticks+1)*(4*ticks+4),
      (machine M p P).run (generatorData n) bits nativeTicks = .halted result := by
  letI := alphabetFintype M P
  letI := controlFintype M p P
  exact (program M p P).run_compiled execution


end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
