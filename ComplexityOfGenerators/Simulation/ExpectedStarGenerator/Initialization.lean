import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Basic

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (P : BoundedPhaseFamily α)

theorem setup_loaded (n random : ℕ) :
    (setup M P).eval (Command.loadedIndex 13 (unitSymbol M P) n (initialMemory M P random)).store =
      Function.update (readyStore M P n) 75 (List.replicate n (unitSymbol M P)) := by
  funext k
  fin_cases k <;> simp [setup, Routine.seq, Routine.assign_eval, Routine.clear, readyStore, Command.loadedIndex,
    initialMemory, Memory.set]

theorem setup_loaded_cost (n random : ℕ) :
    (setup M P).cost (Command.loadedIndex 13 (unitSymbol M P) n (initialMemory M P random)).store = 28*n+9 := by
  simp [setup, Routine.seq, Routine.assign_cost, Routine.assign_eval, Routine.clear, Command.loadedIndex, initialMemory, Memory.set]
  omega

theorem boot_runs (n random : ℕ) (bits : BitString) :
    ∃ ticks ≤ 100*(n+1), (boot M P).Runs n bits (initialMemory M P random) ticks (.done (readyMemory M P n random)) := by
  let loaded := Command.loadedIndex 13 (unitSymbol M P) n (initialMemory M P random)
  let configured : Memory (Cell M P) α 80 := {loaded with store := (setup M P).eval loaded.store}
  have load := Command.loadIndex_runs 13 (unitSymbol M P) n bits (initialMemory M P random) (by simp [initialMemory])
  obtain ⟨ticks, cost, configuration⟩ := (setup M P).runs (n := n) bits loaded (by simp [loaded, Command.loadedIndex])
  have rewind := Command.rewind_runs (n := n) (75 : Fin 80) bits configured (by simp [configured, loaded, Command.loadedIndex])
  have configuredStore : configured.store = Function.update (readyStore M P n) 75 (List.replicate n (unitSymbol M P)) := setup_loaded M P n random
  have clock : (configured.store 75).length = n := by rw [configuredStore]; simp
  have final : Command.rewound 75 configured = readyMemory M P n random := by
    apply Configuration.ext <;> try rfl
    · change configured.indexHead-(configured.store 75).length = 0
      rw [clock]
      change n-n = 0
      omega
    · funext k
      by_cases same : k = 75 <;>
        simp [Command.rewound, Memory.set, configuredStore, Function.update_idem, readyMemory, readyStore, same]
  rw [final, clock] at rewind
  refine ⟨3*n+1+(ticks+1+3*n), ?_, Command.Runs.seq _ _ _ _ _ _ _ load
    (Command.Runs.seq _ _ _ _ _ _ _ configuration rewind)⟩
  have budget := setup_loaded_cost M P n random
  change ticks ≤ (setup M P).cost loaded.store at cost
  change (setup M P).cost loaded.store = _ at budget
  omega

theorem ready_owned (n random : ℕ) (i : Fin 35) :
    (readyMemory M P n random).store (outerSlots i) = (outerStore M n i).map Sum.inl := by
  have thirteen : outerSlots i = (13 : Fin 80) ↔ i = 13 := by
    constructor
    · intro same
      apply Fin.ext
      exact congrArg (fun k : Fin 80 => k.val) same
    · intro same
      subst i
      rfl
  have twentyTwo : outerSlots i = (22 : Fin 80) ↔ i = 22 := by
    constructor
    · intro same
      apply Fin.ext
      exact congrArg (fun k : Fin 80 => k.val) same
    · intro same
      subst i
      rfl
  have slot13 : outerSlots 13 = (13 : Fin 80) := rfl
  have slot22 : outerSlots 22 = (22 : Fin 80) := rfl
  by_cases a : i = 13 <;> by_cases b : i = 22 <;>
    simp [readyMemory, readyStore, outerStore, Function.update_apply, thirteen, twentyTwo, a, b, slot13, slot22, unitSymbol]

theorem outer_indexBudget (p : PolynomialBound) (n : ℕ) : n+1 ≤ CertifiedStarPhase.cap p n := by
  have bound := CertifiedStarPhase.cap_lower p n
  omega

theorem outer_widthBudget (p : PolynomialBound) (n : ℕ) : StarCertification.width p n ≤ CertifiedStarPhase.cap p n := by
  have first := CertifiedStarPhase.cap_lower p n
  have second := CertifiedStarPhase.inputBound_lower p n
  omega

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
