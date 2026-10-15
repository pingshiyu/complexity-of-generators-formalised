import ComplexityOfGenerators.Simulation.CyclicGenerator.Cycle

/-! End-to-end execution and visited-cell accounting for the native cyclic
machine, starting from its blank work tape. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem initial_cycle (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (bits : BitString) :
    ∃ result, (bank D).RegionRun (generatorData n) bits (radius n s) (bank D).initialConfiguration result ∧
      AllowedOutcome D n result := by
  obtain ⟨result, run, allowed⟩ := cycle_terminates D first least deterministic n s halts space bits
    (List.replicate n first) false 0 n (by simp) le_rfl
  have load := ((load_initial D first least n bits).inRegion (bank D) 0
    ((bank D).initial_bounded (generatorData n))).mono (bank D)
      (show 0 + (n + 1) ≤ radius n s by unfold radius; omega)
  exact ⟨result, run.prepend (bank D) load, allowed⟩

theorem native_cycle (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (bits : BitString) :
    ∃ ticks finish result,
      (machine D).Steps (generatorData n) bits (machine D).initialConfiguration ticks finish ∧
      (machine D).observe (generatorData n) bits finish = .halted result ∧
      (machine D).InRegion (radius n s) finish ∧ AllowedOutcome D n result := by
  obtain ⟨result, run, allowed⟩ := initial_cycle D first least deterministic n s halts space bits
  obtain ⟨ready, related, boot, region⟩ := TransducerBank.bank_loaded_inRegion (bank D)
    (generatorData n) bits (radius n s)
  obtain ⟨ticks, finish, path, terminal, bounded⟩ := run.compile (bank D) (fun _ => false) ready related region
  exact ⟨1 + ticks, finish, result, boot.trans _ path, terminal, bounded, allowed⟩

/-- The native machine uses only linear overhead in the source space and the
requested output length. This bounds visited cells, including the final step. -/
theorem machine_spaceBound (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s) :
    (machine D).SpaceBound (generatorData n) (2 * radius n s + 1) := by
  apply Machine.spaceBound_of_terminal_paths
  intro bits
  obtain ⟨ticks, finish, result, path, terminal, region, _⟩ :=
    native_cycle D first least deterministic n s halts space bits
  exact ⟨ticks, finish, result, path, terminal, region.card_le _⟩

theorem machine_haltingTransducer (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s) :
    (machine D).HaltingTransducer (generatorData n) := by
  have terminates : ∀ bits, ∃ t result, (machine D).run (generatorData n) bits t = .halted result ∧
      AllowedOutcome D n result := by
    intro bits
    obtain ⟨ticks, finish, result, path, terminal, _, allowed⟩ :=
      native_cycle D first least deterministic n s halts space bits
    refine ⟨ticks, result, ?_, allowed⟩
    simpa [Machine.runFrom_initial, terminal] using path.runFrom (machine D)
  refine ⟨?_, ?_⟩
  · intro bits
    obtain ⟨t, result, run, _⟩ := terminates bits
    exact ⟨t, result, run⟩
  · intro bits t rejected
    obtain ⟨u, result, run, allowed⟩ := terminates bits
    have same := (machine D).halted_outcome_unique _ bits u t result .rejected run rejected
    cases same
    exact allowed

theorem machine_output_sound (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (bits : BitString) (word : List α) (produces : (machine D).Produces (generatorData n) bits word) :
    word.length = n ∧ D.Accepts (decisionData word) [] := by
  obtain ⟨ticks, finish, result, path, terminal, _, allowed⟩ :=
    native_cycle D first least deterministic n s halts space bits
  have run : (machine D).run (generatorData n) bits ticks = .halted result := by
    simpa [Machine.runFrom_initial, terminal] using path.runFrom (machine D)
  obtain ⟨t, accepted⟩ := produces
  have same := (machine D).halted_outcome_unique _ bits ticks t result (.accepted word) run accepted
  cases same
  exact allowed

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
