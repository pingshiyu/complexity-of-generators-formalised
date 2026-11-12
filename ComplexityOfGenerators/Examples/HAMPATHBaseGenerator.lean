import ComplexityOfGenerators.Examples.HAMPATHBaseSearch
import ComplexityOfGenerators.Proofs.CommandGenerators
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput

namespace ComplexityOfGenerators.Examples.HAMPATH.BaseSearch

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def Productive (n : ℕ) : Prop := ∃ k ≤ n, 1 ≤ k ∧ encodingLength k = n

instance (n : ℕ) : Decidable (Productive n) := by unfold Productive; infer_instance

theorem bases_productive (n : ℕ) :
    selfReduction.bases n = {word | Productive n ∧ word = singleton.encode 0} := by
  ext word
  constructor
  · rintro ⟨ancestor, zeroRank⟩
    obtain ⟨G, start, member, equal⟩ := ancestor.1
    have zero : rank G.size = 0 := by
      change wordRank word = 0 at zeroRank
      rwa [← equal, wordRank_encode G start member.start_bound] at zeroRank
    obtain ⟨rfl, rfl⟩ := rank_zero_graph G member zero
    obtain ⟨_, source, ⟨⟨H, next, sourceMember, encoded⟩, length⟩, _⟩ :=
      selfReduction.mem_ancestors_iff.mp ancestor
    have productiveSize : 1 ≤ H.size := by have := sourceMember.start_bound; omega
    have target : encodingLength H.size = n := by rw [← encoded, H.encode_length] at length; exact length
    have sizeBound : H.size ≤ n := by unfold encodingLength at target; omega
    exact ⟨⟨H.size, sizeBound, productiveSize, target⟩, equal.symm⟩
  · rintro ⟨⟨size, _, positive, target⟩, rfl⟩
    rw [← target, bases_eq]
    exact ⟨positive, rfl⟩

def prepareCommand : Command Unit Symbol 12 :=
  (Command.loadIndex 0 ()).seq
    (Routine.assign 0 1 6 (by decide) (by decide) (by decide) id).command

def preparedMemory (n : ℕ) : Memory Unit Symbol 12 := ⟨(), n, 0, [], initialStore n⟩

theorem prepare_runs (n : ℕ) (bits : BitString) :
    ∃ t ≤ 17 * n + 4,
      prepareCommand.Runs n bits Command.emptyMemory t (.done (preparedMemory n)) := by
  let loaded : Memory Unit Symbol 12 := Command.loadedIndex 0 () n Command.emptyMemory
  have first := Command.loadIndex_runs (0 : Fin 12) () n bits
    (Command.emptyMemory : Memory Unit Symbol 12) (Nat.zero_le _)
  obtain ⟨ticks, cost, last⟩ :=
    (Routine.assign (O := Symbol) (0 : Fin 12) 1 6 (by decide) (by decide) (by decide) id).runs
      (n := n) bits loaded (by simp [loaded, Command.loadedIndex])
  have final : {loaded with store :=
      (Routine.assign (O := Symbol) (0 : Fin 12) 1 6 (by decide) (by decide) (by decide) id).eval loaded.store} =
      preparedMemory n := by
    apply Configuration.ext <;> try rfl
    funext j
    simp [loaded, Routine.assign_eval, Command.loadedIndex,
      Memory.set, preparedMemory, initialStore, Function.update_apply]
    by_cases zero : j = 0 <;> by_cases one : j = 1 <;> by_cases scratch : j = 6 <;>
      simp_all
  rw [final] at last
  have run := Command.Runs.seq _ _ _ _ _ _ _ first last
  refine ⟨3 * n + 1 + ticks, ?_, ?_⟩
  · have costBound : ticks ≤ 14 * n + 3 := by
      simpa [loaded, Routine.assign_cost, Command.loadedIndex, Command.emptyMemory, Memory.set] using cost
    omega
  · simpa only [prepareCommand, Nat.sub_zero] using run

def searchedMemory (n : ℕ) : Memory Unit Symbol 12 :=
  {preparedMemory n with store := search.eval (initialStore n)}

def searchCommand : Command Unit Symbol 12 := prepareCommand.seq search.command

noncomputable def searchBudget (n : ℕ) : ℕ := 17 * n + 5 + n * (bodyBudget n + 4)

theorem search_runs (n : ℕ) (bits : BitString) :
    ∃ t ≤ searchBudget n, searchCommand.Runs n bits Command.emptyMemory t (.done (searchedMemory n)) := by
  obtain ⟨firstTicks, firstCost, first⟩ := prepare_runs n bits
  obtain ⟨ticks, cost, last⟩ := search.runs (n := n) bits (preparedMemory n) (by simp [preparedMemory])
  have bound := search_cost n
  change ticks ≤ search.cost (initialStore n) at cost
  exact ⟨firstTicks + 1 + ticks, by unfold searchBudget; omega,
    Command.Runs.seq _ _ _ _ _ _ _ first last⟩

def emitFixed (word : List Symbol) : Command Unit Symbol 12 := Command.emitFixed 0 word

theorem emitFixed_runs (word : List Symbol) {n : ℕ} (bits : BitString) (m : Memory Unit Symbol 12)
    (bounded : m.indexHead ≤ n) :
    (emitFixed word).Runs n bits m (2 * word.length) (.done {m with output := m.output ++ word}) :=
  Command.emitFixed_runs 0 word bits m bounded

def finishCommand : Command Unit Symbol 12 :=
  .branch 11 fun observation =>
    if observation.1.isSome then emitFixed (singleton.encode 0) else .drain

def baseCommand : Command Unit Symbol 12 := searchCommand.seq finishCommand

def expectedOutcome (n : ℕ) : Outcome Symbol :=
  if Productive n then .accepted (singleton.encode 0) else .exhausted

theorem command_runs (n : ℕ) (bits : BitString) :
    ∃ t ≤ searchBudget n + 12 + bits.length, ∃ result,
      baseCommand.Runs n bits Command.emptyMemory t result ∧ result.outcome = expectedOutcome n := by
  obtain ⟨ticks, cost, searched⟩ := search_runs n bits
  have flag := search_found n
  change ((searchedMemory n).store 11).head?.isSome = decide (Productive n) at flag
  by_cases productive : Productive n
  · have flagTrue : ((searchedMemory n).store 11).head?.isSome = true := by simpa [productive] using flag
    have emitted := emitFixed_runs (n := n) (singleton.encode 0) bits (searchedMemory n)
      (by simp [searchedMemory, preparedMemory])
    have finish : finishCommand.Runs n bits (searchedMemory n) 11
        (.done {searchedMemory n with output := singleton.encode 0}) := by
      apply Command.Runs.branch (n := n) (bits := bits) (searchedMemory n) 11
        (fun observation => if observation.1.isSome then emitFixed (singleton.encode 0) else .drain)
        10 (.done {searchedMemory n with output := singleton.encode 0})
      change (if ((searchedMemory n).store 11).head?.isSome then emitFixed (singleton.encode 0) else .drain).Runs
        n bits (searchedMemory n) 10 _
      rw [flagTrue]
      simpa [singleton_encoding, searchedMemory, preparedMemory] using emitted
    refine ⟨ticks + 1 + 11, by omega, _, Command.Runs.seq _ _ _ _ _ _ _ searched finish, ?_⟩
    simp [expectedOutcome, productive, Result.outcome]
  · have flagFalse : ((searchedMemory n).store 11).head?.isSome = false := by simpa [productive] using flag
    have finish : finishCommand.Runs n bits (searchedMemory n) (1 + bits.length) .exhausted := by
      apply Command.Runs.branch (n := n) (bits := bits) (searchedMemory n) 11
        (fun observation => if observation.1.isSome then emitFixed (singleton.encode 0) else .drain)
        bits.length .exhausted
      change (if ((searchedMemory n).store 11).head?.isSome then emitFixed (singleton.encode 0) else .drain).Runs
        n bits (searchedMemory n) bits.length .exhausted
      rw [flagFalse]
      simpa [searchedMemory, preparedMemory] using
        (Command.Runs.drain (n := n) (bits := bits) (searchedMemory n))
    refine ⟨ticks + 1 + (1 + bits.length), by omega, .exhausted,
      Command.Runs.seq _ _ _ _ _ _ _ searched finish, ?_⟩
    simp [expectedOutcome, productive, Result.outcome]

end ComplexityOfGenerators.Examples.HAMPATH.BaseSearch
