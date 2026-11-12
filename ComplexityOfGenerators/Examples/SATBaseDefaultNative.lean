import ComplexityOfGenerators.Examples.SATBaseDefaults
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput
import ComplexityOfGenerators.Simulation.WordStack.Unary
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops
import ComplexityOfGenerators.Proofs.CommandGenerators

/-! Native bounded default for every productive constant-formula base length. -/
namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseDefaultNative
open Simulation.WordStack
set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 2
abbrev Code := Command Symbol Symbol 2
abbrev Step := Routine Symbol Symbol 2

def tag (n : ℕ) : Option Symbol :=
  if n = 2 then some .one else if n = 4 then some .positive else none

def mark : Option Symbol → Step
  | none => .skip
  | some symbol => .ofLocal (Local.push 1 symbol)

/-- Inspect at most four unary cells, leaving n−4 cells for the long template. -/
def classify (tested : ℕ) : ℕ → Step
  | 0 => .branch 0 (fun head => if head.isNone then mark (tag tested) else mark (some .separator))
  | fuel+1 => .branch 0 (fun head => if head.isNone then mark (tag tested)
      else (Routine.ofLocal (Local.pop 0)).seq (classify (tested+1) fuel))

def loadedStore (n : ℕ) : Store := Function.update (fun _ => []) 0 (List.replicate n .zero)

def flag (n : ℕ) : List Symbol :=
  if n = 2 then [.one] else if n = 4 then [.positive] else if 5 ≤ n then [.separator] else []

def classifiedStore (n : ℕ) : Store :=
  Function.update (Function.update (fun _ => []) 0 (List.replicate (n-4) .zero)) 1 (flag n)

theorem classify_eval (n : ℕ) : (classify 0 4).eval (loadedStore n) = classifiedStore n := by
  rcases n with _ | _ | _ | _ | _ | n <;>
    funext j <;> fin_cases j <;>
    simp [classify, loadedStore, classifiedStore, flag, tag, mark, Routine.branch, Routine.seq,
      Routine.ofLocal, Routine.skip, Local.eval, Local.pop, Local.push, Action.apply]

theorem mark_cost (value : Option Symbol) (s : Store) : (mark value).cost s ≤ 1 := by
  cases value <;> simp [mark, Routine.skip, Routine.ofLocal, Local.push, Local.ticks]

theorem classify_cost (tested fuel : ℕ) (s : Store) : (classify tested fuel).cost s ≤ 3*fuel+2 := by
  induction fuel generalizing tested s with
  | zero =>
    simp only [classify, Routine.branch]
    split
    · have := mark_cost (tag tested) s; omega
    · have := mark_cost (some .separator) s; omega
  | succ fuel ih =>
    simp only [classify, Routine.branch]
    split
    · have := mark_cost (tag tested) s
      omega
    · simp only [Routine.seq, Routine.ofLocal, Local.pop, Local.ticks]
      have bound := ih (tested+1) (Local.pop 0 |>.eval s)
      dsimp only [Local.pop] at bound
      omega

def longCommand : Code :=
  (Command.emitFixed 0 [.separator, .separator, .openClause]).seq
    ((Command.emitWord 0 (fun _ => some .trueConstant)).seq
      (Command.emitFixed 0 [.closeClause]))

def finishCommand : Code := .branch 1 (fun observation => match observation.1 with
  | some .one => Command.emitFixed 0 [.separator, .separator]
  | some .positive => Command.emitFixed 0 [.one, .separator, .zero, .separator]
  | some .separator => longCommand
  | _ => .drain)

def command : Code :=
  (Command.loadIndex 0 .zero).seq ((classify 0 4).command.seq finishCommand)

def preparedMemory (n : ℕ) : Memory Symbol Symbol 2 := ⟨(), n, 0, [], classifiedStore n⟩

theorem long_runs (n : ℕ) (bits : BitString) (m : Memory Symbol Symbol 2)
    (index : m.indexHead ≤ n) (count : m.store 0 = List.replicate (n-4) .zero)
    (output : m.output = []) (large : 5 ≤ n) :
    longCommand.Runs n bits m (4*(n-4)+10)
      (.done {m.set 0 [] with output := baseDefault n}) := by
  let first : Memory Symbol Symbol 2 := {m with output := [.separator, .separator, .openClause]}
  let second := Command.emitted 0 (fun _ : Symbol => some Symbol.trueConstant) first
  have emitFirst := Command.emitFixed_runs (0 : Fin 2) [.separator, .separator, .openClause] bits m index
  have firstRun : (Command.emitFixed (S := Symbol) (0 : Fin 2) [.separator, .separator, .openClause]).Runs
      n bits m 6 (.done first) := by simpa [first, output] using emitFirst
  have emitSecond := Command.emitWord_runs (0 : Fin 2) (fun _ : Symbol => some Symbol.trueConstant) bits first index
  have secondRun : (Command.emitWord (0 : Fin 2) (fun _ : Symbol => some Symbol.trueConstant)).Runs
      n bits first (4*(n-4)) (.done second) := by simpa [first, count, second] using emitSecond
  have emitLast := Command.emitFixed_runs (0 : Fin 2) [Symbol.closeClause] bits second index
  have run := Command.Runs.seq _ _ _ _ _ _ _ firstRun
    (Command.Runs.seq _ _ _ _ _ _ _ secondRun emitLast)
  convert run using 1 <;>
    simp [longCommand, first, second, Command.emitted, Memory.set, output, count,
      baseDefault_long n large, List.filterMap_replicate, List.append_assoc] <;> omega

def expectedOutcome (n : ℕ) : Outcome Symbol :=
  if BaseProductive n then .accepted (baseDefault n) else .exhausted

theorem finish_runs (n : ℕ) (bits : BitString) :
    ∃ t ≤ 4*n+bits.length+20, ∃ result,
      finishCommand.Runs n bits (preparedMemory n) t result ∧ result.outcome = expectedOutcome n := by
  by_cases two : n = 2
  · subst n
    let final : Memory Symbol Symbol 2 := {preparedMemory 2 with output := [.separator, .separator]}
    refine ⟨5, by omega, .done final, ?_, ?_⟩
    · apply Command.Runs.branch (preparedMemory 2) 1 _ 4 (.done final)
      simpa [observe, preparedMemory, classifiedStore, flag, final] using
        Command.emitFixed_runs (0 : Fin 2) [Symbol.separator, .separator] bits (preparedMemory 2) (le_refl 2)
    · simp [Result.outcome, final, expectedOutcome, BaseProductive, baseDefault, Formula.encode]
  · by_cases four : n = 4
    · subst n
      let final : Memory Symbol Symbol 2 := {preparedMemory 4 with output := [.one, .separator, .zero, .separator]}
      refine ⟨9, by omega, .done final, ?_, ?_⟩
      · apply Command.Runs.branch (preparedMemory 4) 1 _ 8 (.done final)
        simpa [observe, preparedMemory, classifiedStore, flag, final] using
          Command.emitFixed_runs (0 : Fin 2) [Symbol.one, .separator, .zero, .separator] bits (preparedMemory 4) (le_refl 4)
      · simp [Result.outcome, final, expectedOutcome, BaseProductive, baseDefault, Formula.encode]
    · by_cases large : 5 ≤ n
      · let final : Memory Symbol Symbol 2 := {(preparedMemory n).set 0 [] with output := baseDefault n}
        refine ⟨1+(4*(n-4)+10), by omega, .done final, ?_, ?_⟩
        · apply Command.Runs.branch
          simpa [observe, preparedMemory, classifiedStore, flag, two, four, large, final] using
            long_runs n bits (preparedMemory n) (le_refl n) (by simp [preparedMemory, classifiedStore]) rfl large
        · have productive : BaseProductive n := ⟨by omega, by omega⟩
          simp [Result.outcome, final, expectedOutcome, productive]
      · refine ⟨1+bits.length, by omega, .exhausted, ?_, ?_⟩
        · apply Command.Runs.branch
          simpa [observe, preparedMemory, classifiedStore, flag, two, four, large] using
            Command.Runs.drain (n := n) (bits := bits) (preparedMemory n)
        · have unproductive : ¬ BaseProductive n := by unfold BaseProductive; omega
          simp [Result.outcome, expectedOutcome, unproductive]

theorem command_runs (n : ℕ) (bits : BitString) :
    ∃ t ≤ 7*n+bits.length+36, ∃ result,
      command.Runs n bits Command.emptyMemory t result ∧ result.outcome = expectedOutcome n := by
  let loaded := Command.loadedIndex (O := Symbol) (0 : Fin 2) Symbol.zero n Command.emptyMemory
  have load := Command.loadIndex_runs (O := Symbol) (0 : Fin 2) Symbol.zero n bits Command.emptyMemory (Nat.zero_le n)
  obtain ⟨ticks, cost, classifyRun⟩ := (classify 0 4).runs (n := n) bits loaded (le_refl n)
  have initial : loaded.store = loadedStore n := by
    simp [loaded, Command.loadedIndex, Command.emptyMemory, Memory.set, loadedStore]
  have final : {loaded with store := (classify 0 4).eval loaded.store} = preparedMemory n := by
    rw [initial, classify_eval]
    rfl
  rw [final] at classifyRun
  have classifierCost : ticks ≤ 14 := cost.trans (classify_cost 0 4 loaded.store)
  obtain ⟨lastTicks, lastCost, result, finishRun, outcome⟩ := finish_runs n bits
  have run := Command.Runs.seq _ _ _ _ _ _ _ load (Command.Runs.seq _ _ _ _ _ _ _ classifyRun finishRun)
  refine ⟨3*n+1+(ticks+1+lastTicks), by omega, result, ?_, outcome⟩
  simpa only [command, Nat.sub_zero] using run

def stackTime : PolynomialBound := ⟨44, 1, by decide⟩

def program : Program command.Control Symbol Symbol 2 := command.program 0

noncomputable def machine : Machine Unit Bool Symbol := program.machine

theorem machine_execution (n : ℕ) (bits : BitString) :
    ∃ ticks, machine.run (generatorData n) bits ticks = .halted (expectedOutcome n) := by
  obtain ⟨ticks, _, result, run, outcome⟩ := command_runs n bits
  obtain ⟨nativeTicks, _, native⟩ := program.run_compiled (run.executes 0)
  exact ⟨nativeTicks, by simpa only [machine, outcome] using native⟩

theorem machine_bounded (n : ℕ) (bits : BitString) (short : bits.length ≤ 1) :
    machine.HaltsWithin (generatorData n) bits (Program.compiledTime stackTime n) := by
  obtain ⟨ticks, cost, result, run, _⟩ := command_runs n bits
  have stackCost : ticks ≤ stackTime n := by
    simp only [stackTime, PolynomialBound.eval, pow_one]
    omega
  obtain ⟨nativeTicks, nativeCost, native⟩ := program.run_compiled (run.executes 0)
  have totalCost := nativeCost.trans (Program.compiledTime_bound stackTime n ticks stackCost)
  exact machine.haltsWithin_mono (generatorData n) bits totalCost ⟨result.outcome, native⟩

theorem machine_accepts_iff (n : ℕ) (bits : BitString) :
    machine.Accepts (generatorData n) bits ↔ BaseProductive n := by
  obtain ⟨ticks, reference⟩ := machine_execution n bits
  constructor
  · rintro ⟨word, time, accepted⟩
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ accepted reference
    by_contra unproductive
    simp [expectedOutcome, unproductive] at same
  · intro productive
    exact ⟨baseDefault n, ticks, by simpa [expectedOutcome, productive] using reference⟩

theorem machine_language (n : ℕ) :
    machine.generatedLanguage (generatorData n) = {word | BaseProductive n ∧ word = baseDefault n} := by
  ext word
  constructor
  · rintro ⟨bits, _, time, accepted⟩
    have productive := (machine_accepts_iff n bits).mp ⟨word, time, accepted⟩
    obtain ⟨ticks, reference⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ accepted reference
    exact ⟨productive, by simpa [expectedOutcome, productive] using same⟩
  · rintro ⟨productive, rfl⟩
    obtain ⟨ticks, execution⟩ := machine_execution n [false]
    exact ⟨[false], by decide, ticks, by simpa [expectedOutcome, productive] using execution⟩

theorem support_nonempty (n : ℕ) :
    (machine.generatedLanguage (generatorData n)).Nonempty ↔ BaseProductive n := by
  rw [machine_language]
  exact ⟨fun ⟨_, productive, _⟩ => productive, fun productive => ⟨_, productive, rfl⟩⟩

theorem machine_halting (n : ℕ) : machine.HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks, execution⟩ := machine_execution n bits
    exact ⟨ticks, _, execution⟩
  · intro bits time rejected
    obtain ⟨ticks, execution⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ rejected execution
    by_cases productive : BaseProductive n <;> simp [expectedOutcome, productive] at same

theorem machine_generator (n : ℕ) : machine.IsGenerator (generatorData n) := by
  apply machine.isGenerator_of_full_trials (generatorData n) 1 (machine_halting n)
  intro bits _
  rw [machine_accepts_iff, support_nonempty]


/-- This exact generator provides an implemented default at every productive
base length; full base support is supplied by the separate proposal sampler. -/
noncomputable def defaultFamily : GeneratorFamily Symbol where
  machine := machine
  isGenerator := machine_generator
  outputLength := by
    intro n word member
    change word ∈ machine.generatedLanguage (generatorData n) at member
    rw [machine_language] at member
    rw [member.2]
    exact baseDefault_length n member.1

theorem defaultFamily_sound (n : ℕ) : defaultFamily.toUniformGenerators.layer n ⊆ selfReduction.bases n := by
  intro word member
  change word ∈ machine.generatedLanguage (generatorData n) at member
  rw [machine_language] at member
  rw [member.2]
  exact baseDefault_mem n member.1

theorem defaultFamily_polynomialTime : defaultFamily.toUniformGenerators.PolynomialTime := by
  refine ⟨⟨1, 0, by decide⟩, Program.compiledTime stackTime, fun n => ⟨?_, ?_⟩⟩
  · intro bits short
    exact machine_bounded n bits short
  · intro bits _
    exact (machine_accepts_iff n bits).trans (support_nonempty n).symm

end ComplexityOfGenerators.Examples.PaddedCNF.BaseDefaultNative
