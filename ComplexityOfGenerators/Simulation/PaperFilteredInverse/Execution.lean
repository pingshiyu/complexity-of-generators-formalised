import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Prepare

/-! Concrete finite executions of the filtered inverse machine, including
input loading, random-prefix preparation, body execution and output/draining.
Accepting costs are independent of the supplied random tape's length. -/
namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

def bodyStore (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) : Store M W :=
  (body M W seed time widthTime).eval (initialStore M W seed data.index data.input data.auxiliary bits)

def bodyMemory (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) : Memory (Cell M W) α 35 :=
  {initialMemory M W seed data bits with store:=bodyStore M W seed time widthTime data bits}

def finishValue (m : Memory (Cell M W) α 35) : Option (Word α) :=
  if (m.store 26).head?.isSome then
    if (m.store 27).head?.isSome then
      if (m.store 28).head?.isSome then some (m.output++(m.store 25).filterMap (decodeOutput M W)) else none
    else none
  else none

def commandValue (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) : Option (Word α) :=
  if seed data.index≤bits.length then finishValue M W (bodyMemory M W seed time widthTime data bits) else none

def controllerBudget (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) : ℕ :=
  BoundedSource.prepareBudget seed data.index+
    (6*data.input.length+1+6*data.auxiliary.length)+
    (body M W seed time widthTime).cost (initialStore M W seed data.index data.input data.auxiliary bits)+
    4*((bodyStore M W seed time widthTime data bits) 25).length+6

theorem finish_runs (n : ℕ) (bits : BitString) (m : Memory (Cell M W) α 35) (index : m.indexHead≤n) :
    ∃ ticks≤3+4*(m.store 25).length+(if finishValue M W m=none then bits.length else 0),∃ result,
      (finish M W).Runs n bits m ticks result ∧ result.outcome.acceptedWord=finishValue M W m := by
  cases a : (m.store 26).head?.isSome with
  | false =>
      refine ⟨1+(bits.length-m.randomHead),?_,.exhausted,?_,?_⟩
      · simp [finishValue,a];omega
      · apply Command.Runs.branch
        simpa [observe,a] using (Command.Runs.drain (n:=n) (bits:=bits) m)
      · simp [Result.outcome,Outcome.acceptedWord,finishValue,a]
  | true =>
      cases b : (m.store 27).head?.isSome with
      | false =>
          refine ⟨1+(1+(bits.length-m.randomHead)),?_,.exhausted,?_,?_⟩
          · simp [finishValue,a,b];omega
          · apply Command.Runs.branch
            simp only [observe,a,↓reduceIte]
            apply Command.Runs.branch
            simpa [observe,b] using (Command.Runs.drain (n:=n) (bits:=bits) m)
          · simp [Result.outcome,Outcome.acceptedWord,finishValue,a,b]
      | true =>
          cases c : (m.store 28).head?.isSome with
          | false =>
              refine ⟨1+(1+(1+(bits.length-m.randomHead))),?_,.exhausted,?_,?_⟩
              · simp [finishValue,a,b,c];omega
              · apply Command.Runs.branch
                simp only [observe,a,↓reduceIte]
                apply Command.Runs.branch
                simp only [observe,b,↓reduceIte]
                apply Command.Runs.branch
                simpa [observe,c] using (Command.Runs.drain (n:=n) (bits:=bits) m)
              · simp [Result.outcome,Outcome.acceptedWord,finishValue,a,b,c]
          | true =>
              refine ⟨1+(1+(1+4*(m.store 25).length)),?_,.done (Command.emitted 25 (decodeOutput M W) m),?_,?_⟩
              · simp [finishValue,a,b,c];omega
              · apply Command.Runs.branch
                simp only [observe,a,↓reduceIte]
                apply Command.Runs.branch
                simp only [observe,b,↓reduceIte]
                apply Command.Runs.branch
                simpa [observe,c] using Command.emitWord_runs 25 (decodeOutput M W) bits m index
              · simp [Result.outcome,Outcome.acceptedWord,Command.emitted,finishValue,a,b,c]


theorem patch_acceptedWord (ambient : NativeMemory M W) (result : Result (Cell M W) α 35) :
    (result.patch slots ambient).outcome.acceptedWord=result.outcome.acceptedWord := by
  cases result <;> rfl

theorem tail_runs (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) :
    ∃ ticks≤(6*data.input.length+1+6*data.auxiliary.length)+
        (body M W seed time widthTime).cost (initialStore M W seed data.index data.input data.auxiliary bits)+
        4*((bodyStore M W seed time widthTime data bits) 25).length+5+
        (if finishValue M W (bodyMemory M W seed time widthTime data bits)=none then bits.length else 0),
      ∃ result,
      ((loadWords M W).command.seq
        (((body M W seed time widthTime).command.rename slots).seq ((finish M W).rename slots))).Runs
          data.index bits (preparedMemory M W seed data bits) ticks result ∧
      result.outcome.acceptedWord=finishValue M W (bodyMemory M W seed time widthTime data bits) := by
  obtain ⟨loadTicks,loadBound,loadRun⟩ := (loadWords M W).runs bits (preparedMemory M W seed data bits) (by rfl)
  change (loadWords M W).command.Runs data.index bits (preparedMemory M W seed data bits)
    loadTicks (.done (loadedWordsMemory M W seed data bits)) at loadRun
  rw [loadWords_cost] at loadBound
  obtain ⟨bodyTicks,bodyBound,bodyRun⟩ := (body M W seed time widthTime).runs bits (initialMemory M W seed data bits) (by rfl)
  change (body M W seed time widthTime).command.Runs data.index bits (initialMemory M W seed data bits)
    bodyTicks (.done (bodyMemory M W seed time widthTime data bits)) at bodyRun
  change bodyTicks≤(body M W seed time widthTime).cost
    (initialStore M W seed data.index data.input data.auxiliary bits) at bodyBound
  have renamedBody := bodyRun.rename slots (loadedWordsMemory M W seed data bits)
  have initialEq := Memory.patch_eq slots (initialMemory M W seed data bits)
    (loadedWordsMemory M W seed data bits) (loadedWords_project M W seed data bits)
  rw [initialEq] at renamedBody
  obtain ⟨finishTicks,finishBound,result,finishRun,value⟩ :=
    finish_runs M W data.index bits (bodyMemory M W seed time widthTime data bits) (by rfl)
  have renamedFinish := finishRun.rename slots (loadedWordsMemory M W seed data bits)
  have bodyFinish := Command.Runs.seq _ _ _ _ _ _ _ renamedBody renamedFinish
  have all := Command.Runs.seq _ _ _ _ _ _ _ loadRun bodyFinish
  refine ⟨loadTicks+1+(bodyTicks+1+finishTicks),?_,result.patch slots (loadedWordsMemory M W seed data bits),all,?_⟩
  · change finishTicks≤3+4*((bodyStore M W seed time widthTime data bits) 25).length+
      (if finishValue M W (bodyMemory M W seed time widthTime data bits)=none then bits.length else 0) at finishBound
    omega
  · rw [patch_acceptedWord]
    exact value

theorem command_runs (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) :
    ∃ ticks≤controllerBudget M W seed time widthTime data bits+
        (if commandValue M W seed time widthTime data bits=none then bits.length else 0),
      ∃ result,(command M W seed time widthTime).Runs data.index bits (loadedMemory M W data) ticks result ∧
        result.outcome.acceptedWord=commandValue M W seed time widthTime data bits := by
  obtain ⟨prepareTicks,prepareBound,prepared⟩ := prepare_runs M W seed data bits
  by_cases enough : seed data.index≤bits.length
  · simp only [enough,ite_true] at prepared
    obtain ⟨tailTicks,tailBound,result,tailRun,value⟩ := tail_runs M W seed time widthTime data bits
    refine ⟨prepareTicks+1+tailTicks,?_,result,?_,?_⟩
    · simp only [commandValue,enough,ite_true]
      unfold controllerBudget
      omega
    · exact Command.Runs.seq _ _ _ _ _ _ _ prepared tailRun
    · simpa only [commandValue,enough,ite_true] using value
  · simp only [enough,ite_false] at prepared
    refine ⟨prepareTicks,?_,.exhausted,?_,?_⟩
    · unfold controllerBudget
      omega
    · exact Command.Runs.seq_absent _ _ _ _ prepared
    · simp [Result.outcome,Outcome.acceptedWord,commandValue,enough]

private theorem compileBudget_mono (arguments : ℕ) {small large : ℕ} (bound : small≤large) :
    InputBank.compileBudget arguments small≤InputBank.compileBudget arguments large := by
  dsimp [InputBank.compileBudget]
  gcongr

theorem native_run (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) :
    ∃ ticks≤InputBank.compileBudget (data.input.length+data.auxiliary.length)
        (controllerBudget M W seed time widthTime data bits+
          (if commandValue M W seed time widthTime data bits=none then bits.length else 0)),
      ∃ result,(machine M W seed time widthTime).run data bits ticks=.halted result ∧
        result≠.rejected ∧ result.acceptedWord=commandValue M W seed time widthTime data bits := by
  obtain ⟨controllerTicks,bound,result,run,value⟩ := command_runs M W seed time widthTime data bits
  let code := command M W seed time widthTime
  let P := code.program 0
  have execution := Program.Evaluates.executes P (run.compiled 0 (Nat.zero_le _))
  obtain ⟨ticks,cost,native⟩ := InputBank.run_compiled P 35 36 Symbol.letter Symbol.letter
    (by decide) data bits controllerTicks result.outcome execution
  refine ⟨ticks,cost.trans (compileBudget_mono _ bound),result.outcome,?_,?_,value⟩
  · exact native
  · cases result <;> simp [Result.outcome]

theorem native_run_some (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString)
    (word : Word α) (accepted : commandValue M W seed time widthTime data bits=some word) :
    ∃ ticks≤InputBank.compileBudget (data.input.length+data.auxiliary.length)
        (controllerBudget M W seed time widthTime data bits),
      (machine M W seed time widthTime).run data bits ticks=.halted (.accepted word) := by
  obtain ⟨ticks,cost,result,run,notRejected,value⟩ := native_run M W seed time widthTime data bits
  rw [accepted] at value
  have equal : result=.accepted word := by
    cases result with
    | accepted output => simpa [Outcome.acceptedWord] using value
    | rejected => exact False.elim (notRejected rfl)
    | exhausted => simp [Outcome.acceptedWord] at value
  refine ⟨ticks,?_,by simpa only [equal] using run⟩
  simpa only [accepted,Option.some_ne_none,ite_false,Nat.add_zero] using cost

theorem machine_produces_iff (seed time widthTime : PolynomialBound) (data : InputData α α)
    (bits : BitString) (word : Word α) :
    (machine M W seed time widthTime).Produces data bits word↔
      commandValue M W seed time widthTime data bits=some word := by
  obtain ⟨ticks,_,result,run,notRejected,value⟩ := native_run M W seed time widthTime data bits
  constructor
  · rintro ⟨t,accepted⟩
    have equal := (machine M W seed time widthTime).halted_outcome_unique data bits ticks t result (.accepted word) run accepted
    simpa only [equal,Outcome.acceptedWord] using value.symm
  · intro accepted
    obtain ⟨ticks,_,run⟩ := native_run_some M W seed time widthTime data bits word accepted
    exact ⟨ticks,run⟩


theorem machine_halting (seed time widthTime : PolynomialBound) (data : InputData α α) :
    (machine M W seed time widthTime).HaltingTransducer data := by
  constructor
  · intro bits
    obtain ⟨ticks,_,result,run,_,_⟩ := native_run M W seed time widthTime data bits
    exact ⟨ticks,result,run⟩
  · intro bits ticks rejected
    obtain ⟨t,_,result,run,notRejected,_⟩ := native_run M W seed time widthTime data bits
    exact notRejected ((machine M W seed time widthTime).halted_outcome_unique data bits t ticks
      result .rejected run rejected)

theorem generatedLanguage_value (seed time widthTime : PolynomialBound) (data : InputData α α) :
    (machine M W seed time widthTime).generatedLanguage data=
      {word | ∃ bits : BitString,bits≠[] ∧ commandValue M W seed time widthTime data bits=some word} := by
  ext word
  change (∃ bits : BitString,bits≠[] ∧ (machine M W seed time widthTime).Produces data bits word)↔_
  simp only [machine_produces_iff,Set.mem_setOf_eq]

theorem machine_accepts_value (seed time widthTime : PolynomialBound) (data : InputData α α) (bits : BitString) :
    (machine M W seed time widthTime).Accepts data bits↔
      ∃ word,commandValue M W seed time widthTime data bits=some word := by
  simp only [Machine.Accepts,machine_produces_iff]

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
