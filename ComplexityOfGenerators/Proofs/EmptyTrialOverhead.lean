import ComplexityOfGenerators.Proofs.ElementaryGenerators

/-!
# A boundary problem in the former equal-budget Remark 1 convention

Consuming a tape of length `t` requires `t` random-read transitions. A single
silent initialization transition therefore makes exhaustion within `t` steps
impossible. This concrete example documents why equal seed and transition
budgets are not stable under even constant simulation overhead.
-/

namespace ComplexityOfGenerators

variable (α : Type) [Fintype α]

/-- The empty generator, preceded by one silent transition. -/
def delayedEmptyGenerator : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 2
  symbols := 0
  initial := 0
  transition := fun q _ _ _ _ => if q = 0 then
    .step 1 none .stay .stay .stay .stay none else .readRandom 1 1

def delayedEmptyConfiguration (n : ℕ) : Configuration (delayedEmptyGenerator α) where
  state := (1 : Fin 2)
  inputHead := 0
  auxiliaryHead := 0
  indexHead := 0
  randomHead := n
  workHead := 0
  work := fun _ => none
  visited := {0}
  output := []

theorem delayedEmptyGenerator_run (data : InputData Unit Bool) (bits : BitString) (t : ℕ) :
    (delayedEmptyGenerator α).run data bits (t + 1) =
      if t < bits.length then .running (delayedEmptyConfiguration α t) else .halted .exhausted := by
  induction t with
  | zero =>
      simp [Machine.run, Machine.observe, Machine.next, Machine.initialConfiguration,
        delayedEmptyGenerator, delayedEmptyConfiguration, Move.onInput, Move.onInt]
  | succ t ih =>
      rw [Machine.run, ih]
      by_cases available : t < bits.length
      · simp only [available, ite_true]
        have bit : ∃ b, bits[t]? = some b := by
          exact ⟨bits[t], List.getElem?_eq_getElem available⟩
        obtain ⟨b, bit⟩ := bit
        simp [Machine.next, Machine.observe, delayedEmptyGenerator,
          delayedEmptyConfiguration, bit]
      · have exhausted : ¬ t + 1 < bits.length := by omega
        simp [available, exhausted]

/-- Its language is empty and it halts on every finite tape, as required of a
generator. The one-step delay changes no generated-language semantics. -/
theorem delayedEmptyGenerator_isGenerator (data : InputData Unit Bool) :
    (delayedEmptyGenerator α).IsGenerator data := by
  let M := delayedEmptyGenerator α
  have noAccepts : ∀ bits, ¬ M.Accepts data bits := by
    rintro bits ⟨word, t, accepted⟩
    cases t with
    | zero => simp [M, Machine.run, Machine.observe, Machine.initialConfiguration, delayedEmptyGenerator] at accepted
    | succ t =>
        rw [delayedEmptyGenerator_run] at accepted
        split_ifs at accepted; cases accepted
  have emptyEvent : M.acceptedStreams data = ∅ := by
    ext stream
    simp only [Machine.acceptedStreams, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨bits, _, accepts⟩
    exact noAccepts bits accepts
  refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
  · intro bits
    exact ⟨bits.length + 1, .exhausted, by simp [delayedEmptyGenerator_run]⟩
  · intro bits t rejected
    cases t with
    | zero => simp [Machine.run, Machine.observe, Machine.initialConfiguration, delayedEmptyGenerator] at rejected
    | succ t =>
        rw [delayedEmptyGenerator_run] at rejected
        split_ifs at rejected; cases rejected
  · rw [emptyEvent]
    simp

/-- There is no equal seed/step budget for this generator, however large. -/
theorem delayedEmptyGenerator_not_generatorTimeBound (data : InputData Unit Bool) (t : ℕ) :
    ¬ (delayedEmptyGenerator α).GeneratorTimeBound data t t := by
  intro bound
  obtain ⟨result, halted⟩ := bound.1 (List.replicate t false) (by simp)
  cases t with
  | zero =>
      simp [Machine.run, Machine.observe, Machine.initialConfiguration, delayedEmptyGenerator] at halted
  | succ t =>
      rw [delayedEmptyGenerator_run] at halted
      simp at halted

end ComplexityOfGenerators
