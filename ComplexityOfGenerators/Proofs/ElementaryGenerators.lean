import ComplexityOfGenerators.Foundations.BoundedGeneration
import ComplexityOfGenerators.Proofs.GeneratorSupport

/-!
# Concrete boundary-case generators

The empty language uses a machine that consumes every random bit and halts by
exhaustion. A singleton uses a finite machine that emits its fixed word before
accepting. Neither construction puts arbitrary computation in a transition.
-/

namespace ComplexityOfGenerators

variable {α : Type} [Fintype α]

/-- The empty generator's only instruction consumes one random bit. -/
def emptyGenerator (α : Type) [Fintype α] : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 0
  initial := 0
  transition := fun _ _ _ _ _ => .readRandom 0 0

def emptyGeneratorConfiguration (α : Type) [Fintype α] (t : ℕ) :
    Configuration (emptyGenerator α) :=
  { (emptyGenerator α).initialConfiguration with randomHead := t }

theorem emptyGenerator_run (data : InputData Unit Bool) (bits : BitString) (t : ℕ) :
    (emptyGenerator α).run data bits t =
      if t < bits.length then .running (emptyGeneratorConfiguration α t)
      else .halted .exhausted := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Machine.run, ih]
      by_cases available : t < bits.length
      · rw [ite_eq_left available]
        have lookup := List.getElem?_eq_getElem available
        simp only [Machine.next, emptyGenerator, emptyGeneratorConfiguration,
          Machine.initialConfiguration, lookup]
        cases bits[t] <;>
          simp [Machine.observe]
      · have finished : ¬ t + 1 < bits.length := by omega
        simp [available, finished]

theorem emptyGenerator_isGenerator :
    (emptyGenerator α).IsGenerator (generatorData 0) := by
  have noAccepts : ∀ bits, ¬ (emptyGenerator α).Accepts (generatorData 0) bits := by
    rintro bits ⟨word, t, accepted⟩
    rw [emptyGenerator_run] at accepted
    split_ifs at accepted; cases accepted
  have emptyEvent : (emptyGenerator α).acceptedStreams (generatorData 0) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro stream ⟨bits, member, accepted⟩
    exact noAccepts bits accepted
  refine ⟨⟨?_, ?_⟩, Or.inr ?_⟩
  · intro bits
    exact ⟨bits.length, .exhausted, by simp [emptyGenerator_run]⟩
  · intro bits t
    rw [emptyGenerator_run]
    split_ifs <;> simp
  · simp [emptyEvent]

theorem empty_language_in_gen : (∅ : Language α) ∈ GEN α := by
  refine ⟨emptyGenerator α, emptyGenerator_isGenerator, ?_⟩
  exact ((emptyGenerator α).acceptedStreams_eq_empty_iff (generatorData 0)).mp (by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro stream ⟨bits, member, word, t, accepted⟩
    rw [emptyGenerator_run] at accepted
    split_ifs at accepted; cases accepted)

/-- A deterministic recognizer that loops on every input, for the empty RE
language. Its transition is a single ordinary native instruction. -/
def emptyRecognizer (α : Type) [Fintype α] : Machine α Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 0
  initial := 0
  transition := fun _ _ _ _ _ => .step 0 none .stay .stay .stay .stay none

theorem emptyRecognizer_run (input : List α) (bits : BitString) (t : ℕ) :
    ∃ c, (emptyRecognizer α).run (decisionData input) bits t = .running c := by
  let M := emptyRecognizer α
  have observation (c : Configuration M) : M.observe (decisionData input) bits c = .running c := by
    simp [M, Machine.observe, emptyRecognizer]
  induction t with
  | zero => exact ⟨M.initialConfiguration, observation _⟩
  | succ t ih =>
      obtain ⟨c, run⟩ := ih
      let d := M.stepConfiguration (decisionData input) c M.initial none .stay .stay .stay .stay none
      have next : M.next (decisionData input) bits c = .running d :=
        M.next_step (decisionData input) bits c _ _ _ _ _ _ _ rfl
      refine ⟨d, ?_⟩
      rw [Machine.run, run]
      dsimp only
      rw [next]
      exact observation d

theorem empty_language_in_re : (∅ : Language α) ∈ RE α := by
  refine ⟨emptyRecognizer α, ?_, ?_⟩
  · unfold Machine.Deterministic
    intro q input auxiliary index work
    simp [emptyRecognizer]
  · intro input
    constructor
    · rintro ⟨word, t, accepted⟩
      obtain ⟨c, run⟩ := emptyRecognizer_run input [] t
      rw [run] at accepted
      cases accepted
    · intro member
      exact False.elim member

/-- One output symbol per transition, followed by acceptance. -/
def wordEmitter (word : List α) : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := word.length + 1
  symbols := 0
  initial := ⟨0, by omega⟩
  transition := fun q _ _ _ _ =>
    if available : q.val < word.length then
      .step ⟨q.val + 1, by omega⟩ none .stay .stay .stay .stay (some word[q.val])
    else .accept

def wordEmitterConfiguration (word : List α) (k : ℕ) (bound : k ≤ word.length) :
    Configuration (wordEmitter word) :=
  { (wordEmitter word).initialConfiguration with
    state := ⟨k, by change k < word.length + 1; omega⟩
    output := word.take k }

theorem wordEmitter_observe_live (word : List α) (data : InputData Unit Bool)
    (bits : BitString) (k : ℕ) (available : k < word.length) :
    (wordEmitter word).observe data bits (wordEmitterConfiguration word k available.le) =
      .running (wordEmitterConfiguration word k available.le) := by
  simp [Machine.observe, wordEmitter, wordEmitterConfiguration, available]

theorem wordEmitter_next (word : List α) (data : InputData Unit Bool)
    (bits : BitString) (k : ℕ) (available : k < word.length) :
    (wordEmitter word).next data bits (wordEmitterConfiguration word k available.le) =
      .running (wordEmitterConfiguration word (k + 1) (by omega)) := by
  simp only [Machine.next, wordEmitter, wordEmitterConfiguration, Machine.initialConfiguration,
    dite_eq_left available, Move.onInt, Move.onInput, Nat.zero_min,
    Finset.insert_eq_of_mem (by simp : (0 : ℤ) ∈ ({0} : Finset ℤ))]
  rw [List.take_succ_eq_append_getElem available]

theorem wordEmitter_run (word : List α) (data : InputData Unit Bool)
    (bits : BitString) (k : ℕ) (bound : k ≤ word.length) :
    (wordEmitter word).run data bits k =
      (wordEmitter word).observe data bits (wordEmitterConfiguration word k bound) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have available : k < word.length := by omega
      rw [Machine.run, ih available.le, wordEmitter_observe_live word data bits k available]
      dsimp only
      rw [wordEmitter_next word data bits k available]

theorem wordEmitter_produces (word : List α) (data : InputData Unit Bool) (bits : BitString) :
    (wordEmitter word).Produces data bits word := by
  refine ⟨word.length, ?_⟩
  rw [wordEmitter_run word data bits word.length le_rfl]
  simp [Machine.observe, wordEmitter, wordEmitterConfiguration]

theorem wordEmitter_isGenerator (word : List α) :
    (wordEmitter word).IsGenerator (generatorData 0) := by
  have produces := wordEmitter_produces word (generatorData 0)
  have allStreams : (wordEmitter word).acceptedStreams (generatorData 0) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro stream
    exact ⟨[], by simp [cylinder], word, produces []⟩
  refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
  · intro bits
    obtain ⟨t, accepted⟩ := produces bits
    exact ⟨t, .accepted word, accepted⟩
  · intro bits t rejected
    obtain ⟨s, accepted⟩ := produces bits
    have impossible := (wordEmitter word).halted_outcome_unique (generatorData 0) bits
      t s .rejected (.accepted word) rejected accepted
    cases impossible
  · rw [allStreams]
    exact MeasureTheory.measure_univ

theorem singleton_language_in_gen (word : List α) : ({word} : Language α) ∈ GEN α := by
  refine ⟨wordEmitter word, wordEmitter_isGenerator word, ?_⟩
  ext output
  constructor
  · rintro ⟨bits, nonempty, produces⟩
    exact (wordEmitter word).produces_unique (generatorData 0) bits output word produces
      (wordEmitter_produces word (generatorData 0) bits)
  · intro member
    have equal : output = word := member
    subst output
    exact ⟨[false], by simp, wordEmitter_produces word (generatorData 0) [false]⟩

end ComplexityOfGenerators
