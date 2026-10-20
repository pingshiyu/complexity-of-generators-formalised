import ComplexityOfGenerators.Simulation.WordStack.SourceLocal
import ComplexityOfGenerators.Simulation.WordStack.RawRun

namespace ComplexityOfGenerators.Simulation.WordStack.Source

variable {I A O : Type} (M : Machine I A O)

/-- A snapshot represents all observable parts of a source configuration.
The visited-cell set is irrelevant to this time-bounded interpreter. -/
structure Represents (data : InputData I A) (bits : BitString)
    (s : Snapshot M) (c : ComplexityOfGenerators.Configuration M) : Prop where
  state : s.status = .live c.state
  input_word : s.input.word = data.input
  input_pos : s.input.position = c.inputHead
  auxiliary_word : s.auxiliary.word = data.auxiliary
  auxiliary_pos : s.auxiliary.position = c.auxiliaryHead
  index_word : s.index.word = List.replicate data.index ()
  index_pos : s.index.position = c.indexHead
  work : ∀ i, s.work.cell none (i - c.workHead) = c.work i
  random : s.random = bits.drop c.randomHead
  output : s.output = c.output.reverse

namespace Represents

variable {M} {data : InputData I A} {bits : BitString}
    {s : Snapshot M} {c : ComplexityOfGenerators.Configuration M}

lemma input_read (h : Represents M data bits s c) : s.input.read = data.input[c.inputHead]? := by
  rw [Zipper.read_eq, h.input_word, h.input_pos]
lemma auxiliary_read (h : Represents M data bits s c) : s.auxiliary.read = data.auxiliary[c.auxiliaryHead]? := by
  rw [Zipper.read_eq, h.auxiliary_word, h.auxiliary_pos]
lemma index_read (h : Represents M data bits s c) :
    s.index.read = if c.indexHead < data.index then some () else none := by
  rw [Zipper.read_eq, h.index_word, h.index_pos, List.getElem?_replicate]
lemma work_read (h : Represents M data bits s c) : s.work.read.getD none = c.work c.workHead := by
  simpa [Zipper.cell_zero, Zipper.read] using h.work c.workHead
lemma random_read (h : Represents M data bits s c) : s.random.head? = bits[c.randomHead]? := by
  rw [h.random, List.head?_drop]

lemma random_step (h : Represents M data bits s c) (q : Fin M.states) (b : Bool) (rest : List Bool)
    (word : s.random = b :: rest) :
    Represents M data bits {s with status := .live q, random := rest}
      {c with state := q, randomHead := c.randomHead + 1} := by
  refine ⟨rfl, h.input_word, h.input_pos, h.auxiliary_word, h.auxiliary_pos,
    h.index_word, h.index_pos, h.work, ?_, h.output⟩
  have tail := congrArg List.tail (word.symm.trans h.random)
  simpa [List.tail_drop] using tail

lemma native_step (h : Represents M data bits s c) (q : Fin M.states)
    (write : Option (Fin M.symbols)) (wm im am nm : Move) (emit : Option O) :
    Represents M data bits
      {s with status := .live q
              input := s.input.clampedMove im
              auxiliary := s.auxiliary.clampedMove am
              index := s.index.clampedMove nm
              work := (match write with | none => s.work | some a => s.work.write (some a)).workMove none wm
              output := match emit with | none => s.output | some a => a :: s.output}
      (M.stepConfiguration data c q write wm im am nm emit) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.random, ?_⟩
  · simpa only [Zipper.clampedMove_word] using h.input_word
  · simp only [Zipper.clampedMove_position, h.input_word, h.input_pos, Machine.stepConfiguration]
  · simpa only [Zipper.clampedMove_word] using h.auxiliary_word
  · simp only [Zipper.clampedMove_position, h.auxiliary_word, h.auxiliary_pos, Machine.stepConfiguration]
  · simpa only [Zipper.clampedMove_word] using h.index_word
  · simp only [Zipper.clampedMove_position, h.index_word, h.index_pos, List.length_replicate,
      Machine.stepConfiguration]
  · intro i
    change ((match write with | none => s.work | some a => s.work.write (some a)).workMove none wm).cell none
      (i - wm.onInt c.workHead) = _
    rw [Zipper.workMove_absolute]
    cases write with
    | none => exact h.work i
    | some a =>
      rw [Zipper.cell_write]
      change (if i - c.workHead = 0 then some a else s.work.cell none (i - c.workHead)) =
        Function.update c.work c.workHead (some a) i
      rw [h.work]
      by_cases same : i = c.workHead <;> simp [same, sub_eq_zero]
  · cases emit <;> simp [Machine.stepConfiguration, h.output]

end Represents

def Related (data : InputData I A) (bits : BitString) (s : Snapshot M) : RunState M → Prop
  | .running c => Represents M data bits s c
  | .halted (.accepted word) => s.status = .accepted ∧ s.output = word.reverse
  | .halted .rejected => s.status = .rejected
  | .halted .exhausted => s.status = .exhausted

theorem related_step (data : InputData I A) (bits : BitString) (s : Snapshot M) (r : RunState M)
    (h : Related M data bits s r) : Related M data bits (s.step M) (M.rawTick data bits r) := by
  cases r with
  | halted result =>
    cases result with
    | accepted word => exact ⟨by simp [Snapshot.step, h.1], by simpa [Snapshot.step, h.1] using h.2⟩
    | rejected =>
      change s.status = .rejected at h
      simp [Related, Machine.rawTick, Snapshot.step, h]
    | exhausted =>
      change s.status = .exhausted at h
      simp [Related, Machine.rawTick, Snapshot.step, h]
  | running c =>
    change Represents M data bits s c at h
    simp only [Machine.rawTick, Snapshot.step, h.state, h.input_read, h.auxiliary_read,
      h.index_read, h.work_read, Machine.next]
    cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
    | accept => exact ⟨rfl, h.output⟩
    | reject => rfl
    | readRandom no yes =>
      cases random : s.random with
      | nil =>
        have absent : bits[c.randomHead]? = none := by rw [← h.random_read, random]; rfl
        simp [absent, Related]
      | cons b rest =>
        have present : bits[c.randomHead]? = some b := by rw [← h.random_read, random]; rfl
        simpa only [present, Related] using h.random_step (if b then yes else no) b rest random
    | step q write wm im am nm emit =>
      exact h.native_step q write wm im am nm emit

def initial (data : InputData I A) (bits : BitString) : Snapshot M where
  status := .live M.initial
  input := ⟨[], data.input⟩
  auxiliary := ⟨[], data.auxiliary⟩
  index := ⟨[], List.replicate data.index ()⟩
  work := ⟨[], []⟩
  random := bits
  output := []

theorem initial_related (data : InputData I A) (bits : BitString) :
    Related M data bits (initial M data bits) (.running M.initialConfiguration) := by
  constructor <;> try rfl
  intro i
  simp [initial, Machine.initialConfiguration, Zipper.cell]

theorem iterate_related (data : InputData I A) (bits : BitString) (t : ℕ) :
    Related M data bits ((Snapshot.step M)^[t] (initial M data bits))
      (M.rawRun data bits (.running M.initialConfiguration) t) := by
  induction t with
  | zero => exact initial_related M data bits
  | succ t ih =>
    simpa only [Function.iterate_succ_apply', Machine.rawRun] using
      related_step M data bits _ _ ih

/-- Acceptance after `time + 1` interpreted steps agrees with the existing
source-machine evaluator at `time`. -/
theorem iterate_accept (data : InputData I A) (bits : BitString) (time : ℕ) (word : List O)
    (run : M.run data bits time = .halted (.accepted word)) :
    let s := (Snapshot.step M)^[time + 1] (initial M data bits)
    s.status = .accepted ∧ s.output = word.reverse := by
  have raw := (M.rawRun_correct data bits M.initialConfiguration time (.accepted word)).mpr
    (by simpa using run)
  have h := iterate_related M data bits (time + 1)
  rw [raw] at h
  exact h

end ComplexityOfGenerators.Simulation.WordStack.Source
