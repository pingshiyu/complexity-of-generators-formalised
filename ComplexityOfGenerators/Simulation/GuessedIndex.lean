import ComplexityOfGenerators.Simulation.GeneratorRecognizerCorrectness
import ComplexityOfGenerators.Foundations.RandomTapeShift
import ComplexityOfGenerators.Simulation.CompositionExecution

/-!
# Guessing a virtual generator index

The random tape starts with `i` true bits and one false delimiter. A finite
loader writes the unary virtual index before handing control to the existing
index simulator and streaming output matcher. No bound or oracle is hidden in
finite control; polynomial clocking is applied only by the NP criterion.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

/-- States: initialize, read a digit, mark a live cell, return, finish. -/
def guessedIndexLoader : Machine α Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 5
  symbols := Fintype.card (IndexCell M.symbols) + 1
  initial := 0
  transition := fun state _ _ _ raw =>
    match state.val with
    | 0 => .step 1 (some (indexWrite M ⟨none, true, false, true, true⟩))
        .stay .stay .stay .stay none
    | 1 => .readRandom 3 2
    | 2 => .step 1 (some (indexWrite M {indexRead M raw with live := true}))
        .right .stay .stay .stay none
    | 3 => if (indexRead M raw).origin then .step 4 none .stay .stay .stay .stay none
        else .step 3 none .left .stay .stay .stay none
    | _ => .accept

/-- The guessed index is followed by the generator's own random tape. -/
def indexChoice (i : ℕ) : BitString := List.replicate i true ++ [false]

/-- Invariant at the next digit of the unary index. -/
structure Guessing (j : ℕ) (c : Configuration (guessedIndexLoader M)) : Prop where
  state : c.state = (1 : Fin 5)
  head : c.workHead = (j : ℤ)
  random : c.randomHead = j
  input : c.inputHead = 0
  auxiliary : c.auxiliaryHead = 0
  index : c.indexHead = 0
  output : c.output = []
  memory : VirtualIndexMemory M j (fun _ => none) (some 0) (some 0) c.work

omit [Fintype α] in
theorem virtualIndexMemory_grow (j : ℕ)
    (work : ℤ → Option (Fin (Fintype.card (IndexCell M.symbols) + 1)))
    (memory : VirtualIndexMemory M j (fun _ => none) (some 0) (some 0) work) :
    VirtualIndexMemory M (j + 1) (fun _ => none) (some 0) (some 0)
      (Function.update work (j : ℤ)
        (some (indexWrite M {indexRead M (work j) with live := true}))) := by
  intro z
  by_cases same : z = (j : ℤ)
  · subst z
    rw [Function.update_self, indexRead_write, memory]
    simp [virtualIndexCell]
  · rw [Function.update_of_ne same, memory]
    have live : (0 ≤ z ∧ z < ((j + 1 : ℕ) : ℤ)) ↔ (0 ≤ z ∧ z < (j : ℤ)) := by omega
    simp only [virtualIndexCell, live]

theorem guessedIndex_begin (w : List α) (bits : BitString) :
    ∃ c, Guessing M 0 c ∧
      (guessedIndexLoader M).run (decisionData w) bits 1 =
        (guessedIndexLoader M).observe (decisionData w) bits c := by
  let N := guessedIndexLoader M
  let c := N.stepConfiguration (decisionData w) N.initialConfiguration
    (1 : Fin 5) (some (indexWrite M ⟨none, true, false, true, true⟩))
    .stay .stay .stay .stay none
  have mem : VirtualIndexMemory M 0 (fun _ => none) (some 0) (some 0) c.work := by
    intro z
    by_cases same : z = 0
    · subst z
      simp [c, Machine.stepConfiguration, Machine.initialConfiguration, virtualIndexCell]
    · have notlive : ¬(0 ≤ z ∧ z < (0 : ℤ)) := by omega
      simp only [c, Machine.stepConfiguration, Machine.initialConfiguration, Function.update_of_ne same]
      change (⟨none, false, false, false, false⟩ : IndexCell M.symbols) = _
      simp [virtualIndexCell, same, Ne.symm same, -Bool.decide_and, notlive]

  refine ⟨c, ⟨rfl, by simp [c, Machine.stepConfiguration, Machine.initialConfiguration, Move.onInt],
    rfl, rfl, rfl, rfl, rfl, mem⟩, ?_⟩
  exact N.runFrom_shift (decisionData w) bits N.initialConfiguration c rfl (by simp [N, Machine.next, guessedIndexLoader, Machine.initialConfiguration, c, Machine.stepConfiguration]) 0

theorem guessedIndex_advance (w : List α) (bits : BitString) (j : ℕ)
    (c : Configuration (guessedIndexLoader M)) (h : Guessing M j c)
    (digit : bits[j]? = some true) :
    ∃ d, Guessing M (j + 1) d ∧
      (guessedIndexLoader M).runFrom (decisionData w) bits c 2 =
        (guessedIndexLoader M).observe (decisionData w) bits d := by
  let N := guessedIndexLoader M
  let read : Configuration N := {c with state := (2 : Fin 5), randomHead := j + 1}
  have available : j < bits.length := List.getElem?_eq_some_iff.mp digit |>.1
  have live : N.observe (decisionData w) bits c = .running c := by
    simp [N, Machine.observe, guessedIndexLoader, h.state, h.random, available]
  have next : N.next (decisionData w) bits c = .running read := by
    simp [N, Machine.next, guessedIndexLoader, h.state, h.random, digit, read]
  let d := N.stepConfiguration (decisionData w) read (1 : Fin 5)
    (some (indexWrite M {indexRead M (read.work read.workHead) with live := true}))
    .right .stay .stay .stay none
  have writeRun : N.runFrom (decisionData w) bits read 1 = N.observe (decisionData w) bits d := by
    exact N.runFrom_shift _ _ _ d rfl (by simp [N, Machine.next, guessedIndexLoader, read, d, Machine.stepConfiguration]) 0
  refine ⟨d, ⟨rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [d, Machine.stepConfiguration, read, h.head, Move.onInt]
  · simp [d, Machine.stepConfiguration, read, h.input, Move.onInput]
  · simp [d, Machine.stepConfiguration, read, h.auxiliary, Move.onInput]
  · simp [d, Machine.stepConfiguration, read, h.index, Move.onInput]
  · exact h.output
  · simpa only [d, Machine.stepConfiguration, read, h.head] using
      virtualIndexMemory_grow M j c.work h.memory
  · rw [show 2 = 1 + 1 from rfl, N.runFrom_shift _ _ c read live next 1]
    exact writeRun

theorem guessedIndex_digits (w : List α) (bits : BitString) (j k : ℕ)
    (c : Configuration (guessedIndexLoader M)) (h : Guessing M j c)
    (digits : ∀ z, j ≤ z → z < j + k → bits[z]? = some true) :
    ∃ d, Guessing M (j + k) d ∧
      (guessedIndexLoader M).runFrom (decisionData w) bits c (2 * k) =
        (guessedIndexLoader M).observe (decisionData w) bits d := by
  induction k generalizing j c with
  | zero => exact ⟨c, by simpa using h, rfl⟩
  | succ k ih =>
    obtain ⟨d, hd, step⟩ := guessedIndex_advance M w bits j c h (digits j le_rfl (by omega))
    obtain ⟨e, he, run⟩ := ih (j + 1) d hd (by intro z lo hi; exact digits z (by omega) (by omega))
    refine ⟨e, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he, ?_⟩
    rw [show 2 * (k + 1) = 2 + 2 * k by omega,
      (guessedIndexLoader M).runFrom_add _ _ c d 2 step]
    exact run


/-- A false delimiter ends the index, and a work-only scan restores its origin. -/
theorem guessedIndex_finish (w : List α) (bits : BitString) (j : ℕ)
    (c : Configuration (guessedIndexLoader M)) (h : Guessing M j c)
    (digit : bits[j]? = some false) :
    ∃ d, d.state = (3 : Fin 5) ∧ d.workHead = 0 ∧ d.randomHead = j + 1 ∧
      d.inputHead = 0 ∧ d.auxiliaryHead = 0 ∧ d.indexHead = 0 ∧ d.output = [] ∧
      VirtualIndexMemory M j (fun _ => none) (some 0) (some 0) d.work ∧
      (guessedIndexLoader M).runFrom (decisionData w) bits c (j + 1) =
        (guessedIndexLoader M).observe (decisionData w) bits d := by
  let N := guessedIndexLoader M
  let read : Configuration N := {c with state := (3 : Fin 5), randomHead := j + 1}
  have available : j < bits.length := List.getElem?_eq_some_iff.mp digit |>.1
  have live : N.observe (decisionData w) bits c = .running c := by
    simp [N, Machine.observe, guessedIndexLoader, h.state, h.random, available]
  have next : N.next (decisionData w) bits c = .running read := by
    simp [N, Machine.next, guessedIndexLoader, h.state, h.random, digit, read]
  have bounds : ReadHeadBounds N (decisionData w) read := by
    constructor <;> simp [read, h.input, h.auxiliary, h.index, decisionData]
  obtain ⟨d, scan, run⟩ := tapeScan_with_heads N (decisionData w) bits read (3 : Fin 5)
    (fun z => ((j - z : ℕ) : ℤ)) (fun _ => .left) j bounds rfl
    (by simpa [read] using h.head)
    (by intro z hz; simp only [Move.onInt]; omega)
    (by intro z hz input auxiliary index
        have nonzero : (j - z : ℕ) ≠ 0 := by omega
        simp only [N, guessedIndexLoader, read]
        simp [h.memory _, virtualIndexCell, nonzero])
  refine ⟨d, scan.state, by simpa using scan.head, scan.random, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact scan.input.trans h.input
  · exact scan.auxiliary.trans h.auxiliary
  · exact scan.index.trans h.index
  · exact scan.output.trans h.output
  · rw [scan.memory]; exact h.memory
  · rw [N.runFrom_shift _ _ c read live next j]
    exact run

/-- Every unary choice has a fully initialized virtual index, in linear time. -/
theorem guessedIndex_loaded (w : List α) (i : ℕ) (tail : BitString) :
    ∃ d : Configuration (guessedIndexLoader M),
      d.state = (3 : Fin 5) ∧ d.workHead = 0 ∧ d.randomHead = i + 1 ∧
      d.inputHead = 0 ∧ d.auxiliaryHead = 0 ∧ d.indexHead = 0 ∧ d.output = [] ∧
      VirtualIndexMemory M i (fun _ => none) (some 0) (some 0) d.work ∧
      (guessedIndexLoader M).run (decisionData w) (indexChoice i ++ tail) (3 * i + 2) =
        (guessedIndexLoader M).observe (decisionData w) (indexChoice i ++ tail) d := by
  let bits := indexChoice i ++ tail
  obtain ⟨c, hc, start⟩ := guessedIndex_begin M w bits
  obtain ⟨d, hd, digits⟩ := guessedIndex_digits M w bits 0 i c hc (by
    intro z _ hz
    have hz' : z < i := by omega
    simp [bits, indexChoice, List.getElem?_append_left (show z < (List.replicate i true).length by simpa using hz'), hz'])
  have hd' : Guessing M i d := by simpa using hd
  have delimiter : bits[i]? = some false := by simp [bits, indexChoice]
  obtain ⟨e, st, wh, rh, inp, aux, ind, out, mem, finish⟩ := guessedIndex_finish M w bits i d hd' delimiter
  refine ⟨e, st, wh, rh, inp, aux, ind, out, mem, ?_⟩
  change (guessedIndexLoader M).run (decisionData w) bits _ = _
  rw [← (guessedIndexLoader M).runFrom_initial] at start
  rw [show 3 * i + 2 = 1 + (2 * i + (i + 1)) by omega,
      ← (guessedIndexLoader M).runFrom_initial,
      (guessedIndexLoader M).runFrom_add _ _ _ c 1 start,
      (guessedIndexLoader M).runFrom_add _ _ c d (2 * i) digits]
  exact finish


/-- A finite bit tape either exhausts during the index or has a unique delimiter. -/
theorem indexChoice_cases (bits : BitString) :
    (∃ i, bits = List.replicate i true) ∨ ∃ i tail, bits = indexChoice i ++ tail := by
  induction bits with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons bit bits ih =>
    cases bit with
    | false => exact Or.inr ⟨0, bits, rfl⟩
    | true =>
      rcases ih with ⟨i, rfl⟩ | ⟨i, tail, rfl⟩
      · exact Or.inl ⟨i + 1, by simp [List.replicate_succ]⟩
      · exact Or.inr ⟨i + 1, tail, by simp [indexChoice, List.replicate_succ]⟩

theorem guessedIndex_exhausted (w : List α) (i : ℕ) :
    (guessedIndexLoader M).run (decisionData w) (List.replicate i true) (2 * i + 1) =
      .halted .exhausted := by
  let N := guessedIndexLoader M
  let bits := List.replicate i true
  obtain ⟨c, hc, begin⟩ := guessedIndex_begin M w bits
  obtain ⟨d, hd, digits⟩ := guessedIndex_digits M w bits 0 i c hc (by
    intro z _ hi
    simp [bits, show z < i by omega])
  have terminal : N.observe (decisionData w) bits d = .halted .exhausted := by
    simp [N, Machine.observe, guessedIndexLoader, hd.state, hd.random, bits]
  change N.run (decisionData w) bits _ = _
  rw [← N.runFrom_initial] at begin ⊢
  rw [show 2 * i + 1 = 1 + 2 * i by omega, N.runFrom_add _ _ _ c 1 begin, digits]
  exact terminal

end
end ComplexityOfGenerators.Simulation
