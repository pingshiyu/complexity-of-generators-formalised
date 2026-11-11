import ComplexityOfGenerators.Simulation.WordStack.SourceCall
import ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame
import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomInput
import ComplexityOfGenerators.Simulation.WordStack.Output
import ComplexityOfGenerators.Proofs.CommandGenerators
import ComplexityOfGenerators.Simulation.BinaryOutputDecoder

/-!
# Finite, uniformly clocked search over expected-length generator indices

At physical index `n`, the search collects one finite random block and replays
it at every virtual source index up to twice the requested collision length.
Reusing this same block needs no probabilistic independence assertion. All
source calls are interpreted with a finite unary clock and an isolated seed.
-/

namespace ComplexityOfGenerators.Simulation.ExpectedCollisionSearch

open WordStack

noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive Symbol (M : Machine Unit Bool Bool)
  | source (cell : Source.Symbol M)
  | bit (b : Bool)
  | unit
  deriving Fintype

variable (M : Machine Unit Bool Bool)

abbrev Cell := Symbol M
abbrev Store := Local.Store (Cell M) 35
abbrev Controller := WordStack.Routine (Cell M) Bool 35

def target (n : ℕ) : ℕ := 4 * (n + 1) + 2

def trials (n : ℕ) : ℕ := 2 * target n + 1

def sourceSlots : Source.Layout 35 where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j eq; exact Fin.ext (congrArg (fun i : Fin 35 => i.val) eq)

@[simp] theorem sourceSlots_apply (i : Fin 17) : sourceSlots i = ⟨i.val, by omega⟩ := rfl

def counterSlots (dst : Fin 35)
    (different : dst ≠ 24 ∧ dst ≠ 25 ∧ dst ≠ 26 ∧ dst ≠ 27) : CounterRoutine.Layout 35 where
  toFun | 0 => 24 | 1 => dst | 2 => 25 | 3 => 26 | 4 => 27
  inj' := by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all [ne_comm]

@[simp] theorem counterSlots_apply (dst : Fin 35) (different) (i : Fin 5) :
    counterSlots dst different i = match i with | 0 => 24 | 1 => dst | 2 => 25 | 3 => 26 | 4 => 27 := rfl

def counter (dst : Fin 35) (different : dst ≠ 24 ∧ dst ≠ 25 ∧ dst ≠ 26 ∧ dst ≠ 27)
    (p : PolynomialBound) : Controller M := CounterRoutine.routine (counterSlots dst different) p .unit

@[simp] theorem counter_eval (dst : Fin 35) (different) (p : PolynomialBound) (s : Store M) :
    (counter M dst different p).eval s =
      Function.update (Function.update (Function.update (Function.update s 27 [])
        25 (List.replicate ((s 24).length + 1) .unit)) 26 [])
        dst (List.replicate (p (s 24).length) .unit) := by
  simp [counter, CounterRoutine.routine_eval]

def sourceDecode : Cell M → Source.Symbol M
  | .source cell => cell
  | _ => .unit

def sourceBit : Cell M → Cell M
  | .bit b => .source (.bit b)
  | _ => .source (.bit false)

def outputBit : Cell M → Cell M
  | .source (.output b) => .bit b
  | _ => .unit

def decodeBit : Cell M → Option Bool
  | .bit b => some b
  | _ => none

def lengthSlots : LengthTest.Layout 35 where
  toFun | 0 => 19 | 1 => 22 | 2 => 28 | 3 => 29 | 4 => 20 | 5 => 21
  inj' := by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem lengthSlots_apply (i : Fin 6) :
    lengthSlots i = match i with | 0 => 19 | 1 => 22 | 2 => 28 | 3 => 29 | 4 => 20 | 5 => 21 := rfl

def takeOutput : Controller M :=
  (WordStack.Routine.clear 19).seq (WordStack.Routine.transfer 10 19 (by decide) (outputBit M))

@[simp] theorem takeOutput_eval (s : Store M) :
    (takeOutput M).eval s = Function.update (Function.update s 10 []) 19 ((s 10).reverse.map (outputBit M)) := by
  funext j
  by_cases h : j = 10 <;> by_cases h' : j = 19 <;>
    simp_all [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.transfer, Function.update_apply]

def offer : Controller M :=
  WordStack.Routine.branch 0 fun status => match status with
    | some (.source (.state .accepted)) =>
      (takeOutput M).seq ((LengthTest.routine lengthSlots (Symbol.unit : Cell M)).seq
        (WordStack.Routine.branch 28 fun matchLength => if matchLength.isSome then
          WordStack.Routine.assign 19 34 18 (by decide) (by decide) (by decide) id else WordStack.Routine.skip))
    | _ => WordStack.Routine.skip

def sourceCall : Controller M :=
  Source.call M sourceSlots Symbol.source (sourceDecode M)
    (fun _ => .source .unit) (fun _ => .source .unit) (sourceBit M)

def trialSetup (p : PolynomialBound) : Controller M :=
  (WordStack.Routine.assign 17 14 18 (by decide) (by decide) (by decide) id).seq
  ((counter M 16 (by decide) p).seq (WordStack.Routine.ofLocal (Local.push 16 .unit)))

def sourceTrial (p : PolynomialBound) : Controller M := (trialSetup M p).seq (sourceCall M)

def trial (p : PolynomialBound) : Controller M :=
  (sourceTrial M p).seq ((offer M).seq (WordStack.Routine.ofLocal (Local.push 13 .unit)))

def targetCounter : Controller M :=
  (counter M 22 (by decide) ⟨4, 1, by decide⟩).seq
  ((WordStack.Routine.ofLocal (Local.push 22 .unit)).seq (WordStack.Routine.ofLocal (Local.push 22 .unit)))

def trialsCounter : Controller M :=
  (counter M 23 (by decide) ⟨8, 1, by decide⟩).seq
  ((WordStack.Routine.ofLocal (Local.push 23 .unit)).seq
  ((WordStack.Routine.ofLocal (Local.push 23 .unit)).seq
  ((WordStack.Routine.ofLocal (Local.push 23 .unit)).seq
  ((WordStack.Routine.ofLocal (Local.push 23 .unit)).seq (WordStack.Routine.ofLocal (Local.push 23 .unit))))))

@[simp] theorem trialSetup_eval (p : PolynomialBound) (s : Store M) :
    (trialSetup M p).eval s =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update s 18 []) 14 (s 17)) 27 [])
        25 (List.replicate ((s 24).length + 1) .unit)) 26 [])
        16 (List.replicate (p (s 24).length + 1) .unit) := by
  funext j
  by_cases h14 : j = 14 <;> by_cases h16 : j = 16 <;>
    by_cases h18 : j = 18 <;> by_cases h25 : j = 25 <;>
    by_cases h26 : j = 26 <;> by_cases h27 : j = 27 <;>
    simp_all [trialSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal, Local.eval_push, Function.update_apply, List.replicate_succ]

theorem sourceTrial_fixed (p : PolynomialBound) (s : Store M) (j : Fin 35)
    (keep : j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 17 ∨ j = 19 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 34) :
    (sourceTrial M p).eval s j = s j := by
  have outside : ∀ i : Fin 11, j ≠ Source.bank (sourceSlots : Source.Layout 35) i := by
    intro i eq
    have small : ((Source.bank (sourceSlots : Source.Layout 35)) i).val < 11 := i.isLt
    have large : 11 ≤ j.val := by
      rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq] at small
    omega
  have clock : j ≠ sourceSlots 16 := by rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  change (sourceCall M).eval ((trialSetup M p).eval s) j = s j
  unfold sourceCall
  rw [Source.call_frame M sourceSlots Symbol.source (sourceDecode M)
    (fun _ => .source .unit) (fun _ => .source .unit) (sourceBit M) _ j outside clock]
  rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem offer_fixed (s : Store M) (j : Fin 35)
    (keep : j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 17 ∨ j = 22 ∨ j = 23 ∨ j = 24) :
    (offer M).eval s j = s j := by
  unfold offer
  simp only [WordStack.Routine.branch]
  split
  · simp only [WordStack.Routine.seq, LengthTest.routine_eval,
      WordStack.Routine.branch, WordStack.Routine.assign_eval]
    split <;> rcases keep with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [takeOutput_eval, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
  · rfl

theorem trial_fixes (p : PolynomialBound) (j : Fin 35)
    (keep : j = 11 ∨ j = 12 ∨ j = 17 ∨ j = 22 ∨ j = 23 ∨ j = 24) :
    (trial M p).Fixes j := by
  intro s
  have extra : j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 17 ∨ j = 22 ∨ j = 23 ∨ j = 24 := by tauto
  change (Function.update ((offer M).eval ((sourceTrial M p).eval s)) 13
    (.unit :: (offer M).eval ((sourceTrial M p).eval s) 13)) j = s j
  rw [Function.update_of_ne (by rcases keep with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  rw [offer_fixed M _ j extra]
  exact sourceTrial_fixed M p s j (by tauto)

def search (p : PolynomialBound) : Controller M :=
  WordStack.Routine.iterate 23 (trial M p) (trial_fixes M p 23 (by tauto))

def setup (p : PolynomialBound) : Controller M :=
  (targetCounter M).seq (trialsCounter M)

def prepareCommand (p : PolynomialBound) : Command (Cell M) Bool 35 :=
  (Command.loadIndex 24 Symbol.unit).seq
  ((counter M 18 (by decide) p).command.seq
  ((Command.push 18 Symbol.unit).seq
    (Command.collect 18 17 Symbol.bit)))

/-- A finite instruction-table construction; unsuccessful searches output the
empty word, an ordinary failed attack rather than an unbounded drain. -/
def command (p : PolynomialBound) : Command (Cell M) Bool 35 :=
  (prepareCommand M p).seq
  (((setup M p).seq (search M p)).command.seq (Command.emitWord 34 (decodeBit M)))

def machine (p : PolynomialBound) : Machine Unit Bool Bool := (command M p).program 32 |>.machine

def snapshot (p : PolynomialBound) (n j : ℕ) (bits : BitString) : Source.Snapshot M :=
  (Source.Snapshot.step M)^[p n + 1] (Source.initial M (generatorData j) bits)

def value (p : PolynomialBound) (n j : ℕ) (bits : BitString) : Option BitString :=
  (snapshot M p n j bits).acceptedOutput

@[simp] theorem value_eq_some (p : PolynomialBound) (n j : ℕ) (bits word : BitString) :
    value M p n j bits = some word ↔
      M.run (generatorData j) bits (p n) = .halted (.accepted word) :=
  Source.iterate_accept_iff M _ _ _ _

def nextAnswer (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) : BitString :=
  match value M p n j bits with
  | some word => if word.length = target n then word else answer
  | none => answer

theorem sourceTrial_bank (p : PolynomialBound) (n j : ℕ) (bits : BitString) (s : Store M)
    (input : s 11 = []) (auxiliary : s 12 = []) (index : (s 13).length = j)
    (physical : (s 24).length = n) (random : s 17 = bits.reverse.map Symbol.bit) :
    (sourceTrial M p).eval s ∘ Source.bank sourceSlots =
      Local.mapStore Symbol.source ((snapshot M p n j bits).store M) := by
  let prepared := (trialSetup M p).eval s
  have iEq : (prepared (sourceSlots 11)).map (fun _ => Symbol.source ((Source.Cell.unit : Source.Symbol M))) =
      (generatorData j).input.map (fun a => Symbol.source (Source.Cell.input a)) := by
    simp [prepared, trialSetup_eval, input, generatorData]
  have aEq : (prepared (sourceSlots 12)).map (fun _ => Symbol.source ((Source.Cell.unit : Source.Symbol M))) =
      (generatorData j).auxiliary.map (fun a => Symbol.source (Source.Cell.auxiliary a)) := by
    simp [prepared, trialSetup_eval, auxiliary, generatorData]
  have nEq : (prepared (sourceSlots 13)).length = (generatorData j).index := by
    simpa [prepared, trialSetup_eval, generatorData] using index
  have rEq : (prepared (sourceSlots 14)).reverse.map (sourceBit M) =
      bits.map (fun a => Symbol.source (Source.Cell.bit a)) := by
    simp [prepared, trialSetup_eval, random, List.map_reverse, List.map_map, Function.comp_def, sourceBit]
  have clock : (prepared (sourceSlots 16)).length = p n + 1 := by
    simp [prepared, trialSetup_eval, physical]
  have result := Source.call_bank (Output := Bool) M sourceSlots Symbol.source (sourceDecode M)
    (fun _ => rfl) (fun _ => .source .unit) (fun _ => .source .unit) (sourceBit M)
    prepared (generatorData j) bits iEq aEq nEq rEq
  rw [clock] at result
  exact result

theorem offer_answer (s : Store M) (status : Source.Status (Fin M.states)) (output answer : BitString)
    (state : s 0 = [.source (.state status)])
    (out : s 10 = output.map (fun b => Symbol.source (Source.Cell.output b)))
    (saved : s 34 = answer.map Symbol.bit) :
    (offer M).eval s 34 =
      ((match status with
        | .accepted => if output.length = (s 22).length then output.reverse else answer
        | _ => answer).map Symbol.bit) := by
  cases status <;>
    simp [offer, WordStack.Routine.branch, state, WordStack.Routine.seq,
      LengthTest.routine_eval, takeOutput_eval, out, List.map_map, Function.comp_def,
      outputBit, WordStack.Routine.assign_eval, WordStack.Routine.skip,
      WordStack.Routine.ofLocal, Local.eval, saved, List.map_reverse]
  split <;> simp_all [WordStack.Routine.assign_eval, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, List.map_reverse]

theorem trial_answer (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (input : s 11 = []) (auxiliary : s 12 = []) (index : (s 13).length = j)
    (physical : (s 24).length = n) (random : s 17 = bits.reverse.map Symbol.bit)
    (targetLength : (s 22).length = target n) (saved : s 34 = answer.map Symbol.bit) :
    (trial M p).eval s 34 = (nextAnswer M p n j bits answer).map Symbol.bit := by
  let c := snapshot M p n j bits
  let t := (sourceTrial M p).eval s
  have bank := sourceTrial_bank M p n j bits s input auxiliary index physical random
  have state : t 0 = [.source (.state c.status)] := by
    simpa [t, c, Local.mapStore, Source.Snapshot.store, Source.bank, sourceSlots]
      using congrFun bank (0 : Fin 11)
  have out : t 10 = c.output.map (fun b => Symbol.source (Source.Cell.output b)) := by
    simpa [t, c, Local.mapStore, Source.Snapshot.store, Source.bank, sourceSlots, List.map_map, Function.comp_def]
      using congrFun bank (10 : Fin 11)
  have kept : t 34 = answer.map Symbol.bit :=
    (sourceTrial_fixed M p s 34 (by tauto)).trans saved
  have targetEq : (t 22).length = target n := by
    change ((sourceTrial M p).eval s 22).length = target n
    rw [sourceTrial_fixed M p s 22 (by tauto), targetLength]
  have offered := offer_answer M t c.status c.output answer state out kept
  change (Function.update ((offer M).eval t) 13 (.unit :: (offer M).eval t 13)) 34 = _
  rw [Function.update_of_ne (by decide), offered, targetEq]
  cases hs : c.status <;> simp [nextAnswer, value, Source.Snapshot.acceptedOutput, c, hs, List.length_reverse]

theorem trial_index (p : PolynomialBound) (s : Store M) :
    ((trial M p).eval s 13).length = (s 13).length + 1 := by
  change (.unit :: (offer M).eval ((sourceTrial M p).eval s) 13).length = _
  rw [List.length_cons, offer_fixed M _ 13 (by tauto), sourceTrial_fixed M p s 13 (by tauto)]

structure Stored (n j : ℕ) (bits answer : BitString) (s : Store M) : Prop where
  input : s 11 = []
  auxiliary : s 12 = []
  index : (s 13).length = j
  physical : (s 24).length = n
  random : s 17 = bits.reverse.map Symbol.bit
  targetLength : (s 22).length = target n
  saved : s 34 = answer.map Symbol.bit

theorem trial_stored (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) :
    Stored M n (j + 1) bits (nextAnswer M p n j bits answer) ((trial M p).eval s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [trial_fixes M p 11 (by tauto), h.input]
  · rw [trial_fixes M p 12 (by tauto), h.auxiliary]
  · rw [trial_index, h.index]
  · rw [trial_fixes M p 24 (by tauto), h.physical]
  · rw [trial_fixes M p 17 (by tauto), h.random]
  · rw [trial_fixes M p 22 (by tauto), h.targetLength]
  · exact trial_answer M p n j bits answer s h.input h.auxiliary h.index h.physical
      h.random h.targetLength h.saved

theorem counted_stored (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) :
    Stored M n (j + 1) bits (nextAnswer M p n j bits answer)
      ((WordStack.Routine.counted 23 (trial M p)).eval s) := by
  apply trial_stored M p n j bits answer (Function.update s 23 (s 23).tail)
  constructor <;> simp_all [Stored.input h, Stored.auxiliary h, Stored.index h, Stored.physical h,
    Stored.random h, Stored.targetLength h, Stored.saved h]

def foldAnswer (p : PolynomialBound) (n : ℕ) (bits : BitString) : ℕ → ℕ → BitString → BitString
  | _, 0, answer => answer
  | j, k + 1, answer => foldAnswer p n bits (j + 1) k (nextAnswer M p n j bits answer)

theorem iterate_stored (p : PolynomialBound) (n j k : ℕ) (bits answer : BitString) (s : Store M)
    (h : Stored M n j bits answer s) :
    Stored M n (j + k) bits (foldAnswer M p n bits j k answer)
      (((WordStack.Routine.counted 23 (trial M p)).eval)^[k] s) := by
  induction k generalizing j answer s with
  | zero => simpa [foldAnswer] using h
  | succ k ih =>
    have first := counted_stored M p n j bits answer s h
    have rest := ih (j + 1) (nextAnswer M p n j bits answer)
      ((WordStack.Routine.counted 23 (trial M p)).eval s) first
    simpa only [foldAnswer, Function.iterate_succ_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

theorem search_saved (p : PolynomialBound) (n : ℕ) (bits : BitString) (s : Store M)
    (h : Stored M n 0 bits [] s) (count : (s 23).length = trials n) :
    (search M p).eval s 34 = (foldAnswer M p n bits 0 (trials n) []).map Symbol.bit := by
  have final := iterate_stored M p n 0 (trials n) bits [] s h
  simpa only [search, WordStack.Routine.iterate, count] using final.saved

theorem nextAnswer_cases (p : PolynomialBound) (n j : ℕ) (bits answer : BitString) :
    nextAnswer M p n j bits answer = answer ∨
      (value M p n j bits = some (nextAnswer M p n j bits answer) ∧
        (nextAnswer M p n j bits answer).length = target n) := by
  unfold nextAnswer
  cases h : value M p n j bits with
  | none => exact Or.inl rfl
  | some word =>
    by_cases length : word.length = target n
    · simp [length]
    · simp [length]

theorem foldAnswer_sources (p : PolynomialBound) (n j k : ℕ) (bits answer : BitString) :
    foldAnswer M p n bits j k answer = answer ∨
      ∃ i, j ≤ i ∧ i < j + k ∧
        value M p n i bits = some (foldAnswer M p n bits j k answer) ∧
        (foldAnswer M p n bits j k answer).length = target n := by
  induction k generalizing j answer with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rcases ih (j + 1) (nextAnswer M p n j bits answer) with same | ⟨i, lower, upper, accepted, length⟩
    · rcases nextAnswer_cases M p n j bits answer with unchanged | ⟨accepted, length⟩
      · exact Or.inl (same.trans unchanged)
      · right
        refine ⟨j, le_rfl, by omega, ?_, ?_⟩
        · simpa only [foldAnswer, same] using accepted
        · simpa only [foldAnswer, same] using length
    · right
      exact ⟨i, by omega, by omega, accepted, length⟩

theorem foldAnswer_preserves_length (p : PolynomialBound) (n j k : ℕ) (bits answer : BitString)
    (length : answer.length = target n) :
    (foldAnswer M p n bits j k answer).length = target n := by
  rcases foldAnswer_sources M p n j k bits answer with same | ⟨_, _, _, _, correct⟩
  · rw [same, length]
  · exact correct

theorem foldAnswer_hits (p : PolynomialBound) (n j k : ℕ) (bits answer word : BitString)
    (i : ℕ) (lower : j ≤ i) (upper : i < j + k)
    (accepted : value M p n i bits = some word) (length : word.length = target n) :
    (foldAnswer M p n bits j k answer).length = target n := by
  induction k generalizing j answer with
  | zero => omega
  | succ k ih =>
    by_cases first : i = j
    · subst i
      have updated : nextAnswer M p n j bits answer = word := by simp [nextAnswer, accepted, length]
      change (foldAnswer M p n bits (j + 1) k _).length = _
      rw [updated]
      exact foldAnswer_preserves_length M p n (j + 1) k bits word length
    · exact ih (j + 1) (nextAnswer M p n j bits answer) (by omega) (by omega)

theorem foldAnswer_collision_witness (p : PolynomialBound) (n i : ℕ) (bits word : BitString)
    (index : i ≤ 2 * target n)
    (accepted : M.run (generatorData i) bits (p n) = .halted (.accepted word))
    (length : word.length = target n) :
    ∃ j ≤ 2 * target n,
      M.run (generatorData j) bits (p n) =
        .halted (.accepted (foldAnswer M p n bits 0 (trials n) [])) ∧
      (foldAnswer M p n bits 0 (trials n) []).length = target n := by
  have positive : 0 < target n := by simp [target]
  have hit := foldAnswer_hits M p n 0 (trials n) bits [] word i (by omega)
    (by simp [trials]; omega) ((value_eq_some M p n i bits word).mpr accepted) length
  rcases foldAnswer_sources M p n 0 (trials n) bits [] with empty | ⟨j, _, bound, output, correct⟩
  · rw [empty] at hit
    simp only [List.length_nil] at hit
    omega
  · exact ⟨j, by simp only [trials] at bound; omega,
      (value_eq_some M p n j bits _).mp output, correct⟩

end
end ComplexityOfGenerators.Simulation.ExpectedCollisionSearch
