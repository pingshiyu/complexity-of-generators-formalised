import ComplexityOfGenerators.Examples.SATNative.HeaderModel
import Mathlib.Tactic.FinCases

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def keepOne (symbol : Symbol) : Bool := symbol == .one

theorem readOnes_parts (word : List Symbol) :
    readOnes word = ((word.takeWhile keepOne).length, word.dropWhile keepOne) := by
  induction word with
  | nil => rfl
  | cons head rest ih => cases head <;> simp [readOnes, keepOne, ih]

def scaffold (capacity : ℕ) (base : Store) : Store :=
  Function.update (Function.update base 4 (List.replicate capacity .one)) 9 []

def setup {O : Type} : Routine Symbol O 16 :=
  (Routine.clearMany [4, 5, 6, 7, 8, 9]).seq
  ((Routine.ofLocal (Local.push 6 .one)).seq (Routine.ofLocal (Local.push 8 .one)))

def extract {O : Type} : Routine Symbol O 16 :=
  setup.seq (Routine.transferWhile 2 4 (by decide) keepOne (fun _ => .one))

theorem extract_eval {O : Type} (base : Store) :
    (extract (O := O)).eval base =
      encoded (scaffold (readOnes (base 2)).1 base)
        ⟨(readOnes (base 2)).2, 0, true, true⟩ [] := by
  funext j
  fin_cases j <;>
    simp [extract, setup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal,
      Routine.transferWhile, encoded, scaffold, readOnes_parts,
      List.reverse_replicate]

def separator (state : ScanState) : ScanState :=
  if state.word.head? = some .separator then {state with word := state.word.tail}
  else {state with valid := false}

def separatorCode : Local Symbol 16 :=
  .read 2 fun head => if head = some .separator then Local.pop 2 else Local.pop 6

theorem separatorCode_eval (base : Store) (state : ScanState) (clock : List Symbol) :
    separatorCode.eval (encoded base state clock) = encoded base (separator state) clock := by
  by_cases found : state.word.head? = some .separator
  · funext j
    fin_cases j <;> simp [separatorCode, separator, Local.eval, Local.pop, encoded, found, Action.apply]
  · cases validity : state.valid <;> funext j <;> fin_cases j <;>
      simp [separatorCode, separator, Local.eval, Local.pop, encoded, found, validity, Action.apply]

def clockSetup {O : Type} : Routine Symbol O 16 :=
  Routine.assign 4 7 9 (by decide) (by decide) (by decide) id

theorem clockSetup_eval {O : Type} (capacity : ℕ) (base : Store) (state : ScanState) :
    (clockSetup (O := O)).eval (encoded (scaffold capacity base) state []) =
      encoded (scaffold capacity base) state (List.replicate capacity .one) := by
  funext j
  fin_cases j <;> simp [clockSetup, Routine.assign_eval, encoded, scaffold]

def parsedState (word : List Symbol) : ScanState :=
  let (capacity, remaining) := readOnes word
  separator (step^[capacity] (separator ⟨remaining, 0, true, true⟩))

/-- Complete executable header parsing, including malformed fields. -/
def headerRoutine {O : Type} : Routine Symbol O 16 :=
  extract.seq ((Routine.ofLocal separatorCode).seq
    (clockSetup.seq (scanRoutine.seq (Routine.ofLocal separatorCode))))

theorem headerRoutine_eval {O : Type} (base : Store) :
    (headerRoutine (O := O)).eval base =
      encoded (scaffold (readOnes (base 2)).1 base) (parsedState (base 2)) [] := by
  simp only [headerRoutine, Routine.seq, extract_eval, Routine.ofLocal,
    separatorCode_eval, clockSetup_eval, scanRoutine_eval, parsedState]

theorem parsedState_canonical (capacity active : ℕ) (bound : active ≤ capacity) (body : List Symbol) :
    parsedState (List.replicate capacity .one ++ .separator ::
      (List.replicate active .one ++ List.replicate (capacity - active) .zero ++ .separator :: body)) =
      ⟨body, active, decide (capacity - active = 0), true⟩ := by
  unfold parsedState
  rw [readOnes_header]
  dsimp only
  have scanned := iterate_canonical active (capacity - active) (.separator :: body)
  have total : capacity - active + active = capacity := by omega
  rw [total] at scanned
  simp only [separator, List.head?_cons, ite_true, List.tail_cons]
  rw [scanned]
  rfl

theorem parsedState_sound (word : List Symbol) (valid : (parsedState word).valid = true) :
    ∃ capacity, (parsedState word).count ≤ capacity ∧
      word = List.replicate capacity .one ++ .separator ::
        (List.replicate (parsedState word).count .one ++
          List.replicate (capacity - (parsedState word).count) .zero ++ .separator :: (parsedState word).word) := by
  let capacity := (readOnes word).1
  let rest := (readOnes word).2
  let first := separator ⟨rest, 0, true, true⟩
  let scanned := step^[capacity] first
  have parsedEq : parsedState word = separator scanned := rfl
  change (separator scanned).valid = true at valid
  have lastSeparator : scanned.word.head? = some .separator := by
    by_contra absent
    simp [separator, absent] at valid
  have scanValid : scanned.valid = true := by simpa [separator, lastSeparator] using valid
  have firstSeparator : rest.head? = some .separator := by
    by_contra absent
    have firstInvalid : first.valid = false := by simp [first, separator, absent]
    have bad := iterate_invalid first firstInvalid capacity
    change scanned.valid = false at bad
    rw [bad] at scanValid
    cases scanValid
  have restEq : rest = .separator :: rest.tail := by
    cases value : rest with
    | nil => simp [value] at firstSeparator
    | cons head tail =>
      have equal : head = .separator := by simpa [value] using firstSeparator
      subst head
      rfl
  have scannedEq : scanned = step^[capacity] ⟨rest.tail, 0, true, true⟩ := by
    simp [scanned, first, separator, firstSeparator]
  rw [scannedEq] at scanValid
  obtain ⟨active, activeBound, _, field, countEq⟩ := iterate_sound capacity rest.tail 0 true scanValid
  have number : scanned.count = active := by rw [scannedEq]; simpa using countEq
  have lastEq : scanned.word = .separator :: scanned.word.tail := by
    cases value : scanned.word with
    | nil => simp [value] at lastSeparator
    | cons head tail =>
      have equal : head = .separator := by simpa [value] using lastSeparator
      subst head
      rfl
  have finalCount : (parsedState word).count = active := by
    rw [parsedEq]
    simp only [separator, lastSeparator, ite_true, number]
  have finalWord : (parsedState word).word = scanned.word.tail := by
    rw [parsedEq]
    simp only [separator, lastSeparator, ite_true]
  refine ⟨capacity, ?_, ?_⟩
  · simpa only [finalCount] using activeBound
  · have reconstruct := readOnes_reconstruct word
    change List.replicate capacity .one ++ rest = word at reconstruct
    have field' := field
    rw [← scannedEq] at field'
    rw [restEq, field', lastEq] at reconstruct
    rw [finalCount, finalWord]
    exact reconstruct.symm

end ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader
