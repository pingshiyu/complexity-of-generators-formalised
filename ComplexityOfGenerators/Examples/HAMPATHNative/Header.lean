import ComplexityOfGenerators.Examples.HAMPATHNative.Rows

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def keepHeader (symbol : Symbol) : Bool := symbol == .bit true

def headerSize (word : List Symbol) : ℕ := (word.takeWhile keepHeader).length

def headerState (word : List Symbol) : RowState :=
  let rest := word.dropWhile keepHeader
  if rest.head? = some .separator then ⟨rest.tail, 0, true⟩ else ⟨rest, 0, false⟩

def separator (state : RowState) : RowState :=
  if state.word.head? = some .separator then {state with word := state.word.tail}
  else {state with valid := false}

def separatorCode : Local Symbol 32 :=
  .read 2 fun head => if head = some .separator then Local.pop 2 else Local.pop 6

theorem separatorCode_eval (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) :
    separatorCode.eval (rowEncoded base size state clock) = rowEncoded base size (separator state) clock := by
  by_cases found : state.word.head? = some .separator
  · funext j
    fin_cases j <;> simp [separatorCode, separator, Local.eval, Local.pop, rowEncoded, cellEncoded, found, Action.apply]
  · cases valid : state.valid <;> funext j <;> fin_cases j <;>
      simp [separatorCode, separator, Local.eval, Local.pop, rowEncoded, cellEncoded, flag, found, valid, Action.apply]

def headerBase (base : Store) : Store := Function.update (Function.update base 12 []) 13 []

def headerSetup {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]).seq
    (Routine.ofLocal (Local.push 6 (.bit true)))

def headerExtract {O : Type} : Routine Symbol O 32 :=
  headerSetup.seq (Routine.transferWhile 2 4 (by decide) keepHeader id)

theorem header_replicate (word : List Symbol) :
    word.takeWhile keepHeader = List.replicate (headerSize word) (.bit true) := by
  induction word with
  | nil => rfl
  | cons head rest ih => cases head with
    | separator => rfl
    | bit value => cases value with
      | false => rfl
      | true =>
          change Symbol.bit true :: rest.takeWhile keepHeader =
            List.replicate ((rest.takeWhile keepHeader).length + 1) (.bit true)
          rw [List.replicate_succ]
          exact congrArg (Symbol.bit true :: ·) ih

theorem headerExtract_eval {O : Type} (base : Store) :
    (headerExtract (O := O)).eval base =
      rowEncoded (headerBase base) (headerSize (base 2))
        ⟨(base 2).dropWhile keepHeader, 0, true⟩ [] := by
  funext j
  fin_cases j <;> simp [headerExtract, headerSetup, headerBase, rowEncoded, cellEncoded, flag,
    Routine.seq, Routine.clearMany_eval, Routine.ofLocal, Local.eval, Local.push, Action.apply,
    Routine.transferWhile, header_replicate, List.reverse_replicate]

def headerClock {O : Type} : Routine Symbol O 32 := Routine.assign 4 5 9 (by decide) (by decide) (by decide) id

theorem headerClock_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) :
    (headerClock (O := O)).eval (rowEncoded base size state []) =
      rowEncoded base size state (List.replicate size (.bit true)) := by
  funext j
  fin_cases j <;> simp [headerClock, rowEncoded, cellEncoded, Routine.assign_eval]

def header {O : Type} : Routine Symbol O 32 :=
  headerExtract.seq ((Routine.ofLocal separatorCode).seq headerClock)

theorem header_eval {O : Type} (base : Store) :
    (header (O := O)).eval base =
      rowEncoded (headerBase base) (headerSize (base 2)) (headerState (base 2))
        (List.replicate (headerSize (base 2)) (.bit true)) := by
  simp only [header, Routine.seq, headerExtract_eval, Routine.ofLocal, separatorCode_eval, headerClock_eval]
  congr 1

attribute [irreducible] header

theorem headerSize_le (word : List Symbol) : headerSize word ≤ word.length := by
  have all := congrArg List.length
    (show word.takeWhile keepHeader ++ word.dropWhile keepHeader = word from List.takeWhile_append_dropWhile)
  simp only [List.length_append] at all
  change (word.takeWhile keepHeader).length ≤ word.length
  omega

theorem headerState_word_le (word : List Symbol) : (headerState word).word.length ≤ word.length := by
  have dropBound : (word.dropWhile keepHeader).length ≤ word.length := by
    induction word with
    | nil => simp
    | cons head rest ih =>
        simp only [List.dropWhile_cons]
        split <;> simp_all
        omega
  dsimp only [headerState]
  split
  · have tailBound : ((word.dropWhile keepHeader).tail).length ≤ (word.dropWhile keepHeader).length := by
      simp only [List.length_tail]; omega
    exact tailBound.trans dropBound
  · exact dropBound

end ComplexityOfGenerators.Examples.HAMPATH.Native
