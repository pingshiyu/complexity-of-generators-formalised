import ComplexityOfGenerators.Examples.HAMPATHNative.Header
import ComplexityOfGenerators.Examples.HAMPATHNative.Start

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def matrixState (word : List Symbol) : RowState :=
  (rowStep (headerSize word))^[headerSize word] (headerState word)

def afterMatrix (word : List Symbol) : RowState := separator (matrixState word)

def parsedState (word : List Symbol) : StartState :=
  startStep^[headerSize word] ⟨(afterMatrix word).word, 0, false, (afterMatrix word).valid⟩

def wellFormed (word : List Symbol) : Bool :=
  (parsedState word).valid && (parsedState word).seen && (parsedState word).word.isEmpty

def startPrepare {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [12, 13]).seq (Routine.assign 4 11 9 (by decide) (by decide) (by decide) id)

theorem startPrepare_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) :
    (startPrepare (O := O)).eval (rowEncoded base size state []) =
      startEncoded (rowEncoded base size state []) ⟨state.word, 0, false, state.valid⟩
        (List.replicate size (.bit true)) := by
  funext j
  fin_cases j <;> simp [startPrepare, rowEncoded, cellEncoded, startEncoded, flag,
    Routine.seq, Routine.clearMany_eval, Routine.assign_eval]

def parser {O : Type} : Routine Symbol O 32 :=
  header.seq (rows.seq ((Routine.ofLocal separatorCode).seq (startPrepare.seq starts)))

theorem parser_eval {O : Type} (base : Store) :
    (parser (O := O)).eval base =
      startEncoded
        (rowEncoded (headerBase base) (headerSize (base 2)) (afterMatrix (base 2)) [])
        (parsedState (base 2)) [] := by
  simp only [parser, Routine.seq, header_eval, rows_eval, Routine.ofLocal, separatorCode_eval,
    startPrepare_eval, starts_eval, afterMatrix, matrixState, parsedState]

theorem parser_decides {O : Type} (base : Store) :
    let output := (parser (O := O)).eval base
    ((output 6).head?.isSome && (output 12).head?.isSome && (output 2).isEmpty) = wellFormed (base 2) := by
  rw [parser_eval]
  cases valid : (parsedState (base 2)).valid <;> cases seen : (parsedState (base 2)).seen <;>
    simp [startEncoded, flag, wellFormed, valid, seen]

-- Clients use the specification above; unfolding the nested controller
-- during unrelated store equalities needlessly expands both bounded loops.
attribute [irreducible] parser

end ComplexityOfGenerators.Examples.HAMPATH.Native
