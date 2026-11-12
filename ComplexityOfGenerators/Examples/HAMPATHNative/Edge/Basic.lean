import ComplexityOfGenerators.Examples.HAMPATHNative.Edge.SkipRows
import ComplexityOfGenerators.Examples.HAMPATHNative.Header

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Edge

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def prepare {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 24 2 9 (by decide) (by decide) (by decide) id).seq
    (header.seq (Routine.assign 26 21 23 (by decide) (by decide) (by decide) id))

def column {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 20).seq
    ((Routine.assign 28 22 23 (by decide) (by decide) (by decide) id).seq
      ((Blocks.routine 22 2 20 (by decide) (by decide)).seq (Routine.clear 20)))

theorem column_eval {O : Type} (s : Store) :
    (column (O := O)).eval s = Function.update (Function.update (Function.update (Function.update s
      23 []) 22 []) 2 ((s 2).drop (s 28).length)) 20 [] := by
  simp only [column, Routine.seq, Routine.clear, Routine.assign_eval,
    Blocks.routine_eval (22 : Fin 32) 2 20 (by decide) (by decide) (by decide)]
  funext j
  by_cases word : j = 2 <;> by_cases buffer : j = 20 <;> by_cases clock : j = 22 <;> by_cases scratch : j = 23 <;>
    simp [Function.update_apply, word, buffer, clock, scratch]

def headCheck {O : Type} : Routine Symbol O 32 :=
  Routine.branch 2 fun head => if head = some (.bit true) then Routine.skip else Routine.clear 16

theorem headCheck_eval {O : Type} (s : Store) :
    (headCheck (O := O)).eval s =
      Function.update s 16 (if (s 2).head? = some (.bit true) then s 16 else []) := by
  simp only [headCheck, Routine.branch]
  split <;> simp [Routine.skip, Routine.ofLocal, Routine.clear, Function.update_eq_self]

def query {O : Type} : Routine Symbol O 32 := prepare.seq (rows.seq (column.seq headCheck))

def bitAt (s : Store) : Option Symbol :=
  (((headerState (s 24)).word).drop ((s 26).length * (s 27).length + (s 28).length)).head?

attribute [irreducible] prepare column

theorem query_flag {O : Type} (s : Store) :
    (query (O := O)).eval s 16 = if bitAt s = some (.bit true) then s 16 else [] := by
  let a := (prepare (O := O)).eval s
  let b := (rows (O := O)).eval a
  let c := (column (O := O)).eval b
  have aWord : a 2 = (headerState (s 24)).word := by
    simp [a, prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded]
  have aWidth : a 27 = s 27 := by
    simp [a, prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have aRow : (a 21).length = (s 26).length := by
    simp [a, prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have aNext : a 28 = s 28 := by
    simp [a, prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have aValid : a 16 = s 16 := by
    simp [a, prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have bWord : b 2 = ((headerState (s 24)).word).drop ((s 26).length * (s 27).length) := by
    have value := (rows_values (O := O) a).1
    rw [aWord, aWidth, aRow] at value
    exact value
  have bNext : b 28 = s 28 := (rows_frame (O := O) a 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans aNext
  have bValid : b 16 = s 16 := (rows_values (O := O) a).2.2.trans aValid
  have cWord : c 2 = ((headerState (s 24)).word).drop ((s 26).length * (s 27).length + (s 28).length) := by
    simp [c, column_eval, bWord, bNext, List.drop_drop, Nat.add_comm]
  have cValid : c 16 = s 16 := by simpa [c, column_eval] using bValid
  change (headCheck (O := O)).eval c 16 = _
  rw [headCheck_eval]
  simp only [Function.update_self, cWord, cValid, bitAt]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Edge
