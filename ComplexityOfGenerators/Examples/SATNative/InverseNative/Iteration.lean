import ComplexityOfGenerators.Examples.SATNative.InverseNative.Canonical

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

noncomputable abbrev countedStep {O : Type} (bit : Bool) : Routine Symbol O 32 := Routine.counted 16 (inverseStep bit)

theorem counted_literal {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (literal : Literal) (valid : literal.valid active) (rest : List Symbol) (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨literal.encode capacity ++ rest, true, seen, enabled⟩ s)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (countedStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, true, enabled⟩ output ∧
      output 31 = choices.tail.map bitSymbol ∧
      output 21 = ((literal.lift active bit (choices.headD false)).encode capacity).reverse ++ s 21 := by
  have rep := NativeBody.popped_represents capacity active _ s represented
  have updated : (Function.update s 16 (s 16).tail) 31 = choices.map bitSymbol := by simpa using mask
  have one := inverseStep_literal (O := O) bit bound literal valid rest seen enabled
    (Function.update s 16 (s 16).tail) rep choices updated
  simpa only [countedStep, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop,
    Function.update_of_ne (show (21 : Fin 32) ≠ 16 by decide)] using one

theorem counted_open {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store) (represented : Represents capacity active ⟨.openClause :: rest, false, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, false, enabled⟩ output ∧
      output 31 = s 31 ∧ output 21 = .openClause :: s 21 := by
  have rep := NativeBody.popped_represents capacity active _ s represented
  have one := inverseStep_open (O := O) bit capacity active rest seen enabled (Function.update s 16 (s 16).tail) rep
  simpa only [countedStep, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop,
    Function.update_of_ne (show (21 : Fin 32) ≠ 16 by decide),
    Function.update_of_ne (show (31 : Fin 32) ≠ 16 by decide)] using one

theorem counted_close {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store) (represented : Represents capacity active ⟨.closeClause :: rest, true, seen, enabled⟩ s) :
    let output := (countedStep (O := O) bit).eval s
    Represents capacity active ⟨rest, false, false, enabled && seen⟩ output ∧
      output 31 = s 31 ∧ output 21 = .closeClause :: s 21 := by
  have rep := NativeBody.popped_represents capacity active _ s represented
  have one := inverseStep_close (O := O) bit capacity active rest seen enabled (Function.update s 16 (s 16).tail) rep
  simpa only [countedStep, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop,
    Function.update_of_ne (show (21 : Fin 32) ≠ 16 by decide),
    Function.update_of_ne (show (31 : Fin 32) ≠ 16 by decide)] using one

theorem iterate_literals {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (clause : Clause) (valid : ∀ literal ∈ clause, literal.valid active) (rest : List Symbol) (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨clause.flatMap (Literal.encode capacity) ++ rest, true, seen, enabled⟩ s)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (countedStep (O := O) bit).eval^[clause.length] s
    Represents capacity active ⟨rest, true, seen || decide (clause ≠ []), enabled⟩ output ∧
      output 31 = (choices.drop clause.length).map bitSymbol ∧
      output 21 = ((clause.lift active bit choices).flatMap (Literal.encode capacity)).reverse ++ s 21 := by
  induction clause generalizing seen s choices with
  | nil => simpa [Clause.lift] using And.intro represented (And.intro mask (show s 21 = [] ++ s 21 by rfl))
  | cons literal tail ih =>
    have current : Represents capacity active
        ⟨literal.encode capacity ++ (tail.flatMap (Literal.encode capacity) ++ rest), true, seen, enabled⟩ s := by
      simpa only [List.flatMap_cons, List.append_assoc] using represented
    have one := counted_literal (O := O) bit bound literal (valid literal (by simp))
      (tail.flatMap (Literal.encode capacity) ++ rest) seen enabled s current choices mask
    let first := (countedStep (O := O) bit).eval s
    have firstBuffer : first 21 = ((literal.lift active bit (choices.headD false)).encode capacity).reverse ++ s 21 := one.2.2
    have tailResult := ih (by intro item member; exact valid item (by simp [member])) true first one.1 choices.tail one.2.1
    simp only [List.length_cons, Function.iterate_succ_apply]
    refine ⟨by simpa using tailResult.1, ?_, ?_⟩
    · simpa only [List.drop_tail] using tailResult.2.1
    · rw [tailResult.2.2, firstBuffer]
      simp [Clause.lift, List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem iterate_clause {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (clause : Clause) (nonempty : clause ≠ []) (valid : ∀ literal ∈ clause, literal.valid active)
    (rest : List Symbol) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨clause.encode capacity ++ rest, false, false, enabled⟩ s)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (countedStep (O := O) bit).eval^[clause.length + 2] s
    Represents capacity active ⟨rest, false, false, enabled⟩ output ∧
      output 31 = (choices.drop clause.length).map bitSymbol ∧
      output 21 = (Clause.encode capacity (clause.lift active bit choices)).reverse ++ s 21 := by
  have current : Represents capacity active
      ⟨.openClause :: (clause.flatMap (Literal.encode capacity) ++ .closeClause :: rest), false, false, enabled⟩ s := by
    simpa [Clause.encode, List.append_assoc] using represented
  have opened := counted_open (O := O) bit capacity active _ false enabled s current
  let first := (countedStep (O := O) bit).eval s
  have firstMask : first 31 = choices.map bitSymbol := opened.2.1.trans mask
  have literals := iterate_literals (O := O) bit bound clause valid (.closeClause :: rest) false enabled first opened.1 choices firstMask
  let middle := (countedStep (O := O) bit).eval^[clause.length] first
  have middleRep : Represents capacity active ⟨.closeClause :: rest, true, true, enabled⟩ middle := by
    simpa [nonempty] using literals.1
  have closed := counted_close (O := O) bit capacity active rest true enabled middle middleRep
  have openedBuffer : first 21 = .openClause :: s 21 := opened.2.2
  have literalBuffer : middle 21 = ((clause.lift active bit choices).flatMap (Literal.encode capacity)).reverse ++ first 21 := literals.2.2
  dsimp only
  rw [show clause.length + 2 = clause.length + 1 + 1 by omega, Function.iterate_succ_apply, Function.iterate_succ_apply']
  refine ⟨by simpa using closed.1, closed.2.1.trans literals.2.1, ?_⟩
  rw [closed.2.2, literalBuffer, openedBuffer]
  simp [Clause.encode, List.reverse_append, List.append_assoc]

theorem iterate_formula {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (rest : List Symbol) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity ++ rest, false, false, enabled⟩ s)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (countedStep (O := O) bit).eval^[NativeBody.tokenCount formula] s
    Represents capacity active ⟨rest, false, false, enabled⟩ output ∧
      output 31 = (choices.drop formula.occurrences).map bitSymbol ∧
      output 21 = ((formula.lift active bit (choiceRows formula choices)).bodyWord capacity).reverse ++ s 21 := by
  induction formula generalizing s choices with
  | nil => simpa [NativeBody.tokenCount, Formula.lift, Formula.bodyWord, Formula.occurrences] using
      And.intro represented (And.intro mask (show s 21 = [] ++ s 21 by rfl))
  | cons clause tail ih =>
    have headGood := valid clause (by simp)
    have current : Represents capacity active ⟨clause.encode capacity ++ (Formula.bodyWord capacity tail ++ rest), false, false, enabled⟩ s := by
      simpa [Formula.bodyWord, List.append_assoc] using represented
    have first := iterate_clause (O := O) bit bound clause headGood.1 headGood.2 (Formula.bodyWord capacity tail ++ rest) enabled s current choices mask
    let middle := (countedStep (O := O) bit).eval^[clause.length + 2] s
    have firstBuffer : middle 21 = (Clause.encode capacity (clause.lift active bit choices)).reverse ++ s 21 := first.2.2
    have tailResult := ih (by intro c member; exact valid c (by simp [member])) middle first.1
      (choices.drop clause.length) first.2.1
    dsimp only
    rw [NativeBody.tokenCount_cons, Function.iterate_add_apply]
    refine ⟨tailResult.1, ?_, ?_⟩
    · change ((countedStep (O := O) bit).eval^[NativeBody.tokenCount tail] middle) 31 = _
      rw [tailResult.2.1]
      simp only [Formula.occurrences, List.drop_drop]
      congr 2
    · rw [tailResult.2.2, firstBuffer]
      simp [Formula.lift, choiceRows, lift_take, Formula.bodyWord, List.reverse_append, List.append_assoc]

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
