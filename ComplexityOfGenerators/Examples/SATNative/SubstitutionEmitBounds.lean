import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteralBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
open Simulation.WordStack NativeBody
set_option backward.isDefEq.respectTransparency false

theorem emitLiteral_temporaries {O : Type} (s : Store) (within : (s 5).length ≤ (s 4).length) :
    (emitLiteral (O := O)).eval s 9 = [] ∧ (emitLiteral (O := O)).eval s 22 = [] ∧
      (emitLiteral (O := O)).eval s 23 = [] ∧ (emitLiteral (O := O)).eval s 24 = [] := by
  simp [emitLiteral, Routine.seq, Routine.ofLocal, emitTag_eval, Routine.copy, Routine.assign_eval,
    Routine.clear, DrainPair.routine_eval (23 : Fin 32) 22 24 (by decide) (by decide) (by decide),
    Routine.transfer, Nat.sub_eq_zero_of_le within]

/-- Only the reversed output grows; the four scratch stacks are reset. -/
theorem emitLiteral_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s)
    (within : (s 5).length ≤ (s 4).length) :
    stackBound (budget+(s 4).length+1) ((emitLiteral (O := O)).eval s) := by
  have temps := emitLiteral_temporaries (O := O) s within
  intro j
  by_cases scratch : j = 9
  · subst j; simp [temps.1]
  · by_cases output : j = 21
    · subst j
      exact (emitLiteral_length s within).trans (by have := sizes 21; omega)
    · by_cases copy : j = 22
      · subst j; simp [temps.2.1]
      · by_cases counter : j = 23
        · subst j; simp [temps.2.2.1]
        · by_cases trash : j = 24
          · subst j; simp [temps.2.2.2]
          · rw [emitLiteral_frame s j scratch output copy counter trash]
            exact (sizes j).trans (by omega)

theorem emitLiteral_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (emitLiteral (O := O)).cost s ≤ 160*(budget+1) := by
  let a := emitTag.eval s
  let b := (Routine.copy (O := O) 5 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).eval a
  let c := (Routine.assign (O := O) 4 22 9 (by decide) (by decide) (by decide) id).eval b
  let d := (Routine.assign (O := O) 5 23 9 (by decide) (by decide) (by decide) id).eval c
  let e := (Routine.clear (S := Symbol) (O := O) 24).eval d
  let f := (DrainPair.routine (O := O) 23 22 24 (by decide) (by decide)).eval e
  have loopCost := DrainPair.routine_cost (O := O) 23 22 24 (by decide) (by decide) e
  have counter : (e 23).length = (s 5).length := by
    simp [e, d, c, b, a, Routine.clear, Routine.assign_eval, Routine.copy, emitTag_eval]
  rw [counter] at loopCost
  have left : (f 22).length ≤ (s 4).length := by
    simp [f, e, d, c, b, a, DrainPair.routine_eval (23 : Fin 32) 22 24 (by decide) (by decide) (by decide),
      Routine.clear, Routine.assign_eval, Routine.copy, emitTag_eval, List.length_drop]
  have tagCost : emitTag.ticks s ≤ 2 := by
    cases head : (s 11).head? <;> simp [emitTag, Local.ticks, Local.push, head]
  have copyCost : (Routine.copy (O := O) 5 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).cost a ≤ 17*budget+2 := by
    have scratch := sizes 9
    have index := sizes 5
    simp [Routine.copy, a, emitTag_eval]
    omega
  have firstAssign : (Routine.assign (O := O) 4 22 9 (by decide) (by decide) (by decide) id).cost b ≤ 17*budget+3 := by
    have cap := sizes 4
    have copy := sizes 22
    simp [Routine.assign_cost, b, a, Routine.copy, emitTag_eval]
    omega
  have secondAssign : (Routine.assign (O := O) 5 23 9 (by decide) (by decide) (by decide) id).cost c ≤ 17*budget+3 := by
    have index := sizes 5
    have counter := sizes 23
    simp [Routine.assign_cost, c, b, a, Routine.assign_eval, Routine.copy, emitTag_eval]
    omega
  have trash : (d 24).length ≤ budget := by
    simpa [d, c, b, a, Routine.assign_eval, Routine.copy, emitTag_eval] using sizes 24
  have index := sizes 5
  change emitTag.ticks s+1+
    ((Routine.copy (O := O) 5 21 9 _ _ _ (fun _ => .one)).cost a+1+
    ((Routine.assign (O := O) 4 22 9 _ _ _ id).cost b+1+
    ((Routine.assign (O := O) 5 23 9 _ _ _ id).cost c+1+
    (3*(d 24).length+1+((DrainPair.routine (O := O) 23 22 24 _ _).cost e+1+6*(f 22).length))))) ≤ _
  have cap := sizes 4
  omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
