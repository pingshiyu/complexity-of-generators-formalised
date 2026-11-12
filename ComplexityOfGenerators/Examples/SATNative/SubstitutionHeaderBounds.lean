import ComplexityOfGenerators.Examples.SATNative.SubstitutionHeader
import ComplexityOfGenerators.Examples.SATNative.SubstitutionEmitBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
open Simulation.WordStack NativeBody
set_option backward.isDefEq.respectTransparency false

theorem emitHeader_temporaries {O : Type} (s : Store)
    (within : (s 10).length-1 ≤ (s 4).length) :
    (emitHeader (O := O)).eval s 9 = [] ∧ (emitHeader (O := O)).eval s 22 = (s 10).tail ∧
      (emitHeader (O := O)).eval s 23 = [] ∧ (emitHeader (O := O)).eval s 24 = [] ∧
      (emitHeader (O := O)).eval s 25 = [] := by
  simp [emitHeader, Routine.seq, Routine.ofLocal, Routine.clear, Routine.copy, Routine.assign_eval,
    Local.eval_pop, Local.eval_push, DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
    Routine.transfer, List.length_tail, Nat.sub_eq_zero_of_le within]

theorem emitHeader_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s)
    (within : (s 10).length-1 ≤ (s 4).length) :
    stackBound (2*budget+2) ((emitHeader (O := O)).eval s) := by
  have temps := emitHeader_temporaries (O := O) s within
  intro j
  by_cases scratch : j = 9
  · subst j; simp [temps.1]
  · by_cases output : j = 21
    · subst j
      rw [emitHeader_buffer]
      have cap := sizes 4
      simp only [headerWord, List.length_reverse, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    · by_cases copy : j = 22
      · subst j
        rw [temps.2.1]
        have active := sizes 10
        simp only [List.length_tail]
        omega
      · by_cases counter : j = 23
        · subst j; simp [temps.2.2.1]
        · by_cases trash : j = 24
          · subst j; simp [temps.2.2.2.1]
          · by_cases discarded : j = 25
            · subst j; simp [temps.2.2.2.2]
            · rw [emitHeader_frame s j scratch output copy counter trash discarded]
              exact (sizes j).trans (by omega)

theorem emitHeader_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (emitHeader (O := O)).cost s ≤ 200*(budget+1) := by
  let a := (Routine.clear (S := Symbol) (O := O) 21).eval s
  let b := (Routine.copy (O := O) 4 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).eval a
  let c := Function.update b 21 (.separator :: b 21)
  let d := (Routine.assign (O := O) 10 22 9 (by decide) (by decide) (by decide) id).eval c
  let e := Function.update d 22 (d 22).tail
  let f := (Routine.copy (O := O) 22 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).eval e
  let g := (Routine.assign (O := O) 4 23 9 (by decide) (by decide) (by decide) id).eval f
  let h := (Routine.assign (O := O) 22 24 9 (by decide) (by decide) (by decide) id).eval g
  let i := (Routine.clear (S := Symbol) (O := O) 25).eval h
  let j := (DrainPair.routine (O := O) 24 23 25 (by decide) (by decide)).eval i
  have loopCost := DrainPair.routine_cost (O := O) 24 23 25 (by decide) (by decide) i
  have counter : (i 24).length ≤ budget := by
    have active := sizes 10
    simp [i, h, g, f, e, d, c, b, a, Routine.clear, Routine.assign_eval, Routine.copy, List.length_tail]
    omega
  have remaining : (j 23).length ≤ budget := by
    have cap := sizes 4
    simp [j, i, h, g, f, e, d, c, b, a,
      DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
      Routine.clear, Routine.assign_eval, Routine.copy, List.length_drop]
    omega
  have pieces :
      (Routine.copy (O := O) 4 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).cost a +
      (Routine.assign (O := O) 10 22 9 (by decide) (by decide) (by decide) id).cost c +
      (Routine.copy (O := O) 22 21 9 (by decide) (by decide) (by decide) (fun _ : Symbol => .one)).cost e +
      (Routine.assign (O := O) 4 23 9 (by decide) (by decide) (by decide) id).cost f +
      (Routine.assign (O := O) 22 24 9 (by decide) (by decide) (by decide) id).cost g ≤ 100*budget+20 := by
    have cap := sizes 4
    have active := sizes 10
    have scratch := sizes 9
    have first := sizes 22
    have second := sizes 23
    have third := sizes 24
    simp [Routine.copy, Routine.assign_cost, g, f, e, d, c, b, a, Routine.clear,
      Routine.assign_eval, List.length_tail]
    omega
  have oldOutput := sizes 21
  have trash : (h 25).length ≤ budget := by
    simpa [h, g, f, e, d, c, b, a, Routine.assign_eval, Routine.copy, Routine.clear] using sizes 25
  change 3*(s 21).length+1+
    ((Routine.copy (O := O) 4 21 9 _ _ _ (fun _ => .one)).cost a+1+
    (1+1+((Routine.assign (O := O) 10 22 9 _ _ _ id).cost c+1+
    (1+1+((Routine.copy (O := O) 22 21 9 _ _ _ (fun _ => .one)).cost e+1+
    ((Routine.assign (O := O) 4 23 9 _ _ _ id).cost f+1+
    ((Routine.assign (O := O) 22 24 9 _ _ _ id).cost g+1+
    (3*(h 25).length+1+((DrainPair.routine (O := O) 24 23 25 _ _).cost i+1+
    (6*(j 23).length+1+1)))))))))) ≤ _
  omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
