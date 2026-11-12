import ComplexityOfGenerators.Examples.SATNative.CertificateCheck
import ComplexityOfGenerators.Examples.SATNative.ParserBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem drain_bound {O : Type} (counter first second : Fin 32) (cf : counter ≠ first) (cs : counter ≠ second)
    (fs : first ≠ second) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((DrainPair.routine (O := O) counter first second cf cs).eval s) := by
  intro j
  rw [DrainPair.routine_eval counter first second cf cs fs]
  by_cases a : j = counter <;> by_cases b : j = first <;> by_cases c : j = second <;>
    simp [Function.update_apply, a, b, c, cf, cs, fs, List.length_drop] <;>
    first | exact sizes _ | have := sizes first; have := sizes second; omega

theorem lookup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget ((lookup (O := O)).eval s) := by
  intro j
  rw [lookup_eval]
  by_cases a : j = 9 <;> by_cases b : j = 22 <;> by_cases c : j = 23 <;>
    by_cases d : j = 24 <;> by_cases e : j = 25 <;>
      simp [Function.update_apply, a, b, c, d, e, List.length_drop] <;>
      first | exact sizes _ | have := sizes 3; omega

theorem lookup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (lookup (O := O)).cost s ≤ 80 * (budget + 1) := by
  let a := (Routine.clear (S := Symbol) (O := O) 24).eval s
  let b := (Routine.assign (O := O) 10 22 9 (by decide) (by decide) (by decide) id).eval a
  let c := (Routine.assign (O := O) 5 23 9 (by decide) (by decide) (by decide) id).eval b
  let d := (DrainPair.routine (O := O) 23 22 24 (by decide) (by decide)).eval c
  let e := (Routine.assign (O := O) 3 25 9 (by decide) (by decide) (by decide) id).eval d
  have ab : stackBound budget a := by
    intro j
    by_cases changed : j = 24 <;> simp [a, Routine.clear, changed] <;> exact sizes j
  have bb := NativeParser.assign_bound (O := O) 10 22 9 (by decide) (by decide) (by decide) id a budget ab
  have cb := NativeParser.assign_bound (O := O) 5 23 9 (by decide) (by decide) (by decide) id b budget bb
  have db := drain_bound (O := O) 23 22 24 (by decide) (by decide) (by decide) c budget cb
  have eb := NativeParser.assign_bound (O := O) 3 25 9 (by decide) (by decide) (by decide) id d budget db
  have one := sizes 24
  have two := NativeParser.assign_cost (O := O) 10 22 9 (by decide) (by decide) (by decide) id a budget ab
  have three := NativeParser.assign_cost (O := O) 5 23 9 (by decide) (by decide) (by decide) id b budget bb
  have four := DrainPair.routine_cost (O := O) 23 22 24 (by decide) (by decide) c
  have five := NativeParser.assign_cost (O := O) 3 25 9 (by decide) (by decide) (by decide) id d budget db
  have six := DrainPair.routine_cost (O := O) 22 25 24 (by decide) (by decide) e
  have cbClock := cb 23
  have ebClock := eb 22
  change (c 23).length ≤ budget at cbClock
  change (e 22).length ≤ budget at ebClock
  change 3 * (s 24).length + 1 +
    ((Routine.assign (O := O) 10 22 9 _ _ _ id).cost a + 1 +
    ((Routine.assign (O := O) 5 23 9 _ _ _ id).cost b + 1 +
    ((DrainPair.routine (O := O) 23 22 24 _ _).cost c + 1 +
    ((Routine.assign (O := O) 3 25 9 _ _ _ id).cost d + 1 +
      (DrainPair.routine (O := O) 22 25 24 _ _).cost e)))) ≤ _
  omega

theorem valueCode_frame (s : Store) (j : Fin 32) (different : j ≠ 26) :
    valueCode.eval s j = s j := by
  cases tag : (s 11).head? with
  | none => simp [valueCode, Local.eval, tag]
  | some symbol =>
    cases symbol <;> by_cases bit : (s 25).head? = some .one <;>
      simp [valueCode, Local.eval, Local.push, Action.apply, tag, bit, different]

theorem literalValue_bound {O : Type} (s : Store) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) : stackBound budget ((literalValue (O := O)).eval s) := by
  have after := lookup_bound (O := O) s budget sizes
  intro j
  by_cases output : j = 26
  · subst j
    rw [literalValue_result]
    split_ifs <;> simp <;> omega
  · change (valueCode.eval (Function.update ((lookup (O := O)).eval s) 26 []) j).length ≤ budget
    rw [valueCode_frame _ j output, Function.update_of_ne output]
    exact after j

theorem literalValue_cost {O : Type} (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (literalValue (O := O)).cost s ≤ (100 + valueCode.bound) * (budget + 1) := by
  have first := lookup_cost (O := O) s budget sizes
  have after := lookup_bound (O := O) s budget sizes
  have clearCost := after 26
  have localCost := valueCode.ticks_le (Function.update ((lookup (O := O)).eval s) 26 [])
  change (lookup (O := O)).cost s + 1 +
    (3 * ((lookup (O := O)).eval s 26).length + 1 +
    valueCode.ticks (Function.update ((lookup (O := O)).eval s) 26 [])) ≤ _
  nlinarith

@[simp] theorem lookup_randomFree {O : Type} : Command.RandomFree (lookup (O := O)).command := by
  simp [lookup, DrainPair.routine]

@[simp] theorem literalValue_randomFree {O : Type} : Command.RandomFree (literalValue (O := O)).command := by
  simp [literalValue]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment
