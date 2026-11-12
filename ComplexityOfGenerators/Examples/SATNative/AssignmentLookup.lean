import ComplexityOfGenerators.Examples.SATNative.BodyRoutine
import ComplexityOfGenerators.Examples.SATWordReduction

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 32

/-- Copy the certificate and drop d-j symbols. Certificates assign active
variables in descending order, as in the manuscript's downward path. -/
def lookup {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 24).seq
  ((Routine.assign 10 22 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.assign 5 23 9 (by decide) (by decide) (by decide) id).seq
  ((DrainPair.routine 23 22 24 (by decide) (by decide)).seq
  ((Routine.assign 3 25 9 (by decide) (by decide) (by decide) id).seq
    (DrainPair.routine 22 25 24 (by decide) (by decide))))))

theorem lookup_eval {O : Type} (s : Store) :
    (lookup (O := O)).eval s =
      Function.update (Function.update (Function.update (Function.update (Function.update s
        9 []) 22 []) 23 []) 24 []) 25 ((s 3).drop ((s 10).length - (s 5).length)) := by
  funext j
  by_cases scratch : j = 9 <;> by_cases clock : j = 22 <;> by_cases temporary : j = 23 <;>
    by_cases discarded : j = 24 <;> by_cases result : j = 25 <;>
      simp [lookup, Routine.seq, Routine.clear, Routine.assign_eval,
        DrainPair.routine_eval (23 : Fin 32) 22 24 (by decide) (by decide) (by decide),
        DrainPair.routine_eval (22 : Fin 32) 25 24 (by decide) (by decide) (by decide),
        scratch, clock, temporary, discarded, result]

theorem assignment_at (bits : List Bool) (index : ℕ) (positive : 0 < index) (bound : index ≤ bits.length) :
    bits[bits.length - index]? = some (assignment bits index) := by
  induction bits generalizing index with
  | nil => simp at bound; omega
  | cons bit rest ih =>
    by_cases last : index = rest.length + 1
    · subst index
      simp [assignment]
    · have tailBound : index ≤ rest.length := by simp only [List.length_cons] at bound; omega
      have position : rest.length + 1 - index = (rest.length - index) + 1 := by omega
      simpa [assignment, last, position] using ih index positive tailBound

/-- The native lookup selects exactly the value used by the paper's
certificate assignment, with no unbounded word operation in an instruction. -/
theorem lookup_certificate {O : Type} (s : Store) (bits : List Bool) (index : ℕ)
    (certificate : s 3 = bits.map bitSymbol) (active : (s 10).length = bits.length)
    (literal : (s 5).length = index) (positive : 0 < index) (bound : index ≤ bits.length) :
    (((lookup (O := O)).eval s) 25).head? = some (bitSymbol (assignment bits index)) := by
  rw [lookup_eval]
  simp only [Function.update_self, certificate, active, literal, List.head?_eq_getElem?, List.getElem?_drop]
  simpa only [Nat.add_zero, List.getElem?_map, assignment_at bits index positive bound, Option.map_some]

def valueCode : Local Symbol 32 :=
  .read 11 fun tag => match tag with
  | some .trueConstant => Local.push 26 .one
  | some .positive => Local.read 25 fun value => if value = some .one then Local.push 26 .one else .skip
  | some .negative => Local.read 25 fun value => if value = some .one then .skip else Local.push 26 .one
  | _ => .skip

def literalValue {O : Type} : Routine Symbol O 32 :=
  lookup.seq ((Routine.clear 26).seq (Routine.ofLocal valueCode))

def value (tag : Option Symbol) (bit : Option Symbol) : Bool :=
  match tag with
  | some .trueConstant => true
  | some .positive => decide (bit = some .one)
  | some .negative => decide (bit ≠ some .one)
  | _ => false

theorem literalValue_result {O : Type} (s : Store) :
    (literalValue (O := O)).eval s 26 =
      if value (s 11).head? ((s 3).drop ((s 10).length - (s 5).length)).head? then [.one] else [] := by
  cases tag : (s 11).head? with
  | none => simp [literalValue, Routine.seq, lookup_eval, Routine.clear, Routine.ofLocal, valueCode, Local.eval, value, tag]
  | some symbol =>
    cases symbol <;> by_cases bit : (s 3)[(s 10).length - (s 5).length]? = some .one <;>
      simp [literalValue, Routine.seq, lookup_eval, Routine.clear, Routine.ofLocal, valueCode,
        Local.eval, Local.push, Action.apply, value, tag, bit]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment
