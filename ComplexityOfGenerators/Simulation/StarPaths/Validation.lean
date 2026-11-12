import ComplexityOfGenerators.Simulation.StarPaths.Basic
import ComplexityOfGenerators.Simulation.StarPaths.Stage
import ComplexityOfGenerators.Simulation.StarPaths.Selection
import ComplexityOfGenerators.Simulation.WordStack.DrainPair

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000

def isUnit : Symbol → Bool | .unit => true | _ => false

def validationFactor {O : Type} : Step O :=
  (WordStack.Routine.ofLocal (Local.pop 16)).seq
    ((WordStack.Routine.clear 19).seq
      ((WordStack.Routine.transferWhile 16 19 (by decide) isUnit id).seq
        ((WordStack.Routine.ofLocal (Local.pop 19)).seq
          ((WordStack.Routine.assign 25 23 12 (by decide) (by decide) (by decide) id).seq
            ((WordStack.Routine.clear 21).seq
              ((DrainPair.routine 19 23 21 (by decide) (by decide)).seq
                (WordStack.Routine.branch 23 fun flag => if available flag then WordStack.Routine.skip
                  else WordStack.Routine.clear 20)))))))

def validationBody {O : Type} : Step O := WordStack.Routine.branch 16 fun token =>
  if token.isSome then validationFactor else WordStack.Routine.skip

theorem validationFactor_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 16) (c : j ≠ 19)
    (d : j ≠ 20) (e : j ≠ 21) (f : j ≠ 23) : (validationFactor (O := O)).Fixes j := by
  unfold validationFactor
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_pop 16 j b)
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear 19 j c)
  apply WordStack.Routine.Fixes.seq
  · intro s
    simp [WordStack.Routine.transferWhile,b,c]
  · apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_pop 19 j c)
    apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_assign 25 23 12 (by decide) (by decide) (by decide) id j f a)
    apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear 21 j e)
    apply WordStack.Routine.Fixes.seq
    · intro s
      simp [DrainPair.routine_eval (19 : Fin 35) 23 21 (by decide) (by decide) (by decide),c,e,f]
    · apply WordStack.Routine.Fixes.branch
      intro flag
      split_ifs
      · exact WordStack.Routine.fixes_skip j
      · exact WordStack.Routine.fixes_clear 20 j d

theorem validationBody_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 16) (c : j ≠ 19)
    (d : j ≠ 20) (e : j ≠ 21) (f : j ≠ 23) : (validationBody (O := O)).Fixes j := by
  unfold validationBody
  apply WordStack.Routine.Fixes.branch
  intro token
  split_ifs
  · exact validationFactor_frame j a b c d e f
  · exact WordStack.Routine.fixes_skip j

def validationLoop {O : Type} : Step O := WordStack.Routine.iterate 18 validationBody
  (validationBody_frame 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

def validationSetup {O : Type} : Step O :=
  (WordStack.Routine.assign 31 16 12 (by decide) (by decide) (by decide) id).seq
    ((WordStack.Routine.assign 22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)).seq
      ((WordStack.Routine.clear 20).seq (WordStack.Routine.ofLocal (Local.push 20 .present))))

def validationRoutine {O : Type} : Step O := validationSetup.seq validationLoop

private theorem payload_stops (parts : Parts) :
    (payload parts).takeWhile isUnit = [] ∧ (payload parts).dropWhile isUnit = payload parts := by
  cases parts <;> simp [payload,isUnit]

private theorem takeWhile_units (n : ℕ) (parts : Parts) :
    (List.replicate n Symbol.unit++payload parts).takeWhile isUnit = List.replicate n Symbol.unit ∧
      (List.replicate n Symbol.unit++payload parts).dropWhile isUnit = payload parts := by
  induction n with
  | zero => simpa using payload_stops parts
  | succ n ih =>
      have first : isUnit Symbol.unit = true := rfl
      simpa [List.replicate_succ,List.takeWhile_cons,List.dropWhile_cons,first] using ih

/-- A native factor check drops exactly j-1 cached flags, then checks the
jth flag. Its work depends on unary lengths, without a numeric oracle. -/
theorem validationFactor_result {O : Type} (flags : List Bool) (j : ℕ) (rest : Parts) (s : Store)
    (positive : 0 < j) (input : s 16 = payload (j::rest)) (source : s 25 = flagsWord flags) :
    (validationFactor (O := O)).eval s 16 = payload rest ∧
      (validationFactor (O := O)).eval s 20 =
        if (flags[j-1]?).getD false then s 20 else [] := by
  have units := takeWhile_units j rest
  have word : s 16 = Symbol.cut::(List.replicate j Symbol.unit++payload rest) := input
  have flag : available ((flagsWord flags).drop (j-1)).head? = (flags[j-1]?).getD false := by
    have canonical := flagsWord_available (flags.drop (j-1))
    simpa [flagsWord,List.map_drop] using canonical
  have flagIndex : available ((flagsWord flags)[j-1]?) = (flags[j-1]?).getD false := by simpa using flag
  unfold validationFactor
  simp only [WordStack.Routine.seq,WordStack.Routine.ofLocal,Local.eval_pop,
    WordStack.Routine.clear,WordStack.Routine.transferWhile,WordStack.Routine.assign_eval,
    DrainPair.routine_eval (19 : Fin 35) 23 21 (by decide) (by decide) (by decide)]
  simp [word,units.1,units.2,source,List.length_reverse,List.length_tail,flag,flagIndex,
    WordStack.Routine.branch,WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.eval,WordStack.Routine.clear]
  split_ifs <;> simp [WordStack.Routine.skip,WordStack.Routine.ofLocal,Local.eval,WordStack.Routine.clear]

end ComplexityOfGenerators.Simulation.StarPaths
