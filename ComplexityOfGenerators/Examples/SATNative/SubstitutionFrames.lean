import ComplexityOfGenerators.Examples.SATNative.SubstitutionStep
import ComplexityOfGenerators.Examples.SATNative.SubstitutionMetadata
import ComplexityOfGenerators.Examples.SATNative.ParserPure

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem bodyStep_upperFrame {O : Type} (s : Store) (j : Fin 32) (upper : 16 ≤ j.val)
    (insideReg : j ≠ 17) (seenReg : j ≠ 18) : (bodyStep (O := O)).eval s j = s j := by
  have wordReg : j ≠ 2 := by intro equal; subst j; omega
  have validReg : j ≠ 6 := by intro equal; subst j; omega
  cases head : (s 2).head? with
  | none => simp [bodyStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil =>
      by_cases opening : tag = .openClause <;>
        simp [bodyStep, Routine.branch, head, inside, Routine.ofLocal, outsideCode,
          Local.eval, Local.pop, Local.push, Action.apply, opening, wordReg, validReg, insideReg, seenReg]
    | cons mark rest =>
      by_cases close : tag = .closeClause
      · cases seen : s 18 <;>
          simp [bodyStep, Routine.branch, head, inside, close, Routine.ofLocal, closeCode,
            Local.eval, Local.pop, Action.apply, seen, wordReg, validReg, insideReg, seenReg]
      · have frame := Routine.rename_eval_frame (NativeLiteral.literalRoutine (O := O)) subslots s j
          (by intro i equal; have := congrArg Fin.val equal; simp only [subslots_val] at this; omega)
        simpa [bodyStep, Routine.branch, head, inside, close, Routine.seq, Routine.ofLocal, Local.eval_write, seenReg] using frame

theorem emitHeader_parserFrame {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state ((emitHeader (O := O)).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 9) (b : j ≠ 21) (c : j ≠ 22) (d : j ≠ 23) (e : j ≠ 24) (f : j ≠ 25) :=
    emitHeader_frame (O := O) s j a b c d e f
  simp [Represents, frame, word, cap, count, valid, inside, seen]

@[simp] theorem replaceTag_randomFree {O : Type} (bit : Bool) : Command.RandomFree (replaceTag (O := O) bit).command := by
  simp only [replaceTag, Routine.randomFree_branch]
  intro tag
  cases tag with
  | none => simp
  | some symbol =>
    cases symbol <;> simp only
    all_goals first
      | exact Routine.randomFree_skip
      | simp only [Routine.randomFree_branch]; intro equal; split_ifs <;> simp

@[simp] theorem rewriteLiteral_randomFree {O : Type} (bit : Bool) : Command.RandomFree (rewriteLiteral (O := O) bit).command := by
  simp [rewriteLiteral, LengthTest.routine, LengthTest.setup, DrainPair.routine]

@[simp] theorem emitLiteral_randomFree {O : Type} : Command.RandomFree (emitLiteral (O := O)).command := by
  simp [emitLiteral, DrainPair.routine]

@[simp] theorem substituteLiteral_randomFree {O : Type} (bit : Bool) : Command.RandomFree (substituteLiteral (O := O) bit).command := by
  simp [substituteLiteral]

@[simp] theorem emitHeader_randomFree {O : Type} : Command.RandomFree (emitHeader (O := O)).command := by
  simp [emitHeader, DrainPair.routine]

@[simp] theorem substitutionStep_randomFree {O : Type} (bit : Bool) :
    Command.RandomFree (substitutionStep (O := O) bit).command := by
  simp only [substitutionStep, Routine.randomFree_branch]
  intro head
  cases head with
  | none => simp
  | some tag =>
    simp only [Routine.randomFree_branch]
    intro inside
    by_cases present : inside.isSome <;> by_cases opening : tag = .openClause <;>
      by_cases close : tag = .closeClause <;> simp [present, opening, close]

@[simp] theorem substitutionRoutine_randomFree {O : Type} (bit : Bool) :
    Command.RandomFree (substitutionRoutine (O := O) bit).command := by simp [substitutionRoutine]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
