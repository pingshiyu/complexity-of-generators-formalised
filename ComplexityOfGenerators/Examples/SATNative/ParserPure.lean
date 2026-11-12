import ComplexityOfGenerators.Examples.SATNative.ParserRoutine
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open Simulation.WordStack
open NativeBody

@[simp] theorem renamed_randomFree {O : Type} {k l : ℕ} (routine : Routine Symbol O k)
    (slots : Fin k ↪ Fin l) (pure : Command.RandomFree routine.command) :
    Command.RandomFree (routine.rename slots).command :=
  (pure.mapSymbols id id).rename slots

@[simp] theorem header_randomFree {O : Type} : Command.RandomFree (header (O := O)).command := by
  apply renamed_randomFree
  simp [NativeHeader.headerRoutine, NativeHeader.extract, NativeHeader.setup, NativeHeader.clockSetup,
    NativeHeader.scanRoutine]
  apply Routine.randomFree_iterate
  simp

@[simp] theorem literal_randomFree {O : Type} :
    Command.RandomFree (NativeLiteral.literalRoutine (O := O)).command := by
  simp [NativeLiteral.literalRoutine, NativeLiteral.setup, NativeLiteral.indexRoutine, NativeLiteral.indexSetup,
    NativeHeader.scanRoutine, NativeHeader.clockSetup, RationalSelection.Compare.routine,
    RationalSelection.Compare.setup, DrainPair.routine]
  constructor <;> apply Routine.randomFree_iterate <;> simp

@[simp] theorem bodyStep_randomFree {O : Type} : Command.RandomFree (bodyStep (O := O)).command := by
  simp only [bodyStep, Routine.randomFree_branch]
  intro head
  cases head with
  | none => simp
  | some tag =>
    simp only [Routine.randomFree_branch]
    intro inside
    by_cases present : inside.isSome <;> by_cases close : tag = .closeClause <;>
      simp [present, close]

@[simp] theorem parser_randomFree {O : Type} : Command.RandomFree (parser (O := O)).command := by
  simp [parser, bodySetup, NativeBody.bodyRoutine]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
