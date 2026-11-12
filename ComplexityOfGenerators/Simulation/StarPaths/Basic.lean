import ComplexityOfGenerators.Simulation.StarPaths.Model
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Simulation.StarPaths

open WordStack
abbrev Store := Local.Store Symbol 35
abbrev Step (O : Type) := WordStack.Routine Symbol O 35

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000

/-- The master length and availability vector are never modified. Register
17 is the supplied cut-coin list; the final path and flag occupy 31/32. -/
def flagWord (available : Bool) : List Symbol := if available then [.present] else []
def held : Option Parts → List Symbol
  | none => []
  | some parts => payload parts

def entry : Option Parts → List Symbol
  | none => [.absent]
  | some parts => .present :: payload parts

def encoded (entries : Table) : List Symbol := entries.flatMap entry

def isPayload : Symbol → Bool
  | .unit | .cut => true
  | _ => false

def available : Option Symbol → Bool
  | some .present => true
  | _ => false

/-- Consume an archive entry, returning its payload in 8 and its availability
flag in 9. The cursor 5 advances to the following entry. -/
def readEntry {O : Type} : Step O :=
  (WordStack.Routine.clear 7).seq ((WordStack.Routine.clear 8).seq
    (WordStack.Routine.branch 5 fun head =>
      ((WordStack.Routine.clear 9).seq (if available head then WordStack.Routine.ofLocal (Local.push 9 .present) else WordStack.Routine.skip)).seq
        ((WordStack.Routine.ofLocal (Local.pop 5)).seq
          ((WordStack.Routine.transferWhile 5 7 (by decide) isPayload id).seq
            (WordStack.Routine.transfer 7 8 (by decide) id)))))

def capture {O : Type} : Step O :=
  (WordStack.Routine.assign 8 10 12 (by decide) (by decide) (by decide) id).seq
    ((WordStack.Routine.copy 3 10 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)).seq
      ((WordStack.Routine.ofLocal (Local.push 10 .cut)).seq (WordStack.Routine.ofLocal (Local.push 11 .present))))

def consider {O : Type} : Step O := WordStack.Routine.branch 11 fun found => if found.isSome then WordStack.Routine.skip else
  WordStack.Routine.branch 6 fun flag => if available flag then
    WordStack.Routine.branch 9 fun previous => if previous.isSome then capture else WordStack.Routine.skip
  else WordStack.Routine.skip

def stageBody {O : Type} : Step O :=
  (WordStack.Routine.ofLocal (Local.push 3 .unit)).seq
    (readEntry.seq (consider.seq (WordStack.Routine.ofLocal (Local.pop 6))))

attribute [local irreducible] readEntry capture consider stageBody

theorem readEntry_frame {O : Type} (j : Fin 35) (a : j ≠ 5) (b : j ≠ 7) (c : j ≠ 8) (d : j ≠ 9) :
    (readEntry (O := O)).Fixes j := by
  unfold readEntry
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear 7 j b)
  apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear 8 j c)
  apply WordStack.Routine.Fixes.branch
  intro head
  apply WordStack.Routine.Fixes.seq
  · apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_clear 9 j d)
    split_ifs
    · exact WordStack.Routine.fixes_push 9 j Symbol.present d
    · exact WordStack.Routine.fixes_skip j
  · apply WordStack.Routine.Fixes.seq (WordStack.Routine.fixes_pop 5 j a)
    apply WordStack.Routine.Fixes.seq
    · intro store
      simp [WordStack.Routine.transferWhile,a,b]
    · exact WordStack.Routine.fixes_transfer 7 8 (by decide) id j b c

theorem capture_frame {O : Type} (j : Fin 35) (a : j ≠ 10) (b : j ≠ 11) (c : j ≠ 12) :
    (capture (O := O)).Fixes j := by
  intro store
  simp [capture,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.copy,
    WordStack.Routine.ofLocal,Local.eval_push,a,b,c]

theorem consider_frame {O : Type} (j : Fin 35) (a : j ≠ 10) (b : j ≠ 11) (c : j ≠ 12) :
    (consider (O := O)).Fixes j := by
  unfold consider
  apply WordStack.Routine.Fixes.branch
  intro found
  split_ifs
  · exact WordStack.Routine.fixes_skip j
  · apply WordStack.Routine.Fixes.branch
    intro flag
    split_ifs
    · apply WordStack.Routine.Fixes.branch
      intro previous
      split_ifs
      · exact capture_frame j a b c
      · exact WordStack.Routine.fixes_skip j
    · exact WordStack.Routine.fixes_skip j

theorem stageBody_frame_all {O : Type} (j : Fin 35) (a : j ≠ 3) (b : j ≠ 5) (c : j ≠ 6)
    (d : j ≠ 7) (e : j ≠ 8) (f : j ≠ 9) (g : j ≠ 10) (h : j ≠ 11) (i : j ≠ 12) :
    (stageBody (O := O)).Fixes j := by
  unfold stageBody
  exact (WordStack.Routine.fixes_push 3 j .unit a).seq
    ((readEntry_frame j b d e f).seq ((consider_frame j g h i).seq (WordStack.Routine.fixes_pop 6 j c)))

theorem stageBody_frame {O : Type} : (stageBody (O := O)).Fixes 2 :=
  stageBody_frame_all 2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

def stageRoutine {O : Type} : Step O := WordStack.Routine.iterate 2 stageBody stageBody_frame

def stageSetup {O : Type} : Step O :=
  (WordStack.Routine.assign 4 5 12 (by decide) (by decide) (by decide) id).seq
    ((WordStack.Routine.assign 25 6 12 (by decide) (by decide) (by decide) id).seq
      ((WordStack.Routine.assign 1 2 12 (by decide) (by decide) (by decide) id).seq
        (WordStack.Routine.clearMany [3,10,11])))

def appendEntry {O : Type} : Step O := WordStack.Routine.branch 11 fun found => if found.isSome then
  (WordStack.Routine.copy 10 4 12 (by decide) (by decide) (by decide) id).seq
    (WordStack.Routine.ofLocal (Local.push 4 .present))
  else WordStack.Routine.ofLocal (Local.push 4 .absent)

def outerBody {O : Type} : Step O :=
  (WordStack.Routine.ofLocal (Local.push 1 .unit)).seq (stageSetup.seq (stageRoutine.seq appendEntry))

theorem outerBody_frame {O : Type} : (outerBody (O := O)).Fixes 0 := by
  have inner : (stageRoutine (O := O)).Fixes 0 :=
    WordStack.Routine.Fixes.iterate 2 stageBody stageBody_frame 0 (by decide)
      (stageBody_frame_all 0 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
  have setup : (stageSetup (O := O)).Fixes 0 := by
    intro store
    simp [stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]
  have append : (appendEntry (O := O)).Fixes 0 := by
    unfold appendEntry
    apply WordStack.Routine.Fixes.branch
    intro found
    split_ifs <;> intro store <;>
      simp [WordStack.Routine.seq,WordStack.Routine.copy,WordStack.Routine.ofLocal,Local.eval_push]
  unfold outerBody
  exact (WordStack.Routine.fixes_push 1 0 Symbol.unit (by decide)).seq (setup.seq (inner.seq append))

def owned : List (Fin 35) := (List.finRange 35).filter (fun j => j != 17 && j != 22 && j != 25)

def prepare {O : Type} : Step O :=
  (WordStack.Routine.clearMany owned).seq
    ((WordStack.Routine.assign 22 0 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit)).seq
      ((WordStack.Routine.ofLocal (Local.push 4 .present)).seq (WordStack.Routine.ofLocal (Local.push 11 .present))))

def dpRoutine {O : Type} : Step O := prepare.seq (WordStack.Routine.iterate 0 outerBody outerBody_frame)

end ComplexityOfGenerators.Simulation.StarPaths
