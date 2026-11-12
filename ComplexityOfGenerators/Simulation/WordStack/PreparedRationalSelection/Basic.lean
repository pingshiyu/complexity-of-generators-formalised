import ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection.Prepare

namespace ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection

set_option backward.isDefEq.respectTransparency false

variable {S O : Type}

def slots : Fin 16 ↪ Fin 35 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 35 => j.val) same)

noncomputable def finalStore (encode : Bool → S) (decode : S → Bool) (low high : Fin 35) (s : Store S) : Store S :=
  Memory.patchStore slots (Local.mapStore encode ((RationalSelection.selector (O := O)).eval (input decode low high s)))
    (preparedStore encode decode low high s)

/-- The actual finite selector command is run only after its owned register
bank has been canonically encoded, making this a total native routine. -/
noncomputable def routine (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) : Routine S O 35 where
  command := (prepare encode decode low high lowSafe highSafe).command.seq
    ((RationalSelection.selector (O := O)).embeddedCommand slots encode decode)
  eval := finalStore (O := O) encode decode low high
  cost := fun s => (prepare (O := O) encode decode low high lowSafe highSafe).cost s + 1 +
    (RationalSelection.selector (O := O)).cost (input decode low high s)
  runs bits memory index := by
    obtain ⟨first, firstCost, firstRun⟩ :=
      (prepare (O := O) encode decode low high lowSafe highSafe).runs bits memory index
    let after : Memory S O 35 := {memory with
      store := (prepare (O := O) encode decode low high lowSafe highSafe).eval memory.store}
    have prepared : ∀ j, after.store (slots j) = (input decode low high memory.store j).map encode := by
      intro j
      simp [after, prepare_eval, preparedStore, slots]
    obtain ⟨second, secondCost, secondRun⟩ :=
      (RationalSelection.selector (O := O)).embedded_runs slots encode decode retract bits after
        (input decode low high memory.store) index prepared
    refine ⟨first + 1 + second, by omega, ?_⟩
    have sequence := Command.Runs.seq memory after _ _ first second _ firstRun secondRun
    simpa only [after, finalStore, prepare_eval] using sequence

attribute [irreducible] routine

theorem routine_eval (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) :
    (routine (O := O) encode decode retract low high lowSafe highSafe).eval s =
      finalStore (O := O) encode decode low high s := by
  unfold routine
  rfl


theorem routine_cost (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) :
    (routine (O := O) encode decode retract low high lowSafe highSafe).cost s =
      (prepare (O := O) encode decode low high lowSafe highSafe).cost s + 1 +
        (RationalSelection.selector (O := O)).cost (input decode low high s) := by
  unfold routine
  rfl

theorem routine_owned (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (j : Fin 16) :
    (routine (O := O) encode decode retract low high lowSafe highSafe).eval s (slots j) =
      ((RationalSelection.selector (O := O)).eval (input decode low high s) j).map encode := by
  rw [routine_eval]
  exact Memory.patchStore_here slots _ _ j

theorem routine_frame (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) (j : Fin 35)
    (outside : 16 ≤ j.val) (scratch : j ≠ 33) :
    (routine (O := O) encode decode retract low high lowSafe highSafe).eval s j = s j := by
  rw [routine_eval, finalStore, Memory.patchStore_outside]
  · simp [preparedStore, not_lt.mpr outside, scratch]
  · intro a same
    have values := congrArg Fin.val same
    simp [slots] at values
    have := a.isLt
    omega

def result (s : Store S) : Option Bool :=
  if (s 12).head?.isSome then some (s 13).head?.isSome else none

theorem result_eq_choose (encode : Bool → S) (decode : S → Bool)
    (retract : Function.LeftInverse decode encode) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S)
    (enough : Nat.clog 2 ((s high).length - (s low).length) ≤ (s 17).length) :
    result ((routine (O := O) encode decode retract low high lowSafe highSafe).eval s) =
      RationalSelection.choose ((s high).length - (s low).length)
        ((s high).length - (s 22).length) ((s 17).map decode) := by
  have twelve := routine_owned (O := O) encode decode retract low high lowSafe highSafe s 12
  have thirteen := routine_owned (O := O) encode decode retract low high lowSafe highSafe s 13
  change (routine (O := O) encode decode retract low high lowSafe highSafe).eval s 12 = _ at twelve
  change (routine (O := O) encode decode retract low high lowSafe highSafe).eval s 13 = _ at thirteen
  have same : result ((routine (O := O) encode decode retract low high lowSafe highSafe).eval s) =
      RationalSelection.result ((RationalSelection.selector (O := O)).eval (input decode low high s)) := by
    simp only [result, RationalSelection.result, twelve, thirteen, List.head?_map, Option.isSome_map]
  rw [same]
  exact RationalSelection.selector_input_result _ _ _ (by simpa only [List.length_map] using enough)

end ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection
