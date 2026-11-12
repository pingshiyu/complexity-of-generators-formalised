import ComplexityOfGenerators.Simulation.StarPaths.Stage

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] stageBody stageRoutine

private theorem stageRep_pop (flags : List Bool) (entries : Table) (j : ℕ) (current : Option Parts)
    (s : Store) (represented : StageRep flags entries j current s) :
    StageRep flags entries j current (Function.update s 2 (s 2).tail) := by
  simpa [StageRep] using represented

/-- The bounded native archive walk implements the whole pure first-witness
scan, including truncated availability vectors. -/
theorem counted_scan {O : Type} (flags : List Bool) (entries : Table) (j : ℕ) (current : Option Parts)
    (s : Store) (positive : 0 < j) (represented : StageRep flags entries j current s) :
    StageRep (flags.drop entries.length) [] (j+entries.length) (scan flags entries j current)
      ((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[entries.length] s) := by
  induction entries generalizing flags j current s with
  | nil => simpa only [List.length_nil,List.drop_zero,Nat.add_zero,scan,Function.iterate_zero,Function.id_def] using represented
  | cons previous rest ih =>
      let ready := (WordStack.Routine.counted 2 (stageBody (O := O))).eval s
      have first := stageBody_represents (O := O) flags previous rest j current
        (Function.update s 2 (s 2).tail) positive (stageRep_pop flags _ j current s represented)
      have next := ih flags.tail (j+1) (offer current (candidate ((flags[0]?).getD false) j previous)) ready (by omega) first
      simpa only [List.length_cons,Function.iterate_succ_apply,scan,List.drop_tail,Nat.add_assoc,Nat.add_comm 1 rest.length] using next

theorem stageRoutine_result {O : Type} (flags : List Bool) (entries : Table) (s : Store)
    (represented : StageRep flags entries 1 none s) (clock : (s 2).length = entries.length) :
    (stageRoutine (O := O)).eval s 10 = held (stage flags entries) ∧
      (stageRoutine (O := O)).eval s 11 = flagWord (stage flags entries).isSome := by
  have result := counted_scan (O := O) flags entries 1 none s (by decide) represented
  unfold stageRoutine
  change (((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[(s 2).length] s) 10 = _) ∧
    (((WordStack.Routine.counted 2 (stageBody (O := O))).eval^[(s 2).length] s) 11 = _)
  rw [clock]
  exact ⟨result.2.2.2.1,result.2.2.2.2⟩

theorem stageRoutine_frame {O : Type} (j : Fin 35) (clock : j ≠ 2) (a : j ≠ 3) (b : j ≠ 5) (c : j ≠ 6)
    (d : j ≠ 7) (e : j ≠ 8) (f : j ≠ 9) (g : j ≠ 10) (h : j ≠ 11) (i : j ≠ 12) :
    (stageRoutine (O := O)).Fixes j := by
  unfold stageRoutine
  exact WordStack.Routine.Fixes.iterate 2 stageBody stageBody_frame j clock (stageBody_frame_all j a b c d e f g h i)

theorem stageSetup_represents {O : Type} (flags : List Bool) (entries : Table) (s : Store)
    (cursor : s 4 = encoded entries) (source : s 25 = flagsWord flags) :
    StageRep flags entries 1 none ((stageSetup (O := O)).eval s) := by
  simp [StageRep,stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,
    WordStack.Routine.clearMany_eval,cursor,source,held,flagWord]

theorem stageSetup_clock {O : Type} (s : Store) :
    ((stageSetup (O := O)).eval s 2).length = (s 1).length := by
  simp [stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval]

theorem stageSetup_frame {O : Type} (j : Fin 35) (a : j ≠ 2) (b : j ≠ 3) (c : j ≠ 5) (d : j ≠ 6)
    (e : j ≠ 10) (f : j ≠ 11) (g : j ≠ 12) : (stageSetup (O := O)).Fixes j := by
  intro s
  simp [stageSetup,WordStack.Routine.seq,WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval,a,b,c,d,e,f,g]

theorem appendEntry_archive {O : Type} (value : Option Parts) (s : Store)
    (word : s 10 = held value) (flag : s 11 = flagWord value.isSome) :
    (appendEntry (O := O)).eval s 4 = entry value++s 4 := by
  cases value <;> simp [appendEntry,WordStack.Routine.branch,WordStack.Routine.seq,WordStack.Routine.copy,
    WordStack.Routine.ofLocal,Local.eval_push,word,flag,held,flagWord,entry]

theorem appendEntry_frame {O : Type} (j : Fin 35) (a : j ≠ 4) (b : j ≠ 12) :
    (appendEntry (O := O)).Fixes j := by
  unfold appendEntry
  apply WordStack.Routine.Fixes.branch
  intro found
  split_ifs <;> intro s <;>
    simp [WordStack.Routine.seq,WordStack.Routine.copy,WordStack.Routine.ofLocal,Local.eval_push,a,b]

end ComplexityOfGenerators.Simulation.StarPaths
