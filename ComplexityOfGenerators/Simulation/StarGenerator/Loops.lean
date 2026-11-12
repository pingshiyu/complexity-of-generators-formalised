import ComplexityOfGenerators.Simulation.StarGenerator.Views

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

theorem InnerStored.pop_clock {table : Table α} {m j : ℕ} {p : Option (List α) × BitString} {s : Store G}
    (stored : InnerStored G table m j p s) :
    InnerStored G table m j p ((Local.pop (30 : Fin 35)).eval s) := by
  rcases stored with ⟨length, input, auxiliary, empty, target, index, random, table, cursor, word, found⟩
  constructor <;> simp_all [Local.eval_pop]

theorem innerLoop_correct (seed time : PolynomialBound) (table : Table α) (m steps j : ℕ)
    (p : Option (List α) × BitString) (s : Store G) (stored : InnerStored G table m j p s)
    (positive : 1 ≤ j) (remaining : j + steps ≤ m + 1) :
    let answer := (List.range' j steps).foldl (fun p j => next G seed time table m j p) p
    InnerStored G table m (j + steps) answer
      ((WordStack.Routine.counted 30 (innerStep G seed time)).eval^[steps] s) := by
  induction steps generalizing j p s with
  | zero => simpa using stored
  | succ steps ih =>
    have nextView := innerStep_correct G seed time table m j p ((Local.pop (30 : Fin 35)).eval s)
      stored.pop_clock positive (by omega)
    have last := ih (j + 1) (next G seed time table m j p) _ nextView (by omega) (by omega)
    simpa only [List.range'_succ, List.foldl_cons, Function.iterate_succ_apply,
      WordStack.Routine.counted, WordStack.Routine.seq, WordStack.Routine.ofLocal,
      Nat.add_assoc, Nat.add_comm 1 steps] using last

structure OuterStored (m : ℕ) (table : Table α) (bits : BitString) (s : Store G) : Prop where
  length : table.length = m + 1
  input : s 11 = []
  auxiliary : s 12 = []
  empty : s 14 = []
  target : (s 23).length = m
  random : s 17 = bits.map Symbol.bit
  archiveWord : s 29 = archive G table
  word : s 31 = UnionGenerator.held G G (table.getLast?.bind id)
  found : s 32 = UnionGenerator.flagWord G G (table.getLast?.bind id).isSome

theorem stageSetup_stored (m : ℕ) (table : Table α) (bits : BitString) (s : Store G)
    (stored : OuterStored G m table bits s) :
    InnerStored G table (m + 1) 1 (none, bits) ((stageSetup G).eval s) := by
  let ready := (stageSetup G).eval s
  have initial : InnerStored G table (m + 1) 1 (none, bits) ready := by
    constructor
    · exact stored.length
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval] using stored.input
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval] using stored.auxiliary
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval] using stored.empty
    · simp [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, stored.target]
    · simp [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval]
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval] using stored.random
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval] using stored.archiveWord
    · simpa [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, archive] using stored.archiveWord
    · simp [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, UnionGenerator.held]
    · simp [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, UnionGenerator.flagWord]
  exact initial

theorem stageSetup_clock (m : ℕ) (table : Table α) (bits : BitString) (s : Store G)
    (stored : OuterStored G m table bits s) : ((stageSetup G).eval s 30).length = m + 1 := by
  let ready := (stageSetup G).eval s
  have clock : (ready 30).length = m + 1 := by
    simp [ready, stageSetup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.clear, WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, stored.target]
  exact clock

theorem stageStep_correct (seed time : PolynomialBound) (m : ℕ) (table : Table α)
    (bits : BitString) (s : Store G) (stored : OuterStored G m table bits s) :
    let answer := extend G seed time (m + 1) (table, bits)
    OuterStored G (m + 1) answer.1 answer.2 ((stageStep G seed time).eval s) := by
  let ready := (stageSetup G).eval s
  have initial : InnerStored G table (m + 1) 1 (none, bits) ready :=
    stageSetup_stored G m table bits s stored
  have clock : (ready 30).length = m + 1 := stageSetup_clock G m table bits s stored
  have last := innerLoop_correct G seed time table (m + 1) (m + 1) 1 (none, bits) ready initial (by omega) (by omega)
  let endStore := (WordStack.Routine.counted 30 (innerStep G seed time)).eval^[m + 1] ready
  have result : InnerStored G table (m + 1) (m + 2) (stage G seed time table (m + 1) bits) endStore := by
    simpa only [stage, Nat.one_add, Nat.add_assoc] using last
  have appended : OuterStored G (m + 1)
      (table ++ [(stage G seed time table (m + 1) bits).1])
      (stage G seed time table (m + 1) bits).2 ((appendEntry G).eval endStore) := by
    constructor
    · simp [stored.length]
    · exact (appendEntry_fixes G 11 (by decide) (by decide) endStore).trans result.input
    · exact (appendEntry_fixes G 12 (by decide) (by decide) endStore).trans result.auxiliary
    · exact (appendEntry_fixes G 14 (by decide) (by decide) endStore).trans result.empty
    · exact (congrArg List.length (appendEntry_fixes G 23 (by decide) (by decide) endStore)).trans result.target
    · exact (appendEntry_fixes G 17 (by decide) (by decide) endStore).trans result.random
    · rw [appendEntry_archive G _ endStore result.word result.found, result.archiveWord, archive_append]
    · simpa [List.getLast?_concat] using (appendEntry_fixes G 31 (by decide) (by decide) endStore).trans result.word
    · simpa [List.getLast?_concat] using (appendEntry_fixes G 32 (by decide) (by decide) endStore).trans result.found
  change OuterStored G (m + 1) _ _ ((appendEntry G).eval
    ((WordStack.Routine.counted 30 (innerStep G seed time)).eval^[(ready 30).length] ready))
  rw [clock]
  exact appended

theorem OuterStored.pop_clock {m : ℕ} {table : Table α} {bits : BitString} {s : Store G}
    (stored : OuterStored G m table bits s) :
    OuterStored G m table bits ((Local.pop (22 : Fin 35)).eval s) := by
  rcases stored with ⟨length, input, auxiliary, empty, target, random, table, word, found⟩
  constructor <;> simp_all [Local.eval_pop]

theorem outerLoop_correct (seed time : PolynomialBound) (steps m : ℕ)
    (p : Table α × BitString) (s : Store G) (stored : OuterStored G m p.1 p.2 s) :
    let answer := (List.range' (m + 1) steps).foldl (fun p m => extend G seed time m p) p
    OuterStored G (m + steps) answer.1 answer.2
      ((WordStack.Routine.counted 22 (stageStep G seed time)).eval^[steps] s) := by
  induction steps generalizing m p s with
  | zero => simpa using stored
  | succ steps ih =>
    have nextView := stageStep_correct G seed time m p.1 p.2 ((Local.pop (22 : Fin 35)).eval s) stored.pop_clock
    have last := ih (m + 1) (extend G seed time (m + 1) p) _ nextView
    simpa only [List.range'_succ, List.foldl_cons, Function.iterate_succ_apply,
      WordStack.Routine.counted, WordStack.Routine.seq, WordStack.Routine.ofLocal,
      Nat.add_assoc, Nat.add_comm 1 steps] using last

structure Chosen (answer : Option (List α)) (s : Store G) : Prop where
  word : s 31 = UnionGenerator.held G G answer
  found : s 32 = UnionGenerator.flagWord G G answer.isSome

theorem body_chosen (sourceSeed sourceTime : PolynomialBound) (n read : ℕ) (bits : BitString) :
    Chosen G (algorithm G sourceSeed sourceTime n bits)
      ((body G sourceSeed sourceTime).eval
        (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store) := by
  let start := (BoundedSource.preparedMemory (O := α) (Symbol.unit : Cell G) Symbol.bit n read bits).store
  let ready := (setup G).eval start
  have initial : OuterStored G 0 [some []] bits ready := by
    constructor <;>
      simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
        WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval,
        BoundedSource.preparedMemory, archive, encoded, entry, UnionGenerator.held,
        UnionGenerator.letters, UnionGenerator.flagWord]
  have clock : (ready 22).length = n := by
    simp [ready, start, setup, WordStack.Routine.seq, WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal, Local.eval_push, UnionGenerator.flag_eval, BoundedSource.preparedMemory]
  have last := outerLoop_correct G sourceSeed sourceTime n 0 ([some []], bits) ready initial
  let endStore := (WordStack.Routine.counted 22 (stageStep G sourceSeed sourceTime)).eval^[n] ready
  have result : OuterStored G n (tableRun G sourceSeed sourceTime n bits).1
      (tableRun G sourceSeed sourceTime n bits).2 endStore := by
    simpa only [tableRun, Nat.zero_add] using last
  change Chosen G (algorithm G sourceSeed sourceTime n bits)
    ((WordStack.Routine.counted 22 (stageStep G sourceSeed sourceTime)).eval^[(ready 22).length] ready)
  rw [clock]
  exact ⟨result.word, result.found⟩

end ComplexityOfGenerators.Simulation.StarGenerator
