import ComplexityOfGenerators.Simulation.StarGenerator.Components

set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace ComplexityOfGenerators.Simulation.StarGenerator

open WordStack
open UnionGenerator (Symbol)

variable {α : Type} [Fintype α] (G : Machine Unit Bool α)

structure InnerStored (table : Table α) (m j : ℕ) (p : Option (List α) × BitString) (s : Store G) : Prop where
  length : table.length = m
  input : s 11 = []
  auxiliary : s 12 = []
  empty : s 14 = []
  target : (s 23).length = m
  index : (s 24).length = j
  random : s 17 = p.2.map Symbol.bit
  archiveWord : s 29 = archive G table
  cursor : s 34 = encoded G (table.reverse.drop (j - 1))
  word : s 31 = UnionGenerator.held G G p.1
  found : s 32 = UnionGenerator.flagWord G G p.1.isSome

theorem cursorValue_eq (table : Table α) (m j : ℕ)
    (length : table.length = m) (positive : 1 ≤ j) (bounded : j ≤ m) :
    ((table.reverse.drop (j - 1)).head?).bind id = (table[m - j]?).bind id := by
  have eq : table.reverse[j - 1]? = table[m - j]? :=
    List.getElem?_reverse' (by omega)
  simpa only [List.head?_drop] using congrArg (fun value : Option (Option (List α)) => value.bind id) eq

theorem selected_value (previous left right : Option (List α)) (bits : BitString) (s : Store G)
    (word : s 31 = UnionGenerator.held G G previous)
    (found : s 32 = UnionGenerator.flagWord G G previous.isSome)
    (leftWord : s 25 = UnionGenerator.held G G left)
    (leftFlag : s 27 = UnionGenerator.flagWord G G left.isSome)
    (rightWord : s 26 = UnionGenerator.held G G right)
    (rightFlag : s 28 = UnionGenerator.flagWord G G right.isSome)
    (random : s 17 = bits.map Symbol.bit) :
    let answer := ConcatenationGenerator.offer previous (ConcatenationGenerator.pairValue left right)
      (bits.head? == some true)
    (ConcatenationGenerator.offerStored G G).eval s 31 = UnionGenerator.held G G answer ∧
      (ConcatenationGenerator.offerStored G G).eval s 32 = UnionGenerator.flagWord G G answer.isSome := by
  cases bits with
  | nil =>
    cases previous <;> cases left <;> cases right <;>
      constructor <;>
      simp [ConcatenationGenerator.offerStored, ConcatenationGenerator.offer, ConcatenationGenerator.pairValue,
        WordStack.Routine.branch, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval,
        ConcatenationGenerator.save_eval, word, found, leftWord, leftFlag, rightWord, rightFlag, random,
        UnionGenerator.held, UnionGenerator.flagWord, UnionGenerator.letters, List.map_append, Option.or]
  | cons bit rest =>
    cases bit <;> cases previous <;> cases left <;> cases right <;>
      constructor <;>
      simp [ConcatenationGenerator.offerStored, ConcatenationGenerator.offer, ConcatenationGenerator.pairValue,
        WordStack.Routine.branch, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval,
        ConcatenationGenerator.save_eval, word, found, leftWord, leftFlag, rightWord, rightFlag, random,
        UnionGenerator.held, UnionGenerator.flagWord, UnionGenerator.letters, List.map_append, Option.or]

theorem sourceSetup_stored (table : Table α) (m j : ℕ)
    (p : Option (List α) × BitString) (s : Store G) (stored : InnerStored G table m j p s) :
    UnionGenerator.Stored G G j p.2 none ((table.reverse.drop (j - 1)).head?.bind id)
      ((sourceSetup G).eval s) := by
  let remaining := table.reverse.drop (j - 1)
  let old := remaining.head?.bind id
  let r := (readEntry G).eval s
  have readSpec := readEntry_summary G remaining s stored.cursor
  have readFrame (q : Fin 35) (a : q ≠ 25) (b : q ≠ 26) (c : q ≠ 28) (d : q ≠ 34) : r q = s q :=
    readEntry_fixes G q a b c d s
  have r25 : r 25 = [] := by simpa using congrFun readSpec 25
  have r26 : r 26 = UnionGenerator.held G G old := by simpa [old, r] using congrFun readSpec 26
  have r28 : r 28 = UnionGenerator.flagWord G G old.isSome := by simpa [old, r] using congrFun readSpec 28
  have r34 : r 34 = encoded G (remaining.drop 1) := by simpa using congrFun readSpec 34
  let a := (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).eval
    ((UnionGenerator.flag G G 27 false).eval r)
  have initial : UnionGenerator.Stored G G j p.2 none old a := by
    constructor
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
        readFrame 11 (by decide) (by decide) (by decide) (by decide), stored.input]
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
        readFrame 12 (by decide) (by decide) (by decide) (by decide), stored.auxiliary]
    · simpa [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
        readFrame 24 (by decide) (by decide) (by decide) (by decide)] using stored.index
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
        readFrame 17 (by decide) (by decide) (by decide) (by decide), stored.random]
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval,
        readFrame 14 (by decide) (by decide) (by decide) (by decide), stored.empty]
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval, r25, UnionGenerator.held]
    · simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval, UnionGenerator.flagWord]
    · simpa [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval] using r26
    · simpa [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval] using r28
  exact initial

theorem innerStep_correct (seed time : PolynomialBound) (table : Table α) (m j : ℕ)
    (p : Option (List α) × BitString) (s : Store G) (stored : InnerStored G table m j p s)
    (positive : 1 ≤ j) (bounded : j ≤ m) :
    InnerStored G table m (j + 1) (next G seed time table m j p) ((innerStep G seed time).eval s) := by
  let remaining := table.reverse.drop (j - 1)
  let old := remaining.head?.bind id
  let r := (readEntry G).eval s
  have readSpec := readEntry_summary G remaining s stored.cursor
  have readFrame (q : Fin 35) (a : q ≠ 25) (b : q ≠ 26) (c : q ≠ 28) (d : q ≠ 34) : r q = s q :=
    readEntry_fixes G q a b c d s
  have r34 : r 34 = encoded G (remaining.drop 1) := by simpa using congrFun readSpec 34
  let a := (WordStack.Routine.assign (O := α) 24 13 33 (by decide) (by decide) (by decide) id).eval
    ((UnionGenerator.flag G G 27 false).eval r)
  have initial : UnionGenerator.Stored G G j p.2 none old a := by
    exact sourceSetup_stored G table m j p s stored
  let b := (UnionGenerator.leftFinish G G).eval ((UnionGenerator.leftTrial G G seed time).eval a)
  have source := UnionGenerator.leftStep_stored G G seed time j p.2 none old a initial
  have bOuter (q : Fin 35) (allowed : q = 23 ∨ q = 24 ∨ q = 29 ∨ q = 31 ∨ q = 32) : b q = s q := by
    have large : 22 ≤ q.val := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nw : q ≠ 25 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have nf : q ≠ 27 := by rcases allowed with rfl | rfl | rfl | rfl | rfl <;> decide
    have first : b q = a q := ConcatenationGenerator.leftStep_frame G G seed time a q large nw nf
    apply first.trans
    have second : a q = r q := by
      rcases allowed with rfl | rfl | rfl | rfl | rfl <;>
        simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval]
    apply second.trans
    rcases allowed with rfl | rfl | rfl | rfl | rfl <;>
      exact readFrame _ (by decide) (by decide) (by decide) (by decide)
  have b34 : b 34 = encoded G (table.reverse.drop j) := by
    have first : b 34 = a 34 := ConcatenationGenerator.leftStep_frame G G seed time a 34 (by decide) (by decide) (by decide)
    have second : a 34 = r 34 := by simp [a, WordStack.Routine.assign_eval, UnionGenerator.flag_eval]
    have drop : remaining.drop 1 = table.reverse.drop j := by
      dsimp [remaining]
      rw [List.drop_drop]
      congr 1
      omega
    exact first.trans (second.trans (r34.trans (congrArg (encoded G) drop)))
  have selection := selected_value G p.1 (UnionGenerator.sourceValue G time j (p.2.take (seed j))) old
    (p.2.drop (seed j)) b
    ((bOuter 31 (by simp)).trans stored.word) ((bOuter 32 (by simp)).trans stored.found)
    source.leftWord source.leftFlag source.rightWord source.rightFlag source.random
  have oldEq : old = (table[m - j]?).bind id := cursorValue_eq table m j stored.length positive bounded
  rw [oldEq] at selection
  let o := (ConcatenationGenerator.offerStored G G).eval b
  have offerFrame (q : Fin 35) (nw : q ≠ 31) (nf : q ≠ 32) (ns : q ≠ 33) : o q = b q :=
    offerStored_fixes G q nw nf ns b
  have oi : o 11 = [] := (offerFrame 11 (by decide) (by decide) (by decide)).trans source.input
  have oa : o 12 = [] := (offerFrame 12 (by decide) (by decide) (by decide)).trans source.auxiliary
  have oe : o 14 = [] := (offerFrame 14 (by decide) (by decide) (by decide)).trans source.empty
  have ot : (o 23).length = m :=
    (congrArg List.length ((offerFrame 23 (by decide) (by decide) (by decide)).trans (bOuter 23 (by simp)))).trans stored.target
  have oj : (o 24).length = j :=
    (congrArg List.length ((offerFrame 24 (by decide) (by decide) (by decide)).trans (bOuter 24 (by simp)))).trans stored.index
  have orandom : o 17 = (p.2.drop (seed j)).map Symbol.bit :=
    (offerFrame 17 (by decide) (by decide) (by decide)).trans source.random
  have oarchive : o 29 = archive G table :=
    ((offerFrame 29 (by decide) (by decide) (by decide)).trans (bOuter 29 (by simp))).trans stored.archiveWord
  have ocursor : o 34 = encoded G (table.reverse.drop j) :=
    (offerFrame 34 (by decide) (by decide) (by decide)).trans b34
  change InnerStored G table m (j + 1) (next G seed time table m j p) ((advance G).eval o)
  constructor
  · exact stored.length
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using oi
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using oa
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using oe
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using ot
  · simp [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push, oj]
  · simp [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push,
      next, orandom, List.drop_one]
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using oarchive
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push] using ocursor
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push, next] using selection.1
  · simpa [advance, WordStack.Routine.seq, WordStack.Routine.ofLocal, Local.eval_pop, Local.eval_push, next] using selection.2

end ComplexityOfGenerators.Simulation.StarGenerator
