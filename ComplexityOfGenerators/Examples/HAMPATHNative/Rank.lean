import ComplexityOfGenerators.Examples.HAMPATHNative.Metadata
import ComplexityOfGenerators.Examples.HAMPATHNative.Logarithm
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel
import ComplexityOfGenerators.Examples.HAMPATHNative.Syntax
import ComplexityOfGenerators.Examples.HAMPATHWordReduction
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem wordRank_eq_header (word : List Symbol) :
    wordRank word = if wellFormed word then rank (headerSize word) else 0 := by
  cases decoded : decode word with
  | none =>
      have invalid : wellFormed word = false := by
        cases valid : wellFormed word with
        | false => rfl
        | true => have good := (wellFormed_iff_decode word).mp valid; simp [decoded] at good
      simp [wordRank, decoded, invalid]
  | some pair =>
      obtain ⟨graph, start⟩ := pair
      obtain ⟨inside, encoded⟩ := decode_sound decoded
      rw [← encoded]
      simp [wordRank_encode graph start inside, headerSize_encode, wellFormed_encode graph start inside]

noncomputable def rankBody {O : Type} : Routine Symbol O 32 :=
  (Routine.ofLocal (Local.push 17 (.bit true))).seq
    (Logarithm.routine.seq (Routine.transfer 19 20 (by decide) id))

theorem rankBody_values {O : Type} (s : Store) :
    (rankBody (O := O)).eval s 17 = .bit true :: s 17 ∧
    (rankBody (O := O)).eval s 20 =
      List.replicate (Nat.clog 2 ((s 17).length + 1)) (.bit true) ++ s 20 ∧
    (rankBody (O := O)).eval s 16 = s 16 ∧
    (rankBody (O := O)).eval s 21 = s 21 := by
  let a := (Routine.ofLocal (O := O) (Local.push (17 : Fin 32) (.bit true))).eval s
  let b := (Logarithm.routine (O := O)).eval a
  have output := Logarithm.routine_value (O := O) a
  have source := Logarithm.routine_frame (O := O) a 17 (by decide) (by decide) (by decide)
  have total := Logarithm.routine_frame (O := O) a 20 (by decide) (by decide) (by decide)
  have valid := Logarithm.routine_frame (O := O) a 16 (by decide) (by decide) (by decide)
  have clock := Logarithm.routine_frame (O := O) a 21 (by decide) (by decide) (by decide)
  change ((Routine.transfer (O := O) 19 20 (by decide) id).eval b 17 = _) ∧
    ((Routine.transfer (O := O) 19 20 (by decide) id).eval b 20 = _) ∧
    ((Routine.transfer (O := O) 19 20 (by decide) id).eval b 16 = _) ∧
    ((Routine.transfer (O := O) 19 20 (by decide) id).eval b 21 = _)
  change b 19 = _ at output
  change b 17 = _ at source
  change b 20 = _ at total
  change b 16 = _ at valid
  change b 21 = _ at clock
  simp [Routine.transfer, output, source, total, valid, clock, a, Routine.ofLocal, Local.eval, Local.push,
    Action.apply]

theorem rankBody_clock {O : Type} (s : Store) : (rankBody (O := O)).eval s 21 = s 21 :=
  (rankBody_values s).2.2.2

noncomputable def rankCounted {O : Type} : Routine Symbol O 32 := Routine.counted 21 rankBody

theorem rankCounted_values {O : Type} (s : Store) :
    (rankCounted (O := O)).eval s 17 = .bit true :: s 17 ∧
    (rankCounted (O := O)).eval s 20 =
      List.replicate (Nat.clog 2 ((s 17).length + 1)) (.bit true) ++ s 20 ∧
    (rankCounted (O := O)).eval s 16 = s 16 ∧
    (rankCounted (O := O)).eval s 21 = (s 21).tail := by
  simpa [rankCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop] using
    rankBody_values (O := O) (Function.update s 21 (s 21).tail)

theorem rankIterate_values {O : Type} (s : Store) (source : s 17 = []) (total : s 20 = []) (count : ℕ) :
    ((rankCounted (O := O)).eval^[count] s) 17 = List.replicate count (.bit true) ∧
    ((rankCounted (O := O)).eval^[count] s) 20 = List.replicate (rank count) (.bit true) ∧
    ((rankCounted (O := O)).eval^[count] s) 16 = s 16 ∧
    ((rankCounted (O := O)).eval^[count] s) 21 = (s 21).drop count := by
  induction count with
  | zero => simp [source, total]
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have next := rankCounted_values (O := O) ((rankCounted (O := O)).eval^[count] s)
      rw [ih.1, ih.2.1, ih.2.2.1, ih.2.2.2] at next
      simpa [rank_succ, width, List.replicate_succ, ← List.replicate_add, Nat.add_comm, List.tail_drop] using next

noncomputable def ranks {O : Type} : Routine Symbol O 32 := Routine.iterate 21 rankBody rankBody_clock

def rankSetup {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 17 21 18 (by decide) (by decide) (by decide) id).seq (Routine.clearMany [17, 19, 20])

noncomputable def rankCore {O : Type} : Routine Symbol O 32 :=
  metadata.seq (rankSetup.seq (ranks.seq (gate 20)))

theorem rankCore_value {O : Type} (s : Store) :
    (rankCore (O := O)).eval s 20 =
      if acceptedSyntax s then List.replicate (rank (s 4).length) (.bit true) else [] := by
  let a := (metadata (O := O)).eval s
  let b := (rankSetup (O := O)).eval a
  have source : b 17 = [] := by simp [b, rankSetup, Routine.seq, Routine.clearMany_eval]
  have total : b 20 = [] := by simp [b, rankSetup, Routine.seq, Routine.clearMany_eval]
  have clock : (b 21).length = (s 4).length := by
    simp [b, a, rankSetup, metadata_eval, Routine.seq, Routine.clearMany_eval, Routine.assign_eval]
  have saved : b 16 = flag (acceptedSyntax s) := by
    simp [b, a, rankSetup, metadata_eval, Routine.seq, Routine.clearMany_eval, Routine.assign_eval]
  have scanned := rankIterate_values (O := O) b source total (b 21).length
  have output : (ranks (O := O)).eval b 20 = List.replicate (rank (s 4).length) (.bit true) := by
    simpa [ranks, Routine.iterate, rankCounted, clock] using scanned.2.1
  have valid : (ranks (O := O)).eval b 16 = flag (acceptedSyntax s) := by
    simpa [ranks, Routine.iterate, rankCounted, saved] using scanned.2.2.1
  change (gate (O := O) 20).eval ((ranks (O := O)).eval b) 20 = _
  rw [gate_eval, output, valid]
  cases acceptedSyntax s <;> simp [flag]

noncomputable def rankRoutine : Routine Symbol Unit 32 := prepare.seq (parser.seq rankCore)

theorem rankRoutine_value (word : List Symbol) (auxiliary : List Unit) :
    rankRoutine.eval (loaded word auxiliary).store 20 = List.replicate (wordRank word) (.bit true) := by
  let s := (prepared word auxiliary).store
  have wordEq : s 2 = word := prepared_word word auxiliary
  have syntaxValue : acceptedSyntax ((parser (O := Unit)).eval s) = wellFormed word := by
    simpa only [acceptedSyntax, wordEq] using parser_decides (O := Unit) s
  have size : (((parser (O := Unit)).eval s) 4).length = headerSize word := by
    rw [parser_eval]
    simp [s, startEncoded, rowEncoded, cellEncoded, prepared_word]
  change (rankCore (O := Unit)).eval ((parser (O := Unit)).eval s) 20 = _
  rw [rankCore_value, syntaxValue, size, wordRank_eq_header]
  cases wellFormed word <;> simp

end ComplexityOfGenerators.Examples.HAMPATH.Native
