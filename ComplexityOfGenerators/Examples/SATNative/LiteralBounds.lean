import ComplexityOfGenerators.Examples.SATNative.LiteralCheck

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral

open Simulation.WordStack
open NativeHeader

set_option backward.isDefEq.respectTransparency false

theorem field_count (capacity : ℕ) (word : List Symbol) :
    (fieldState capacity word).count ≤ capacity := by
  have bound := NativeHeader.iterate_count ⟨word.tail, 0, true, true⟩ capacity
  simpa only [fieldState, Nat.zero_add] using bound

theorem field_length (capacity : ℕ) (word : List Symbol) :
    (fieldState capacity word).word.length ≤ word.length := by
  rw [fieldState, NativeHeader.iterate_word]
  simp only [List.length_drop, List.length_tail]
  omega

theorem setup_bound {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol)
    (enabled : Bool) (budget : ℕ) (sizes : ∀ j, (base j).length ≤ budget)
    (cap : capacity ≤ budget) (count : active ≤ budget) (wordSize : word.length ≤ budget) :
    ∀ j, ((setup (O := O)).eval (inputStore base capacity active word enabled) j).length ≤ budget + 1 := by
  have tagLength : word.head?.toList.length ≤ 1 := by cases word <;> simp
  intro j
  rw [setup_eval]
  fin_cases j <;> simp [NativeHeader.encoded, scaffold, List.length_tail] <;>
    (try split_ifs) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (sizes _).trans (by omega) | omega

theorem literalRoutine_bound {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol)
    (enabled : Bool) (budget : ℕ) (sizes : ∀ j, (base j).length ≤ budget)
    (cap : capacity ≤ budget) (count : active ≤ budget) (wordSize : word.length ≤ budget) :
    ∀ j, ((literalRoutine (O := O)).eval (inputStore base capacity active word enabled) j).length ≤ budget + 1 := by
  have number := field_count capacity word
  have residual := field_length capacity word
  have tagLength : word.head?.toList.length ≤ 1 := by cases word <;> simp
  intro j
  rw [literalRoutine_eval]
  fin_cases j <;> simp [NativeHeader.encoded, scaffold, indexFrame, checked,
    NativeHeader.restrict] <;> (try split_ifs) <;>
    (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (sizes _).trans (by omega) | omega

/-- Fixed bounds do not grow during repeated parsing: the only extra unary
mark is in the comparison threshold, whose length is active+1. -/
theorem literalRoutine_bound_same {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol)
    (enabled : Bool) (budget : ℕ) (positive : 0 < budget) (sizes : ∀ j, (base j).length ≤ budget)
    (cap : capacity ≤ budget) (count : active + 1 ≤ budget) (wordSize : word.length ≤ budget) :
    ∀ j, ((literalRoutine (O := O)).eval (inputStore base capacity active word enabled) j).length ≤ budget := by
  have number := field_count capacity word
  have residual := field_length capacity word
  have tagLength : word.head?.toList.length ≤ 1 := by cases word <;> simp
  intro j
  rw [literalRoutine_eval]
  fin_cases j <;> simp [NativeHeader.encoded, scaffold, indexFrame, checked,
    NativeHeader.restrict] <;> (try split_ifs) <;>
    (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact sizes _ | omega

theorem tagCode_ticks (s : Store) : tagCode.ticks s ≤ 4 := by
  cases head : (s 2).head? <;> simp [tagCode, Local.ticks, Local.push, Local.pop, head]

theorem setup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (setup (O := O)).cost s ≤ 50 * (budget + 1) := by
  let first := (Routine.clearMany (O := O) [5, 7, 8, 9, 11, 12, 13, 14, 15]).eval s
  let second := (Local.push 8 .one).eval first
  let third := tagCode.eval second
  have clearing := Routine.clearMany_cost (O := O) [5, 7, 8, 9, 11, 12, 13, 14, 15] s budget
    (by intro j _; exact sizes j)
  simp only [List.length_cons, List.length_nil] at clearing
  have tagging := tagCode_ticks second
  have clockCost : (NativeHeader.clockSetup (O := O)).cost third = 14 * (s 4).length + 3 := by
    cases head : (s 2).head? <;>
      simp [NativeHeader.clockSetup, Routine.assign_cost, third, second, first,
        Routine.clearMany_eval, tagCode, Local.eval, Local.push, Local.pop, Action.apply, head]
  change (Routine.clearMany [5, 7, 8, 9, 11, 12, 13, 14, 15]).cost s + 1 +
    (1 + 1 + (tagCode.ticks second + 1 + (NativeHeader.clockSetup (O := O)).cost third)) ≤ _
  rw [clockCost]
  have capacity := sizes 4
  omega

theorem indexSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((indexSetup (O := O)).eval s j).length ≤ budget + 1 := by
  intro j
  by_cases changed : j = 15 <;> by_cases scratch : j = 9 <;>
    simp [indexSetup, Routine.seq, Routine.assign_eval, Routine.ofLocal, Local.eval_push,
      changed, scratch] <;> exact (sizes _).trans (by omega)

theorem indexRoutine_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (indexRoutine (O := O)).cost s ≤ 200 * (budget + 1) := by
  have second := RationalSelection.Compare.routine_cost (O := O) indexSlots .one
    ((indexSetup (O := O)).eval s) (budget + 1) (indexSetup_bound s budget sizes)
  have h₉ := sizes 9
  have h₁₀ := sizes 10
  have h₁₅ := sizes 15
  have first : (indexSetup (O := O)).cost s ≤ 20 * budget + 5 := by
    simp only [indexSetup, Routine.seq, Routine.assign_cost, Routine.ofLocal, Local.push, Local.ticks]
    omega
  change (indexSetup (O := O)).cost s + 1 +
    (RationalSelection.Compare.routine (O := O) indexSlots .one).cost ((indexSetup (O := O)).eval s) ≤ _
  omega

/-- A genuine linear primitive-command bound for one padded literal parse.
The finite tag check contributes only its fixed syntax-tree constant. -/
theorem literalRoutine_cost {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol)
    (enabled : Bool) (budget : ℕ) (sizes : ∀ j, (base j).length ≤ budget)
    (cap : capacity ≤ budget) (count : active ≤ budget) (wordSize : word.length ≤ budget) :
    (literalRoutine (O := O)).cost (inputStore base capacity active word enabled) ≤
      (1000 + tagCheck.bound) * (budget + 1) := by
  let start := inputStore base capacity active word enabled
  let prepared := (setup (O := O)).eval start
  let scanned := (NativeHeader.scanRoutine (O := O)).eval prepared
  have tagLength : word.head?.toList.length ≤ 1 := by cases word <;> simp
  have initial : ∀ j, (start j).length ≤ budget + 1 := by
    intro j
    by_cases wordReg : j = 2 <;> by_cases capReg : j = 4 <;>
      by_cases countReg : j = 10 <;> by_cases validReg : j = 6 <;>
        simp [start, inputStore, wordReg, capReg, countReg, validReg] <;>
        (try split_ifs) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
        first | exact (sizes _).trans (by omega) | omega
  have first := setup_cost (O := O) start (budget + 1) initial
  have scanning := NativeHeader.scanRoutine_cost (O := O) prepared
  have clock : (prepared 7).length = capacity := by simp [prepared, start, setup_eval, NativeHeader.encoded]
  rw [clock] at scanning
  have scannedBound : ∀ j, (scanned j).length ≤ budget + 1 := by
    intro j
    rw [show scanned = NativeHeader.encoded (scaffold base capacity active word)
        (NativeHeader.restrict (fieldState capacity word) enabled) [] by exact scan_eval _ _ _ _ _]
    have number := field_count capacity word
    have residual := field_length capacity word
    fin_cases j <;> simp [NativeHeader.encoded, scaffold, NativeHeader.restrict] <;>
      (try split_ifs) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
      first | exact (sizes _).trans (by omega) | omega
  have comparing := indexRoutine_cost (O := O) scanned (budget + 1) scannedBound
  have tagging := tagCheck.ticks_le ((indexRoutine (O := O)).eval scanned)
  change (setup (O := O)).cost start + 1 +
    ((NativeHeader.scanRoutine (O := O)).cost prepared + 1 +
    ((indexRoutine (O := O)).cost scanned + 1 + tagCheck.ticks ((indexRoutine (O := O)).eval scanned))) ≤ _
  nlinarith

end ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral
