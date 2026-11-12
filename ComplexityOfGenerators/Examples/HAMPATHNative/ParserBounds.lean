import ComplexityOfGenerators.Examples.HAMPATHNative.Parser
import ComplexityOfGenerators.Examples.HAMPATHNative.HeaderBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.RowBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem headerState_row (word : List Symbol) : (headerState word).row = 0 := by
  dsimp only [headerState]
  split <;> rfl

theorem startPrepare_cost {O : Type} (base : Store) (size : ℕ) (state : RowState)
    (budget : ℕ) (seen : (base 12).length ≤ budget) (start : (base 13).length ≤ budget) :
    (startPrepare (O := O)).cost (rowEncoded base size state []) ≤ 6 * budget + 14 * size + 10 := by
  have clearing := Routine.clearMany_cost (O := O) ([12, 13] : List (Fin 32))
    (rowEncoded base size state []) budget (by
      intro j member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · simpa [rowEncoded, cellEncoded] using seen
      · simpa [rowEncoded, cellEncoded] using start)
  have assigning : (Routine.assign (O := O) 4 11 9 (by decide) (by decide) (by decide) id).cost
      ((Routine.clearMany (O := O) [12, 13]).eval (rowEncoded base size state [])) = 14 * size + 3 := by
    simp [Routine.assign_cost, Routine.clearMany_eval, rowEncoded, cellEncoded]
  simp only [List.length_cons, List.length_nil] at clearing
  change (Routine.clearMany (O := O) [12, 13]).cost (rowEncoded base size state []) + 1 + _ ≤ _
  rw [assigning]
  omega

/-- The parser scans k² matrix symbols and k start symbols. Missing or
malformed input still follows these finite clocks, so this is a total bound. -/
theorem parser_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (parser (O := O)).cost s ≤ 500 * (budget + 1)^2 := by
  let base := headerBase s
  let size := headerSize (s 2)
  let initial := headerState (s 2)
  let scanned := (rowStep size)^[size] initial
  let final := separator scanned
  let ready := startEncoded (rowEncoded base size final []) ⟨final.word, 0, false, final.valid⟩
    (List.replicate size (.bit true))
  have headerCost := header_cost (O := O) s budget sizes
  have rowCost := rows_cost (O := O) base size initial size
  have rowZero : initial.row = 0 := headerState_row _
  rw [rowZero] at rowCost
  have separatorCost := separatorCode_ticks (rowEncoded base size scanned [])
  have setupCost := startPrepare_cost (O := O) base size final 0
    (by simp [base, headerBase]) (by simp [base, headerBase])
  have startCost : (starts (O := O)).cost ready ≤ 10 * size := by
    simpa [ready, startEncoded] using starts_cost (O := O) ready
  have sizeBound := (headerSize_le (s 2)).trans (sizes 2)
  change size ≤ budget at sizeBound
  simp only [parser, Routine.seq, header_eval, rows_eval, Routine.ofLocal, separatorCode_eval, startPrepare_eval]
  change (header (O := O)).cost s + 1 +
    ((rows (O := O)).cost (rowEncoded base size initial (List.replicate size (.bit true))) + 1 +
      (separatorCode.ticks (rowEncoded base size scanned []) + 1 +
        ((startPrepare (O := O)).cost (rowEncoded base size final []) + 1 + (starts (O := O)).cost ready))) ≤ _
  nlinarith only [headerCost, rowCost, separatorCost, setupCost, startCost, sizeBound,
    Nat.mul_self_le_mul_self sizeBound]

end ComplexityOfGenerators.Examples.HAMPATH.Native
