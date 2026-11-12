import ComplexityOfGenerators.Examples.HAMPATHNative.Header

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem separatorCode_ticks (s : Store) : separatorCode.ticks s ≤ 2 := by
  simp only [separatorCode, Local.ticks]
  split <;> simp [Local.pop, Local.ticks]

theorem headerSetup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (headerSetup (O := O)).cost s ≤ 33 * budget + 24 := by
  have clearing := Routine.clearMany_cost (O := O) [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]
    s budget (by intro j _; exact sizes j)
  simp only [List.length_cons, List.length_nil] at clearing
  simp only [headerSetup, Routine.seq, Routine.ofLocal, Local.ticks, Local.push]
  omega

theorem headerExtract_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (headerExtract (O := O)).cost s ≤ 39 * budget + 25 := by
  have first := headerSetup_cost (O := O) s budget sizes
  have headerLength := headerSize_le (s 2)
  have source := sizes 2
  have saved : (headerSetup (O := O)).eval s 2 = s 2 := by
    simp [headerSetup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal]
  change (headerSetup (O := O)).cost s + 1 +
    6 * ((((headerSetup (O := O)).eval s) 2).takeWhile keepHeader).length ≤ _
  rw [saved]
  change headerSize (s 2) ≤ (s 2).length at headerLength
  change (headerSetup (O := O)).cost s + 1 + 6 * headerSize (s 2) ≤ _
  omega

theorem header_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (header (O := O)).cost s ≤ 60 * (budget + 1) := by
  let initial : RowState := ⟨(s 2).dropWhile keepHeader, 0, true⟩
  let base := headerBase s
  let size := headerSize (s 2)
  have extractCost := headerExtract_cost (O := O) s budget sizes
  have separatorCost := separatorCode_ticks (rowEncoded base size initial [])
  have clockCost : (headerClock (O := O)).cost (rowEncoded base size (separator initial) []) = 14 * size + 3 := by
    simp [headerClock, Routine.assign_cost, rowEncoded, cellEncoded]
  have sizeBound := (headerSize_le (s 2)).trans (sizes 2)
  unfold header
  change (headerExtract (O := O)).cost s + 1 +
    (separatorCode.ticks ((headerExtract (O := O)).eval s) + 1 +
      (headerClock (O := O)).cost (separatorCode.eval ((headerExtract (O := O)).eval s))) ≤ _
  rw [show (headerExtract (O := O)).eval s = rowEncoded base size initial [] from headerExtract_eval s,
    separatorCode_eval, clockCost]
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native
