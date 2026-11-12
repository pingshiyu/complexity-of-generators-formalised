import ComplexityOfGenerators.Examples.SATNative.HeaderRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader

open Simulation.WordStack

theorem step_word (state : ScanState) : (step state).word = state.word.tail := by
  cases value : state.word with
  | nil => simp [step, value]
  | cons head rest => cases head <;> simp [step, value]

theorem step_count (state : ScanState) : (step state).count ≤ state.count + 1 := by
  cases value : state.word with
  | nil => simp [step, value]
  | cons head rest =>
    cases head <;> simp [step, value]
    split <;> omega

theorem iterate_count (state : ScanState) (count : ℕ) :
    (step^[count] state).count ≤ state.count + count := by
  induction count generalizing state with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply]
    have bound := ih (step state)
    have first := step_count state
    omega

theorem iterate_word (state : ScanState) (count : ℕ) :
    (step^[count] state).word = state.word.drop count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, ih, step_word, List.drop_tail]

theorem separator_count (state : ScanState) : (separator state).count = state.count := by
  unfold separator
  split <;> rfl

theorem separator_word_length (state : ScanState) : (separator state).word.length ≤ state.word.length := by
  unfold separator
  split <;> simp [List.length_tail]

theorem parsedState_bounds (word : List Symbol) :
    (parsedState word).count ≤ (readOnes word).1 ∧ (parsedState word).word.length ≤ word.length := by
  have cap := readOnes_lengths word
  let first := separator ⟨(readOnes word).2, 0, true, true⟩
  have counter := iterate_count first (readOnes word).1
  have firstCount : first.count = 0 := separator_count _
  have sourceSize := separator_word_length ⟨(readOnes word).2, 0, true, true⟩
  have lastSize := separator_word_length (step^[(readOnes word).1] first)
  constructor
  · change (separator (step^[(readOnes word).1] first)).count ≤ _
    rw [separator_count]
    omega
  · change (separator (step^[(readOnes word).1] first)).word.length ≤ word.length
    rw [iterate_word] at lastSize
    simp only [List.length_drop] at lastSize
    change first.word.length ≤ (readOnes word).2.length at sourceSize
    omega

theorem separatorCode_ticks (s : Store) : separatorCode.ticks s ≤ 2 := by
  simp only [separatorCode, Local.ticks]
  split <;> simp [Local.pop, Local.ticks]

theorem setup_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (setup (O := O)).cost s ≤ 18 * budget + 10 := by
  have clearing := Routine.clearMany_cost (O := O) [4, 5, 6, 7, 8, 9] s budget (by intro j _; exact sizes j)
  simp only [List.length_cons, List.length_nil] at clearing
  simp only [setup, Routine.seq, Routine.ofLocal, Local.ticks, Local.push]
  omega

theorem extract_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (extract (O := O)).cost s ≤ 24 * budget + 11 := by
  have first := setup_cost (O := O) s budget sizes
  have prefixLength : ((s 2).takeWhile keepOne).length ≤ (s 2).length := by
    have lengths := readOnes_lengths (s 2)
    rw [readOnes_parts] at lengths
    omega
  have source := sizes 2
  change (setup (O := O)).cost s + 1 +
    (Routine.transferWhile (O := O) 2 4 (by decide) keepOne (fun _ => .one)).cost ((setup (O := O)).eval s) ≤ _
  have saved : (setup (O := O)).eval s 2 = s 2 := by
    simp [setup, Routine.seq, Routine.ofLocal, Routine.clearMany_eval]
  change (setup (O := O)).cost s + 1 + 6 * (((setup (O := O)).eval s 2).takeWhile keepOne).length ≤ _
  rw [saved]
  omega

theorem headerRoutine_cost {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (headerRoutine (O := O)).cost s ≤ 50 * (budget + 1) := by
  let capacity := (readOnes (s 2)).1
  let rest := (readOnes (s 2)).2
  let frame := scaffold capacity s
  let initial : ScanState := ⟨rest, 0, true, true⟩
  let first := separator initial
  have setupBound := extract_cost (O := O) s budget sizes
  have firstSep := separatorCode_ticks (encoded frame initial [])
  have clockCost : (clockSetup (O := O)).cost (encoded frame first []) = 14 * capacity + 3 := by
    simp [clockSetup, Routine.assign_cost, frame, scaffold, encoded]
  have scanBound : (scanRoutine (O := O)).cost (encoded frame first (List.replicate capacity .one)) ≤ 10 * capacity := by
    have cost := scanRoutine_cost (O := O) (encoded frame first (List.replicate capacity .one))
    simpa only [encoded, Function.update_self, List.length_replicate] using cost
  have lastSep := separatorCode_ticks (encoded frame (step^[capacity] first) [])
  have capacityBound : capacity ≤ budget := by
    have source := sizes 2
    have header := readOnes_lengths (s 2)
    omega
  simp only [headerRoutine, Routine.seq, Routine.ofLocal, extract_eval,
    separatorCode_eval, clockSetup_eval, scanRoutine_eval]
  change (extract (O := O)).cost s + 1 +
    (separatorCode.ticks (encoded frame initial []) + 1 +
    ((clockSetup (O := O)).cost (encoded frame first []) + 1 +
    ((scanRoutine (O := O)).cost (encoded frame first (List.replicate capacity .one)) + 1 +
      separatorCode.ticks (encoded frame (step^[capacity] first) [])))) ≤ _
  rw [clockCost]
  omega

theorem headerRoutine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((headerRoutine (O := O)).eval s j).length ≤ budget + 1 := by
  have parsed := parsedState_bounds (s 2)
  have source := sizes 2
  have capacity := readOnes_lengths (s 2)
  intro j
  rw [headerRoutine_eval]
  fin_cases j <;> simp [encoded, scaffold] <;> (try split_ifs) <;>
    (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact (sizes _).trans (by omega) | omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeHeader
