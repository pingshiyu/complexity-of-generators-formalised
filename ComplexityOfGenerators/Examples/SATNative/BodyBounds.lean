import ComplexityOfGenerators.Examples.SATNative.BodyRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeBody

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def stackBound (budget : ℕ) (s : Store) : Prop := ∀ j, (s j).length ≤ budget

theorem renamed_literal_bound {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound budget (((NativeLiteral.literalRoutine (O := O)).rename subslots).eval s) := by
  have wordSize : state.word.length ≤ budget := by rw [← represented.1]; exact sizes 2
  have localBound := NativeLiteral.literalRoutine_bound_same (O := O) (s ∘ subslots) capacity active
    state.word state.valid budget positive (by intro j; exact sizes (subslots j)) cap count wordSize
  rw [literal_input_eq capacity active state s represented] at localBound
  intro j
  by_cases member : ∃ i, subslots i = j
  · obtain ⟨i, rfl⟩ := member
    rw [Routine.rename_eval_here]
    exact localBound i
  · rw [Routine.rename_eval_frame _ _ _ _ (by intro i equal; exact member ⟨i, equal.symm⟩)]
    exact sizes j

theorem outside_bound (capacity active : ℕ) (state : State) (s : Store) (tag : Symbol)
    (represented : Represents capacity active state s) (outside : state.inside = false)
    (budget : ℕ) (positive : 0 < budget) (sizes : stackBound budget s) :
    stackBound budget ((outsideCode tag).eval s) := by
  intro j
  have empty : s 17 = [] := by simpa [outside] using represented.2.2.2.2.1
  by_cases opening : tag = .openClause <;>
    by_cases wordReg : j = 2 <;> by_cases seenReg : j = 18 <;>
      by_cases insideReg : j = 17 <;> by_cases validReg : j = 6 <;>
        simp [outsideCode, Local.eval, Local.pop, Local.push, Action.apply, opening,
          wordReg, seenReg, insideReg, validReg, empty, List.length_tail] <;>
          first | exact sizes _ | have := sizes 2; have := sizes 6; have := sizes 18; omega

theorem close_bound (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget (closeCode.eval s) := by
  intro j
  cases seen : s 18 with
  | nil =>
    by_cases wordReg : j = 2 <;> by_cases seenReg : j = 18 <;>
      by_cases insideReg : j = 17 <;> by_cases validReg : j = 6 <;>
        simp [closeCode, Local.eval, Local.pop, Action.apply, seen,
          wordReg, seenReg, insideReg, validReg, List.length_tail] <;>
          first | exact sizes _ | have := sizes 2; have := sizes 6; have := sizes 17; omega
  | cons mark tail =>
    by_cases wordReg : j = 2 <;> by_cases seenReg : j = 18 <;> by_cases insideReg : j = 17 <;>
      simp [closeCode, Local.eval, Local.pop, Action.apply, seen,
        wordReg, seenReg, insideReg, List.length_tail] <;>
        first | exact sizes _ | have := sizes 2; have := sizes 17; have := sizes 18; simp only [seen, List.length_cons] at *; omega

theorem bodyStep_bound {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound budget ((bodyStep (O := O)).eval s) := by
  have saved := represented
  rcases saved with ⟨wordReg, _, _, _, insideReg, seenReg⟩
  cases word : state.word with
  | nil => simpa [bodyStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval] using sizes
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, Routine.ofLocal] using
        outside_bound capacity active state s tag represented inside budget positive sizes
    | true =>
      by_cases close : tag = .closeClause
      · subst tag
        simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, Routine.ofLocal] using close_bound s budget sizes
      · have before := renamed_literal_bound (O := O) capacity active state s represented budget positive sizes cap count
        have seen := (literal_represents (O := O) capacity active state s represented).2.2.2.2.2
        intro j
        by_cases changed : j = 18
        · subst j
          cases mark : state.nonempty <;>
            simp [bodyStep, Routine.branch, wordReg, word, insideReg, inside, close,
              Routine.seq, Routine.ofLocal, Local.eval_write, seen, seenReg, mark] <;> omega
        · simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, close,
            Routine.seq, Routine.ofLocal, Local.eval_write, changed] using before j

theorem outside_ticks (tag : Symbol) (s : Store) : (outsideCode tag).ticks s ≤ 5 := by
  by_cases opening : tag = .openClause <;> simp [outsideCode, Local.ticks, Local.pop, Local.push, opening]

theorem close_ticks (s : Store) : closeCode.ticks s ≤ 9 := by
  cases seen : s 18 <;> simp [closeCode, Local.ticks, Local.pop, Local.eval, Action.apply, seen]

noncomputable def stepConstant : ℕ := 1100 + NativeLiteral.tagCheck.bound

theorem bodyStep_cost {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    (bodyStep (O := O)).cost s ≤ stepConstant * (budget + 1) := by
  have saved := represented
  rcases saved with ⟨wordReg, _, _, _, insideReg, _⟩
  cases word : state.word with
  | nil =>
    simp only [bodyStep, Routine.branch, wordReg, word, List.head?_nil, Routine.skip, Routine.ofLocal, Local.ticks]
    unfold stepConstant
    nlinarith
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      have ticks := outside_ticks tag s
      simp only [bodyStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
        Bool.false_eq_true, ite_false, List.head?_nil, Option.isSome_none, Routine.ofLocal]
      unfold stepConstant
      nlinarith
    | true =>
      by_cases close : tag = .closeClause
      · have ticks := close_ticks s
        simp only [bodyStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, Routine.ofLocal]
        unfold stepConstant
        nlinarith
      · have wordSize : state.word.length ≤ budget := by rw [← wordReg]; exact sizes 2
        have ticks := NativeLiteral.literalRoutine_cost (O := O) (s ∘ subslots) capacity active state.word
          state.valid budget (by intro j; exact sizes (subslots j)) cap (by omega) wordSize
        rw [literal_input_eq capacity active state s represented] at ticks
        simp only [bodyStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, ite_false, Routine.seq, Routine.rename_cost,
          Routine.ofLocal, Local.write, Local.ticks, Local.pop, Local.push]
        unfold stepConstant
        nlinarith

end ComplexityOfGenerators.Examples.PaddedCNF.NativeBody
