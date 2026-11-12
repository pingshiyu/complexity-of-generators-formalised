import ComplexityOfGenerators.Simulation.WordStack.ComparisonBounds
import ComplexityOfGenerators.Simulation.WordStack.TakeWord
import ComplexityOfGenerators.Simulation.WordStack.InsertAt
import ComplexityOfGenerators.Simulation.WordStack.OneHot

/-! Compositional bounds for actual finite routines. These rules combine
proved evaluators and costs; they do not postulate a machine implementation. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

variable {S O : Type} {k : ℕ}

def ResourceBound (routine : Routine S O k) (input output ticks : ℕ) : Prop :=
  ∀ s, StoreBound s input → StoreBound (routine.eval s) output ∧ routine.cost s≤ticks

namespace ResourceBound

theorem weaken {routine : Routine S O k} {input output ticks smaller larger more : ℕ}
    (bound : ResourceBound routine input output ticks)
    (starts : smaller ≤ input) (finishes : output≤larger) (costs : ticks≤more) :
    ResourceBound routine smaller larger more := by
  intro s sizes
  have result := bound s (sizes.mono starts)
  exact ⟨result.1.mono finishes,result.2.trans costs⟩

theorem seq {first second : Routine S O k} {input middle output left right : ℕ}
    (a : ResourceBound first input middle left) (b : ResourceBound second middle output right) :
    ResourceBound (first.seq second) input output (left+1+right) := by
  intro s sizes
  have firstBound := a s sizes
  have secondBound := b (first.eval s) firstBound.1
  exact ⟨secondBound.1,by change first.cost s+1+second.cost (first.eval s)≤_; omega⟩

theorem branch (j : Fin k) (next : Option S → Routine S O k) (input output ticks : ℕ)
    (all : ∀ value,ResourceBound (next value) input output ticks) :
    ResourceBound (Routine.branch j next) input output (1+ticks) := by
  intro s sizes
  have result := all (s j).head? s sizes
  exact ⟨result.1,by change 1+(next (s j).head?).cost s≤_; omega⟩

theorem skip (budget : ℕ) : ResourceBound (Routine.skip (S := S) (O := O) (k := k)) budget budget 0 := by
  intro s sizes
  exact ⟨sizes,by simp [Routine.skip,Routine.ofLocal,Local.ticks]⟩

theorem clear (j : Fin k) (budget : ℕ) : ResourceBound (Routine.clear (S := S) (O := O) j) budget budget (3*budget) := by
  intro s sizes
  exact ⟨sizes.clear j,Nat.mul_le_mul_left 3 (sizes j)⟩

theorem clearMany (registers : List (Fin k)) (budget : ℕ) :
    ResourceBound (Routine.clearMany (S := S) (O := O) registers) budget budget
      (registers.length*(3*budget+1)) := by
  intro s sizes
  exact ⟨sizes.clearMany registers,Routine.clearMany_cost registers s budget (fun j _ => sizes j)⟩

theorem assign (source target scratch : Fin k) (a : source≠target) (b : source≠scratch) (c : target≠scratch)
    (map : S→S) (budget : ℕ) :
    ResourceBound (Routine.assign (O := O) source target scratch a b c map) budget budget (20*(budget+1)) := by
  intro s sizes
  constructor
  · exact sizes.assign source target scratch a b c map
  · have x := sizes source
    have y := sizes target
    have z := sizes scratch
    rw [Routine.assign_cost]
    omega

theorem push (j : Fin k) (letter : S) (budget : ℕ) :
    ResourceBound (Routine.ofLocal (O := O) (Local.push j letter)) budget (budget+1) 1 := by
  intro s sizes
  constructor
  · change StoreBound (Function.update s j (letter::s j)) (budget+1)
    exact (sizes.mono (by omega)).update j _ (by simp only [List.length_cons]; exact Nat.add_le_add_right (sizes j) 1)
  · rfl

theorem strictCompare (slots : RationalSelection.Compare.Layout k) (unit : S) (budget : ℕ)
    (positive : 1≤budget) :
    ResourceBound (RationalSelection.Compare.routine (O := O) slots unit) budget budget (80*(budget+1)) := by
  intro s sizes
  exact ⟨sizes.strictCompare slots unit positive,RationalSelection.Compare.routine_cost slots unit s budget sizes⟩

theorem lengthTest (slots : LengthTest.Layout k) (unit : S) (budget : ℕ) (positive : 1≤budget) :
    ResourceBound (LengthTest.routine (O := O) slots unit) budget budget (80*(budget+1)) := by
  intro s sizes
  exact ⟨sizes.lengthTest slots unit positive,LengthTest.routine_cost slots unit s budget sizes⟩

theorem rename {l : ℕ} {routine : Routine S O k} {input output ticks : ℕ}
    (bound : ResourceBound routine input output ticks) (slots : Fin k↪Fin l) (grows : input≤output) :
    ResourceBound (routine.rename slots) input output ticks := by
  intro s sizes
  have source := bound (s ∘ slots) (fun j => sizes (slots j))
  constructor
  · intro j
    by_cases owned : ∃ i,slots i=j
    · obtain ⟨i,rfl⟩ := owned
      rw [Routine.rename_eval_here]
      exact source.1 i
    · rw [Routine.rename_eval_frame]
      · exact (sizes j).trans grows
      · intro i equal
        exact owned ⟨i,equal.symm⟩
  · simpa only [Routine.rename_cost] using source.2

theorem transfer (source target : Fin k) (different : source≠target) (map : S→S) (budget : ℕ) :
    ResourceBound (Routine.transfer (O := O) source target different map) budget (2*budget) (6*budget) := by
  intro s sizes
  constructor
  · rw [Routine.transfer]
    apply ((sizes.mono (by omega)).clear source).update target
    have a := sizes source
    have b := sizes target
    simp only [List.length_append,List.length_map,List.length_reverse]
    omega
  · exact Nat.mul_le_mul_left 6 (sizes source)

theorem takeWord (slots : TakeWord.Layout k) (budget : ℕ) :
    ResourceBound (TakeWord.routine (S := S) (O := O) slots) budget budget (100*(budget+1)) := by
  intro s sizes
  exact ⟨TakeWord.routine_bound slots s budget sizes,TakeWord.routine_cost slots s budget sizes⟩

theorem insertAt (slots : InsertAt.Layout k) (unit letter : S) (budget : ℕ) :
    ResourceBound (InsertAt.routine (O := O) slots unit letter) budget (budget+1) (60*(budget+2)) := by
  intro s sizes
  exact ⟨InsertAt.routine_bound slots unit letter s budget sizes,InsertAt.routine_cost slots unit letter s budget sizes⟩

theorem dropAt (slots : DropAt.Layout k) (unit : S) (budget : ℕ) :
    ResourceBound (DropAt.routine (O := O) slots unit) budget budget (60*(budget+1)) := by
  intro s sizes
  exact ⟨DropAt.routine_bound slots unit s budget sizes,DropAt.routine_cost slots unit s budget sizes⟩

theorem oneHot (slots : OneHot.Layout k) (encode : Bool→S) (budget : ℕ) :
    ResourceBound (OneHot.routine (O := O) slots encode) budget (2*budget+1) (14*budget+3) := by
  intro s sizes
  constructor
  · apply OneHot.routine_bound slots encode s (2*budget+1) (sizes.mono (by omega)) (by omega)
    have a := sizes (slots 0)
    have b := sizes (slots 3)
    omega
  · exact (OneHot.routine_cost slots encode s).trans (by have a := sizes (slots 0); have b := sizes (slots 2); omega)

end ResourceBound
end ComplexityOfGenerators.Simulation.WordStack.Routine
