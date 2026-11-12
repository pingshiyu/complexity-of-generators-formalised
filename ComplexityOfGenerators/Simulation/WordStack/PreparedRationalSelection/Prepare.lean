import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.DrainPair
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Input

/-! Canonical preparation of the rational selector in an ambient 35-register
store. The source words and target remain outside its private register bank. -/

namespace ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection

set_option backward.isDefEq.respectTransparency false

variable {S O : Type}

abbrev Store (S : Type) := Local.Store S 35

abbrev Safe (register : Fin 35) : Prop := 16 ≤ register.val ∧ register ≠ 33

def bank : List (Fin 35) := List.ofFn (fun j : Fin 16 => ⟨j.val, by omega⟩)

theorem mem_bank (j : Fin 35) : j ∈ bank ↔ j.val < 16 := by
  simp only [bank, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro small
    exact ⟨⟨j.val, small⟩, by apply Fin.ext; rfl⟩

def difference (encode : Bool → S) (high subtractor destination : Fin 35)
    (highSafe : Safe high) (subtractorSafe : Safe subtractor) (small : destination.val < 2) : Routine S O 35 :=
  (Routine.assign high destination 33 (by intro h; have := highSafe.1; subst high; omega) highSafe.2
    (by intro h; subst destination; norm_num at small) (fun _ => encode true)).seq
  ((Routine.assign subtractor 3 33 (by intro h; have := subtractorSafe.1; subst subtractor; omega) subtractorSafe.2
    (by decide) (fun _ => encode true)).seq
  ((Routine.clear 4).seq (DrainPair.routine 3 destination 4 (by intro h; subst destination; norm_num at small) (by decide))))

theorem difference_eval (encode : Bool → S) (high subtractor destination : Fin 35)
    (highSafe : Safe high) (subtractorSafe : Safe subtractor) (small : destination.val < 2) (s : Store S) :
    (difference (O := O) encode high subtractor destination highSafe subtractorSafe small).eval s =
      Function.update (Function.update (Function.update (Function.update s 33 [])
        destination (List.replicate ((s high).length - (s subtractor).length) (encode true))) 3 []) 4 [] := by
  have highDst : high ≠ destination := by intro h; have := highSafe.1; subst high; omega
  have subDst : subtractor ≠ destination := by intro h; have := subtractorSafe.1; subst subtractor; omega
  have dstThree : destination ≠ 3 := by intro h; subst destination; norm_num at small
  have dstFour : destination ≠ 4 := by intro h; subst destination; norm_num at small
  have dstScratch : destination ≠ 33 := by intro h; subst destination; norm_num at small
  have subScratch := subtractorSafe.2
  have subThree : subtractor ≠ 3 := by intro h; have := subtractorSafe.1; subst subtractor; omega
  simp only [difference, Routine.seq, Routine.assign_eval, Routine.clear,
    DrainPair.routine_eval 3 destination 4 dstThree.symm (by decide) dstFour]
  funext j
  by_cases jf : j = 4 <;> by_cases jt : j = 3 <;> by_cases jd : j = destination <;> by_cases js : j = 33 <;>
    simp_all [List.map_const', List.drop_replicate]

/-- The prefix owns exactly the selector bank and the shared copy scratch. -/
def prepare (encode : Bool → S) (decode : S → Bool) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) : Routine S O 35 :=
  (Routine.clearMany bank).seq
  ((difference encode high low 0 highSafe lowSafe (by decide)).seq
  ((difference encode high 22 1 highSafe (by decide) (by decide)).seq
  (Routine.assign 17 2 33 (by decide) (by decide) (by decide) (fun symbol => encode (decode symbol)))))

def input (decode : S → Bool) (low high : Fin 35) (s : Store S) : RationalSelection.Store :=
  RationalSelection.inputStore ((s high).length - (s low).length)
    ((s high).length - (s 22).length) ((s 17).map decode)

def preparedStore (encode : Bool → S) (decode : S → Bool) (low high : Fin 35) (s : Store S) : Store S :=
  fun j => if small : j.val < 16 then (input decode low high s ⟨j.val, small⟩).map encode
    else if j = 33 then [] else s j

theorem prepare_eval (encode : Bool → S) (decode : S → Bool) (low high : Fin 35)
    (lowSafe : Safe low) (highSafe : Safe high) (s : Store S) :
    (prepare (O := O) encode decode low high lowSafe highSafe).eval s =
      preparedStore encode decode low high s := by
  have lowOut : ¬ low.val < 16 := by have := lowSafe.1; omega
  have highOut : ¬ high.val < 16 := by have := highSafe.1; omega
  have highZero : high ≠ 0 := by have := highSafe.1; intro h; subst high; omega
  have highThree : high ≠ 3 := by have := highSafe.1; intro h; subst high; omega
  have highFour : high ≠ 4 := by have := highSafe.1; intro h; subst high; omega
  have highScratch := highSafe.2
  simp only [prepare, Routine.seq, Routine.clearMany_eval, difference_eval, Routine.assign_eval]
  funext j
  simp only [preparedStore, input, RationalSelection.inputStore]
  by_cases zero : j.val = 0 <;> by_cases one : j.val = 1 <;> by_cases two : j.val = 2 <;>
    by_cases three : j.val = 3 <;> by_cases four : j.val = 4 <;> by_cases scratch : j.val = 33 <;>
    simp [Function.update_apply, mem_bank, List.map_map, List.map_replicate, Function.comp_def,
      zero, one, two, three, four, scratch, lowOut, highOut, highZero, highThree, highFour, highScratch, Fin.ext_iff]

end ComplexityOfGenerators.Simulation.WordStack.PreparedRationalSelection
