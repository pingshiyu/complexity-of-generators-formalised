import ComplexityOfGenerators.Examples.SATNative.InverseNative.Choices

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

set_option backward.isDefEq.respectTransparency false

/-- The finite mask algorithm used by the native inverse controller. -/
def value (n : ℕ) (target label : List Symbol) (bits : BitString) : Option (List Symbol) :=
  if target.length = n then
    match decode target with
    | none => none
    | some (capacity, active, formula) =>
        if label = [] then if active = 0 then some target else none
        else match labelValue label with
          | none => none
          | some bit => if active+1 ≤ capacity then
              if n ≤ bits.length then
                some ((formula.lift active bit (choiceRows formula (bits.take n))).encode capacity (active+1))
              else none
            else none
  else none

theorem occurrences_le_encoding {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) :
    formula.occurrences ≤ (formula.encode capacity active).length := by
  rw [Formula.encode_length bound formula valid]
  have product : formula.occurrences ≤ (capacity+1)*formula.occurrences := by
    simpa only [one_mul] using Nat.mul_le_mul_right formula.occurrences (show 1 ≤ capacity+1 by omega)
  omega

theorem value_bit {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (n : ℕ) (bit : Bool) (bits : BitString) :
    value n (formula.encode capacity active) [bitSymbol bit] bits =
      if (formula.encode capacity active).length = n ∧ active+1 ≤ capacity ∧ n ≤ bits.length then
        some ((formula.lift active bit (choiceRows formula (bits.take n))).encode capacity (active+1)) else none := by
  simp only [value, decode_encode bound formula valid, List.cons_ne_nil, ite_false, labelValue_bit]
  split_ifs <;> simp_all

theorem value_empty {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (n : ℕ) (bits : BitString) :
    value n (formula.encode capacity active) [] bits =
      if active = 0 ∧ (formula.encode capacity active).length = n then some (formula.encode capacity active) else none := by
  cases active with
  | zero => simp [value, decode_encode bound formula valid]
  | succ active => simp [value, decode_encode bound formula valid]

theorem value_bit_sound {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (bit : Bool) (bits : BitString) (word : List Symbol)
    (produces : value n (formula.encode capacity active) [bitSymbol bit] bits = some word) :
    word ∈ selfReduction.inverseFibre n (formula.encode capacity active) [bitSymbol bit] := by
  rw [value_bit bound formula valid] at produces
  split_ifs at produces with good
  obtain ⟨length, more, _⟩ := good
  rw [inverseFibre_bit bound formula valid satisfiable]
  exact ⟨more, length, choiceRows formula (bits.take n), (Option.some.inj produces).symm⟩

theorem value_bit_complete {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (bit : Bool) (word : List Symbol)
    (member : word ∈ selfReduction.inverseFibre n (formula.encode capacity active) [bitSymbol bit]) :
    ∃ bits : BitString, bits.length = n+1 ∧ value n (formula.encode capacity active) [bitSymbol bit] bits = some word := by
  rw [inverseFibre_bit bound formula valid satisfiable] at member
  obtain ⟨more, length, choices, rfl⟩ := member
  have enough : formula.occurrences ≤ n := (occurrences_le_encoding bound formula valid).trans length.le
  obtain ⟨mask, maskLength, same⟩ := lift_flat_block_complete active bit formula choices n enough
  refine ⟨mask ++ [false], by simp [maskLength], ?_⟩
  rw [value_bit bound formula valid]
  have available : n ≤ (mask ++ [false]).length := by simp [maskLength]
  rw [if_pos ⟨length, more, available⟩]
  have window : (mask ++ [false]).take n = mask := List.take_left' maskLength
  rw [window, same]

theorem invalid_label_output (word label : List Symbol) (nonempty : label ≠ []) (invalid : labelValue label = none) :
    wordReduce word label = [] := by
  cases decoded : decode word with
  | none => simp [wordReduce, decoded]
  | some triple =>
      rcases triple with ⟨capacity, active, formula⟩
      by_cases zero : active = 0 <;> simp [wordReduce, decoded, zero, nonempty, invalid]

theorem inverseFibre_invalid (n : ℕ) (target label : List Symbol) (targetNonempty : target ≠ [])
    (nonempty : label ≠ []) (invalid : labelValue label = none) :
    selfReduction.inverseFibre n target label = ∅ := by
  ext word
  constructor
  · rintro ⟨_, reduction, _⟩
    change wordReduce word label = target at reduction
    rw [invalid_label_output word label nonempty invalid] at reduction
    exact False.elim (targetNonempty reduction.symm)
  · intro empty; exact False.elim empty

theorem labelValue_some (label : List Symbol) (bit : Bool) (decoded : labelValue label = some bit) :
    label = [bitSymbol bit] := by
  cases label with
  | nil => simp [labelValue] at decoded
  | cons symbol rest =>
      cases rest with
      | nil => cases symbol <;> cases bit <;> simp [labelValue,bitSymbol] at decoded ⊢
      | cons next rest => cases symbol <;> simp [labelValue] at decoded

theorem value_invalid (n : ℕ) (target label : List Symbol) (bits : BitString)
    (nonempty : label ≠ []) (invalid : labelValue label = none) : value n target label bits = none := by
  by_cases size : target.length = n
  · simp only [value,size,ite_true]
    cases decoded : decode target with
    | none => rfl
    | some triple => rcases triple with ⟨capacity,active,formula⟩; simp [nonempty,invalid]
  · simp only [value,size,ite_false]

theorem value_empty_sound {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (bits : BitString) (word : List Symbol)
    (produces : value n (formula.encode capacity active) [] bits = some word) :
    word ∈ selfReduction.inverseFibre n (formula.encode capacity active) [] := by
  rw [value_empty bound formula valid] at produces
  split_ifs at produces with good
  rw [inverseFibre_empty bound formula valid satisfiable]
  exact ⟨good.1,good.2,(Option.some.inj produces).symm⟩

theorem value_empty_complete {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (word : List Symbol)
    (member : word ∈ selfReduction.inverseFibre n (formula.encode capacity active) []) :
    ∃ bits : BitString, bits.length = n+1 ∧ value n (formula.encode capacity active) [] bits = some word := by
  rw [inverseFibre_empty bound formula valid satisfiable] at member
  obtain ⟨zero,length,rfl⟩ := member
  refine ⟨List.replicate (n+1) false,by simp,?_⟩
  rw [value_empty bound formula valid,if_pos ⟨zero,length⟩]

theorem value_sound {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString) (word : List Symbol)
    (produces : value n (formula.encode capacity active) label bits = some word) :
    word ∈ selfReduction.inverseFibre n (formula.encode capacity active) label := by
  by_cases empty : label = []
  · subst label; exact value_empty_sound bound formula valid satisfiable n bits word produces
  · cases decoded : labelValue label with
    | none => rw [value_invalid n _ label bits empty decoded] at produces; cases produces
    | some bit =>
        have labelEq := labelValue_some label bit decoded
        subst label
        exact value_bit_sound bound formula valid satisfiable n bit bits word produces

theorem value_complete {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (word : List Symbol)
    (member : word ∈ selfReduction.inverseFibre n (formula.encode capacity active) label) :
    ∃ bits : BitString, bits.length = n+1 ∧ value n (formula.encode capacity active) label bits = some word := by
  by_cases empty : label = []
  · subst label; exact value_empty_complete bound formula valid satisfiable n word member
  · cases decoded : labelValue label with
    | none =>
        have nonempty : formula.encode capacity active ≠ [] := by
          intro absent
          have size := Formula.encode_length bound formula valid
          rw [absent,List.length_nil] at size
          omega
        rw [inverseFibre_invalid n _ label nonempty empty decoded] at member
        exact False.elim member
    | some bit =>
        have labelEq := labelValue_some label bit decoded
        subst label
        exact value_bit_complete bound formula valid satisfiable n bit word member

theorem value_full {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) (bits : BitString) (enough : n ≤ bits.length) :
    (value n (formula.encode capacity active) label bits).isSome ↔
      (selfReduction.inverseFibre n (formula.encode capacity active) label).Nonempty := by
  by_cases empty : label = []
  · subst label
    rw [value_empty bound formula valid,inverseFibre_empty bound formula valid satisfiable]
    have condition : ({word | active = 0 ∧ (formula.encode capacity active).length = n ∧
        word = formula.encode capacity active} : Set (List Symbol)).Nonempty ↔
        active = 0 ∧ (formula.encode capacity active).length = n :=
      ⟨fun ⟨_,zero,length,_⟩ => ⟨zero,length⟩,
        fun ⟨zero,length⟩ => ⟨_,zero,length,rfl⟩⟩
    rw [condition]
    by_cases good : active = 0 ∧ (formula.encode capacity active).length = n <;> simp [good]
  · cases decoded : labelValue label with
    | none =>
        have nonempty : formula.encode capacity active ≠ [] := by
          intro absent
          have size := Formula.encode_length bound formula valid
          rw [absent,List.length_nil] at size
          omega
        rw [value_invalid n _ label bits empty decoded,inverseFibre_invalid n _ label nonempty empty decoded]
        simp
    | some bit =>
        have labelEq := labelValue_some label bit decoded
        subst label
        rw [value_bit bound formula valid,inverseFibre_bit_nonempty bound formula valid satisfiable]
        by_cases good : (formula.encode capacity active).length = n ∧ active+1 ≤ capacity ∧ n ≤ bits.length
        · simp [good]
        · simp [good] <;> tauto

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
