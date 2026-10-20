import ComplexityOfGenerators.Simulation.LibraryTM.Alphabet.Program

/-! Copy a bounded unary letter code directly from finite-alphabet input. The
encoded input tape is charged, and no exponential output history is stored. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {n : ℕ} (M : Complexity.TM n) (bits : BitString)

def copying (position : ℕ) (front : BitString) (q : State (α := α) M) : Config (α := α) M :=
  ⟨q, position, 0, 0, 0, [], fun j => if j = 0 then front.length + 1 else 0,
    fun j => if j = 0 then image (Complexity.Tape.init (front.map Complexity.Γ.ofBool)) else fun _ => .blank⟩

theorem copy_bit (word : List α) (position : ℕ) (front : BitString) (q next : State (α := α) M)
    (bit : Bool) (input : Move) (selected : select M q = 0)
    (table : (bank M).instruction (decisionData word) (copying (α := α) M position front q) =
      .step next (Complexity.Γ.ofBool bit) .right input .stay .stay none) :
    (bank M).Steps (decisionData word) bits (copying (α := α) M position front q) 1
      (copying (α := α) M (input.onInput word.length position) (front ++ [bit]) next) := by
  have path := TapeBank.Steps.single (bank M) _ bits _ _ _ _ _ _ _ _ table
  convert path using 1
  apply BankConfiguration.ext
  all_goals simp [TapeBank.advance, copying, bank, selected, Move.onInt, Move.onInput, decisionData]
  · funext j; by_cases same : j = 0 <;> simp [same]
  · funext j
    by_cases same : j = 0
    · subst j; simpa using (image_init_append front bit).symm
    · simp [same]

theorem emit_run (word : List α) (position : ℕ) (front : BitString) (k : ℕ)
    (room : k < Fintype.card α + 1) (pos : position < word.length) :
    (bank M).Steps (decisionData word) bits (copying (α := α) M position front (.emit ⟨k, room⟩)) (k + 1)
      (copying (α := α) M (position + 1) (front ++ List.replicate k false ++ [true]) .load) := by
  induction k generalizing front with
  | zero =>
    simpa [Move.onInput, Nat.min_eq_left (by omega : position + 1 ≤ word.length)] using
      copy_bit M bits word position front (.emit ⟨0, room⟩) .load true .right rfl
        (by simp [TapeBank.instruction, bank, transition, copying, Complexity.Γ.ofBool])
  | succ k ih =>
    have first := copy_bit M bits word position front (.emit ⟨k + 1, room⟩)
      (.emit ⟨k, by omega⟩) false .stay rfl
      (by simp [TapeBank.instruction, bank, transition, copying, Complexity.Γ.ofBool])
    simp only [Move.onInput, Nat.min_eq_left pos.le] at first
    have tail := ih (front ++ [false]) (by omega)
    simpa [List.replicate_succ, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      first.trans (bank M) tail

theorem load_entry (front rest : List α) (a : α) :
    (bank M).Steps (decisionData (front ++ a :: rest)) bits
      (copying (α := α) M front.length (NativeNTM.encode front) .load) 1
      (copying (α := α) M front.length (NativeNTM.encode front)
        (.emit ⟨(Fintype.equivFin α a).val, by have := (Fintype.equivFin α a).isLt; omega⟩)) := by
  apply TapeBank.Steps.go (bank M) _ bits _ _ (by simp [copying, decisionData])
    (by simp [copying, decisionData]) (by simp [copying, decisionData])
  simp [TapeBank.instruction, bank, transition, copying, select, decisionData]

theorem load_rest (front rest : List α) :
    (bank M).Steps (decisionData (front ++ rest)) bits
      (copying (α := α) M front.length (NativeNTM.encode front) .load)
      ((NativeNTM.encode rest).length + rest.length + 1)
      (copying (α := α) M (front ++ rest).length (NativeNTM.encode (front ++ rest)) .rewind) := by
  induction rest generalizing front with
  | nil =>
    simpa [copying] using TapeBank.Steps.go (bank M) (decisionData front) bits
      (copying (α := α) M front.length (NativeNTM.encode front) .load) .rewind
      le_rfl (Nat.zero_le _) (Nat.zero_le _)
      (by simp [TapeBank.instruction, bank, transition, copying, select, decisionData])
  | cons a rest ih =>
    have first := load_entry M bits front rest a
    have middle := emit_run M bits (front ++ a :: rest) front.length (NativeNTM.encode front)
      (Fintype.equivFin α a).val (by have := (Fintype.equivFin α a).isLt; omega) (by simp)
    have tail := ih (front ++ [a])
    simp only [List.append_assoc, List.singleton_append] at tail
    have one := first.trans (bank M) middle
    simp only [NativeNTM.encode_append, NativeNTM.encode_cons, NativeNTM.encode_nil, List.append_nil,
      NativeNTM.letterCode, List.length_append, List.length_singleton] at tail
    simp only [List.append_assoc] at one tail
    have joined := one.trans (bank M) tail
    simpa [NativeNTM.encode_cons, NativeNTM.letterCode, List.length_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem loaded_eq (word : List α) :
    {copying (α := α) M word.length (NativeNTM.encode word) .rewind with
      state := .run (ready M M.qstart),
      head := Function.update (copying (α := α) M word.length (NativeNTM.encode word) .rewind).head 0 0} =
      lift M word (configuration M (NativeNTM.encode word) (M.initCfg (NativeNTM.encode word))) := by
  have h := congrArg (lift M word) (LibraryTM.loaded_eq M (NativeNTM.encode word))
  simpa only [lift, copying, LibraryTM.loading] using h

theorem load_initial (word : List α) :
    (bank M).Steps (decisionData word) bits (bank M).initialConfiguration
      (2 * (NativeNTM.encode word).length + word.length + 4)
      (lift M word (configuration M (NativeNTM.encode word) (M.initCfg (NativeNTM.encode word)))) := by
  have start : (bank M).Steps (decisionData word) bits (bank M).initialConfiguration 1 (copying (α := α) M 0 [] .load) := by
    have path := TapeBank.Steps.single (bank M) (decisionData word) bits
      (bank M).initialConfiguration .load .blank .right .stay .stay .stay none rfl
    convert path using 1
    apply BankConfiguration.ext
    all_goals simp [TapeBank.advance, TapeBank.initialConfiguration, bank, select, copying,
      Move.onInt, Move.onInput, image_init_nil]
    · funext j; by_cases h : j = 0 <;> simp [h]
  have load := load_rest M bits [] word
  simp only [List.nil_append, List.length_nil, NativeNTM.encode_nil] at load
  have rewind := TapeBank.rewind_steps (bank M) (decisionData word) bits .rewind (.run (ready M M.qstart))
    0 rfl (by intros; rfl) ((NativeNTM.encode word).length + 1)
    (copying (α := α) M word.length (NativeNTM.encode word) .rewind) rfl
    (by simp [copying]) le_rfl (Nat.zero_le _) (Nat.zero_le _)
  rw [loaded_eq] at rewind
  convert (start.trans (bank M) load).trans (bank M) rewind using 1 <;> omega

end
end ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
