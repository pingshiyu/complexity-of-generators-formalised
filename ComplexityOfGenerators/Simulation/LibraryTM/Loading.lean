import ComplexityOfGenerators.Simulation.LibraryTM.Schedule

/-! Copy the binary input onto virtual tape zero and rewind. Other tapes start
blank; their protected origins are supplied by the representation's decoder. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM

open TransducerBank
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (M : Complexity.TM n) (bits : BitString)

theorem image_init_nil : image (Complexity.Tape.init []) = fun _ => .blank := by
  funext i
  simp [image, Complexity.Tape.init]

theorem image_init_append (front : BitString) (bit : Bool) :
    Function.update (image (Complexity.Tape.init (front.map Complexity.Γ.ofBool)))
      (front.length + 1 : ℤ) (Complexity.Γ.ofBool bit) =
    image (Complexity.Tape.init ((front ++ [bit]).map Complexity.Γ.ofBool)) := by
  funext i
  by_cases same : i = (front.length + 1 : ℤ)
  · subst i
    simp [image, Complexity.Tape.init, List.map_append]
  · rw [Function.update_of_ne same]
    by_cases positive : 0 < i
    · have nonzero : i.toNat ≠ 0 := by omega
      have different : i.toNat - 1 ≠ front.length := by omega
      simp only [image, positive, ↓reduceIte, Complexity.Tape.init, nonzero, List.map_append,
        List.map_cons, List.map_nil, List.getElem?_append, List.length_map]
      split_ifs with before
      · rfl
      · have later : 1 ≤ i.toNat - 1 - front.length := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · simp [image, positive]

def loading (front : BitString) : Config M :=
  ⟨.load, front.length, 0, 0, 0, [],
    fun j => if j = 0 then front.length + 1 else 0,
    fun j => if j = 0 then image (Complexity.Tape.init (front.map Complexity.Γ.ofBool))
      else fun _ => .blank⟩

theorem load_letter (front : BitString) (bit : Bool) (rest : BitString) :
    (bank M).Steps (decisionData (front ++ bit :: rest)) bits (loading M front) 1
      (loading M (front ++ [bit])) := by
  have table : (bank M).instruction (decisionData (front ++ bit :: rest)) (loading M front) =
      .step .load (Complexity.Γ.ofBool bit) .right .right .stay .stay none := by
    simp [TapeBank.instruction, bank, transition, loading, decisionData]
  have path := TapeBank.Steps.single (bank M) _ bits _ _ _ _ _ _ _ _ table
  convert path using 1
  apply BankConfiguration.ext
  all_goals simp [TapeBank.advance, loading, bank, select, Move.onInput, Move.onInt, decisionData]
  · funext j
    by_cases same : j = 0 <;> simp [same]
  · funext j
    by_cases same : j = 0
    · subst j; simpa using (image_init_append front bit).symm
    · simp [same]

theorem load_rest (front rest : BitString) :
    (bank M).Steps (decisionData (front ++ rest)) bits (loading M front) (rest.length + 1)
      {loading M (front ++ rest) with state := .rewind} := by
  induction rest generalizing front with
  | nil =>
      have path := TapeBank.Steps.go (bank M) (decisionData front) bits (loading M front) .rewind
        le_rfl (Nat.zero_le _) (Nat.zero_le _) (by
          simp [TapeBank.instruction, bank, transition, loading, decisionData])
      simpa using path
  | cons bit rest ih =>
      have first := load_letter M bits front bit rest
      have tail := ih (front ++ [bit])
      simp only [List.append_assoc, List.singleton_append] at tail
      simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        first.trans (bank M) tail

theorem loaded_eq (word : BitString) :
    {loading M word with state := ready M M.qstart, head := Function.update (loading M word).head 0 0} =
      configuration M word (M.initCfg word) := by
  apply BankConfiguration.ext
  all_goals try rfl
  · funext j
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j
    all_goals simp [loading, configuration, encoded, tapes, -Fin.succ_last]
  · funext j
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun i => ?_) j) j
    all_goals simp [loading, configuration, encoded, tapes, image_init_nil, -Fin.succ_last]

theorem load_initial (word : BitString) :
    (bank M).Steps (decisionData word) bits (bank M).initialConfiguration (2 * word.length + 4)
      (configuration M word (M.initCfg word)) := by
  have start : (bank M).Steps (decisionData word) bits (bank M).initialConfiguration 1 (loading M []) := by
    have path := TapeBank.Steps.single (bank M) (decisionData word) bits
      (bank M).initialConfiguration .load .blank .right .stay .stay .stay none rfl
    convert path using 1
    apply BankConfiguration.ext
    all_goals simp [TapeBank.advance, TapeBank.initialConfiguration, bank, select, loading,
      Move.onInt, Move.onInput, image_init_nil]
    · funext j; by_cases h : j = 0 <;> simp [h]
  have load := load_rest M bits [] word
  simp only [List.nil_append] at load
  have rewind := TapeBank.rewind_steps (bank M) (decisionData word) bits .rewind (ready M M.qstart)
    0 rfl (by intros; rfl) (word.length + 1) {loading M word with state := .rewind}
    rfl (by simp [loading]) le_rfl (Nat.zero_le _) (Nat.zero_le _)
  rw [show ({loading M word with state := .rewind} : Config M).head = (loading M word).head from rfl] at rewind
  simp only [loaded_eq] at rewind
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul] using
    (start.trans (bank M) load).trans (bank M) rewind

end ComplexityOfGenerators.Simulation.LibraryTM
