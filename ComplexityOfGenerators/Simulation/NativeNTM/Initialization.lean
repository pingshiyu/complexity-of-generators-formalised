import ComplexityOfGenerators.Simulation.NativeNTM.Loading

/-! Initialization is uniform in the queried word and has a bound on every
prefix, whether the binary encoding is valid or malformed. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)

theorem init_right (full : BitString) :
    (Tape.init (full.map Γ.ofBool)).move .right = inputTape full 0 := by
  apply Tape.ext
  · rfl
  funext p
  cases p with
  | zero => rfl
  | succ p =>
    simp only [Tape.move, Tape.init, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, List.getElem?_map, inputTape, positiveTape, bitCells]
    cases h : full[p]? with
    | none => rfl
    | some b => cases b <;> rfl

def marked (full : BitString) : Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M .mark (inputTape full 0) (fun _ => positiveTape 0 (fun _ => .blank)) blankOutput

theorem boot_step (bit : Bool) (full : BitString) :
    (tm M).stepCfg bit ((tm M).initCfg full) = marked M full := by
  change (tm M).stepCfg bit (config M .boot (Tape.init (full.map Γ.ofBool))
    (fun _ => Tape.init []) (Tape.init [])) = _
  rw [step_config]
  simp only [core, Tape.read, Tape.init, ↓reduceIte, safeDir, writable, reduceCtorEq,
    Tape.writeAndMove, Tape.write]
  change config M .mark ((Tape.init (full.map Γ.ofBool)).move .right)
    (fun _ => (Tape.init []).move .right) ((Tape.init []).move .right) = _
  rw [init_right]
  have empty := init_right ([] : BitString)
  simp only [List.map_nil, inputTape, bitCells, List.getElem?_nil] at empty
  simp only [empty]
  rfl

@[simp] theorem initialize_origin :
    Function.update (fun _ : ℕ => Γw.blank) 0 Γw.one = originCells := by
  funext p
  by_cases h : p = 0 <;> simp [h, originCells]

theorem mark_step (bit : Bool) (full : BitString) :
    (tm M).stepCfg bit (marked M full) = loading M full 0 [] 0 := by
  simp only [marked, step_config, core, loading, inputTape, positiveTape_read, safeDir_toΓ,
    safeDir_blank, blankOutput_read, Tape.writeAndMove, toΓ_blank, blankOutput_write,
    tape_move_stay, List.length_nil]
  congr 1
  funext t
  cases t with
  | input a => cases a with
    | none => simpa [loadedTracks, tracks] using positiveTape_write 0 (fun _ => .blank) Γw.one
    | some a =>
      have empty : inputCells ([] : List α) a = fun _ => .blank := by funext p; simp [inputCells, oneHot]
      simpa only [blankOutput, toΓ_blank, loadedTracks, tracks, empty] using blankOutput_write
  | index b => cases b with
    | false =>
      have empty : indexCells 0 = fun _ => .blank := by funext p; simp [indexCells]
      simpa only [blankOutput, toΓ_blank, loadedTracks, tracks, List.length_nil, empty] using blankOutput_write
    | true => simpa [loadedTracks, tracks] using positiveTape_write 0 (fun _ => .blank) Γw.one
  | work a => cases a with
    | none => simpa [loadedTracks, tracks] using positiveTape_write 0 (fun _ => .blank) Γw.one
    | some a =>
      rcases a with ⟨b, a⟩
      simpa only [blankOutput, toΓ_blank, loadedTracks, tracks, oneHot, reduceCtorEq, ↓reduceIte] using blankOutput_write

theorem boot_path (full : BitString) : InitPath M full ((tm M).initCfg full) (loading M full 0 [] 0) := by
  refine .step ?_ (by intro h; cases h) (fun b => boot_step M b full)
    (.step ?_ (by intro h; cases h) (fun b => mark_step M b full) (.refl _))
  · exact ⟨⟨fun _ => Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩
  · exact ⟨⟨fun _ => by change 1 ≤ full.length + 1; omega,
      by change 1 ≤ full.length + (full.length + 1) + 1; omega⟩, by change 1 ≤ full.length + 1 + 1; omega⟩

def rejected (full : BitString) (position : ℕ) (word : List α) :
    Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M .halt (inputTape full position) (loadedTracks M word word.length) (blankOutput.write Γ.zero)

@[simp] theorem rejected_halted (full : BitString) (position : ℕ) (word : List α) :
    (tm M).halted (rejected M full position word) := rfl

@[simp] theorem rejected_output (full : BitString) (position : ℕ) (word : List α) :
    (rejected M full position word).output.cells 1 = Γ.zero := by
  simp [rejected, config, blankOutput, positiveTape, Tape.write]

theorem rejected_bound (full : BitString) (position : ℕ) (word : List α)
    (pos : position ≤ full.length) (len : word.length ≤ full.length) :
    (rejected M full position word).WithinDecisionSpace full.length (full.length + 1) :=
  loading_bounded M full position word 0 pos len

theorem load_bad_bit (bit letter : Bool) (front rest : BitString) (word : List α)
    (count : Fin (Fintype.card α + 1)) (h : ¬ count.val < Fintype.card α) :
    (tm M).stepCfg bit (loading M (front ++ letter :: rest) front.length word count) =
      rejected M (front ++ letter :: rest) front.length word := by
  cases letter <;> simp [loading, rejected, step_config, core, inputTape, loadedTracks,
    Tape.writeAndMove, h, -Γw.toΓ]

theorem load_bad_end (bit : Bool) (full : BitString) (word : List α)
    (count : Fin (Fintype.card α + 1)) (h : count.val ≠ 0) :
    (tm M).stepCfg bit (loading M full full.length word count) = rejected M full full.length word := by
  have ne : count ≠ 0 := by intro eq; subst count; exact h rfl
  simp [loading, rejected, step_config, core, inputTape, loadedTracks, Tape.writeAndMove, h, ne, -Γw.toΓ]

/-- Every binary input either loads a word no longer than itself, or halts with
rejection. This is a statement about actual finite transition tables. -/
theorem load_total (front rest : BitString) (word : List α) (count : Fin (Fintype.card α + 1))
    (length : word.length ≤ front.length) :
    ∃ c, InitPath M (front ++ rest) (loading M (front ++ rest) front.length word count) c ∧
      ((∃ w : List α, w.length ≤ (front ++ rest).length ∧
          c = simulated M (front ++ rest) w (M.decisionView M.initialConfiguration) false 0) ∨
        ((tm M).halted c ∧ c.output.cells 1 = .zero ∧
          c.WithinDecisionSpace (front ++ rest).length ((front ++ rest).length + 1))) := by
  induction rest generalizing front word count with
  | nil =>
    simp only [List.append_nil]
    by_cases zero : count.val = 0
    · have eq : count = 0 := Fin.ext zero
      subst count
      exact ⟨_, .step (loading_bounded M front front.length word 0 le_rfl length)
        (by intro h; cases h) (fun b => load_end M b front word)
        (rewind_path M front word word.length length), Or.inl ⟨word, length, rfl⟩⟩
    · exact ⟨_, .step (loading_bounded M front front.length word count le_rfl length)
        (by intro h; cases h) (fun b => load_bad_end M b front word count zero) (.refl _),
        Or.inr ⟨rejected_halted M front front.length word, rejected_output M front front.length word,
          rejected_bound M front front.length word le_rfl length⟩⟩
  | cons letter rest ih =>
    have pos : front.length ≤ (front ++ letter :: rest).length := by simp
    have len := length.trans pos
    by_cases good : count.val < Fintype.card α
    · cases letter with
      | false =>
        obtain ⟨c, tail, finish⟩ := ih (front ++ [false]) word ⟨count.val + 1, by omega⟩ (by simp; omega)
        simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at tail finish
        exact ⟨c, .step (loading_bounded M _ _ word count pos len) (by intro h; cases h)
          (fun b => load_zero M b front rest word count good) tail, by simpa only [List.length_append] using finish⟩
      | true =>
        let a := (Fintype.equivFin α).symm ⟨count.val, good⟩
        obtain ⟨c, tail, finish⟩ := ih (front ++ [true]) (word ++ [a]) 0 (by simp; omega)
        simp only [List.append_assoc, List.singleton_append, List.length_append, List.length_singleton] at tail finish
        exact ⟨c, .step (loading_bounded M _ _ word count pos len) (by intro h; cases h)
          (fun b => load_one M b front rest word count good) tail, by simpa only [List.length_append] using finish⟩
    · exact ⟨_, .step (loading_bounded M _ _ word count pos len) (by intro h; cases h)
        (fun b => load_bad_bit M b letter front rest word count good) (.refl _),
        Or.inr ⟨rejected_halted M _ _ word, rejected_output M _ _ word,
          rejected_bound M _ _ word pos len⟩⟩

end
end ComplexityOfGenerators.Simulation.NativeNTM
