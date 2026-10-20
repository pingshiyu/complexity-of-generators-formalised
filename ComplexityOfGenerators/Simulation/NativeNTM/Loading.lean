import ComplexityOfGenerators.Simulation.NativeNTM.Encoding
import ComplexityOfGenerators.Simulation.NativeNTM.Prelude

/-! The loader scans bounded unary letter codes, rejecting malformed inputs.
All initialization prefixes occupy at most the binary input length plus one. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)
local instance loadingAlphabetDecEq : DecidableEq α := Classical.decEq α

abbrev InitPath (full : BitString) := Prelude (tm M)
  (fun c => c.WithinDecisionSpace full.length (full.length + 1))

theorem load_zero (bit : Bool) (front rest : BitString) (word : List α)
    (count : Fin (Fintype.card α + 1)) (h : count.val < Fintype.card α) :
    (tm M).stepCfg bit (loading M (front ++ false :: rest) front.length word count) =
      loading M (front ++ false :: rest) (front.length + 1) word ⟨count.val + 1, by omega⟩ := by
  simp [loading, step_config, core, inputTape, loadedTracks, h, -Γw.toΓ,
    Tape.writeAndMove]

theorem load_one_work (word : List α) (letter : α) (t : Tracks M) :
    (loadedTracks M word word.length t).writeAndMove
        (match t with
        | .input (some a) => if a = letter then Γw.one else .blank
        | .index false => Γw.one
        | t => writable (loadedTracks M word word.length t).read : Γw)
        (match t with | .input _ | .index _ => .right | _ => .stay) =
      loadedTracks M (word ++ [letter]) (word ++ [letter]).length t := by
  cases t with
  | input a => cases a with
    | none => simp only [loadedTracks, tracks, Tape.writeAndMove, positiveTape_read, writable_toΓ,
        positiveTape_write_current, positiveTape_right, positiveTape_stay, List.length_append, List.length_singleton]
    | some a =>
      have eq : (if a = letter then Γw.one else .blank) = oneHot (some letter) a := by
        simp [oneHot, eq_comm]
      simp only [eq, loadedTracks, tracks, Tape.writeAndMove, positiveTape_write,
        inputCells_append, positiveTape_right, List.length_append, List.length_singleton]
  | index b => cases b with
    | false =>
      change ((positiveTape word.length (indexCells word.length)).write Γw.one).move .right = _
      rw [positiveTape_write, indexCells_succ, positiveTape_right]
      simp [loadedTracks, tracks]
    | true => simp only [loadedTracks, tracks, Tape.writeAndMove, positiveTape_read, writable_toΓ,
        positiveTape_write_current, positiveTape_right, List.length_append, List.length_singleton]
  | work a => cases a with
    | none => simp only [loadedTracks, tracks, Tape.writeAndMove, positiveTape_read, writable_toΓ,
        positiveTape_write_current, positiveTape_right, positiveTape_stay, List.length_append, List.length_singleton]
    | some a => rcases a with ⟨b, a⟩; simp only [loadedTracks, tracks, Tape.writeAndMove, positiveTape_read, writable_toΓ,
        positiveTape_write_current, positiveTape_right, positiveTape_stay, List.length_append, List.length_singleton]

theorem load_one (bit : Bool) (front rest : BitString) (word : List α)
    (count : Fin (Fintype.card α + 1)) (h : count.val < Fintype.card α) :
    (tm M).stepCfg bit (loading M (front ++ true :: rest) front.length word count) =
      loading M (front ++ true :: rest) (front.length + 1)
        (word ++ [(Fintype.equivFin α).symm ⟨count.val, h⟩]) 0 := by
  simp only [loading, step_config, inputTape, positiveTape_read, bitCells_append, 
    ↓reduceIte, toΓ_one, core, h, ↓reduceDIte]
  simp only [loadedTracks, tracks_safeDir, safeDir_one, safeDir_blank,
    positiveTape_right, Tape.writeAndMove, blankOutput_write, tape_move_stay,
    show blankOutput.read = Γ.blank from rfl, toΓ_blank]
  congr 1
  funext t
  exact load_one_work M word _ t

theorem load_end (bit : Bool) (full : BitString) (word : List α) :
    (tm M).stepCfg bit (loading M full full.length word 0) =
      rewinding M full word word.length := by
  simp [loading, rewinding, step_config, core, inputTape, loadedTracks,
    Tape.writeAndMove, -Γw.toΓ, Tape.move]

theorem rewind_zero (bit : Bool) (full : BitString) (word : List α) :
    (tm M).stepCfg bit (rewinding M full word 0) =
      simulated M full word (M.decisionView M.initialConfiguration) false 0 := by
  rw [← loaded_at_initial]
  simp [rewinding, step_config, core, inputTape, loadedTracks,
    tracks, originCells, Tape.writeAndMove, -Γw.toΓ]
  congr 1
  funext t
  exact tracks_keep_move M word 0 0 0 (fun _ => none) t

theorem rewind_succ (bit : Bool) (full : BitString) (word : List α) (p : ℕ) :
    (tm M).stepCfg bit (rewinding M full word (p + 1)) = rewinding M full word p := by
  simp only [rewinding, step_config]
  simp only [core, loadedTracks, tracks, positiveTape_read, originCells, toΓ_blank, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceIte, reduceCtorEq]
  simp only [inputTape, positiveTape_read, bitCells_end, safeDir_toΓ, safeDir,
    reduceCtorEq, ↓reduceIte, positiveTape_stay, Tape.writeAndMove,
    blankOutput_read, blankOutput_write, safeDir_blank, tape_move_stay,
    positiveTape_read, positiveTape_write_current, toΓ_blank]
  congr 1
  funext t
  cases t with
  | input a => cases a <;> simp [-Γw.toΓ, tracks, positiveTape_left _ (by omega : 0 < p + 1)]
  | index b => cases b <;> simp [-Γw.toΓ, tracks, positiveTape_left _ (by omega : 0 < p + 1)]
  | work a => cases a with
    | none => simp [-Γw.toΓ, tracks]
    | some a => rcases a with ⟨b, a⟩; simp [-Γw.toΓ, tracks]

theorem rewind_path (full : BitString) (word : List α) (p : ℕ) (bound : p ≤ full.length) :
    InitPath M full (rewinding M full word p)
      (simulated M full word (M.decisionView M.initialConfiguration) false 0) := by
  induction p with
  | zero =>
    exact .step (rewinding_bounded M full word 0 bound) (by intro h; cases h)
      (fun bit => rewind_zero M bit full word) (.refl _)
  | succ p ih =>
    exact .step (rewinding_bounded M full word (p + 1) bound) (by intro h; cases h)
      (fun bit => rewind_succ M bit full word p) (ih (by omega))

end
end ComplexityOfGenerators.Simulation.NativeNTM
