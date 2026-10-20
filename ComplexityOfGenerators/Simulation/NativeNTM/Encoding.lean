import ComplexityOfGenerators.Simulation.NativeNTM.Program

/-! Tape representations for loading and simulation. Letter codes are nonempty,
including when the alphabet has one symbol; the empty alphabet needs no case
split because its only word is the empty word. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
local instance encodingAlphabetDecEq : DecidableEq α := Classical.decEq α

/-- A bounded unary letter followed by its delimiter. -/
def letterCode (a : α) : BitString :=
  List.replicate (Fintype.equivFin α a).val false ++ [true]

def encode (word : List α) : BitString := word.flatMap letterCode

@[simp] theorem encode_nil : encode ([] : List α) = [] := rfl
@[simp] theorem encode_cons (a : α) (word : List α) :
    encode (a :: word) = letterCode a ++ encode word := by simp [encode]
@[simp] theorem encode_append (x y : List α) : encode (x ++ y) = encode x ++ encode y := by
  simp [encode]

theorem encode_length (word : List α) :
    word.length ≤ (encode word).length ∧
      (encode word).length ≤ (Fintype.card α + 1) * word.length := by
  induction word with
  | nil => simp
  | cons a word ih =>
    have := (Fintype.equivFin α a).isLt
    simp only [encode_cons, List.length_append, letterCode, List.length_replicate,
      List.length_cons, List.length_nil, Nat.mul_add, Nat.mul_one] at *
    omega

def originCells (p : ℕ) : Γw := if p = 0 then .one else .blank

def inputCells (word : List α) (a : α) (p : ℕ) : Γw := oneHot word[p]? a

def indexCells (length p : ℕ) : Γw := if p < length then .one else .blank

def bitCells (word : BitString) (p : ℕ) : Γw :=
  match word[p]? with | none => .blank | some false => .zero | some true => .one

def inputTape (word : BitString) (p : ℕ) : Tape := positiveTape p (bitCells word)

def blankOutput : Tape := positiveTape 0 (fun _ => .blank)

@[simp] theorem blankOutput_read : blankOutput.read = Γ.blank := rfl

@[simp] theorem blankOutput_write : blankOutput.write Γ.blank = blankOutput := by
  simp [blankOutput, positiveTape, Tape.write, Function.update_eq_self]

@[simp] theorem bitCells_end (word : BitString) : bitCells word word.length = .blank := by
  simp [bitCells]

@[simp] theorem bitCells_append (front rest : BitString) (bit : Bool) :
    bitCells (front ++ bit :: rest) front.length = if bit then .one else .zero := by
  cases bit <;> simp [bitCells]

@[simp] theorem originCells_one (p : ℕ) : originCells p = .one ↔ p = 0 := by
  simp [originCells]

@[simp] theorem originCells_toΓ_one (p : ℕ) : (originCells p).toΓ = .one ↔ p = 0 := by
  by_cases zero : p = 0 <;> simp [originCells, zero, Γw.toΓ]

@[simp] theorem indexCells_toΓ_one (length p : ℕ) :
    (indexCells length p).toΓ = .one ↔ p < length := by
  by_cases h : p < length <;> simp [indexCells, h, Γw.toΓ]

theorem inputCells_append (word : List α) (letter a : α) :
    Function.update (inputCells word a) word.length (oneHot (some letter) a) =
      inputCells (word ++ [letter]) a := by
  funext p
  by_cases same : p = word.length
  · subst p; simp [inputCells]
  · rw [Function.update_of_ne same]
    by_cases before : p < word.length
    · simp [inputCells, List.getElem?_append, before]
    · have later : 1 ≤ p - word.length := by omega
      simp [inputCells, List.getElem?_append, before, List.getElem?_eq_none (by omega : word.length ≤ p),
        List.getElem?_eq_none (by simp; omega : [letter].length ≤ p - word.length)]

theorem indexCells_succ (length : ℕ) :
    Function.update (indexCells length) length .one = indexCells (length + 1) := by
  funext p
  by_cases same : p = length
  · subst p; simp [indexCells]
  · rw [Function.update_of_ne same]
    by_cases before : p < length
    · simp [indexCells, before, show p < length + 1 by omega]
    · simp [indexCells, before, show ¬p < length + 1 by omega]

variable (M : Machine α Bool Unit)

def tracks (word : List α) (input index work : ℕ) (cells : ℤ → Option (Fin M.symbols)) :
    Tracks M → Tape
  | .input none => positiveTape input originCells
  | .input (some a) => positiveTape input (inputCells word a)
  | .index true => positiveTape index originCells
  | .index false => positiveTape index (indexCells word.length)
  | .work none => positiveTape work originCells
  | .work (some (negative, a)) =>
      positiveTape work (fun p => oneHot (cells (coordinate negative p)) a)

def simulated (full : BitString) (word : List α) (v : M.DecisionView) (negative : Bool) (p : ℕ) :
    Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M (.simulate v.state negative) (inputTape full full.length)
    (tracks M word v.inputHead v.indexHead p v.work) blankOutput

def loadedTracks (word : List α) (p : ℕ) : Tracks M → Tape :=
  tracks M word p p 0 (fun _ => none)

def loading (full : BitString) (position : ℕ) (word : List α)
    (count : Fin (Fintype.card α + 1)) : Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M (.load count) (inputTape full position) (loadedTracks M word word.length) blankOutput

def rewinding (full : BitString) (word : List α) (p : ℕ) :
    Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M .rewind (inputTape full full.length) (loadedTracks M word p) blankOutput

@[simp] theorem loaded_at_initial (full : BitString) (word : List α) :
    config M (.simulate M.initial false) (inputTape full full.length)
        (loadedTracks M word 0) blankOutput =
      simulated M full word (M.decisionView M.initialConfiguration) false 0 := rfl

@[simp] theorem tracks_keep (word : List α) (i j p : ℕ) (cells : ℤ → Option (Fin M.symbols))
    (t : Tracks M) :
    (tracks M word i j p cells t).write
        (writable (tracks M word i j p cells t).read) = tracks M word i j p cells t := by
  cases t with
  | input a => cases a <;> simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
  | index b => cases b <;> simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
  | work a => cases a with
    | none => simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
    | some a => rcases a with ⟨b, a⟩; simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]

@[simp] theorem tracks_safeDir (word : List α) (i j p : ℕ)
    (cells : ℤ → Option (Fin M.symbols)) (t : Tracks M) (d : Dir3) :
    safeDir (tracks M word i j p cells t).read d = d := by
  cases t with
  | input a => cases a <;> simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
  | index b => cases b <;> simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
  | work a => cases a with
    | none => simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]
    | some a => rcases a with ⟨b, a⟩; simp only [tracks, positiveTape_read, writable_toΓ, positiveTape_write_current, safeDir_toΓ]

@[simp] theorem tracks_keep_move (word : List α) (i j p : ℕ)
    (cells : ℤ → Option (Fin M.symbols)) (t : Tracks M) :
    (tracks M word i j p cells t).writeAndMove
        (writable (tracks M word i j p cells t).read)
        (safeDir (tracks M word i j p cells t).read .stay) = tracks M word i j p cells t := by
  simp only [tracks_safeDir, Tape.writeAndMove, tracks_keep, tape_move_stay]

theorem tracks_bound (word : List α) (i j p s : ℕ) (cells : ℤ → Option (Fin M.symbols))
    (hi : i + 1 ≤ s) (hj : j + 1 ≤ s) (hp : p + 1 ≤ s) (t : Tracks M) :
    (tracks M word i j p cells t).head ≤ s := by
  cases t with
  | input a => cases a <;> exact hi
  | index b => cases b <;> exact hj
  | work a => cases a with
    | none => exact hp
    | some a => rcases a with ⟨b, a⟩; exact hp

theorem loading_bounded (full : BitString) (position : ℕ) (word : List α)
    (count : Fin (Fintype.card α + 1)) (pos : position ≤ full.length) (len : word.length ≤ full.length) :
    (loading M full position word count).WithinDecisionSpace full.length (full.length + 1) := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · exact tracks_bound M word word.length word.length 0 _ _ (by omega) (by omega) (by omega) _
  · change position + 1 ≤ _; omega
  · change 1 ≤ _; omega

theorem rewinding_bounded (full : BitString) (word : List α) (p : ℕ) (pos : p ≤ full.length) :
    (rewinding M full word p).WithinDecisionSpace full.length (full.length + 1) := by
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · exact tracks_bound M word p p 0 _ _ (by omega) (by omega) (by omega) _
  · change full.length + 1 ≤ _; omega
  · change 1 ≤ _; omega

end
end ComplexityOfGenerators.Simulation.NativeNTM
