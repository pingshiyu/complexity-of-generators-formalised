import ComplexityOfGenerators.Simulation.NativeNTM.Encoding

/-! One native graph edge is one library choice step. Only native random-read
instructions consult the library choice; deterministic instructions ignore it. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)
local instance stepAlphabetDecEq : DecidableEq α := Classical.decEq α

def sourceData (word : List α) : InputData α Bool := ⟨word, [], word.length⟩

def sourceAction (word : List α) (v : M.DecisionView) :=
  M.transition v.state word[v.inputHead]? none
    (if v.indexHead < word.length then some () else none) (v.work v.workHead)

def finished (full : BitString) (word : List α) (v : M.DecisionView) (p : ℕ) (verdict : Bool) :
    Cfg (Fintype.card (Tracks M)) (tm M).Q :=
  config M .halt (inputTape full full.length)
    (tracks M word v.inputHead v.indexHead p v.work)
    (blankOutput.write (if verdict then Γw.one else .zero : Γw))

@[simp] theorem finished_halted (full : BitString) (word : List α) (v : M.DecisionView)
    (p : ℕ) (verdict : Bool) : (tm M).halted (finished M full word v p verdict) := rfl

@[simp] theorem finished_output (full : BitString) (word : List α) (v : M.DecisionView)
    (p : ℕ) (verdict : Bool) :
    (finished M full word v p verdict).output.cells 1 = .one ↔ verdict = true := by
  cases verdict <;> simp [finished, config, blankOutput, Tape.write, positiveTape]

theorem getElem_isNone (word : List α) (h : ℕ) (bound : h ≤ word.length) :
    word[h]?.isNone = decide (h = word.length) := by
  by_cases last : h = word.length
  · subst h; simp
  · have before : h < word.length := by omega
    simp [List.getElem?_eq_getElem before, last]

theorem step_terminal (bit : Bool) (full : BitString) (word : List α)
    (v : M.DecisionView) (negative : Bool) (p : ℕ)
    (head : v.workHead = coordinate negative p) (verdict : Bool)
    (action : sourceAction M word v = if verdict then .accept else .reject) :
    (tm M).stepCfg bit (simulated M full word v negative p) = finished M full word v p verdict := by
  have act := action
  simp only [sourceAction, head] at act
  cases verdict <;>
    simp [simulated, finished, step_config, core, tracks, inputCells, inputTape, head,
      act, Tape.writeAndMove, originCells, -Γw.toΓ]
  all_goals congr 1; funext t; exact tracks_keep_move M word v.inputHead v.indexHead p v.work t

theorem step_random (bit : Bool) (full : BitString) (word : List α)
    (v : M.DecisionView) (negative : Bool) (p : ℕ)
    (head : v.workHead = coordinate negative p) (no yes : Fin M.states)
    (action : sourceAction M word v = .readRandom no yes) :
    (tm M).stepCfg bit (simulated M full word v negative p) =
      simulated M full word {v with state := if bit then yes else no} negative p := by
  have act := action
  simp only [sourceAction, head] at act
  simp [simulated, step_config, core, tracks, inputCells, inputTape, head,
    act, Tape.writeAndMove, originCells, -Γw.toΓ]
  congr 1
  funext t
  exact tracks_keep_move M word v.inputHead v.indexHead p v.work t

def nextView (word : List α) (v : M.DecisionView) (q : Fin M.states)
    (write : Option (Fin M.symbols)) (work input auxiliary index : Move) : M.DecisionView where
  state := q
  inputHead := input.onInput word.length v.inputHead
  auxiliaryHead := auxiliary.onInput 0 v.auxiliaryHead
  indexHead := index.onInput word.length v.indexHead
  workHead := work.onInt v.workHead
  work := match write with | none => v.work | some a => Function.update v.work v.workHead (some a)

theorem step_native (bit : Bool) (full : BitString) (word : List α)
    (v : M.DecisionView) (negative : Bool) (p : ℕ)
    (head : v.workHead = coordinate negative p) (inputBound : v.inputHead ≤ word.length)
    (indexBound : v.indexHead ≤ word.length)
    (q : Fin M.states) (write : Option (Fin M.symbols)) (work input auxiliary index : Move)
    (emit : Option Unit) (action : sourceAction M word v = .step q write work input auxiliary index emit) :
    (tm M).stepCfg bit (simulated M full word v negative p) =
      simulated M full word (nextView M word v q write work input auxiliary index)
        (foldedSign negative (decide (p = 0)) work) (foldedHead negative p work) := by
  have act := action
  simp only [sourceAction, head] at act
  have endIndex' : word.length ≤ v.indexHead ↔ v.indexHead = word.length := by omega
  have endIndex : (¬ v.indexHead < word.length) ↔ v.indexHead = word.length := by omega
  simp only [simulated, step_config, core, tracks, positiveTape_read, inputCells,
    decodeTracks_oneHot, originCells_toΓ_one, indexCells_toΓ_one, act,
    getElem_isNone word v.inputHead inputBound, endIndex]
  simp only [nextView, inputTape, positiveTape_read, bitCells_end, toΓ_blank, safeDir_blank,
    Tape.writeAndMove, positiveTape_write_current, tape_move_stay,
    show blankOutput.read = Γ.blank from rfl, blankOutput_write]
  congr 1
  funext t
  cases t with
  | input a => cases a <;>
      simpa [-Γw.toΓ, tracks, endIndex', positiveTape_read, writable_toΓ, safeDir_toΓ] using
        positiveTape_boundedDir v.inputHead word.length _ input inputBound
  | index b => cases b <;>
      simpa [-Γw.toΓ, tracks, endIndex', positiveTape_read, writable_toΓ, safeDir_toΓ] using
        positiveTape_boundedDir v.indexHead word.length _ index indexBound
  | work a => cases a with
    | none => simpa [-Γw.toΓ, tracks, endIndex', positiveTape_read, writable_toΓ, safeDir_toΓ] using
        positiveTape_foldedDir negative p originCells work
    | some a =>
      rcases a with ⟨half, a⟩
      cases write with
      | none => simpa [-Γw.toΓ, tracks, endIndex', positiveTape_read, writable_toΓ, safeDir_toΓ] using
          positiveTape_foldedDir negative p (fun r => oneHot (v.work (coordinate half r)) a) work
      | some symbol =>
        simp only [positiveTape_read, writable_toΓ, safeDir_toΓ, decide_eq_true_eq, head]
        rw [folded_write, positiveTape_foldedDir]
        rfl

end
end ComplexityOfGenerators.Simulation.NativeNTM
