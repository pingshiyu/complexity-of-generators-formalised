import ComplexityOfGenerators.Examples.SATNative.LiteralRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral

open Simulation.WordStack
open NativeHeader

set_option backward.isDefEq.respectTransparency false

def indexFrame (base : Store) (active index : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    15 (List.replicate (active + 1) .one)) 9 []) 13 []) 14 []) 12 (if index ≤ active then [.one] else [])

theorem indexRoutine_eval {O : Type} (base : Store) (state : ScanState) (active : ℕ)
    (count : base 10 = List.replicate active .one) :
    (indexRoutine (O := O)).eval (NativeHeader.encoded base state []) =
      NativeHeader.encoded (indexFrame base active state.count) state [] := by
  funext j
  fin_cases j <;>
    simp [indexRoutine, indexSetup, Routine.seq, Routine.assign_eval, Routine.ofLocal,
      RationalSelection.Compare.routine_eval, indexSlots, NativeHeader.encoded,
      indexFrame, count, List.replicate_succ]

def acceptsTag (active index : ℕ) (tag : Option Symbol) : Bool :=
  (tag.bind (fun tag => ofTag active tag index)).isSome

theorem readLiteral_isSome (capacity active : ℕ) (word : List Symbol) :
    (readLiteral capacity active word).isSome =
      ((fieldState capacity word).valid && acceptsTag active (fieldState capacity word).count word.head?) := by
  unfold readLiteral acceptsTag
  cases valid : (fieldState capacity word).valid <;> simp [valid]

theorem tagCheck_frame (s : Store) (j : Fin 16) (outside : j ≠ 6) : tagCheck.eval s j = s j := by
  cases head : (s 11).head? with
  | none => simp [tagCheck, Local.eval, Local.pop, head, outside]
  | some symbol =>
    cases symbol <;> cases index : (s 5).head? <;> cases within : (s 12).head? <;>
      simp [tagCheck, Local.eval, Local.pop, head, index, within, outside]

def checked (state : ScanState) (active : ℕ) (tag : Option Symbol) : ScanState :=
  {state with valid := state.valid && acceptsTag active state.count tag}

theorem tagCheck_eval (base : Store) (state : ScanState) (active : ℕ) (tag : Option Symbol)
    (stored : base 11 = tag.toList) (within : base 12 = if state.count ≤ active then [.one] else []) :
    tagCheck.eval (NativeHeader.encoded base state []) =
      NativeHeader.encoded base (checked state active tag) [] := by
  funext j
  by_cases changed : j = 6
  · subst j
    cases tag with
    | none =>
      cases validity : state.valid <;>
        simp [tagCheck, Local.eval, Local.pop, Action.apply, NativeHeader.encoded,
          stored, checked, acceptsTag, validity]
    | some symbol =>
      cases symbol <;> cases validity : state.valid <;>
        by_cases zero : state.count = 0 <;> by_cases bound : state.count ≤ active <;>
          simp [tagCheck, Local.eval, Local.pop, Action.apply, NativeHeader.encoded,
            stored, within, checked, acceptsTag, ofTag, validity, zero, bound, Nat.pos_iff_ne_zero]
  · rw [tagCheck_frame _ j changed]
    simp [NativeHeader.encoded, checked, Function.update_apply, changed]

theorem literalRoutine_eval {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool) :
    (literalRoutine (O := O)).eval (inputStore base capacity active word enabled) =
      NativeHeader.encoded
        (indexFrame (scaffold base capacity active word) active (fieldState capacity word).count)
        (checked (NativeHeader.restrict (fieldState capacity word) enabled) active word.head?) [] := by
  let original := scaffold base capacity active word
  let field := NativeHeader.restrict (fieldState capacity word) enabled
  have saved : original 10 = List.replicate active .one := by simp [original, scaffold]
  have tag : (indexFrame original active field.count) 11 = word.head?.toList := by
    simp [indexFrame, original, scaffold]
  have within : (indexFrame original active field.count) 12 = if field.count ≤ active then [.one] else [] := by
    simp [indexFrame]
  simp only [literalRoutine, Routine.seq, Routine.ofLocal]
  rw [scan_eval, indexRoutine_eval _ _ active saved, tagCheck_eval _ _ active word.head? tag within]
  rfl

theorem literalRoutine_spec {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool) :
    let output := (literalRoutine (O := O)).eval (inputStore base capacity active word enabled)
    output 2 = (fieldState capacity word).word ∧
    output 5 = List.replicate (fieldState capacity word).count .one ∧
    output 6 = (if enabled && (readLiteral capacity active word).isSome then [.one] else []) ∧
    output 11 = word.head?.toList := by
  dsimp only
  rw [literalRoutine_eval]
  simp [NativeHeader.encoded, indexFrame, scaffold, NativeHeader.restrict,
    checked, readLiteral_isSome, Bool.and_assoc, Bool.and_comm]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral
