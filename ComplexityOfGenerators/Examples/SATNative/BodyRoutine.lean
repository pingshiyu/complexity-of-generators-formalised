import ComplexityOfGenerators.Examples.SATNative.BodyComplete
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.RoutineLoops

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeBody

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 32

def subslots : Fin 16 ↪ Fin 32 := ⟨fun j => ⟨j.val, by omega⟩, by intro i j equal; exact Fin.ext (congrArg (fun t : Fin 32 => t.val) equal)⟩

@[simp] theorem subslots_val (j : Fin 16) : (subslots j).val = j.val := rfl

/-- Canonical flag stores, retained between parser iterations. -/
def Represents (capacity active : ℕ) (state : State) (s : Store) : Prop :=
  s 2 = state.word ∧ s 4 = List.replicate capacity .one ∧ s 10 = List.replicate active .one ∧
  s 6 = (if state.valid then [.one] else []) ∧
  s 17 = (if state.inside then [.one] else []) ∧ s 18 = (if state.nonempty then [.one] else [])

def outsideCode (tag : Symbol) : Local Symbol 32 :=
  (Local.pop 2).seq ((Local.pop 18).seq
    (if tag = .openClause then Local.push 17 .one else Local.pop 6))

def closeCode : Local Symbol 32 :=
  (Local.pop 2).seq ((Local.pop 17).seq
    ((Local.read 18 fun present => if present.isSome then .skip else Local.pop 6).seq (Local.pop 18)))

noncomputable def bodyStep {O : Type} : Routine Symbol O 32 :=
  Routine.branch 2 fun head => match head with
  | none => Routine.skip
  | some tag => Routine.branch 17 fun inside =>
      if inside.isSome then
        if tag = .closeClause then Routine.ofLocal closeCode
        else ((NativeLiteral.literalRoutine (O := O)).rename subslots).seq
          (Routine.ofLocal (Local.write 18 .one))
      else Routine.ofLocal (outsideCode tag)

theorem literal_input_eq (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    NativeLiteral.inputStore (s ∘ subslots) capacity active state.word state.valid = s ∘ subslots := by
  rcases represented with ⟨word, cap, count, valid, _, _⟩
  funext j
  by_cases a : j = 2 <;> by_cases b : j = 4 <;> by_cases c : j = 10 <;> by_cases d : j = 6 <;>
    simp [NativeLiteral.inputStore, Function.comp_def, subslots, a, b, c, d] <;>
    first | exact word.symm | exact cap.symm | exact count.symm | exact valid.symm

theorem literal_represents {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    let output := ((NativeLiteral.literalRoutine (O := O)).rename subslots).eval s
    output 2 = (NativeLiteral.fieldState capacity state.word).word ∧
    output 4 = List.replicate capacity .one ∧ output 10 = List.replicate active .one ∧
    output 6 = (if state.valid && (NativeLiteral.readLiteral capacity active state.word).isSome then [.one] else []) ∧
    output 17 = s 17 ∧ output 18 = s 18 := by
  dsimp only
  have evalHere (j : Fin 16) :
      ((NativeLiteral.literalRoutine (O := O)).rename subslots).eval s (subslots j) =
        (NativeLiteral.literalRoutine (O := O)).eval
          (NativeLiteral.inputStore (s ∘ subslots) capacity active state.word state.valid) j := by
    rw [Routine.rename_eval_here, literal_input_eq capacity active state s represented]
  have word := evalHere 2
  have cap := evalHere 4
  have count := evalHere 10
  have valid := evalHere 6
  rw [NativeLiteral.literalRoutine_eval] at word cap count valid
  have seventeen := Routine.rename_eval_frame (NativeLiteral.literalRoutine (O := O)) subslots s 17
    (by intro i equal; have := congrArg Fin.val equal; simp only [subslots_val] at this; omega)
  have eighteen := Routine.rename_eval_frame (NativeLiteral.literalRoutine (O := O)) subslots s 18
    (by intro i equal; have := congrArg Fin.val equal; simp only [subslots_val] at this; omega)
  refine ⟨?_, ?_, ?_, ?_, seventeen, eighteen⟩
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.checked, NativeHeader.restrict] using word
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.indexFrame, NativeLiteral.scaffold] using cap
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.indexFrame, NativeLiteral.scaffold] using count
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.checked, NativeHeader.restrict,
      NativeLiteral.readLiteral_isSome, Bool.and_assoc, Bool.and_comm] using valid

theorem outside_represents (capacity active : ℕ) (state : State) (s : Store) (tag : Symbol) (rest : List Symbol)
    (represented : Represents capacity active state s) (word : state.word = tag :: rest)
    (outside : state.inside = false) :
    Represents capacity active (step capacity active state) ((outsideCode tag).eval s) := by
  rcases represented with ⟨savedWord, cap, count, valid, inside, seen⟩
  by_cases opening : tag = .openClause <;> cases mark : state.nonempty <;> cases good : state.valid <;>
    simp [Represents, outsideCode, Local.eval, Local.pop, Local.push, Action.apply,
      step, word, outside, opening, savedWord, cap, count, valid, inside, seen, mark, good]

theorem close_represents (capacity active : ℕ) (state : State) (s : Store) (rest : List Symbol)
    (represented : Represents capacity active state s) (word : state.word = .closeClause :: rest)
    (inside : state.inside = true) :
    Represents capacity active (step capacity active state) (closeCode.eval s) := by
  rcases represented with ⟨savedWord, cap, count, valid, savedInside, seen⟩
  cases mark : state.nonempty <;> cases good : state.valid <;>
    simp [Represents, closeCode, Local.eval, Local.pop, Action.apply,
      step, word, inside, savedWord, cap, count, valid, savedInside, seen, mark, good]

theorem bodyStep_represents {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active (step capacity active state) ((bodyStep (O := O)).eval s) := by
  have saved := represented
  rcases saved with ⟨wordReg, _, _, _, insideReg, seenReg⟩
  cases word : state.word with
  | nil =>
    simpa [bodyStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval, step] using represented
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, Routine.ofLocal] using
        outside_represents capacity active state s tag rest represented word inside
    | true =>
      by_cases close : tag = .closeClause
      · subst tag
        simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, Routine.ofLocal] using
          close_represents capacity active state s rest represented word inside
      · have literal := literal_represents (O := O) capacity active state s represented
        dsimp only at literal
        rcases literal with ⟨remaining, cap, count, validity, savedInside, savedSeen⟩
        simp only [bodyStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, ite_false,
          Routine.seq, Routine.ofLocal]
        cases mark : state.nonempty <;>
          simp [Represents, Local.eval_write, remaining, cap, count, validity, savedInside, savedSeen,
            insideReg, seenReg, inside, mark, step, word, close]

theorem bodyStep_frame {O : Type} (s : Store) : (bodyStep (O := O)).eval s 16 = s 16 := by
  cases head : (s 2).head? with
  | none => simp [bodyStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil =>
      by_cases opening : tag = .openClause <;>
        simp [bodyStep, Routine.branch, head, inside, Routine.ofLocal, outsideCode,
          Local.eval, Local.pop, Local.push, Action.apply, opening]
    | cons mark tail =>
      by_cases close : tag = .closeClause
      · cases seen : s 18 <;>
          simp [bodyStep, Routine.branch, head, inside, close, Routine.ofLocal, closeCode,
            Local.eval, Local.pop, Action.apply, seen]
      · have frame := Routine.rename_eval_frame (NativeLiteral.literalRoutine (O := O)) subslots s 16
          (by intro i equal; have := congrArg Fin.val equal; simp only [subslots_val] at this; omega)
        simpa [bodyStep, Routine.branch, head, inside, close, Routine.seq, Routine.ofLocal, Local.eval_write] using frame

noncomputable def bodyRoutine {O : Type} : Routine Symbol O 32 :=
  Routine.iterate 16 bodyStep bodyStep_frame

theorem bodyRoutine_represents {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active ((step capacity active)^[(s 16).length] state) ((bodyRoutine (O := O)).eval s) := by
  have one (state : State) (s : Store) (represented : Represents capacity active state s) :
      Represents capacity active (step capacity active state) ((Routine.counted 16 (bodyStep (O := O))).eval s) := by
    apply bodyStep_represents
    rcases represented with ⟨word, cap, count, valid, inside, seen⟩
    simp [Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop, Represents,
      word, cap, count, valid, inside, seen]
  have iter (count : ℕ) : ∀ state s, Represents capacity active state s →
      Represents capacity active ((step capacity active)^[count] state)
        ((Routine.counted 16 (bodyStep (O := O))).eval^[count] s) := by
    induction count with
    | zero => intro state s h; exact h
    | succ count ih =>
      intro state s h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ (one state s h)
  exact iter _ state s represented

end ComplexityOfGenerators.Examples.PaddedCNF.NativeBody
