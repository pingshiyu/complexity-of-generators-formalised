import ComplexityOfGenerators.Examples.SATNative.SubstitutionComplete
import ComplexityOfGenerators.Examples.SATNative.VerifierRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

noncomputable def bodyTransform {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  emitHeader.seq (substitutionRoutine bit)

attribute [local irreducible] emitHeader substitutionRoutine

theorem bodyTransform_eval {O : Type} (bit : Bool) (s : Store) :
    (bodyTransform (O := O) bit).eval s = (substitutionRoutine (O := O) bit).eval ((emitHeader (O := O)).eval s) := by
  simp only [bodyTransform, Routine.seq]

theorem encode_as_headerBody (capacity active : ℕ) (formula : Formula) :
    formula.encode capacity active = headerWord capacity active ++ formula.bodyWord capacity := by
  simp [Formula.encode, headerWord, Formula.bodyWord, List.append_assoc]

theorem syntaxVerdict_of_represents (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    NativeEvaluation.verdict s = NativeBody.accepts state := by
  rcases represented with ⟨word, _, _, valid, inside, _⟩
  rw [NativeEvaluation.verdict, word, valid, inside]
  cases flag : state.inside <;> cases good : state.valid <;> simp [NativeBody.accepts, flag, good]

theorem bodyTransform_represents {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active ((NativeBody.step capacity active)^[(s 16).length] state)
      ((bodyTransform (O := O) bit).eval s) := by
  rw [bodyTransform_eval]
  have prepared := emitHeader_parserFrame (O := O) capacity active state s represented
  have clock := emitHeader_frame (O := O) s 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have parsed := substitutionRoutine_represents (O := O) bit capacity active state _ prepared
  rw [clock] at parsed
  exact parsed

theorem bodyTransform_verdict {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    NativeEvaluation.verdict ((bodyTransform (O := O) bit).eval s) =
      NativeBody.accepts ((NativeBody.step capacity active)^[(s 16).length] state) :=
  syntaxVerdict_of_represents _ _ _ _ (bodyTransform_represents bit capacity active state s represented)

set_option maxHeartbeats 800000 in
theorem bodyTransform_formula {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity, false, false, enabled⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length) :
    let output := (bodyTransform (O := O) bit).eval s
    Represents capacity active ⟨[], false, false, enabled⟩ output ∧
      output 21 = ((formula.substitute active bit).encode capacity (active - 1)).reverse := by
  dsimp only
  rw [bodyTransform_eval]
  let prepared := (emitHeader (O := O)).eval s
  have preparedRep := emitHeader_parserFrame (O := O) capacity active _ s represented
  have clock : prepared 16 = s 16 := emitHeader_frame (O := O) s 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have clockEnough : NativeBody.tokenCount formula ≤ (prepared 16).length := by rw [clock]; exact enough
  have parsed := substitutionRoutine_formula (O := O) bit bound formula valid enabled prepared preparedRep clockEnough
  refine ⟨parsed.1, ?_⟩
  have initialBuffer : prepared 21 = (headerWord capacity (active - 1)).reverse := by
    have buffer := emitHeader_buffer (O := O) s
    simpa only [represented.2.1, represented.2.2.1, List.length_replicate] using buffer
  rw [parsed.2, initialBuffer, ← List.reverse_append, ← encode_as_headerBody]

@[simp] theorem bodyTransform_randomFree {O : Type} (bit : Bool) : Command.RandomFree (bodyTransform (O := O) bit).command := by
  simp [bodyTransform]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
