import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Mask

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeSubstitution.prepareStream InverseNative.bodyTransform

def Represents (capacity active : ℕ) (state : NativeBody.State) (s : Store) : Prop :=
  NativeBody.Represents capacity active state (s ∘ slots)

theorem parse_project (s : Store) :
    parse.eval s ∘ slots = (NativeSubstitution.prepareStream (O := Symbol)).eval (s ∘ slots) := by
  funext j
  exact parse_here s j

theorem parse_canonical {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (s : Store) (word : s 2 = formula.encode capacity active) :
    Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ (parse.eval s) ∧
      (parse.eval s 16).length = (formula.bodyWord capacity).length := by
  have properties := NativeSubstitution.prepareStream_properties (O := Symbol) (s ∘ slots)
  dsimp only at properties
  have sourceWord : (s ∘ slots) 2 = formula.encode capacity active := word
  rw [sourceWord,NativeParser.header_encode capacity active bound formula,NativeParser.capacity_encode] at properties
  constructor
  · rw [Represents,parse_project]
    exact properties.1
  · have here := parse_here s 16
    change parse.eval s 16 = _ at here
    rw [here]
    exact properties.2.1

theorem parse_label (s : Store) : parse.eval s 3 = s 3 := by
  have here := parse_here s 3
  change parse.eval s 3 = _ at here
  rw [here]
  exact (NativeSubstitution.prepareStream_properties (O := Symbol) (s ∘ slots)).2.2

theorem parse_mask (s : Store) : parse.eval s 31 = s 31 := by
  have here := parse_here s 31
  change parse.eval s 31 = _ at here
  rw [here,InverseNative.prepareStream_mask]
  rfl

theorem moreRoutine_represents (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state (moreRoutine.eval s) := by
  simpa [Represents,NativeBody.Represents,Function.comp_def,moreRoutine_eval,slots,BaseSampler.verifierSlots] using represented

theorem masked_represents (capacity active : ℕ) (state : NativeBody.State) (s : Memory) (n : ℕ) (bits : BitString)
    (represented : Represents capacity active state s.store) :
    Represents capacity active state (masked n bits s).store := by
  simpa [Represents,NativeBody.Represents,Function.comp_def,masked,slots,BaseSampler.verifierSlots] using represented

theorem transform_buffer (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity) (formula : Formula)
    (valid : formula.valid active) (s : Store)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ s)
    (enough : NativeBody.tokenCount formula ≤ (s 16).length)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    (transform bit).eval s 21 =
      ((formula.lift active bit (choiceRows formula choices)).encode capacity (active+1)).reverse := by
  have result := bodyTransform_formula (O := Symbol) bit bound formula valid true (s ∘ slots) represented enough choices mask
  have here := transform_here bit s 21
  change (transform bit).eval s 21 = _ at here
  exact here.trans result.2.2

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
