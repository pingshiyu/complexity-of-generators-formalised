import ComplexityOfGenerators.Foundations.Probability

/-! Finite words over a countable alphabet carry the discrete sigma-algebra.
This also supplies a concrete measurable result space for finite call records. -/
namespace ComplexityOfGenerators

instance countableListMeasurableSpace (A : Type) [Countable A] : MeasurableSpace (List A) := ⊤
instance countableListMeasurableSingletonClass (A : Type) [Countable A] :
    MeasurableSingletonClass (List A) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end ComplexityOfGenerators
