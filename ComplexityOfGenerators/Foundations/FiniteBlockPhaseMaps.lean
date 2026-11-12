import ComplexityOfGenerators.Foundations.FiniteBlockPhaseLists

/-! Deterministic changes to successful payloads commute with the actual
flag-only fair offers. The random bits and success flags are unchanged. -/
namespace ComplexityOfGenerators.FiniteBlockPhase
set_option backward.isDefEq.respectTransparency false
variable {α β : Type}

abbrev relabel (phase : FiniteBlockPhase α) (transform : List α → List β) : FiniteBlockPhase β :=
  ⟨phase.width,fun bits => (phase.value bits).map transform⟩

theorem relabel_combine (first second : FiniteBlockPhase α) (transform : List α → List β) :
    (combine first second).relabel transform=combine (first.relabel transform) (second.relabel transform) := by
  apply congrArg (fun value => (⟨first.width+(second.width+1),value⟩ : FiniteBlockPhase β))
  funext bits
  let sliced := fairOfferBitEquiv first.width second.width bits
  change (OptionPhase.fairOffer sliced.1 (first.value sliced.2.1) (second.value sliced.2.2)).map transform=
    OptionPhase.fairOffer sliced.1 ((first.value sliced.2.1).map transform) ((second.value sliced.2.2).map transform)
  generalize sliced.1=coin
  generalize first.value sliced.2.1=left
  generalize second.value sliced.2.2=right
  cases coin <;> cases left <;> cases right <;> rfl

theorem relabel_foldl (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α)
    (transform : List α → List β) :
    (phases.foldl combine initial).relabel transform=
      (phases.map (fun phase => phase.relabel transform)).foldl combine (initial.relabel transform) := by
  induction phases generalizing initial with
  | nil => rfl
  | cons phase phases ih =>
      simp only [List.foldl_cons,List.map_cons]
      rw [ih,relabel_combine]

theorem relabel_scan (phases : List (FiniteBlockPhase α)) (transform : List α → List β) :
    (scan phases).relabel transform=scan (phases.map (fun phase => phase.relabel transform)) := by
  exact relabel_foldl phases empty transform

theorem evaluate_relabel (phase : FiniteBlockPhase α) (transform : List α → List β) (bits : BitString) :
    (phase.relabel transform).evaluate bits=(phase.evaluate bits).map transform := by
  unfold evaluate
  by_cases enough : phase.width≤bits.length
  · simp only [relabel,dite_eq_left enough]
  · simp only [relabel,dite_eq_right enough,Option.map_none]

theorem concatenate_markers {γ : Type} (first second : FiniteBlockPhase α)
    (left right : List γ) :
    concatenate (first.relabel (fun _ => left)) (second.relabel (fun _ => right))=
      (concatenate first second).relabel (fun _ => left++right) := by
  apply congrArg (fun value => (⟨first.width+second.width,value⟩ : FiniteBlockPhase γ))
  funext bits
  let sliced := splitBitVector first.width second.width bits
  change OptionPhase.append ((first.value sliced.1).map (fun _ => left)) ((second.value sliced.2).map (fun _ => right))=
    (OptionPhase.append (first.value sliced.1) (second.value sliced.2)).map (fun _ => left++right)
  cases first.value sliced.1 <;> cases second.value sliced.2 <;> rfl

theorem relabel_marker {γ : Type} (phase : FiniteBlockPhase α) (payload : List β)
    (transform : List β → List γ) :
    (phase.relabel (fun _ => payload)).relabel transform=phase.relabel (fun _ => transform payload) := by
  apply congrArg (fun value => (⟨phase.width,value⟩ : FiniteBlockPhase γ))
  funext bits
  change ((phase.value bits).map (fun _ => payload)).map transform=(phase.value bits).map (fun _ => transform payload)
  cases phase.value bits <;> rfl

end ComplexityOfGenerators.FiniteBlockPhase
