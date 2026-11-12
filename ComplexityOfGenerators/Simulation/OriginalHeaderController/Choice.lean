import ComplexityOfGenerators.Simulation.OriginalHeaderController.Basic

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
abbrev Request := Bool × ℕ

def allowed (e : Event) (index : ℕ) : Prop := e.2=decide (index=0)
def eventList (requests : List Request) : List (Event×ℕ) :=
  requests.map (fun entry => ((entry.1,decide (entry.2=0)),entry.2))

def Choice : Operation → ℕ → List Bool → List Request → Prop
  | .union,n,header,requests => ∃ tag,header=List.replicate (n+1) tag ∧ requests=[(tag,n)]
  | .concatenation,n,header,requests => ∃ j≤n,
      header=List.replicate (j+1) false++List.replicate (n-j+1) true ∧ requests=[(false,j),(true,n-j)]

theorem Choice.indices {operation : Operation} {n : ℕ} {header : List Bool} {requests : List Request}
    (choice : Choice operation n header requests) : ∀ entry∈requests,entry.2≤n := by
  cases operation with
  | union =>
      obtain ⟨tag,_,rfl⟩ := choice
      simp
  | concatenation =>
      obtain ⟨j,within,_,rfl⟩ := choice
      intro entry member
      rcases List.mem_cons.mp member with equal|member
      · simpa only [equal] using within
      · have equal := List.mem_singleton.mp member
        simpa only [equal] using Nat.sub_le n j

theorem Choice.length {operation : Operation} {n : ℕ} {header : List Bool} {requests : List Request}
    (choice : Choice operation n header requests) : requests.length≤2 := by
  cases operation with
  | union => obtain ⟨_,_,rfl⟩ := choice; simp
  | concatenation => obtain ⟨_,_,_,rfl⟩ := choice; exact le_rfl

theorem Choice.header_length {operation : Operation} {n : ℕ} {header : List Bool} {requests : List Request}
    (choice : Choice operation n header requests) : header.length≤n+2 := by
  cases operation with
  | union => obtain ⟨_,rfl,_⟩ := choice; simp
  | concatenation =>
      obtain ⟨j,within,rfl,_⟩ := choice
      simp only [List.length_append,List.length_replicate]
      omega

end ComplexityOfGenerators.Simulation.OriginalHeaderController
