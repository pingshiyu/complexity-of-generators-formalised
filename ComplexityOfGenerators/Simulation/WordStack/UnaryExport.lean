import ComplexityOfGenerators.Simulation.WordStack.Compiler
import ComplexityOfGenerators.Simulation.WordStack.Local
import ComplexityOfGenerators.Simulation.TransducerBank.Compiler

/-! A positive unary parameter exported by one word stack occupies rows
`0,...,j-1`: row zero is the shared origin and rows `1,...,j-1` are stack cells.
Head-marker changes do not affect this predicate. -/
namespace ComplexityOfGenerators.Simulation.WordStack
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ}
    [Fintype I] [Fintype A] [Fintype O] [Fintype Q] [Fintype S]
    (B : TapeBank I A O Q (Option S) k)

def unaryExport (slot : Fin k) (raw : Option (Fin (Fintype.card (BankCell (Option S) k)))) : Bool :=
  (bankRead B raw).origin || ((bankRead B raw).symbol slot).isSome

theorem tape_replicate_isSome (symbol : S) (length position : ℕ) :
    (tape (List.replicate length symbol) (position : ℤ)).isSome = decide (0<position ∧ position≤length) := by
  cases position with
  | zero => simp
  | succ position =>
      simp [tape,List.reverse_replicate,List.getElem?_replicate]
      split_ifs <;> simp_all

theorem unaryExport_memory (slot : Fin k) (store : Local.Store S k)
    (heads : Fin k → Option ℤ) (memory) (length : ℕ) (symbol : S)
    (positive : 0<length) (exported : store slot=List.replicate (length-1) symbol)
    (represented : BankMemory B (fun j=>tape (store j)) heads memory) :
    ∀ position : ℕ, unaryExport B slot (memory position)=decide (position<length) := by
  intro position
  simp only [unaryExport,represented position,bankCell,exported,tape_replicate_isSome]
  cases position with
  | zero => simp [positive]
  | succ position =>
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true,decide_eq_true_eq]
      omega

end
end ComplexityOfGenerators.Simulation.WordStack
