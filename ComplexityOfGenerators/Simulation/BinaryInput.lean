import ComplexityOfGenerators.Simulation.OutputEncoding

/-!
# Native random initialization for a recursive program

This finite transition table samples a candidate code, then a clock, in their
canonical binary representations. It writes the stack initialization for
`[clock, candidate]`, rewinds to the reserved marker and enters the compiled
Post program. Every request consumes one random bit and every write changes
one cell. Random-tape exhaustion is the original model's exhaustion outcome.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

inductive BinaryInputControl (states : ℕ)
  | start
  | mark
  | bottom
  | select : Bool → BinaryInputControl states
  | flag : Bool → BinaryInputControl states
  | digit : Bool → BinaryInputControl states
  | write : Bool → Bool → BinaryInputControl states
  | finish : Bool → BinaryInputControl states
  | rewind
  | run : Fin states → BinaryInputControl states
  deriving Fintype

def binaryInputControl {states : ℕ} :
    BinaryInputControl states ≃ Fin (Fintype.card (BinaryInputControl states)) := Fintype.equivFin _

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}

theorem recursiveInput_pair (clock candidate : ℕ) :
    recursiveInput [clock, candidate] = [stackBottom .cons] ++
      (PartrecToTM2.trNat candidate).reverse.map stackLetter ++ [stackLetter .cons] ++
      (PartrecToTM2.trNat clock).reverse.map stackLetter := by
  have reverse : (PartrecToTM2.trList [clock, candidate]).reverse = .cons ::
      ((PartrecToTM2.trNat candidate).reverse ++ .cons :: (PartrecToTM2.trNat clock).reverse) := by
    simp [PartrecToTM2.trList, List.reverse_append]
  unfold recursiveInput TM2to1.trInit
  rw [reverse]
  dsimp only
  simp [stackBottom, stackLetter, List.append_assoc]
  rfl

def binaryInputInstruction (program : TM0.Machine RecursiveAlphabet Q)
    (control : Q ≃ Fin states) (alphabet : RecursiveAlphabet ≃ Fin symbols)
    (phase : BinaryInputControl states) (work : Option (Fin (symbols + 1))) :
    Instruction Unit (Fintype.card (BinaryInputControl states)) (symbols + 1) :=
  let state := binaryInputControl
  match phase with
  | .start => .step (state .mark) none .left .stay .stay .stay none
  | .mark => .step (state .bottom) (some (Fin.last symbols)) .right .stay .stay .stay none
  | .bottom => .step (state (.select false)) (some (bootEncode alphabet (stackBottom .cons)))
      .right .stay .stay .stay none
  | .select family => .readRandom (state (.finish family)) (state (.write family true))
  | .flag family => .readRandom (state (.finish family)) (state (.digit family))
  | .digit family => .readRandom (state (.write family false)) (state (.write family true))
  | .write family bit => .step (state (.flag family))
      (some (bootEncode alphabet (stackLetter (if bit then .bit1 else .bit0))))
      .right .stay .stay .stay none
  | .finish false => .step (state (.select true)) (some (bootEncode alphabet (stackLetter .cons)))
      .right .stay .stay .stay none
  | .finish true => .step (state .rewind) none .stay .stay .stay .stay none
  | .rewind => if work = some (Fin.last symbols) then
      .step (state (.run (control default))) none .right .stay .stay .stay none
    else .step (state .rewind) none .left .stay .stay .stay none
  | .run q => postInstruction (fun q => state (.run (control q))) (bootEncode alphabet)
      (program (control.symm q) (bootDecode alphabet work))

def binaryInputMachine (program : TM0.Machine RecursiveAlphabet Q)
    (control : Q ≃ Fin states) (alphabet : RecursiveAlphabet ≃ Fin symbols) : Machine Unit Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (BinaryInputControl states)
  symbols := symbols + 1
  initial := binaryInputControl .start
  transition := fun q _ _ _ work => binaryInputInstruction program control alphabet
    (binaryInputControl.symm q) work

/-- The execution core is an actual Post simulator, sharing the sampler's tape
alphabet and finite control. The source's initial configuration is supplied by
the preceding random-input routine. -/
def binaryInputSimulator (program : TM0.Machine RecursiveAlphabet Q)
    (control : Q ≃ Fin states) (alphabet : RecursiveAlphabet ≃ Fin symbols) :
    PostSimulator program Unit where
  machine := binaryInputMachine program control alphabet
  control := fun q => binaryInputControl (.run (control q))
  encode := bootEncode alphabet
  decode := bootDecode alphabet
  writeCorrect := bootDecode_encode alphabet
  transitionCorrect := by
    intro q input auxiliary index work
    simp [binaryInputMachine, binaryInputInstruction]

theorem binaryInputMachine_never_rejects (program : TM0.Machine RecursiveAlphabet Q)
    (control : Q ≃ Fin states) (alphabet : RecursiveAlphabet ≃ Fin symbols)
    (phase : BinaryInputControl states)
    (work : Option (Fin (symbols + 1))) :
    binaryInputInstruction program control alphabet phase work ≠ .reject := by
  cases phase <;> simp only [binaryInputInstruction]
  all_goals try simp
  · rename_i family
    cases family <;> simp
  · split_ifs <;> simp
  · rename_i q
    cases program (control.symm q) (bootDecode alphabet work) with
    | none => simp [postInstruction]
    | some action => rcases action with ⟨q, action⟩; cases action <;> simp [postInstruction]

end

end ComplexityOfGenerators.Simulation
