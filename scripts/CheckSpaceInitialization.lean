import ComplexityOfGenerators.Simulation.SavitchMachine.Initialize
import ComplexityOfGenerators.Simulation.SavitchMachine.CoordinateDecode

/-! Execute the actual finite initialization and coordinate-decoding programs.
The universal correctness and space bounds are kernel-checked in the imported
modules; these checks exercise their composed control tables on small inputs. -/

open ComplexityOfGenerators Simulation StackSpace SavitchMachine Complexity

namespace SpaceInitializationChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def execute {S Q V : Type} {k : ℕ} (P : Q → Stmt S Q V k) :
    ℕ → Source S Q V k → Option (Source S Q V k)
  | 0, _ => none
  | fuel + 1, c => match Turing.TM2.step P c with
      | none => some c
      | some next => execute P fuel next

def coordinate (bits : List Bool) (bound : ℕ) : Bool :=
  let initial := localConfig CoordinateDecode.Label.copyInput (carrying false false)
    (BoundedDecode.registers (bits.reverse.map some) 0 bound)
  (execute CoordinateDecode.program 20000 initial).any fun final =>
    decide (final.var.1.returned = some ((FixedWidthCodec.fin bound).decode bits).isSome) &&
    decide (final.stk 2 = BoundedDecode.unary bound) && decide (final.stk 3 = [] ∧ final.stk 4 = []) &&
    match (FixedWidthCodec.fin bound).decode bits with
    | none => decide ((final.stk 1).length ≤ bound)
    | some value => decide (final.stk 1 = BoundedDecode.unary value.val ∧ final.stk 0 = [])

#guard coordinate [] 0
#guard coordinate [] 1
#guard coordinate [false] 1
#guard coordinate [true] 1
#guard coordinate [false, false] 1
#guard coordinate (bitsOfLenLE 3 0) 3
#guard coordinate (bitsOfLenLE 3 2) 3
#guard coordinate (bitsOfLenLE 3 3) 3
#guard coordinate (bitsOfLenLE 4 15) 4
#guard coordinate (bitsOfLenLE 8 7) 8
#guard coordinate (bitsOfLenLE 8 255) 8

-- Five input symbols are distinct from the three interpreter symbols.
abbrev Alphabet := Sum (Fin 5) Frames.Symbol

def write : Frames.Symbol → Alphabet := Sum.inr
def read : Alphabet → Frames.Symbol := Sum.elim (fun _ => none) id

def initialized (space depth : PolynomialBound) (word : List Alphabet) : Bool :=
  let state := [true, false, true]
  let P := Initialize.program write read state 2 space depth
  let initial := sourceInitial (Initialize.Label.load) (carrying false false, none) word
  (execute P 100000 initial).any fun final =>
    let frame := Root.frame (depth word.length) (InitialVertex.code state 2 word.length (space word.length))
    decide (final.var.1 = status ⟨false, false, none, []⟩) && decide (final.var.2 = none) &&
    decide (final.stk (Fin.last 12) = word) &&
    decide (∀ j : Fin 12, final.stk j.castSucc = (Frames.memory [frame] (fun _ => []) j).map write)

#guard initialized ⟨1, 0, by decide⟩ ⟨1, 0, by decide⟩ []
#guard initialized ⟨1, 1, by decide⟩ ⟨1, 1, by decide⟩ [Sum.inl 0]
#guard initialized ⟨1, 1, by decide⟩ ⟨2, 1, by decide⟩ [Sum.inl 4, Sum.inl 2, Sum.inl 0]
#guard initialized ⟨2, 2, by decide⟩ ⟨1, 0, by decide⟩ [Sum.inl 1, Sum.inl 3]

end SpaceInitializationChecks
