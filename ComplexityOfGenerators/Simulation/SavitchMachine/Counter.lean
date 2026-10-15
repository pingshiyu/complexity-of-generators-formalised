import ComplexityOfGenerators.Simulation.StackSpace.Trace
import Complexitylib.Classes.Containments.Internal.SavitchBits

/-!
# The midpoint counter as a finite stack program

This implements Complexitylib's little-endian Savitch counter, including its
overflow flag. Two stacks suffice: the counter and a temporary reversed copy.
Every source configuration uses at most the original counter width per stack.
`StackSpace.Trace.compile` includes the compiler's intermediate native work.
-/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.Counter

open Turing StackSpace

set_option backward.isDefEq.respectTransparency false

inductive Label
  | scan | restore | finish
  deriving DecidableEq, Fintype

abbrev Local := Bool × Option Bool
abbrev Config := Source Bool Label Local 1

def program : Label → Stmt Bool Label Local 1
  | .scan => .pop 0 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.push 1 (fun v => xor v.1 (v.2.getD false))
          (.load (fun v => (v.1 && v.2.getD false, none)) (.goto fun _ => .scan)))
        (.goto fun _ => .restore))
  | .restore => .pop 1 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome)
        (.push 0 (fun v => v.2.getD false)
          (.load (fun v => (v.1, none)) (.goto fun _ => .restore)))
        (.goto fun _ => .finish))
  | .finish => .halt

def config (label : Label) (carry : Bool) (word acc : List Bool) : Config :=
  ⟨some label, (carry, none), ![word, acc]⟩

theorem config_bound (label : Label) (carry : Bool) (word acc : List Bool) (r : ℕ)
    (size : word.length + acc.length ≤ r) : Within r (config label carry word acc) := by
  intro j
  fin_cases j <;> simp [config] <;> omega

theorem scan_nil (carry : Bool) (acc : List Bool) :
    TM2.step program (config .scan carry [] acc) = some (config .restore carry [] acc) := by
  simp [TM2.step, TM2.stepAux, program, config]

theorem scan_cons (carry bit : Bool) (word acc : List Bool) :
    TM2.step program (config .scan carry (bit :: word) acc) =
      some (config .scan (carry && bit) word (xor carry bit :: acc)) := by
  simp [TM2.step, TM2.stepAux, program, config, Function.update_apply, funext_iff, Fin.forall_fin_succ]

theorem restore_nil (carry : Bool) (word : List Bool) :
    TM2.step program (config .restore carry word []) = some (config .finish carry word []) := by
  simp [TM2.step, TM2.stepAux, program, config]

theorem restore_cons (carry bit : Bool) (word acc : List Bool) :
    TM2.step program (config .restore carry word (bit :: acc)) =
      some (config .restore carry (bit :: word) acc) := by
  simp [TM2.step, TM2.stepAux, program, config, Function.update_apply, funext_iff, Fin.forall_fin_succ]

/-- Each scan step reads one bit, updates the carry in finite control and
pushes one result bit. No operation on a whole counter is a machine instruction. -/
theorem scan_trace (carry : Bool) (word acc : List Bool) (r : ℕ)
    (size : word.length + acc.length ≤ r) :
    Trace program r (config .scan carry word acc)
      (config .restore (Complexity.addBit carry word).1 []
        ((Complexity.addBit carry word).2.reverse ++ acc)) := by
  induction word generalizing carry acc with
  | nil =>
      exact .step (config_bound _ _ _ _ r size) (scan_nil carry acc)
        (.refl _ (config_bound _ _ _ _ r size))
  | cons bit word ih =>
      have tail := ih (carry && bit) (xor carry bit :: acc) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using size)
      have first := Trace.step (config_bound _ _ _ _ r size) (scan_cons carry bit word acc) tail
      simpa [Complexity.addBit, List.reverse_cons, List.append_assoc] using first

theorem restore_trace (carry : Bool) (word acc : List Bool) (r : ℕ)
    (size : word.length + acc.length ≤ r) :
    Trace program r (config .restore carry word acc) (config .finish carry (acc.reverse ++ word) []) := by
  induction acc generalizing word with
  | nil =>
      exact .step (config_bound _ _ _ _ r size) (restore_nil carry word)
        (.refl _ (config_bound _ _ _ _ r size))
  | cons bit acc ih =>
      have tail := ih (bit :: word) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using size)
      have first := Trace.step (config_bound _ _ _ _ r size) (restore_cons carry bit word acc) tail
      simpa [List.reverse_cons, List.append_assoc] using first

/-- Exact agreement with the two counter operations used by the existing
Savitch proof, also at width zero and at overflow. -/
theorem counter_trace (word : List Bool) :
    Trace program word.length (config .scan true word [])
      (config .finish (Complexity.bumpOver word) (Complexity.bumpBits word) []) := by
  have scan := scan_trace true word [] word.length (by simp)
  have restore := restore_trace (Complexity.addBit true word).1 []
    ((Complexity.addBit true word).2.reverse ++ []) word.length (by simp)
  simpa [Complexity.bumpOver, Complexity.bumpBits] using scan.trans restore

noncomputable section

/-- The counter executes on the real tape-bank machine inside a fixed region.
The arbitrary physical input and random tape are never read by this routine. -/
theorem counter_bank (word input : List Bool) (bits : BitString) :
    ∃ ticks, (bank program .scan (true, none) Prod.fst).RegionSteps
      (decisionData input) bits (word.length + programCost program)
      (ready program input.length (config .scan true word [])) ticks
      (ready program input.length
        (config .finish (Complexity.bumpOver word) (Complexity.bumpBits word) [])) :=
  (counter_trace word).compile .scan (true, none) Prod.fst input bits

/-- The same routine on the retained single-work-tape machine. It preserves
the region even when called repeatedly during midpoint enumeration. -/
theorem counter_native (word input : List Bool) (bits : BitString)
    (sides : Fin 2 → Bool)
    (start : Configuration (machine program .scan (true, none) Prod.fst))
    (related : TransducerBank.BankReady (bank program .scan (true, none) Prod.fst)
      (ready program input.length (config .scan true word [])) sides start)
    (region : (machine program .scan (true, none) Prod.fst).InRegion
      (word.length + programCost program) start) :
    ∃ ticks finish signs,
      TransducerBank.BankReady (bank program .scan (true, none) Prod.fst)
        (ready program input.length
          (config .finish (Complexity.bumpOver word) (Complexity.bumpBits word) [])) signs finish ∧
      (machine program .scan (true, none) Prod.fst).Steps (decisionData input) bits start ticks finish ∧
      (machine program .scan (true, none) Prod.fst).InRegion
        (word.length + programCost program) finish := by
  obtain ⟨ticks, path⟩ := counter_bank word input bits
  exact path.compile _ sides start related region

end
end ComplexityOfGenerators.Simulation.SavitchMachine.Counter
