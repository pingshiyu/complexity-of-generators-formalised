import ComplexityOfGenerators.Examples.SAT
import ComplexityOfGenerators.Foundations.FixedBitBlocks
import ComplexityOfGenerators.Simulation.WordStack.RandomInput

/-! A fixed four-coin native choice covers every SAT encoding symbol. Each
choice either consumes exactly four coins or exhausts its finite random tape. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Code := Command Symbol Symbol 35
abbrev Memory := Simulation.WordStack.Memory Symbol Symbol 35

def decodeSymbol (bits : BitString) : Symbol :=
  match FixedBitBlocks.decode bits with
  | 0 => .zero | 1 => .one | 2 => .separator | 3 => .trueConstant
  | 4 => .falseConstant | 5 => .positive | 6 => .negative | 7 => .openClause
  | 8 => .closeClause | _ => .zero

def symbolCode : Symbol → ℕ
  | .zero => 0 | .one => 1 | .separator => 2 | .trueConstant => 3
  | .falseConstant => 4 | .positive => 5 | .negative => 6 | .openClause => 7
  | .closeClause => 8

def encodeSymbol (symbol : Symbol) : BitString := FixedBitBlocks.encode 4 (symbolCode symbol)

@[simp] theorem encodeSymbol_length (symbol : Symbol) : (encodeSymbol symbol).length = 4 :=
  FixedBitBlocks.encode_length _ _

@[simp] theorem decode_encodeSymbol (symbol : Symbol) : decodeSymbol (encodeSymbol symbol) = symbol := by
  unfold decodeSymbol encodeSymbol
  rw [FixedBitBlocks.decode_encode _ _ (by cases symbol <;> decide)]
  cases symbol <;> rfl

def readLetter (dst : Fin 35) : ℕ → BitString → Code
  | 0, previous => Command.push dst (decodeSymbol previous.reverse)
  | remaining + 1, previous =>
      .random (readLetter dst remaining (false :: previous)) (readLetter dst remaining (true :: previous))

def afterLetter (dst : Fin 35) (previous : BitString) (remaining : ℕ) (bits : BitString) (m : Memory) : Memory :=
  {m.set dst (decodeSymbol (previous.reverse ++ (bits.drop m.randomHead).take remaining) :: m.store dst)
    with randomHead := m.randomHead + remaining}

theorem readLetter_full (dst : Fin 35) (remaining : ℕ) (previous : BitString)
    (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (available : m.randomHead + remaining ≤ bits.length) :
    (readLetter dst remaining previous).Runs n bits m (remaining + 1)
      (.done (afterLetter dst previous remaining bits m)) := by
  induction remaining generalizing previous m with
  | zero => simpa [readLetter, afterLetter, Memory.set] using Command.push_runs dst (decodeSymbol previous.reverse) bits m index
  | succ remaining ih =>
      have inside : m.randomHead < bits.length := by omega
      let bit := bits[m.randomHead]
      have rest := ih (bit :: previous) (Program.readBit m) index (by
        change m.randomHead + 1 + remaining ≤ bits.length
        omega)
      have window : (bits.drop m.randomHead).take (remaining + 1) =
          bit :: (bits.drop (m.randomHead + 1)).take remaining := by
        rw [List.drop_eq_getElem_cons inside, List.take_succ_cons]
      have final : afterLetter dst (bit :: previous) remaining bits (Program.readBit m) =
          afterLetter dst previous (remaining + 1) bits m := by
        apply Configuration.ext <;> try rfl
        · simp only [afterLetter, Program.readBit]; omega
        · simp [afterLetter, Memory.set, Program.readBit, window, List.reverse_cons, List.append_assoc]
      rw [final] at rest
      have selected : (if bit then readLetter dst remaining (true :: previous)
          else readLetter dst remaining (false :: previous)).Runs n bits (Program.readBit m)
          (remaining + 1) (.done (afterLetter dst previous (remaining + 1) bits m)) := by
        cases choice : bit <;> simpa only [choice, Bool.false_eq_true, ite_false, ite_true] using rest
      have run := Command.Runs.random m (readLetter dst remaining (false :: previous))
        (readLetter dst remaining (true :: previous)) bit (remaining + 1)
        (.done (afterLetter dst previous (remaining + 1) bits m)) (List.getElem?_eq_getElem inside) selected
      simpa only [readLetter, Nat.add_comm 1] using run

theorem readLetter_short (dst : Fin 35) (remaining : ℕ) (previous : BitString)
    (n : ℕ) (bits : BitString) (m : Memory) (index : m.indexHead ≤ n)
    (randomBound : m.randomHead ≤ bits.length)
    (short : bits.length < m.randomHead + remaining) :
    ∃ ticks ≤ remaining, (readLetter dst remaining previous).Runs n bits m ticks .exhausted := by
  induction remaining generalizing previous m with
  | zero => omega
  | succ remaining ih =>
      by_cases inside : m.randomHead < bits.length
      · let bit := bits[m.randomHead]
        obtain ⟨ticks, cost, rest⟩ := ih (bit :: previous) (Program.readBit m) index (by
          change m.randomHead + 1 ≤ bits.length
          omega) (by
          change bits.length < m.randomHead + 1 + remaining
          omega)
        refine ⟨1 + ticks, by omega, ?_⟩
        apply Command.Runs.random m _ _ bit ticks .exhausted (List.getElem?_eq_getElem inside)
        cases choice : bit <;> simpa only [choice, Bool.false_eq_true, ite_false, ite_true] using rest
      · exact ⟨0, Nat.zero_le _, Command.Runs.random_absent m _ _ (List.getElem?_eq_none (by omega))⟩

end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
