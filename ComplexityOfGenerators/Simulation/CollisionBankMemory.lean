import ComplexityOfGenerators.Simulation.CollisionBank

namespace ComplexityOfGenerators.Simulation

noncomputable section
variable (M : Machine Bool Bool Bool)

/-- A finite word occupies positions `0,...,length-1` on a two-way tape. -/
def collisionWord (word : BitString) (i : ℤ) : CollisionCell M.symbols :=
  ⟨if 0 ≤ i then word[i.toNat]? else none, none⟩

@[simp] theorem collisionWord_nat (word : BitString) (i : ℕ) :
    collisionWord M word i = ⟨word[i]?, none⟩ := by simp [collisionWord]

@[simp] theorem collisionWord_nil : collisionWord M [] = fun _ => collisionBlank M := by
  funext i
  simp [collisionWord, collisionBlank]

@[simp] theorem collisionWord_end (word : BitString) :
    collisionWord M word word.length = collisionBlank M := by
  simp [collisionBlank]

theorem collisionWord_append (word : BitString) (b : Bool) :
    Function.update (collisionWord M word) (word.length : ℤ) (collisionBit M b) =
      collisionWord M (word ++ [b]) := by
  funext i
  cases i with
  | ofNat n =>
    by_cases inside : n < word.length
    · have ne : (n : ℤ) ≠ (word.length : ℤ) := by omega
      simp [Function.update_of_ne ne, List.getElem?_append_left inside]
    · by_cases atEnd : n = word.length
      · simp [atEnd, collisionBit, List.getElem?_append_right]
      · have outside : word.length + 1 ≤ n := by omega
        have ne : (n : ℤ) ≠ (word.length : ℤ) := by omega
        simp [Function.update_of_ne ne, List.getElem?_eq_none (by omega : word.length ≤ n),
          List.getElem?_eq_none (by simpa using outside : (word ++ [b]).length ≤ n)]
  | negSucc n =>
    have ne : Int.negSucc n ≠ (word.length : ℤ) := by omega
    simp [Function.update_of_ne ne, collisionWord]

theorem collisionReadMove_correct (word : BitString) (head : ℕ) (bound : head ≤ word.length)
    (move : Move) :
    (collisionReadMove (decide ((head : ℤ) = 0)) word[head]? move).onInt head =
      ((move.onInput word.length head : ℕ) : ℤ) := by
  cases move with
  | left =>
      by_cases zero : head = 0 <;>
        simp [collisionReadMove, Move.onInt, Move.onInput, zero] <;> omega
  | stay => simp [collisionReadMove, Move.onInt, Move.onInput, Nat.min_eq_left bound]
  | right =>
      by_cases inside : head < word.length
      · simp [collisionReadMove, List.getElem?_eq_getElem inside, Move.onInt, Move.onInput]
        omega
      · have equal : head = word.length := by omega
        simp [collisionReadMove, equal, Move.onInt, Move.onInput]

def hashInputTape (second : Bool) : Fin 7 := if second then 1 else 0
def hashWorkTape (second : Bool) : Fin 7 := if second then 4 else 3
def hashOutputTape (second : Bool) : Fin 7 := if second then 6 else 5

/-- A snapshot of a native hash computation, embedded in a tape bank. Other
tapes are inherited verbatim from `frame`, so the second hash preserves the
first hash's stored output. -/
def hashBankConfiguration (second : Bool)
    (frame : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7)
    (source : Configuration M) : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 where
  state := .hashWork second source.state
  inputHead := frame.inputHead
  head := Function.update (Function.update (Function.update (Function.update frame.head
    (hashInputTape second) source.inputHead) 2 source.indexHead)
    (hashWorkTape second) source.workHead) (hashOutputTape second) source.output.length
  tape := Function.update (Function.update frame.tape (hashWorkTape second)
    (fun i => ⟨none, source.work i⟩)) (hashOutputTape second) (collisionWord M source.output)

end
end ComplexityOfGenerators.Simulation
