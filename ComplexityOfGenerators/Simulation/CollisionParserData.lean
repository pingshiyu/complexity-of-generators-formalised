import ComplexityOfGenerators.Simulation.CollisionBankMemory
import ComplexityOfGenerators.Simulation.TapeBankRewind

namespace ComplexityOfGenerators.Simulation

/-- Binary encoding of a string of ordinary pair symbols, without a separator. -/
def collisionBits (xs : BitString) : BitString := xs.flatMap (fun b => [false, b])

@[simp] theorem collisionBits_nil : collisionBits [] = [] := rfl
@[simp] theorem collisionBits_cons (b : Bool) (xs : BitString) :
    collisionBits (b :: xs) = false :: b :: collisionBits xs := rfl
@[simp] theorem collisionBits_append (xs ys : BitString) :
    collisionBits (xs ++ ys) = collisionBits xs ++ collisionBits ys := by simp [collisionBits]
@[simp] theorem collisionBits_length (xs : BitString) : (collisionBits xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]; omega

def splitCollisionInput : BitString → Option (BitString × BitString)
  | false :: b :: rest => (splitCollisionInput rest).map (fun pair => (b :: pair.1, pair.2))
  | true :: false :: rest => some ([], rest)
  | _ => none

def readCollisionBits : BitString → Option BitString
  | [] => some []
  | false :: b :: rest => (readCollisionBits rest).map (b :: ·)
  | _ => none

theorem splitCollisionInput_encoded (xs rest : BitString) :
    splitCollisionInput (collisionBits xs ++ true :: false :: rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [splitCollisionInput, ih]

theorem readCollisionBits_encoded (xs : BitString) : readCollisionBits (collisionBits xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [readCollisionBits, ih]

theorem splitCollisionInput_sound (word xs rest : BitString)
    (h : splitCollisionInput word = some (xs, rest)) :
    word = collisionBits xs ++ true :: false :: rest := by
  induction word using splitCollisionInput.induct generalizing xs with
  | case1 b word ih =>
      cases read : splitCollisionInput word with
      | none => simp [splitCollisionInput, read] at h
      | some pair =>
          have eq : (b :: pair.1, pair.2) = (xs, rest) := by simpa [splitCollisionInput, read] using h
          have second := congrArg Prod.snd eq
          have first := congrArg Prod.fst eq
          obtain ⟨x, tail⟩ := pair
          dsimp at second first
          subst tail xs
          simp [ih x read]
  | case2 word =>
      have eq : ([], word) = (xs, rest) := by simpa [splitCollisionInput] using h
      cases eq
      rfl
  | case3 word bad bad' => simp [splitCollisionInput] at h

noncomputable section
variable (M : Machine Bool Bool Bool)

def collisionLoadedTapes (x y : BitString) : Fin 7 → ℤ → CollisionCell M.symbols :=
  Function.update (Function.update (Function.update (fun _ _ => collisionBlank M)
    0 (collisionWord M x)) 1 (collisionWord M y)) 2
      (collisionWord M (List.replicate (x.length - 1) true))

def collisionXConfiguration (x : BitString) :
    BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 where
  state := .xHeader (!x.isEmpty)
  inputHead := 2 * x.length
  head := Function.update (Function.update (fun _ => 0) 0 x.length) 2 (x.length - 1 : ℕ)
  tape := collisionLoadedTapes M x []

def collisionYConfiguration (x y : BitString) :
    BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 where
  state := .yHeader (decide (x.take y.length ≠ y))
  inputHead := 2 * x.length + 2 + 2 * y.length
  head := Function.update (Function.update (Function.update (fun _ => 0) 0 y.length) 1 y.length)
    2 (x.length - 1 : ℕ)
  tape := collisionLoadedTapes M x y

def collisionParsedConfiguration (word x y : BitString) :
    BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 where
  state := .hashWork false M.initial
  inputHead := word.length
  head := fun _ => 0
  tape := collisionLoadedTapes M x y

@[simp] theorem collisionX_initial : collisionXConfiguration M [] = (collisionBank M).initialConfiguration := by
  apply BankConfiguration.ext
  · rfl
  · rfl
  · funext j
    simp [collisionXConfiguration, TapeBank.initialConfiguration, Function.update_eq_self]
  · funext j i
    simp [collisionXConfiguration, collisionLoadedTapes, TapeBank.initialConfiguration, collisionBank,
      Function.update_eq_self]

end
end ComplexityOfGenerators.Simulation
