import ComplexityOfGenerators.Simulation.CollisionHashInitialize
import ComplexityOfGenerators.Simulation.CollisionCompare

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The complete computation after parsing: two actual hash simulations,
explicit resets, and comparison of the two output tapes. -/
theorem collision_hash_pair (h : HashFunction) (word : BitString) (n : ℕ) (a b : Bits (n + 1)) :
    ∃ t, t ≤ 12 * h.time n + 5 * n + 10 ∧
      (collisionBank h.implementation).Executes word
        (collisionParsedConfiguration h.implementation word (bitsWord a) (bitsWord b)) t
        (decide (h.hash n a = h.hash n b)) := by
  let M := h.implementation
  let B := collisionBank M
  let initial := collisionParsedConfiguration M word (bitsWord a) (bitsWord b)
  have initialEq : hashBankConfiguration M false initial M.initialConfiguration = initial := by
    have equal := hashBankConfiguration_initial M false initial rfl rfl rfl rfl
      (by simp [initial, collisionParsedConfiguration, collisionLoadedTapes, hashWorkTape])
      (by simp [initial, collisionParsedConfiguration, collisionLoadedTapes, hashOutputTape])
    exact equal
  obtain ⟨s, firstLast, cost₁, output₁, index₁, run₁⟩ := collision_hash_runFrom M h.deterministic word false
    initial (bitsWord a) n (by rfl)
    (by simp [initial, collisionParsedConfiguration, collisionLoadedTapes, hashInputTape])
    (by simp [initial, collisionParsedConfiguration, collisionLoadedTapes])
    (h.time n) M.initialConfiguration (bitsWord (h.hash n a)) ⟨by simp [Machine.initialConfiguration],
      by simp [Machine.initialConfiguration], by simp [Machine.initialConfiguration]⟩
    (by simpa using h.run_at_hash_bound n a)
  rw [initialEq] at run₁
  let first : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {hashBankConfiguration M false initial firstLast with state := .resetIndex}
  let second : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {first with state := .hashWork true M.initial, head := Function.update first.head 2 0}
  have resetIndex : B.Steps word first (firstLast.indexHead + 1) second :=
    TapeBank.rewind B word .resetIndex (.hashWork true M.initial) 2 rfl
      (fun _ _ _ => rfl) firstLast.indexHead first rfl (by simp [first]) (by rfl)
  have secondEq : hashBankConfiguration M true second M.initialConfiguration = second := by
    have equal := hashBankConfiguration_initial M true second
      (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
        hashInputTape, hashWorkTape, hashOutputTape])
      (by simp [second])
      (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
        hashInputTape, hashWorkTape, hashOutputTape])
      (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
        hashInputTape, hashWorkTape, hashOutputTape])
      (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
        collisionLoadedTapes, hashWorkTape, hashOutputTape])
      (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
        collisionLoadedTapes, hashWorkTape, hashOutputTape])
    exact equal
  obtain ⟨u, secondLast, cost₂, output₂, index₂, run₂⟩ := collision_hash_runFrom M h.deterministic word true
    second (bitsWord b) n (by rfl)
    (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
      collisionLoadedTapes, hashInputTape, hashWorkTape, hashOutputTape])
    (by simp [second, first, hashBankConfiguration, initial, collisionParsedConfiguration,
      collisionLoadedTapes, hashWorkTape, hashOutputTape])
    (h.time n) M.initialConfiguration (bitsWord (h.hash n b)) ⟨by simp [Machine.initialConfiguration],
      by simp [Machine.initialConfiguration], by simp [Machine.initialConfiguration]⟩
    (by simpa using h.run_at_hash_bound n b)
  rw [secondEq] at run₂
  let done : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {hashBankConfiguration M true second secondLast with state := .resetOutput false}
  let leftReset : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {done with state := .resetOutput true, head := Function.update done.head 5 0}
  let compare : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {leftReset with state := .compareLeft, head := Function.update leftReset.head 6 0}
  have firstLength : firstLast.output.length = n := by simp [output₁]
  have secondLength : secondLast.output.length = n := by simp [output₂]
  have resetLeft : B.Steps word done (n + 1) leftReset :=
    TapeBank.rewind B word (.resetOutput false) (.resetOutput true) 5 rfl
      (fun _ _ _ => rfl) n done rfl
      (by simp [done, second, first, hashBankConfiguration, hashInputTape, hashWorkTape, hashOutputTape, firstLength])
      (by rfl)
  have resetRight : B.Steps word leftReset (n + 1) compare :=
    TapeBank.rewind B word (.resetOutput true) .compareLeft 6 rfl
      (fun _ _ _ => rfl) n leftReset rfl (by simp [leftReset, done, hashBankConfiguration, hashOutputTape, secondLength])
      (by rfl)
  obtain ⟨v, cost₃, compared⟩ := collision_compare M word (bitsWord (h.hash n a)) (bitsWord (h.hash n b)) 0 compare
    rfl (by rfl) (by simp [compare, leftReset]) (by simp [compare])
    (fun i => by simp [compare, leftReset, done, second, first, hashBankConfiguration, hashWorkTape, hashOutputTape, output₁])
    (fun i => by simp [compare, leftReset, done, hashBankConfiguration, hashOutputTape, output₂])
  have path := (((run₁.trans B resetIndex).trans B run₂).trans B resetLeft).trans B resetRight
  refine ⟨s + (firstLast.indexHead + 1) + u + (n + 1) + (n + 1) + v, ?_, ?_⟩
  · simp only [bitsWord_length] at cost₃
    omega
  · simpa only [bitsWord_inj] using path.executes B compared

end
end ComplexityOfGenerators.Simulation
