import ComplexityOfGenerators.Foundations.RandomTape

/-! A clock-for-clock simulation needs only compatibility with observation and
one primitive transition. Both prepared configurations and initial runs share
this induction, including terminal observation after the final transition. -/

namespace ComplexityOfGenerators.Machine

variable {I A O J B P : Type} {M : Machine I A O} {N : Machine J B P}
  {sourceData : InputData I A} {targetData : InputData J B} {sourceBits targetBits : BitString}
  {config : Configuration M → Configuration N} {outcome : Outcome O → Outcome P}
  {lift : RunState M → RunState N}

theorem runFrom_map
    (running : ∀ c, lift (.running c) = .running (config c))
    (halted : ∀ r, lift (.halted r) = .halted (outcome r))
    (observe : ∀ c, N.observe targetData targetBits (config c) = lift (M.observe sourceData sourceBits c))
    (next : ∀ c, N.next targetData targetBits (config c) = lift (M.next sourceData sourceBits c))
    (start : Configuration M) (t : ℕ) :
    N.runFrom targetData targetBits (config start) t = lift (M.runFrom sourceData sourceBits start t) := by
  induction t with
  | zero => exact observe start
  | succ t ih =>
      simp only [runFrom, ih]
      cases M.runFrom sourceData sourceBits start t with
      | halted r => simp only [halted]
      | running c =>
          simp only [running, next]
          cases M.next sourceData sourceBits c with
          | halted r => simp only [halted]
          | running d => simpa only [running] using observe d

theorem run_map
    (running : ∀ c, lift (.running c) = .running (config c))
    (halted : ∀ r, lift (.halted r) = .halted (outcome r))
    (observe : ∀ c, N.observe targetData targetBits (config c) = lift (M.observe sourceData sourceBits c))
    (next : ∀ c, N.next targetData targetBits (config c) = lift (M.next sourceData sourceBits c))
    (initial : config M.initialConfiguration = N.initialConfiguration) (t : ℕ) :
    N.run targetData targetBits t = lift (M.run sourceData sourceBits t) := by
  simpa only [initial, runFrom_initial] using runFrom_map running halted observe next M.initialConfiguration t

end ComplexityOfGenerators.Machine
