import ComplexityOfGenerators.Simulation.PairCollisionDecisionBasic

namespace ComplexityOfGenerators.Simulation.PairCollisionDecision
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (M : Machine Bool Bool Unit)

def snapshot (p : PolynomialBound) (word : List PairSymbol) : Source.Snapshot M :=
  (Source.Snapshot.step M)^[sourceClock p word.length]
    (Source.initial M (decisionData (binaryPairWord word)) [])

theorem final_bank (p : PolynomialBound) (word : List PairSymbol) :
    (routine M p).eval (loaded M word).store ∘ Source.bank sourceSlots=
      Local.mapStore Cell.source ((snapshot M p word).store M) := by
  change (call M).eval (prepared M p word) ∘ Source.bank sourceSlots=_
  have bank := Source.call_bank (Output:=Unit) M sourceSlots Cell.source (sourceDecode M)
    (by intro symbol;rfl) id id id (prepared M p word) (decisionData (binaryPairWord word)) []
    (prepared_input M p word) (by simp [prepared_auxiliary,decisionData]) (prepared_index M p word)
    (by simp [prepared_bits])
  change (call M).eval (prepared M p word) ∘ Source.bank sourceSlots=
    Local.mapStore Cell.source (((Source.Snapshot.step M)^[(prepared M p word 16).length]
      (Source.initial M (decisionData (binaryPairWord word)) [])).store M) at bank
  rw [prepared_clock] at bank
  exact bank

def accepted : Option (Cell M)→Bool
  | some (.source (.state .accepted))=>true
  | _=>false

def checks : Program.BooleanChecks (Cell M) 32 := fun _=>(0,accepted M)

theorem checks_eq (p : PolynomialBound) (word : List PairSymbol) :
    Program.checksPass (checks M) ((routine M p).eval (loaded M word).store)=
      decide ((snapshot M p word).status=.accepted) := by
  have state := congrFun (final_bank M p word) (0 : Fin 11)
  change (routine M p).eval (loaded M word).store 0=
    ([(Source.Cell.state (snapshot M p word).status)] : List (Source.Symbol M)).map Cell.source at state
  simp only [Program.checksPass,checks]
  rw [state]
  cases status : (snapshot M p word).status <;> simp [accepted,status]

theorem checks_correct (p : PolynomialBound)
    (bounded : ∀ input,M.TimeBound (decisionData input) (p input.length))
    (word : List PairSymbol) :
    Program.checksPass (checks M) ((routine M p).eval (loaded M word).store)=true ↔
      M.Accepts (decisionData (binaryPairWord word)) [] := by
  classical
  rw [checks_eq,decide_eq_true_eq]
  have status : (snapshot M p word).status=.accepted ↔
      ∃ output,(snapshot M p word).acceptedOutput=some output := by
    cases value : (snapshot M p word).status <;> simp [Source.Snapshot.acceptedOutput,value]
  rw [status]
  have positive : 1≤sourceClock p word.length := by
    have lower := sourceClock_lower p word.length
    omega
  have deadline : sourceClock p word.length-1+1=sourceClock p word.length := by omega
  have later : p (binaryPairWord word).length≤sourceClock p word.length-1 := by
    rw [binaryPairWord_length]
    have lower := sourceClock_lower p word.length
    omega
  have native (output : List Unit) := Source.iterate_accept_iff M
    (decisionData (binaryPairWord word)) [] (sourceClock p word.length-1) output
  simp only [deadline] at native
  constructor
  · rintro ⟨output,produced⟩
    exact ⟨output,sourceClock p word.length-1,(native output).mp produced⟩
  · rintro ⟨output,produced⟩
    have atBound := M.produces_at_bound (decisionData (binaryPairWord word)) []
      (p (binaryPairWord word).length) output (bounded (binaryPairWord word) []) produced
    have padded := M.run_halted_add (decisionData (binaryPairWord word)) []
      (p (binaryPairWord word).length) (.accepted output) atBound
      (sourceClock p word.length-1-p (binaryPairWord word).length)
    rw [Nat.add_sub_of_le later] at padded
    exact ⟨output,(native output).mpr padded⟩

end
end ComplexityOfGenerators.Simulation.PairCollisionDecision
