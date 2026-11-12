import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.Counters

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex

set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

theorem after_index_steps (data : InputData I A) (choices : BitString) (index : ℕ)
    (current : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current)
    (small : index≤data.input.length) (space : 2*Nat.clog 2 (data.input.length+1)+4≤radius)
    (live : Bool) (availability : live=decide (index<data.input.length)) (move : Move) :
    ∃ time, (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (afterStep current.state live move)) time
      (configuration source data.input.length (move.onInput data.input.length index) current (.probe current.state (.scan false))) := by
  cases move with
  | left =>
      obtain ⟨time,path⟩ := decrease_steps source data choices index current radius bounded small space
      exact ⟨time,path⟩
  | stay =>
      refine ⟨0,?_⟩
      simpa only [afterStep,Move.onInput,Nat.min_eq_left small] using
        TapeBank.RegionSteps.refl (B:=bank source) (data:=data) (bits:=choices)
          (configuration source data.input.length index current (.probe current.state (.scan false)))
          (configuration_bounded source data data.input.length index current (.probe current.state (.scan false)) radius bounded)
  | right =>
      by_cases active : index<data.input.length
      · have trueFlag : live=true := by simpa [active] using availability
        subst live
        have path := increase_steps source data choices index current radius bounded small (by omega)
        refine ⟨2*(BinaryCounter.carryOffset (BinaryCounter.increment^[index] [])+1)+1,?_⟩
        simpa [afterStep,active,Move.onInput,Nat.min_eq_left (by omega : index+1≤data.input.length)] using path
      · have falseFlag : live=false := by simpa [active] using availability
        have atEnd : index=data.input.length := by omega
        subst live
        subst index
        refine ⟨0,?_⟩
        simpa [afterStep,Move.onInput] using
          TapeBank.RegionSteps.refl (B:=bank source) (data:=data) (bits:=choices)
            (configuration source data.input.length data.input.length current (.probe current.state (.scan false)))
            (configuration_bounded source data data.input.length data.input.length current (.probe current.state (.scan false)) radius bounded)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
