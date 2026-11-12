import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.SourceStep

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

theorem counter_go (data : InputData I A) (choices : BitString) (length index : ℕ)
    (current : BankConfiguration O Q S k) (state next : Control Q) (radius : ℕ)
    (bounded : source.Bounded (sourceData data) radius current)
    (table : (bank source).instruction data (configuration source length index current state)=
      .step next ((configuration source length index current state).tape ((bank source).select state)
        ((configuration source length index current state).head ((bank source).select state))) .stay .stay .stay .stay none) :
    (bank source).RegionSteps data choices radius (configuration source length index current state) 1
      (configuration source length index current next) := by
  apply TapeBank.RegionSteps.step _ next _ .stay .stay .stay .stay none 0 _
    (configuration_bounded source data length index current state radius bounded) table
  have advanced : (bank source).advance data (configuration source length index current state) next
      ((configuration source length index current state).tape ((bank source).select state)
        ((configuration source length index current state).head ((bank source).select state))) .stay .stay .stay .stay none=
      configuration source length index current next := by
    simpa only [configuration] using TapeBank.advance_stay (bank source) data
      (configuration source length index current state) next bounded.input bounded.auxiliary (Nat.zero_le _)
  rw [advanced]
  exact .refl _ (configuration_bounded source data length index current next radius bounded)

theorem comparison_memory (length index : ℕ) :
    Comparison.memory (1 : Fin 3) (0 : Fin 3) (fun _ _ => none)
      (Comparison.paired (increment^[index] []) (increment^[length] []))=counterMemory length index := by
  funext position track
  by_cases first : track=0
  · subst track
    simp [Comparison.memory,Comparison.cellTape_paired,counterMemory]
  · by_cases second : track=1
    · subst track
      simp [Comparison.memory,Comparison.cellTape_paired,counterMemory]
    · simp [Comparison.memory,Comparison.cellTape_paired,counterMemory,Function.update_of_ne first,Function.update_of_ne second]

theorem probe_steps (data : InputData I A) (choices : BitString) (index : ℕ)
    (current : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current)
    (small : index≤data.input.length) (space : 2*Nat.clog 2 (data.input.length+1)+2≤radius) :
    (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.probe current.state (.scan false)))
      (2*(max (increment^[index] []).length (increment^[data.input.length] []).length+1)+1)
      (configuration source data.input.length index current (.execute current.state (decide (index<data.input.length)))) := by
  have path := (Comparison.routine_framed (O:=O) (1 : Fin 3) (0 : Fin 3) (by decide) (fun _ _ => none) data choices
    (Context.mk current.inputHead current.auxiliaryHead 0 current.randomHead current.output)
    (by exact ⟨bounded.input,bounded.auxiliary,Nat.zero_le _⟩)
    (increment^[index] []) (increment^[data.input.length] []) (iterate_canonical _) (iterate_canonical _) data.input.length
    (by simpa only [iterate_value] using small) (by simp [iterate_value])).mono
    (Comparison.bank I A O (1 : Fin 3) (0 : Fin 3)) space
  have lifted := LeftBankEmbedding.regionSteps_lift (Comparison.bank I A O (1 : Fin 3) (0 : Fin 3))
    (encodeCounter source) Prod.snd (by intro;rfl) current.head
    (fun tape position => encodeSource (current.tape tape position)) bounded.head path
  have mapped := lifted.mapState (probeBank source) (bank source) (Control.probe current.state)
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux idx emit table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.probe current.state) (.execute current.state (probeAnswer state)) cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.probe current.state) (.execute current.state (probeAnswer state)) cell) table)
  have actual : (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.probe current.state (.scan false)))
      (2*(max (increment^[index] []).length (increment^[data.input.length] []).length+1))
      (configuration source data.input.length index current (.probe current.state (.done (decide (index<data.input.length))))) := by
    simpa only [configuration,LeftBankEmbedding.lift,Context.frame,Comparison.encoded,comparison_memory,
      BankConfiguration.mapState,iterate_value,Int.natCast_zero] using mapped
  have finish := counter_go source data choices data.input.length index current
    (.probe current.state (.done (decide (index<data.input.length)))) (.execute current.state (decide (index<data.input.length))) radius bounded (by
      rfl)
  exact actual.trans (bank source) finish

theorem increase_steps (data : InputData I A) (choices : BitString) (index : ℕ)
    (current : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current)
    (small : index≤data.input.length) (space : 2*Nat.clog 2 (data.input.length+1)+2≤radius) :
    (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.increase current.state .carry))
      (2*(carryOffset (increment^[index] [])+1)+1)
      (configuration source data.input.length (index+1) current (.probe current.state (.scan false))) := by
  have path := increment_regionSteps (O:=O) data choices (increment^[index] []) (iterate_canonical _) data.input.length
    (by simpa only [iterate_value] using small)
  have tracked := Tracks.regionSteps_lift (BinaryCounter.bank I A O) (1 : Fin 3)
    (fun _ position => Function.update (fun _ => none) 0 (digitTape (increment^[data.input.length] []) position)) path
  have framed := Context.regionSteps_frame (Tracks.bank (BinaryCounter.bank I A O) (1 : Fin 3))
    (Tracks.workOnly _ _ (increment_workOnly I A O)) data choices
    (Context.mk current.inputHead current.auxiliaryHead 0 current.randomHead current.output)
    (by exact ⟨bounded.input,bounded.auxiliary,Nat.zero_le _⟩) tracked
  have lifted := LeftBankEmbedding.regionSteps_lift (Tracks.bank (BinaryCounter.bank I A O) (1 : Fin 3))
    (encodeCounter source) Prod.snd (by intro;rfl) current.head
    (fun tape position => encodeSource (current.tape tape position)) bounded.head
    (framed.mono _ space)
  have mapped := lifted.mapState (increaseBank source) (bank source) (Control.increase current.state)
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux idx emit table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.increase current.state) (.probe current.state (.scan false)) cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.increase current.state) (.probe current.state (.scan false)) cell) table)
  have actual : (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.increase current.state .carry))
      (2*(carryOffset (increment^[index] [])+1))
      (configuration source data.input.length (index+1) current (.increase current.state .done)) := by
    simpa only [configuration,LeftBankEmbedding.lift,Context.frame,Tracks.lift,BinaryCounter.encoded,
      counterMemory,BankConfiguration.mapState,Function.iterate_succ_apply',Int.natCast_zero] using mapped
  have finish := counter_go source data choices data.input.length (index+1) current
    (.increase current.state .done) (.probe current.state (.scan false)) radius bounded rfl
  exact actual.trans (bank source) finish

theorem decrement_iterate (index : ℕ) : decrement (increment^[index] [])=increment^[index-1] [] := by
  cases index with
  | zero => rfl
  | succ index => simpa only [Function.iterate_succ_apply',Nat.add_sub_cancel] using
      decrement_increment (increment^[index] []) (iterate_canonical index)

theorem decrease_steps (data : InputData I A) (choices : BitString) (index : ℕ)
    (current : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded (sourceData data) radius current)
    (small : index≤data.input.length) (space : 2*Nat.clog 2 (data.input.length+1)+4≤radius) :
    ∃ time, (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.decrease current.state .borrow)) time
      (configuration source data.input.length (index-1) current (.probe current.state (.scan false))) := by
  obtain ⟨time,path⟩ := Decrement.decrement_regionSteps (O:=O) data choices (increment^[index] []) (iterate_canonical _) data.input.length
    (by simpa only [iterate_value] using small)
  have tracked := Tracks.regionSteps_lift (Decrement.bank I A O) (1 : Fin 3)
    (fun _ position => Function.update (fun _ => none) 0 (digitTape (increment^[data.input.length] []) position)) path
  have framed := Context.regionSteps_frame (Tracks.bank (Decrement.bank I A O) (1 : Fin 3))
    (Tracks.workOnly _ _ (Decrement.workOnly I A O)) data choices
    (Context.mk current.inputHead current.auxiliaryHead 0 current.randomHead current.output)
    (by exact ⟨bounded.input,bounded.auxiliary,Nat.zero_le _⟩) tracked
  have lifted := LeftBankEmbedding.regionSteps_lift (Tracks.bank (Decrement.bank I A O) (1 : Fin 3))
    (encodeCounter source) Prod.snd (by intro;rfl) current.head
    (fun tape position => encodeSource (current.tape tape position)) bounded.head
    (framed.mono _ space)
  have mapped := lifted.mapState (decreaseBank source) (bank source) (Control.decrease current.state)
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux idx emit table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.decrease current.state) (.probe current.state (.scan false)) cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,transition,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction (Control.decrease current.state) (.probe current.state (.scan false)) cell) table)
  have actual : (bank source).RegionSteps data choices radius
      (configuration source data.input.length index current (.decrease current.state .borrow)) time
      (configuration source data.input.length (index-1) current (.decrease current.state .done)) := by
    simpa only [configuration,LeftBankEmbedding.lift,Context.frame,Tracks.lift,Decrement.encoded,
      counterMemory,BankConfiguration.mapState,decrement_iterate,Int.natCast_zero] using mapped
  have finish := counter_go source data choices data.input.length (index-1) current
    (.decrease current.state .done) (.probe current.state (.scan false)) radius bounded rfl
  exact ⟨time+1,actual.trans (bank source) finish⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
