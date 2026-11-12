import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem clockTape_extend (fuel : ℕ) :
    Function.update (Fuel.clockTape B fuel) (fuel:ℤ) (.inr ()) = Fuel.clockTape B (fuel+1) := by
  funext p
  by_cases same : p=(fuel:ℤ)
  · subst p; simp [Fuel.clockTape]
  · have condition : (0≤p ∧ p<(fuel:ℤ)) ↔ (0≤p ∧ p<((fuel+1:ℕ):ℤ)) := by omega
    simp only [Function.update_of_ne same,Fuel.clockTape,condition]


 theorem configuration_stay (copies fuel cursor index n : ℕ)
    (phase next : Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies)
    (ctor : BankConfiguration Unit QC SC kc) (within : index≤n) :
    (bank C B copies).advance (generatorData n) (configuration C B copies phase fuel cursor index ctor) next
      ((configuration C B copies phase fuel cursor index ctor).tape
        ((bank C B copies).select phase)
        ((configuration C B copies phase fuel cursor index ctor).head ((bank C B copies).select phase)))
      .stay .stay .stay .stay none = configuration C B copies next fuel cursor index ctor := by
  simpa only [configuration] using TapeBank.advance_stay (bank C B copies) (generatorData n)
    (configuration C B copies phase fuel cursor index ctor) next
    (by simp [configuration,generatorData]) (by simp [configuration,generatorData])
    (by simpa [configuration,generatorData] using within)


 theorem configuration_writeClock (copies fuel index n : ℕ)
    (phase next : Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies)
    (ctor : BankConfiguration Unit QC SC kc) (within : index≤n)
    (selected : (bank C B copies).select phase=clock (kc:=kc) (k:=k)) :
    (bank C B copies).advance (generatorData n) (configuration C B copies phase fuel fuel index ctor) next
      (C.blank,.inr ()) .right .stay .stay .stay none =
      configuration C B copies next (fuel+1) (fuel+1) index ctor := by
  apply BankConfiguration.ext <;> try rfl
  case indexHead => simp [TapeBank.advance,configuration,generatorData,Move.onInput,Nat.min_eq_left within]
  case head =>
    simp only [TapeBank.advance,configuration,selected,clock,Fin.addCases_right,
      Fin.lastCases_last,BankEmbedding.update_right,Move.onInt]
    congr 1
    rw [Fuel.lastCases_update_last]
    simp
  case tape =>
    simp only [TapeBank.advance,configuration,selected,clock,Fin.addCases_right,
      Fin.lastCases_last,BankEmbedding.update_right]
    congr 1
    rw [Fuel.lastCases_update_last]
    congr 1
    funext p
    by_cases same : p=(fuel:ℤ)
    · subst p; simp [Fuel.clockTape]
    · simpa only [Function.update_of_ne same] using
        congrArg (fun value => (C.blank,value)) (congrFun (clockTape_extend B fuel) p)

 theorem configuration_rewind (copies fuel cursor index n : ℕ)
    (ctor : BankConfiguration Unit QC SC kc) (within : index≤n) :
    (bank C B copies).advance (generatorData n)
      (configuration C B copies .rewind fuel (cursor+1) index ctor) .rewind
      ((configuration C B copies .rewind fuel (cursor+1) index ctor).tape
        (clock (kc:=kc) (k:=k)) (cursor+1))
      .left .stay .stay .left none =
      configuration C B copies .rewind fuel cursor (index-1) ctor := by
  apply BankConfiguration.ext <;> try rfl
  case head =>
    simp only [TapeBank.advance,configuration,bank,clock,Fin.addCases_right,
      Fin.lastCases_last,BankEmbedding.update_right,Move.onInt]
    congr 1
    rw [Fuel.lastCases_update_last]
    simp
  case tape =>
    simp only [TapeBank.advance,configuration,bank,clock,Fin.addCases_right,
      Fin.lastCases_last]
    simp only [Nat.cast_add,Nat.cast_one,Function.update_eq_self,
      BankEmbedding.update_right,Fuel.lastCases_update_last]

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
