import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Prepare
import ComplexityOfGenerators.Simulation.TransducerBank.ControlEmbedding

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem source_executes (copies : ℕ) (leftHead : Fin kc→ℤ)
    (leftTape : Fin kc→ℤ→Cell (SC:=SC) (S:=S))
    {data : InputData Unit Bool} {bits : BitString}
    {start : BankConfiguration O (Fuel.Phase Q S O k) (S⊕Unit) (k+1)}
    {ticks : ℕ} {result : Outcome O} (run : (Fuel.bank B).Executes data bits start ticks result) :
    (bank C B copies).Executes data bits
      ((BankEmbedding.lift (encodeSource C) leftHead leftTape start).mapState Phase.source) ticks result := by
  have embedded := BankEmbedding.executes_lift (Fuel.bank B) (encodeSource C) Prod.snd
    (fun _=>rfl) leftHead leftTape run
  apply TapeBank.Executes.mapState (sourceBank C B) (bank C B copies) Phase.source (fun _=>rfl) _ embedded
  intro q i a x origin cell
  cases action : (sourceBank C B).transition q i a x origin cell <;>
    simp only [bank,action,BankInstruction.mapState]


 theorem source_configuration (copies fuel : ℕ) (ctor : BankConfiguration Unit QC SC kc) :
    configuration C B copies (.source (.fetch B.initial)) fuel 0 0 ctor =
      (BankEmbedding.lift (encodeSource C) ctor.head
        (fun j p=>(ctor.tape j p,.inl B.blank))
        (Fuel.configuration B fuel 0 B.initialConfiguration)).mapState Phase.source := by
  apply BankConfiguration.ext <;> try rfl
  case tape =>
    funext j p
    refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simp only [configuration,BankConfiguration.mapState,BankEmbedding.lift,Fin.addCases_left]
    · simp only [configuration,BankConfiguration.mapState,BankEmbedding.lift,Fin.addCases_right,Fuel.configuration]
      refine Fin.lastCases ?_ (fun j=>?_) j <;>
        simp only [Fin.lastCases_last,Fin.lastCases_castSucc,encodeSource,TapeBank.initialConfiguration]

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
