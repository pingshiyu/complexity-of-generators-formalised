import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! Retyping a fixed tape count along a natural-number equality changes no
transition, work position, or execution time. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeCast

variable {I A O Q S : Type} {k l : ℕ}

def bank (source : TapeBank I A O Q S k) (equal : k=l) : TapeBank I A O Q S l where
  initial := source.initial
  blank := source.blank
  select := fun state => Fin.cast equal (source.select state)
  transition := source.transition

def configuration (equal : k=l) (current : BankConfiguration O Q S k) : BankConfiguration O Q S l :=
  ⟨current.state,current.inputHead,current.auxiliaryHead,current.indexHead,current.randomHead,current.output,
    fun tape => current.head (Fin.cast equal.symm tape),fun tape => current.tape (Fin.cast equal.symm tape)⟩

theorem state (equal : k=l) (current : BankConfiguration O Q S k) :
    (configuration equal current).state=current.state := by cases equal;rfl

theorem head (equal : k=l) (current : BankConfiguration O Q S k) (tape : Fin k) :
    (configuration equal current).head (Fin.cast equal tape)=current.head tape := by cases equal;rfl

theorem tape (equal : k=l) (current : BankConfiguration O Q S k) (index : Fin k) (position : ℤ) :
    (configuration equal current).tape (Fin.cast equal index) position=current.tape index position := by cases equal;rfl

theorem instruction (source : TapeBank I A O Q S k) (equal : k=l) (data : InputData I A)
    (current : BankConfiguration O Q S k) :
    (bank source equal).instruction data (configuration equal current)=source.instruction data current := by cases equal;rfl

theorem advance (source : TapeBank I A O Q S k) (equal : k=l) (data : InputData I A)
    (current : BankConfiguration O Q S k) (next write work input auxiliary index emit) :
    (bank source equal).advance data (configuration equal current) next write work input auxiliary index emit=
      configuration equal (source.advance data current next write work input auxiliary index emit) := by cases equal;rfl

theorem bounded (source : TapeBank I A O Q S k) (equal : k=l) (data : InputData I A)
    (radius : ℕ) (current : BankConfiguration O Q S k) (bound : source.Bounded data radius current) :
    (bank source equal).Bounded data radius (configuration equal current) := by cases equal;exact bound

theorem steps (source : TapeBank I A O Q S k) (equal : k=l) {data : InputData I A} {choices : BitString}
    {start finish : BankConfiguration O Q S k} {time : ℕ} (path : source.Steps data choices start time finish) :
    (bank source equal).Steps data choices (configuration equal start) time (configuration equal finish) := by
  cases equal;exact path

theorem regionSteps (source : TapeBank I A O Q S k) (equal : k=l) {data : InputData I A} {choices : BitString}
    {start finish : BankConfiguration O Q S k} {radius time : ℕ} (path : source.RegionSteps data choices radius start time finish) :
    (bank source equal).RegionSteps data choices radius (configuration equal start) time (configuration equal finish) := by
  cases equal;exact path

theorem executes (source : TapeBank I A O Q S k) (equal : k=l) {data : InputData I A} {choices : BitString}
    {start : BankConfiguration O Q S k} {time : ℕ} {result : Outcome O} (run : source.Executes data choices start time result) :
    (bank source equal).Executes data choices (configuration equal start) time result := by cases equal;exact run

theorem regionRun (source : TapeBank I A O Q S k) (equal : k=l) {data : InputData I A} {choices : BitString}
    {start : BankConfiguration O Q S k} {radius : ℕ} {result : Outcome O} (run : source.RegionRun data choices radius start result) :
    (bank source equal).RegionRun data choices radius (configuration equal start) result := by cases equal;exact run

end ComplexityOfGenerators.Simulation.TransducerBank.TapeCast
