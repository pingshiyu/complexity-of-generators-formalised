import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.RegionTapeSupport

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O QC SC QB SB : Type} {k m : ℕ}
    (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m)

theorem source_bounded (length : ℕ) (ctor : BankConfiguration Unit QC SC k) (data : InputData I A) (radius : ℕ)
    (heads : ∀ j,(ctor.head j).natAbs≤radius) :
    (sourceBank constructor source).Bounded data radius (sourceConfiguration constructor source length ctor) := by
  apply LeftBankEmbedding.bounded_lift source (encodeSource constructor.blank) decodeSource
    (frameHead ctor) (frameTape constructor source length ctor) data radius source.initialConfiguration
    ((source.initial_bounded data).mono source (Nat.zero_le _))
  intro j
  refine Fin.addCases (fun j=>?_) (fun j=>?_) j
  · simpa only [frameHead,Fin.addCases_left] using heads j
  · simp [frameHead]

private theorem digitTape_none_outside (digits : List Bool) (radius : ℕ) (size : digits.length≤radius)
    (position : ℤ) (outside : radius<position.natAbs) : digitTape digits position=none := by
  by_cases nonnegative : 0≤position
  · have beyond : digits.length≤position.toNat := by cases position <;> simp_all <;> omega
    simp [digitTape,nonnegative,List.getElem?_eq_none beyond]
  · simp [digitTape,nonnegative]

theorem source_supported (length : ℕ) (ctor : BankConfiguration Unit QC SC k) (ctorRadius radius : ℕ)
    (supported : constructor.TapeSupported ctorRadius ctor) (small : ctorRadius≤radius)
    (digits : Nat.clog 2 (length+1)≤radius) :
    (sourceBank constructor source).TapeSupported radius (sourceConfiguration constructor source length ctor) := by
  intro tape position outside
  refine Fin.addCases (fun j=>?_) (fun j=>?_) tape
  · simp only [sourceConfiguration,LeftBankEmbedding.lift,sourceBank,LeftBankEmbedding.bank,
      Fin.addCases_left,TapeBank.initialConfiguration]
  · refine Fin.addCases (fun j=>?_) (fun j=>?_) j
    · simp only [sourceConfiguration,LeftBankEmbedding.lift,sourceBank,LeftBankEmbedding.bank,
        frameTape,Fin.addCases_left,Fin.addCases_right,encodeSource]
      rw [supported j position (by omega)]
    · simp only [sourceConfiguration,LeftBankEmbedding.lift,sourceBank,LeftBankEmbedding.bank,
        frameTape,Fin.addCases_right,encodeSource]
      have empty := digitTape_none_outside (increment^[length] []) radius (by simpa only [iterate_length_eq] using digits) position outside
      rw [Prelude.memory_empty_temporary,empty]
      congr 2
      exact Function.update_eq_self _ _

theorem source_valid (length : ℕ) (ctor : BankConfiguration Unit QC SC k) (ctorRadius radius : ℕ)
    (heads : ∀ j,(ctor.head j).natAbs≤ctorRadius)
    (supported : constructor.TapeSupported ctorRadius ctor) (small : ctorRadius≤radius)
    (digits : Nat.clog 2 (length+1)≤radius) :
    SpaceShortRuns.Valid (sourceBank constructor source).blank length radius
      (SpaceShortRuns.snapshot (sourceConfiguration constructor source length ctor)) := by
  have bounded := source_bounded constructor source length ctor (InputData.mk [] [] 0) radius (fun j=>(heads j).trans small)
  exact ⟨Nat.zero_le _,bounded.head,source_supported constructor source length ctor ctorRadius radius supported small digits⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
