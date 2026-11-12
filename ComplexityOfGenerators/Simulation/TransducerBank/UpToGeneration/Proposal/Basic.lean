import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceBasic
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

def configuration (word : Word α) (consumed position : ℕ) (state : Control B fallback) :
    BankConfiguration α (Control B fallback) (Cell S α) (k+1) :=
  ⟨state,0,0,position,consumed,[],Fin.lastCases (position:ℤ) (fun _=>0),
    Fin.lastCases (wordTape B word) (fun _ _=>(B.blank,none))⟩

 theorem bounded (n : ℕ) (word : Word α) (consumed position : ℕ) (state : Control B fallback)
    (within : position≤n) :
    (bank B fallback).Bounded (generatorData n) n (configuration B fallback word consumed position state) := by
  refine ⟨Nat.zero_le _,Nat.zero_le _,within,?_⟩
  intro j
  refine Fin.lastCases ?_ (fun j=>?_) j <;>
    simp only [configuration,Fin.lastCases_last,Fin.lastCases_castSucc,Int.natAbs_natCast,Int.natAbs_zero]
  · exact within
  · exact Nat.zero_le _

 theorem source_configuration (word : Word α) (consumed : ℕ) :
    configuration B fallback word consumed 0 (.fetch B.initial)=
      UpToGeneration.configuration B fallback word consumed B.initialConfiguration := rfl

 theorem initial_configuration :
    {(bank B fallback).initialConfiguration with state:=.guess}=configuration B fallback [] 0 0 .guess := by
  apply BankConfiguration.ext <;> try rfl
  case head =>
    funext j
    refine Fin.lastCases ?_ (fun j=>?_) j <;> simp [TapeBank.initialConfiguration,configuration]
  case tape =>
    funext j p
    refine Fin.lastCases ?_ (fun j=>?_) j <;>
      simp [TapeBank.initialConfiguration,configuration,bank,wordTape]

 theorem choose_configuration (word : Word α) (consumed position : ℕ) (state next : Control B fallback) :
    TapeBank.choose (configuration B fallback word consumed position state) next=
      configuration B fallback word (consumed+1) position next := rfl

 theorem advance_stay (n : ℕ) (word : Word α) (consumed position : ℕ) (state next : Control B fallback)
    (within : position≤n) :
    (bank B fallback).advance (generatorData n) (configuration B fallback word consumed position state) next
      ((configuration B fallback word consumed position state).tape ((bank B fallback).select state)
        ((configuration B fallback word consumed position state).head ((bank B fallback).select state)))
      .stay .stay .stay .stay none=configuration B fallback word consumed position next := by
  simpa only [configuration] using TapeBank.advance_stay (bank B fallback) (generatorData n)
    (configuration B fallback word consumed position state) next (Nat.zero_le _) (Nat.zero_le _) within

 theorem write_letter (n : ℕ) (bits : BitString) (word : Word α) (consumed : ℕ)
    (position : Fin (Fintype.card α)) (room : word.length<n) :
    (bank B fallback).RegionSteps (generatorData n) bits n
      (configuration B fallback word consumed word.length (.writeLetter position)) 1
      (configuration B fallback (word++[letter position]) consumed (word.length+1) .guess) := by
  apply TapeBank.RegionSteps.step _ .guess (B.blank,some (letter position)) .right .stay .stay .right none 0 _
    (bounded B fallback n word consumed word.length _ (by omega)) rfl
  have advanced : (bank B fallback).advance (generatorData n)
      (configuration B fallback word consumed word.length (.writeLetter position)) .guess
      (B.blank,some (letter position)) .right .stay .stay .right none=
      configuration B fallback (word++[letter position]) consumed (word.length+1) .guess := by
    apply BankConfiguration.ext <;> try rfl
    case indexHead => simp [TapeBank.advance,configuration,generatorData,Move.onInput];omega
    case head =>
      simp only [TapeBank.advance,configuration,bank,Fin.lastCases_last,Move.onInt,Fuel.lastCases_update_last]
      simp
    case tape =>
      simp only [TapeBank.advance,configuration,bank,Fin.lastCases_last,Fuel.lastCases_update_last,wordTape_append]
  rw [advanced]
  exact .refl _ (bounded B fallback n _ consumed (word.length+1) .guess (by omega))

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
