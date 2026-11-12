import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

/-- A bounded-space proposal path ending at real random-tape exhaustion. -/
def Exhausts (n : ℕ) (bits : BitString) (start : BankConfiguration α (Control B fallback) (Cell S α) (k+1))
    (ticks : ℕ) : Prop :=
  ∃ finish,(bank B fallback).RegionSteps (generatorData n) bits n start ticks finish ∧
    (bank B fallback).Executes (generatorData n) bits finish 0 .exhausted

 theorem Exhausts.executes {n : ℕ} {bits : BitString} {start : BankConfiguration α (Control B fallback) (Cell S α) (k+1)}
    {ticks : ℕ} (run : Exhausts B fallback n bits start ticks) :
    (bank B fallback).Executes (generatorData n) bits start ticks .exhausted := by
  obtain ⟨finish,path,terminal⟩ := run
  simpa using (path.toSteps _).executes _ terminal

 theorem Exhausts.prepend {n : ℕ} {bits : BitString} {start middle : BankConfiguration α (Control B fallback) (Cell S α) (k+1)}
    {ticks before : ℕ} (run : Exhausts B fallback n bits middle ticks)
    (prefixPath : (bank B fallback).RegionSteps (generatorData n) bits n start before middle) :
    Exhausts B fallback n bits start (before+ticks) := by
  obtain ⟨finish,path,terminal⟩ := run
  exact ⟨finish,prefixPath.trans _ path,terminal⟩

 theorem select_runs_aux (remaining n : ℕ) (bits : BitString) (word : Word α) (consumed : ℕ)
    (position : Fin (Fintype.card α)) (within : word.length≤n) (available : consumed≤bits.length)
    (fits : Fintype.card α-position.val≤remaining) :
    ∃ ticks,ticks≤remaining ∧
      (Exhausts B fallback n bits (configuration B fallback word consumed word.length (.symbol position)) ticks ∨
        ∃ chosen nextConsumed,consumed≤nextConsumed ∧ nextConsumed≤bits.length ∧
          (bank B fallback).RegionSteps (generatorData n) bits n
            (configuration B fallback word consumed word.length (.symbol position)) ticks
            (configuration B fallback word nextConsumed word.length (.writeLetter chosen))) := by
  induction remaining generalizing consumed position with
  | zero => omega
  | succ remaining ih =>
      by_cases more : position.val+1<Fintype.card α
      · let next : Fin (Fintype.card α) := ⟨position.val+1,more⟩
        have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback word consumed word.length (.symbol position))=
            .readRandom (.writeLetter position) (.symbol next) := by
          simp [TapeBank.instruction,configuration,bank,more,next]
        cases lookup : bits[consumed]? with
        | none =>
            refine ⟨0,by omega,Or.inl ⟨_,.refl _ (bounded B fallback n word consumed word.length _ within),?_⟩⟩
            exact .exhausted _ _ _ table lookup
        | some bit =>
            have nextAvailable : consumed+1≤bits.length := by
              have live := (List.getElem?_eq_some_iff.mp lookup).1
              omega
            cases bit with
            | false =>
                refine ⟨1,by omega,Or.inr ⟨position,consumed+1,by omega,nextAvailable,?_⟩⟩
                apply TapeBank.RegionSteps.random _ (.writeLetter position) (.symbol next) false 0 _
                  (bounded B fallback n word consumed word.length _ within) table lookup
                rw [choose_configuration]
                exact .refl _ (bounded B fallback n word (consumed+1) word.length _ within)
            | true =>
                obtain ⟨ticks,cost,result⟩ := ih (consumed+1) next nextAvailable (by dsimp [next];omega)
                have first : (bank B fallback).RegionSteps (generatorData n) bits n
                    (configuration B fallback word consumed word.length (.symbol position)) 1
                    (configuration B fallback word (consumed+1) word.length (.symbol next)) := by
                  apply TapeBank.RegionSteps.random _ (.writeLetter position) (.symbol next) true 0 _
                    (bounded B fallback n word consumed word.length _ within) table lookup
                  rw [choose_configuration]
                  exact .refl _ (bounded B fallback n word (consumed+1) word.length _ within)
                refine ⟨1+ticks,by omega,?_⟩
                rcases result with failure | ⟨chosen,nextConsumed,lower,upper,path⟩
                · exact Or.inl (failure.prepend B fallback first)
                · exact Or.inr ⟨chosen,nextConsumed,by omega,upper,first.trans _ path⟩
      · have table : (bank B fallback).instruction (generatorData n)
            (configuration B fallback word consumed word.length (.symbol position))=
            .step (.writeLetter position) (wordTape B word word.length) .stay .stay .stay .stay none := by
          simp [TapeBank.instruction,configuration,bank,more]
        refine ⟨1,by omega,Or.inr ⟨position,consumed,le_rfl,available,?_⟩⟩
        apply TapeBank.RegionSteps.step _ (.writeLetter position) _ .stay .stay .stay .stay none 0 _
          (bounded B fallback n word consumed word.length _ within) table
        have cell : wordTape B word word.length=
            (configuration B fallback word consumed word.length (.symbol position)).tape
              ((bank B fallback).select (.symbol position))
              ((configuration B fallback word consumed word.length (.symbol position)).head ((bank B fallback).select (.symbol position))) := by
          simp only [configuration,bank,Fin.lastCases_last]
        rw [cell,advance_stay B fallback n word consumed word.length _ _ within]
        exact .refl _ (bounded B fallback n word consumed word.length _ within)

 theorem select_runs (n : ℕ) (bits : BitString) (word : Word α) (consumed : ℕ)
    (position : Fin (Fintype.card α)) (within : word.length≤n) (available : consumed≤bits.length) :
    ∃ ticks,ticks≤Fintype.card α-position.val ∧
      (Exhausts B fallback n bits (configuration B fallback word consumed word.length (.symbol position)) ticks ∨
        ∃ chosen nextConsumed,consumed≤nextConsumed ∧ nextConsumed≤bits.length ∧
          (bank B fallback).RegionSteps (generatorData n) bits n
            (configuration B fallback word consumed word.length (.symbol position)) ticks
            (configuration B fallback word nextConsumed word.length (.writeLetter chosen))) :=
  select_runs_aux B fallback (Fintype.card α-position.val) n bits word consumed position within available le_rfl

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
