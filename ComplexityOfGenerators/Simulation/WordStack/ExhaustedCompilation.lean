import ComplexityOfGenerators.Simulation.WordStack.NoEmission
import ComplexityOfGenerators.Simulation.WordStack.EventCompilation
import ComplexityOfGenerators.Simulation.TransducerBank.TerminalSnapshot

namespace ComplexityOfGenerators.Simulation.WordStack.Program
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Q R S E : Type} {k : ℕ} [Fintype R] [Fintype S] [Fintype E]
    (P : Program Q S E k) (T : Program R S E k)

theorem Executes.exhausted_native_of_embeds {n : ℕ} {bits : BitString} {ticks : ℕ}
    (run : P.Executes n bits P.initialConfiguration ticks .exhausted)
    (pure : P.NoEmit) (f : Q→R) (embedding : P.Embeds T f) (initial : f P.initial=T.initial) :
    ∃ nativeTicks last, T.machine.Steps (generatorData n) bits T.machine.initialConfiguration nativeTicks last ∧
      last.output=[] ∧ T.machine.observe (generatorData n) bits last=.halted .exhausted := by
  obtain ⟨source,path,no,yes,terminal,absent⟩ := run.exhausted_path P
  have output : source.output=[] := path.output_eq P pure
  have bounded : source.indexHead≤n := path.index_le P (Nat.zero_le _)
  have mapped := embedding.steps P path
  have initialEq : P.initialConfiguration.mapState f=T.initialConfiguration := by
    apply Configuration.ext <;> try rfl
    exact initial
  rw [initialEq] at mapped
  have random : T.instruction n (source.mapState f)=.random (f no) (f yes) := by
    simp only [instruction,Configuration.mapState,embedding.select]
    exact embedding.random _ _ _ _ _ terminal
  obtain ⟨loaded,ready,loadPath,_⟩ := bank_loaded_inRegion T.bank (generatorData n) bits 0
  have initialReady : BankReady T.bank (T.encoded T.initialConfiguration) (fun _=>false) loaded := by
    rw [T.encoded_initial]
    exact ready
  obtain ⟨cost,after,sides,afterReady,native⟩ := T.steps_native mapped _ _ loaded initialReady
    (T.encoded_bounded n T.initialConfiguration (Nat.zero_le _))
  have table := T.encoded_instruction n (source.mapState f)
  rw [random] at table
  obtain ⟨last,tail,snapshot,exhausted⟩ := bank_exhausted_path T.bank (generatorData n) bits _
    (T.encoded (source.mapState f)) sides after afterReady
    (T.encoded_bounded n (source.mapState f) bounded) (.ready (f no)) (.ready (f yes)) table absent
  refine ⟨1+cost+_,(last),((loadPath.trans T.machine native).trans T.machine tail),?_,exhausted⟩
  exact snapshot.output.trans output

end
end ComplexityOfGenerators.Simulation.WordStack.Program
