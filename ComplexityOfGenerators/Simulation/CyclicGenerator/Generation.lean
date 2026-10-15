import ComplexityOfGenerators.Simulation.CyclicGenerator.Support
import ComplexityOfGenerators.Simulation.CyclicGenerator.Stop
import ComplexityOfGenerators.Proofs.GeneratorSupport
import ComplexityOfGenerators.Proofs.CyclicSelection

/-! The cyclic machine is a genuine generator: its support is exactly the
accepted length slice, and a nonempty slice is produced almost surely. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem machine_accepts_stop (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (nonempty : ∃ v : List α, v.length = n ∧ D.Accepts (decisionData v) [])
    (bits : BitString) (stop : false ∈ bits) : (machine D).Accepts (generatorData n) bits := by
  have before : Before D n (List.replicate n first) false := by
    intro _ v _ rank
    rw [wordRank_replicate first least] at rank
    omega
  obtain ⟨output, run⟩ := cycle_accepts_stop D first least deterministic n s halts space nonempty bits
    (List.replicate n first) false 0 n (by simp) le_rfl before (by simpa using stop)
  have load := ((load_initial D first least n bits).inRegion (bank D) 0
    ((bank D).initial_bounded (generatorData n))).mono (bank D)
      (show 0 + (n + 1) ≤ radius n s by unfold radius; omega)
  have whole := run.prepend (bank D) load
  obtain ⟨ready, related, boot, region⟩ := TransducerBank.bank_loaded_inRegion (bank D)
    (generatorData n) bits (radius n s)
  obtain ⟨ticks, finish, path, terminal, _⟩ := whole.compile (bank D) (fun _ => false) ready related region
  have wholePath : (machine D).Steps (generatorData n) bits (machine D).initialConfiguration
      (1 + ticks) finish := boot.trans (machine D) path
  have observed : (machine D).observe (generatorData n) bits finish = .halted (.accepted output) := terminal
  exact ⟨output, 1 + ticks, by simpa [Machine.runFrom_initial, observed] using wholePath.runFrom (machine D)⟩

theorem machine_isGenerator (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s) :
    (machine D).IsGenerator (generatorData n) := by
  classical
  refine ⟨machine_haltingTransducer D first least deterministic n s halts space, ?_⟩
  by_cases nonempty : ∃ v : List α, v.length = n ∧ D.Accepts (decisionData v) []
  · left
    have accepted : ∀ᵐ stream ∂fairCoinMeasure, stream ∈ (machine D).acceptedStreams (generatorData n) := by
      filter_upwards [fairCoin_ae_stop_after_every_offset] with stream stops
      obtain ⟨k, _, stop⟩ := stops 0
      have present : false ∈ streamPrefix stream (k + 1) := by
        have lookup : (streamPrefix stream (k + 1))[k]? = some false := by
          apply List.getElem?_eq_some_iff.mpr
          refine ⟨by simp, ?_⟩
          simpa only [streamPrefix, List.getElem_ofFn] using stop
        exact List.mem_of_getElem? lookup
      exact ⟨streamPrefix stream (k + 1), stream_mem_prefix_cylinder _ _,
        machine_accepts_stop D first least deterministic n s halts space nonempty _ present⟩
    exact (MeasureTheory.measure_congr
      (Filter.eventuallyEqSet_univ.mpr accepted)).trans MeasureTheory.measure_univ
  · right
    have empty : (machine D).generatedLanguage (generatorData n) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro word ⟨bits, _, produces⟩
      exact nonempty ⟨word, machine_output_sound D first least deterministic n s halts space bits word produces⟩
    rw [((machine D).acceptedStreams_eq_empty_iff (generatorData n)).mpr empty]
    exact MeasureTheory.measure_empty

theorem machine_language (first : α) (least : firstLetter = some first)
    (deterministic : D.Deterministic) (n s : ℕ)
    (halts : ∀ word : List α, word.length = n → D.Halts (decisionData word) [])
    (space : ∀ word : List α, word.length = n → D.SpaceBound (decisionData word) s)
    (L : Language α) (language : ∀ word, D.Accepts (decisionData word) [] ↔ word ∈ L) :
    (machine D).generatedLanguage (generatorData n) = lengthSlice L n := by
  ext word
  constructor
  · rintro ⟨bits, _, produces⟩
    obtain ⟨length, accepts⟩ := machine_output_sound D first least deterministic n s halts space bits word produces
    exact ⟨(language word).mp accepts, length⟩
  · rintro ⟨member, length⟩
    exact machine_output_complete D first least deterministic n s halts space word length ((language word).mpr member)

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
