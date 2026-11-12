import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Paths
import ComplexityOfGenerators.Foundations.FreshStreamSamplers

/-! The completed source call is identified by its minimal accepting random
prefix. These prefixes form a measurable prefix-free partition of the actual
accepted streams; the empty prefix is allowed. -/
namespace ComplexityOfGenerators.Machine
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem MinimalAcceptedSeed.eq_of_prefix {first second : BitString}
    (a : M.MinimalAcceptedSeed data first) (b : M.MinimalAcceptedSeed data second)
    (initial : first <+: second) : first=second := by
  have bound := initial.length_le
  have description := List.prefix_iff_eq_take.mp initial
  have notShorter : ¬first.length<second.length := by
    intro shorter
    exact b.2 first.length shorter (description ▸ a.1)
  have length : first.length=second.length := by omega
  simpa only [length,List.take_length] using description

theorem MinimalAcceptedSeed.eq_of_common_stream {first second : BitString} {stream : BitStream}
    (a : M.MinimalAcceptedSeed data first) (b : M.MinimalAcceptedSeed data second)
    (left : stream∈cylinder first) (right : stream∈cylinder second) : first=second := by
  rcases le_total first.length second.length with short | short
  · exact a.eq_of_prefix M data b (cylinder_prefix_comparable left right short)
  · exact (b.eq_of_prefix M data a (cylinder_prefix_comparable right left short)).symm

namespace OriginalSource

instance recordMeasurableSpace : MeasurableSpace (Option BitString) := ⊤
instance recordMeasurableSingletonClass : MeasurableSingletonClass (Option BitString) where
  measurableSet_singleton _ := trivial

theorem exists_seed {stream : BitStream} (accepted : stream∈M.acceptedStreams data) :
    ∃ bits, stream∈cylinder bits ∧ M.MinimalAcceptedSeed data bits := by
  rw [M.acceptedStreams_eq_minimal_prefixes data] at accepted
  exact accepted

/-- The actual shortest accepting random prefix, with `none` on streams
that never accept. Its length will equal the native terminal random cursor. -/
def seed (stream : BitStream) : Option BitString := by
  classical
  exact if accepted : stream∈M.acceptedStreams data then
    some (Classical.choose (exists_seed M data accepted)) else none

theorem seed_spec {stream : BitStream} (accepted : stream∈M.acceptedStreams data) :
    ∃ bits, seed M data stream=some bits ∧ stream∈cylinder bits ∧ M.MinimalAcceptedSeed data bits := by
  classical
  unfold seed
  rw [dite_eq_left accepted]
  exact ⟨_,rfl,Classical.choose_spec (exists_seed M data accepted)⟩

theorem seed_eq_some_iff (stream : BitStream) (bits : BitString) :
    seed M data stream=some bits ↔ M.MinimalAcceptedSeed data bits ∧ stream∈cylinder bits := by
  classical
  constructor
  · intro selected
    have accepted : stream∈M.acceptedStreams data := by
      by_contra absent
      simp [seed,absent] at selected
    obtain ⟨found,equal,member,minimal⟩ := seed_spec M data accepted
    have same : found=bits := Option.some.inj (equal.symm.trans selected)
    exact same ▸ ⟨minimal,member⟩
  · rintro ⟨minimal,member⟩
    obtain ⟨found,selected,foundMember,foundMinimal⟩ := seed_spec M data ⟨bits,member,minimal.1⟩
    have same := foundMinimal.eq_of_common_stream M data minimal foundMember member
    simpa only [same] using selected

theorem seed_eq_none_iff (stream : BitStream) :
    seed M data stream=none ↔ stream∉M.acceptedStreams data := by
  classical
  by_cases accepted : stream∈M.acceptedStreams data
  · obtain ⟨bits,equal,_⟩ := seed_spec M data accepted
    simp [equal,accepted]
  · simp [seed,accepted]

theorem measurable_seed : Measurable (seed M data) := by
  classical
  apply measurable_to_countable'
  intro result
  cases result with
  | none =>
      have description : seed M data ⁻¹' {none}=(M.acceptedStreams data)ᶜ := by
        ext stream
        exact seed_eq_none_iff M data stream
      rw [description]
      exact (M.measurableSet_acceptedStreams data).compl
  | some bits =>
      have description : seed M data ⁻¹' {some bits}=
          if M.MinimalAcceptedSeed data bits then cylinder bits else ∅ := by
        ext stream
        simp only [Set.mem_preimage,Set.mem_singleton_iff,seed_eq_some_iff]
        split_ifs <;> simp_all
      rw [description]
      split_ifs
      · exact measurableSet_cylinder bits
      · exact MeasurableSet.empty

def tail (stream : BitStream) : BitStream :=
  (splitStream ((seed M data stream).getD []).length stream).2

theorem measurable_tail : Measurable (tail M data) := by
  let shift : Option BitString × BitStream → BitStream :=
    fun pair => (splitStream (pair.1.getD []).length pair.2).2
  have shifted : Measurable shift := by
    apply measurable_from_prod_countable_right
    intro bits
    change Measurable (fun stream : BitStream => (splitStream (bits.getD []).length stream).2)
    exact measurable_snd.comp (measurable_splitStream _)
  exact shifted.comp ((measurable_seed M data).prodMk measurable_id)

theorem tail_of_seed {stream : BitStream} {bits : BitString}
    (selected : seed M data stream=some bits) :
    tail M data stream=(splitStream bits.length stream).2 := by
  change (splitStream ((seed M data stream).getD []).length stream).2=_
  rw [selected]
  rfl

theorem ae_accepted (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    ∀ᵐ stream∂fairCoinMeasure, stream∈M.acceptedStreams data := by
  have mass := (M.generator_probability_one_iff_nonempty data generator).mpr active
  apply ae_iff.mpr
  change fairCoinMeasure (M.acceptedStreams data)ᶜ=0
  rw [measure_compl (M.measurableSet_acceptedStreams data) (by simp [mass]),mass]
  simp

end OriginalSource
end
end ComplexityOfGenerators.Machine
