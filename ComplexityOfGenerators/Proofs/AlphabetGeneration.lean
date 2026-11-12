import ComplexityOfGenerators.Foundations.SymbolRelabel
import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties

/-! Concrete, clock-preserving alphabet transport for the three generator
classes. Output relabelling is the native finite transition-table construction;
no closure property or alphabet-invariance hypothesis is assumed. -/
namespace ComplexityOfGenerators.AlphabetGeneration
open Simulation MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β]

@[simp] theorem identityData (n : ℕ) :
    SymbolRelabel.data (id : Unit→Unit) (id : Bool→Bool) (generatorData n)=generatorData n := by
  simp [SymbolRelabel.data,generatorData]

def family (G : UniformGenerators α) (f : α→β) : UniformGenerators β where
  machine := SymbolRelabel.machine G.machine id id f
  isGenerator n := SymbolRelabel.generator G.machine id id f (generatorData n) (G.isGenerator n)

theorem layer (G : UniformGenerators α) (f : α→β) (n : ℕ) :
    (family G f).layer n=List.map f '' G.layer n :=
  SymbolRelabel.language G.machine id id f (generatorData n)

theorem language (G : UniformGenerators α) (f : α→β) :
    (family G f).language=List.map f '' G.language := by
  ext word
  constructor
  · rintro ⟨n,member⟩
    rw [layer] at member
    obtain ⟨source,member,rfl⟩ := member
    exact ⟨source,⟨n,member⟩,rfl⟩
  · rintro ⟨source,⟨n,member⟩,rfl⟩
    exact ⟨n,by rw [layer];exact ⟨source,member,rfl⟩⟩

theorem activeIndices (G : UniformGenerators α) (f : α→β) :
    (family G f).activeIndices=G.activeIndices := by
  ext n
  change ((family G f).layer n).Nonempty ↔ (G.layer n).Nonempty
  rw [layer,Set.image_nonempty]

theorem streamLength (G : UniformGenerators α) (f : α→β) (n : ℕ) (stream : BitStream) :
    (family G f).machine.streamLength (generatorData n) stream=
      G.machine.streamLength (generatorData n) stream := by
  by_cases accepted : stream∈G.machine.acceptedStreams (generatorData n)
  · obtain ⟨bits,cylinder,word,source⟩ := accepted
    have produced : G.machine.streamProduces (generatorData n) stream word := ⟨bits,cylinder,source⟩
    have target : (family G f).machine.streamProduces (generatorData n) stream (word.map f) := by
      refine ⟨bits,cylinder,?_⟩
      exact (SymbolRelabel.produces G.machine id id f (generatorData n) bits _).mpr ⟨word,source,rfl⟩
    rw [(family G f).machine.streamLength_of_produces _ target,G.machine.streamLength_of_produces _ produced,
      List.length_map]
  · have absent : stream∉(family G f).machine.acceptedStreams (generatorData n) := by
      change stream∉(SymbolRelabel.machine G.machine id id f).acceptedStreams (generatorData n)
      simpa only [SymbolRelabel.streams,identityData] using accepted
    rw [(family G f).machine.streamLength_eq_zero_of_not_accepted _ absent,
      G.machine.streamLength_eq_zero_of_not_accepted _ accepted]

theorem streamAcceptsBy (G : UniformGenerators α) (f : α→β) (n : ℕ) (stream : BitStream) (t : ℕ) :
    (family G f).machine.streamAcceptsBy (generatorData n) stream t ↔
      G.machine.streamAcceptsBy (generatorData n) stream t := by
  constructor
  · rintro ⟨bits,word,cylinder,accepted⟩
    change (SymbolRelabel.machine G.machine id id f).run (generatorData n) bits t=.halted (.accepted word) at accepted
    rw [SymbolRelabel.run,identityData] at accepted
    cases source : G.machine.run (generatorData n) bits t with
    | running c=>simp [source,SymbolRelabel.state] at accepted
    | halted terminal=>
        cases terminal with
        | accepted original=>exact ⟨bits,original,cylinder,source⟩
        | rejected=>simp [source,SymbolRelabel.state,SymbolRelabel.outcome] at accepted
        | exhausted=>simp [source,SymbolRelabel.state,SymbolRelabel.outcome] at accepted
  · rintro ⟨bits,word,cylinder,accepted⟩
    refine ⟨bits,word.map f,cylinder,?_⟩
    change (SymbolRelabel.machine G.machine id id f).run (generatorData n) bits t=.halted (.accepted (word.map f))
    rw [SymbolRelabel.run,identityData,accepted]
    rfl

theorem streamRuntime (G : UniformGenerators α) (f : α→β) (n : ℕ) (stream : BitStream) :
    (family G f).machine.streamRuntime (generatorData n) stream=
      G.machine.streamRuntime (generatorData n) stream := by
  classical
  simp only [Machine.streamRuntime,streamAcceptsBy]

theorem expectedLength (G : UniformGenerators α) (f : α→β) (n : ℕ) :
    (family G f).machine.expectedLength (generatorData n)=G.machine.expectedLength (generatorData n) := by
  simp only [Machine.expectedLength,streamLength]

theorem expectedRuntime (G : UniformGenerators α) (f : α→β) (n : ℕ) :
    (family G f).machine.expectedRuntime (generatorData n)=G.machine.expectedRuntime (generatorData n) := by
  simp only [Machine.expectedRuntime,streamRuntime]

def exactFamily (G : GeneratorFamily α) (f : α→β) : GeneratorFamily β where
  toUniformGenerators := family G.toUniformGenerators f
  outputLength := by
    intro n word member
    rw [layer] at member
    obtain ⟨source,member,rfl⟩ := member
    simpa using G.outputLength n source member

theorem pg_image {L : Language α} (f : α→β) (member : L∈PG α) : List.map f '' L∈PG β := by
  obtain ⟨G,equal,seed,time,bounded⟩ := member
  refine ⟨exactFamily G f,?_,seed,time,?_⟩
  · rw [show (exactFamily G f).toUniformGenerators=family G.toUniformGenerators f from rfl,language,equal]
  · intro n
    exact SymbolRelabel.trialBound G.machine id id f (generatorData n) (seed n) (time n) (bounded n)

theorem expectedPolynomialTime (G : UniformGenerators α) (f : α→β)
    (expected : G.ExpectedPolynomialTime) : (family G f).ExpectedPolynomialTime := by
  obtain ⟨p,runtime,fast⟩ := expected
  refine ⟨p,?_,?_⟩
  · intro n active
    rw [layer,Set.image_nonempty] at active
    rw [expectedRuntime]
    exact runtime n active
  · intro n word member
    rw [layer] at member
    obtain ⟨source,member,rfl⟩ := member
    obtain ⟨bits,nonempty,accepted⟩ := fast n source member
    refine ⟨bits,nonempty,?_⟩
    change (SymbolRelabel.machine G.machine id id f).run (generatorData n) bits (p n)=.halted (.accepted (source.map f))
    rw [SymbolRelabel.run,identityData,accepted]
    rfl

theorem epg_image {L : Language α} (f : α→β) (member : L∈EPG α) : List.map f '' L∈EPG β := by
  obtain ⟨G,equal,expected⟩ := member
  refine ⟨exactFamily G f,?_,expectedPolynomialTime G.toUniformGenerators f expected⟩
  rw [show (exactFamily G f).toUniformGenerators=family G.toUniformGenerators f from rfl,language,equal]

theorem globalWordTime (G : UniformGenerators α) (f : α→β)
    (fast : G.GlobalWordPolynomialTime) : (family G f).GlobalWordPolynomialTime := by
  obtain ⟨p,fast⟩ := fast
  refine ⟨p,?_⟩
  intro word member
  rw [language] at member
  obtain ⟨source,member,rfl⟩ := member
  obtain ⟨n,bits,nonempty,accepted⟩ := fast source member
  refine ⟨n,bits,nonempty,?_⟩
  change (SymbolRelabel.machine G.machine id id f).run (generatorData n) bits (p (source.map f).length)=.halted (.accepted (source.map f))
  rw [List.length_map,SymbolRelabel.run,identityData,accepted]
  rfl

theorem elepg_image {L : Language α} (f : α→β) (infinite : (List.map f '' L).Infinite)
    (member : L∈ELEPG α) : List.map f '' L∈ELEPG β := by
  obtain ⟨_,G,equal,active,mean,⟨p,runtime⟩,fast⟩ := member
  refine ⟨infinite,family G f,?_,?_,?_,?_,globalWordTime G f fast⟩
  · rw [language,equal]
  · rw [activeIndices]
    exact active
  · intro n member
    change n∈(family G f).activeIndices at member
    rw [activeIndices] at member
    rw [expectedLength]
    exact mean n member
  · refine ⟨p,?_⟩
    intro n member
    rw [activeIndices] at member
    rw [expectedRuntime]
    exact runtime n member

end
end ComplexityOfGenerators.AlphabetGeneration
