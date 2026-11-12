import ComplexityOfGenerators.Foundations.OriginalSourceSampler
import ComplexityOfGenerators.Foundations.FreshStreamListSequence
import ComplexityOfGenerators.Foundations.FreshStreamTails
import ComplexityOfGenerators.ExpectedGenerators

/-! Tagged original-source calls retain the family index and the exact
consumed random prefix. All costs are original primitive runtimes. -/
namespace ComplexityOfGenerators.OriginalSourceFamilySampler
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type}

abbrev Request := Bool × ℕ
abbrev Record := Bool × ℕ × Option BitString

def request (record : Record) : Request := (record.1,record.2.1)
def coins (record : Record) : ℕ := (record.2.2.getD []).length

variable (families : Bool → UniformGenerators α)

def word (record : Record) : List α :=
  match record.2.2 with
  | none => []
  | some bits => Machine.OriginalSource.output (families record.1).machine (generatorData record.2.1) bits

def time (record : Record) : ℕ :=
  match record.2.2 with
  | none => 0
  | some bits => Machine.OriginalSource.time (families record.1).machine (generatorData record.2.1) bits

def words (records : List Record) : List α := (records.map (word families)).flatten
def totalTime (records : List Record) : ℕ := (records.map (time families)).sum
def consumed (records : List Record) : ℕ := (records.map coins).sum

def call (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty) :
    FreshStreamSampler Record :=
  (Machine.OriginalSource.sampler (families tag).machine (generatorData index)
    ((families tag).isGenerator index) active).map
      (fun bits => (tag,index,bits)) (measurable_of_countable _)

theorem call_request (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty)
    (stream : BitStream) : request ((call families tag index active).run stream).1=(tag,index) := rfl

theorem call_tail (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty)
    (stream : BitStream) :
    ((call families tag index active).run stream).2=
      fun i => stream (coins ((call families tag index active).run stream).1+i) := rfl

def NativeTrace (stream : BitStream) (record : Record) : Prop :=
  ∃ bits finish, record.2.2=some bits ∧ stream∈cylinder bits ∧
    (families record.1).machine.Steps (generatorData record.2.1) bits
      (families record.1).machine.initialConfiguration (time families record) finish ∧
    (families record.1).machine.observe (generatorData record.2.1) bits finish=
      .halted (.accepted (word families record)) ∧ finish.randomHead=coins record

theorem call_native_ae (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty) :
    ∀ᵐ stream∂fairCoinMeasure, NativeTrace families stream ((call families tag index active).run stream).1 := by
  filter_upwards [Machine.OriginalSource.ae_native (families tag).machine (generatorData index)
    ((families tag).isGenerator index) active] with stream trace
  obtain ⟨bits,finish,selected,member,path,terminal,cursor,_,_⟩ := trace
  refine ⟨bits,finish,selected,member,?_,?_,?_⟩
  · simpa only [call,FreshStreamSampler.map,Machine.OriginalSource.sampler,time,selected] using path
  · simpa only [call,FreshStreamSampler.map,Machine.OriginalSource.sampler,word,selected] using terminal
  · simpa only [call,FreshStreamSampler.map,Machine.OriginalSource.sampler,coins,selected,Option.getD_some] using cursor

theorem call_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty) :
    (∫⁻ stream,((word families ((call families tag index active).run stream).1).length : ℝ≥0∞)
      ∂fairCoinMeasure)=(index : ℝ≥0∞) := by
  have same : ∀ stream, ((word families ((call families tag index active).run stream).1).length : ℝ≥0∞)=
      Machine.OriginalSource.recordedLength (families tag).machine (generatorData index)
        (Machine.OriginalSource.seed (families tag).machine (generatorData index) stream) := by
    intro stream
    cases selected : Machine.OriginalSource.seed (families tag).machine (generatorData index) stream <;>
      simp [word,call,FreshStreamSampler.map,Machine.OriginalSource.sampler,
        Machine.OriginalSource.recordedLength,selected]
  simp_rw [same]
  rw [Machine.OriginalSource.lintegral_recordedLength (families tag).machine (generatorData index)
    ((families tag).isGenerator index) active]
  exact mean tag index active

theorem call_runtime (tag : Bool) (index : ℕ) (active : ((families tag).layer index).Nonempty) :
    (∫⁻ stream,(time families ((call families tag index active).run stream).1 : ℝ≥0∞)∂fairCoinMeasure)=
      (families tag).machine.expectedRuntime (generatorData index) := by
  have same : ∀ stream, (time families ((call families tag index active).run stream).1 : ℝ≥0∞)=
      Machine.OriginalSource.recordedTime (families tag).machine (generatorData index)
        (Machine.OriginalSource.seed (families tag).machine (generatorData index) stream) := by
    intro stream
    cases selected : Machine.OriginalSource.seed (families tag).machine (generatorData index) stream <;>
      simp [time,call,FreshStreamSampler.map,Machine.OriginalSource.sampler,
        Machine.OriginalSource.recordedTime,selected]
  simp_rw [same]
  exact Machine.OriginalSource.lintegral_recordedTime (families tag).machine (generatorData index)
    ((families tag).isGenerator index) active

end
end ComplexityOfGenerators.OriginalSourceFamilySampler
