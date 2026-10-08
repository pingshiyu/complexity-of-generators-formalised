import ComplexityOfGenerators.Cryptography
import Mathlib.Data.List.GetD

/-!
# Fair-coin events

These facts use Mathlib's product probability measure directly. They establish
that generator and collision success probabilities are probabilities of
measurable events, rather than leaving them as arbitrary outer-measure values.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

def streamPrefix (stream : BitStream) (n : ℕ) : BitString :=
  List.ofFn (fun i : Fin n => stream i.val)

@[simp] theorem streamPrefix_length (stream : BitStream) (n : ℕ) :
    (streamPrefix stream n).length = n := by simp [streamPrefix]

theorem stream_mem_prefix_cylinder (stream : BitStream) (n : ℕ) :
    stream ∈ cylinder (streamPrefix stream n) := by
  intro i
  change stream i.val = (List.ofFn (fun j : Fin n => stream j.val))[i.val]
  rw [List.getElem_ofFn]

theorem mem_cylinder_of_prefix {stream : BitStream} {small large : BitString}
    (initial : small <+: large) (member : stream ∈ cylinder large) :
    stream ∈ cylinder small := by
  obtain ⟨extra, rfl⟩ := initial
  intro i
  have bound : i.val < (small ++ extra).length := by simp; omega
  have letter := member ⟨i.val, bound⟩
  change stream i.val = (small ++ extra)[i.val] at letter
  change stream i.val = small[i.val]
  simpa only [List.getElem_append_left i.isLt] using letter

theorem mem_cylinder_append {stream : BitStream} {first second : BitString}
    (left : stream ∈ cylinder first)
    (right : (fun i => stream (first.length + i)) ∈ cylinder second) :
    stream ∈ cylinder (first ++ second) := by
  intro i
  change stream i.val = (first ++ second)[i.val]
  by_cases inFirst : i.val < first.length
  · have letter := left ⟨i.val, inFirst⟩
    change stream i.val = first[i.val] at letter
    simpa only [List.getElem_append_left inFirst] using letter
  · have inSecond : i.val - first.length < second.length := by
      have bound := i.isLt
      simp only [List.length_append] at bound
      omega
    have offset : first.length + (i.val - first.length) = i.val := by omega
    have letter := right ⟨i.val - first.length, inSecond⟩
    change stream (first.length + (i.val - first.length)) = second[i.val - first.length] at letter
    simpa only [offset, List.getElem_append_right (by omega : first.length ≤ i.val)] using letter

instance : IsProbabilityMeasure fairCoinMeasure := by
  unfold fairCoinMeasure
  infer_instance

theorem fairCoinMeasure_le_one (s : Set BitStream) : fairCoinMeasure s ≤ 1 :=
  prob_le_one

theorem measurableSet_cylinder (b : BitString) : MeasurableSet (cylinder b) := by
  change MeasurableSet {stream : BitStream | ∀ i : Fin b.length, stream i = b[i]}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro (i : Fin b.length)
  have evaluation : Measurable (fun stream : BitStream => stream i.val) :=
    measurable_pi_apply i.val
  exact evaluation (measurableSet_singleton (b[i]))

/-- A specified prefix of `k` independent unbiased bits has mass `2⁻ᵏ`. -/
theorem fairCoinMeasure_cylinder (b : BitString) :
    fairCoinMeasure (cylinder b) = (2 : ℝ≥0∞)⁻¹ ^ b.length := by
  have description : cylinder b =
      Set.pi (Finset.range b.length) (fun i => {b.getD i false}) := by
    ext stream
    constructor
    · intro h i hi
      have hi' : i < b.length := Finset.mem_range.mp hi
      change stream i = b.getD i false
      rw [List.getD_eq_getElem b false hi']
      exact h ⟨i, hi'⟩
    · intro h i
      have eq := h i.val (Finset.mem_range.mpr i.isLt)
      change stream i.val = b.getD i.val false at eq
      rw [List.getD_eq_getElem b false i.isLt] at eq
      exact eq
  rw [description, fairCoinMeasure, Measure.infinitePi_pi]
  · simp [PMF.uniformOfFintype_apply]
  · intro i _
    exact measurableSet_singleton _

theorem Machine.measurableSet_acceptedStreams {I A O : Type}
    (M : Machine I A O) (data : InputData I A) :
    MeasurableSet (M.acceptedStreams data) := by
  classical
  have description : M.acceptedStreams data =
      ⋃ b : BitString, ⋃ (_ : M.Accepts data b), cylinder b := by
    ext stream
    simp only [Machine.acceptedStreams, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [description]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => measurableSet_cylinder b

/-- Even malformed or incorrect outputs of an attacker simply fail this event.
The union is indexed by countably many finite strings, rather than by machines. -/
theorem measurableSet_collisionSuccess (h : HashFunction) (A : CollisionFinder) (n : ℕ) :
    MeasurableSet (collisionSuccess h A n) := by
  classical
  have description : collisionSuccess h A n =
      ⋃ x : BitString, ⋃ y : BitString, ⋃ b : BitString,
        ⋃ (_ : A.machine.Produces (generatorData n) b (encodePair x y) ∧
          h.IsCollision n x y), cylinder b := by
    ext stream
    simp only [collisionSuccess, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [description]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => measurableSet_cylinder b

end ComplexityOfGenerators
