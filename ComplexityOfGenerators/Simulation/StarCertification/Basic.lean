import ComplexityOfGenerators.Simulation.WordStack.BoundedSource
import ComplexityOfGenerators.Simulation.StarPaths.Stage
import ComplexityOfGenerators.Simulation.StarPaths.NativeProposal
import ComplexityOfGenerators.Foundations.IndexwiseCertification

/-! An actual bounded scan of source indices 1 through n. Source symbols and
path-control symbols occupy disjoint sides of one finite alphabet. -/
namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

abbrev Cell := Sum (Source.Symbol M) StarPaths.Symbol
abbrev Store := Local.Store (Cell M) 35
abbrev Step := WordStack.Routine (Cell M) α 35

def unit : Cell M := .inr .unit
def bitSymbol (bit : Bool) : Cell M := .inr (StarPaths.coinSymbol bit)
def flagSymbol (flag : Bool) : Cell M := .inr (StarPaths.flagSymbol flag)
def cacheWord (flags : List Bool) : List (Cell M) := flags.map (flagSymbol M)
def encode : Source.Symbol M → Cell M := Sum.inl

def decode : Cell M → Source.Symbol M
  | .inl cell => cell
  | .inr _ => .unit

def bitMap : Cell M → Cell M
  | .inr .bitTrue => .inl (.bit true)
  | _ => .inl (.bit false)

@[simp] theorem decode_encode (cell : Source.Symbol M) : decode M (encode M cell) = cell := rfl
@[simp] theorem bitMap_bit (bit : Bool) : bitMap M (bitSymbol M bit) = encode M (.bit bit) := by cases bit <;> rfl

def accepted : Option (Cell M) → Bool
  | some (.inl (.state .accepted)) => true
  | _ => false

set_option backward.isDefEq.respectTransparency true

noncomputable def trial (p : PolynomialBound) : Step M :=
  BoundedSource.sourceTrial (unit M) (bitSymbol M) M (encode M) (decode M)
    (fun _ => encode M .unit) (fun _ => encode M .unit) (bitMap M)
    (IndexwiseCertification.seed p) (IndexwiseCertification.clock p)

def bodyPrefix : Step M :=
  (WordStack.Routine.ofLocal (Local.push 24 (unit M))).seq
    ((WordStack.Routine.assign 24 13 15 (by decide) (by decide) (by decide) id).seq
      (WordStack.Routine.clearMany [11,12,14]))

def record : Step M := WordStack.Routine.branch 0 fun state =>
  WordStack.Routine.ofLocal (Local.push 25 (flagSymbol M (accepted M state)))

noncomputable def body (p : PolynomialBound) : Step M := bodyPrefix M |>.seq ((trial M p).seq (record M))

theorem trial_frame (p : PolynomialBound) (j : Fin 35) (upper : 22 ≤ j.val) : (trial M p).Fixes j := by
  intro s
  have frame := BoundedSource.sourceTrial_outside (O := α) (unit M) (bitSymbol M) M (encode M) (decode M)
    (fun _ => encode M .unit) (fun _ => encode M .unit) (bitMap M)
    (IndexwiseCertification.seed p) (IndexwiseCertification.clock p) s j (by omega) (by omega)
  simpa [trial,BoundedSource.trialPrepared,show j ≠ 14 from by omega,show j ≠ 15 from by omega,
    show j ≠ 16 from by omega,show j ≠ 17 from by omega,show j ≠ 18 from by omega,
    show j ≠ 19 from by omega,show j ≠ 20 from by omega,show j ≠ 21 from by omega] using frame

theorem bodyPrefix_frame (j : Fin 35) (a : j ≠ 11) (b : j ≠ 12) (c : j ≠ 13) (d : j ≠ 14)
    (e : j ≠ 15) (f : j ≠ 24) : (bodyPrefix M).Fixes j := by
  intro s
  simp [bodyPrefix,WordStack.Routine.seq,WordStack.Routine.ofLocal,Local.eval_push,
    WordStack.Routine.assign_eval,WordStack.Routine.clearMany_eval,a,b,c,d,e,f]

theorem record_frame (j : Fin 35) (different : j ≠ 25) : (record M).Fixes j := by
  unfold record
  apply WordStack.Routine.Fixes.branch
  intro state
  exact WordStack.Routine.fixes_push 25 j _ different

theorem body_frame (p : PolynomialBound) (j : Fin 35) (upper : 22 ≤ j.val) (a : j ≠ 24) (b : j ≠ 25) :
    (body M p).Fixes j := by
  unfold body
  exact (bodyPrefix_frame M j (by omega) (by omega) (by omega) (by omega) (by omega) a).seq
    ((trial_frame M p j upper).seq (record_frame M j b))

noncomputable def scan (p : PolynomialBound) : Step M := WordStack.Routine.iterate 23 (body M p)
  (body_frame M p 23 (by decide) (by decide) (by decide))

def prepare : Step M :=
  (WordStack.Routine.clear 24).seq ((WordStack.Routine.clear 25).seq
    (WordStack.Routine.assign 22 23 33 (by decide) (by decide) (by decide) (fun _ => unit M)))

def finish : Step M :=
  (WordStack.Routine.clear 34).seq ((WordStack.Routine.transfer 25 34 (by decide) id).seq
    ((WordStack.Routine.assign 34 25 33 (by decide) (by decide) (by decide) id).seq (WordStack.Routine.clear 34)))

noncomputable def routine (p : PolynomialBound) : Step M := (prepare M).seq ((scan M p).seq (finish M))

end ComplexityOfGenerators.Simulation.StarCertification
