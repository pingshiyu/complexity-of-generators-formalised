import ComplexityOfGenerators.MultitapeSpaceConfigurations

/-! A finite configuration graph for an ordinary-input bank. The read-only
auxiliary and index tapes are empty. Random position and accumulated output
are omitted because the program cannot inspect them. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
open Multitape.SpaceConfigurations
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ}

@[ext] structure Snapshot (Q S : Type) (k : ℕ) where
  state : Q
  inputHead : ℕ
  head : Fin k → ℤ
  tape : Fin k → ℤ → S

def snapshot (c : BankConfiguration O Q S k) : Snapshot Q S k := ⟨c.state,c.inputHead,c.head,c.tape⟩

def Snapshot.restore (c : Snapshot Q S k) (randomHead : ℕ) (output : List O) : BankConfiguration O Q S k :=
  ⟨c.state,c.inputHead,0,0,randomHead,output,c.head,c.tape⟩

structure Valid (blank : S) (n radius : ℕ) (c : Snapshot Q S k) : Prop where
  input : c.inputHead≤n
  head : ∀ j,(c.head j).natAbs≤radius
  outside : ∀ j position, radius<position.natAbs → c.tape j position=blank

abbrev Vertex (blank : S) (n radius : ℕ) := {c : Snapshot Q S k // Valid blank n radius c}

def vertexCode (blank : S) (n radius : ℕ) (c : Vertex (Q:=Q) (k:=k) blank n radius) :
    RegionConfiguration Q S k n radius :=
  encodeOrdinary (c.val.restore 0 ([] : List Unit)) n radius c.property.input (Nat.zero_le _) c.property.head

theorem vertexCode_injective (blank : S) (n radius : ℕ) :
    Function.Injective (vertexCode (Q:=Q) (k:=k) blank n radius) := by
  intro first second same
  apply Subtype.ext
  apply Snapshot.ext
  · exact congrArg RegionConfiguration.state same
  · exact congrArg (fun code => code.indexHead.val) same
  · funext j
    have equal := congrArg (fun code => position radius (code.head j)) same
    simpa only [vertexCode,encodeOrdinary,Snapshot.restore,position_coordinate] using equal
  · funext j p
    by_cases inside : p.natAbs≤radius
    · have equal := congrArg (fun code => code.tape j (coordinate radius p inside)) same
      simpa only [vertexCode,encodeOrdinary,Snapshot.restore,position_coordinate] using equal
    · rw [first.property.outside j p (by omega),second.property.outside j p (by omega)]

noncomputable instance [Fintype Q] [Fintype S] (blank : S) (n radius : ℕ) :
    Fintype (Vertex (Q:=Q) (k:=k) blank n radius) :=
  Fintype.ofInjective (vertexCode blank n radius) (vertexCode_injective blank n radius)

theorem vertex_card_le [Fintype Q] [Fintype S] (blank : S) (n radius : ℕ) :
    Fintype.card (Vertex (Q:=Q) (k:=k) blank n radius) ≤ 2^(clockWidth (Q:=Q) (S:=S) (k:=k) n radius) :=
  (Fintype.card_le_of_injective _ (vertexCode_injective blank n radius)).trans (region_card_le_clock n radius)

def initialSnapshot (source : TapeBank I A O Q S k) : Snapshot Q S k :=
  ⟨source.initial,0,fun _=>0,fun _ _=>source.blank⟩

theorem initial_valid (source : TapeBank I A O Q S k) (n radius : ℕ) :
    Valid source.blank n radius (initialSnapshot source) := by
  constructor <;> simp [initialSnapshot]

def initialVertex (source : TapeBank I A O Q S k) (n radius : ℕ) :
    Vertex (Q:=Q) (k:=k) source.blank n radius := ⟨initialSnapshot source,initial_valid source n radius⟩

end ComplexityOfGenerators.Simulation.TransducerBank.SpaceShortRuns
