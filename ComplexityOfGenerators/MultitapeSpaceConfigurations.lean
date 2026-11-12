import ComplexityOfGenerators.MultitapeSpace
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-! Finite codes for bounded-space generator/output-matcher configurations.
Random-tape positions are omitted: the configuration graph chooses each next
bit nondeterministically. Output is represented by its prefix position and a
mismatch bit, since the source cannot inspect its output tape. -/
namespace ComplexityOfGenerators.Multitape.SpaceConfigurations
open Simulation.TransducerBank
variable {Q S O : Type} {k : ℕ}

@[ext] structure RegionConfiguration (Q S : Type) (k n radius : ℕ) where
  state : Q
  indexHead : Fin (n+1)
  outputHead : Fin (n+1)
  mismatch : Bool
  head : Fin k → Fin (2*radius+1)
  tape : Fin k → Fin (2*radius+1) → S

def position (radius : ℕ) (index : Fin (2*radius+1)) : ℤ := (index.val : ℤ)-radius

def coordinate (radius : ℕ) (position : ℤ) (bounded : position.natAbs ≤ radius) : Fin (2*radius+1) :=
  ⟨(position+(radius : ℤ)).toNat,by cases position <;> simp_all <;> omega⟩

theorem position_coordinate (radius : ℕ) (value : ℤ) (bounded : value.natAbs ≤ radius) :
    position radius (coordinate radius value bounded) = value := by
  dsimp [position,coordinate]
  cases value <;> simp_all <;> omega

noncomputable def encode (target : List O) (configuration : BankConfiguration O Q S k)
    (n radius : ℕ) (indexBound : configuration.indexHead ≤ n)
    (outputBound : configuration.output.length ≤ n)
    (headBound : ∀ j, (configuration.head j).natAbs ≤ radius) : RegionConfiguration Q S k n radius := by
  classical
  exact {
    state := configuration.state
    indexHead := ⟨configuration.indexHead,by omega⟩
    outputHead := ⟨configuration.output.length,by omega⟩
    mismatch := decide (configuration.output ≠ target.take configuration.output.length)
    head := fun j => coordinate radius (configuration.head j) (headBound j)
    tape := fun j index => configuration.tape j (position radius index) }

theorem encode_scanned_cell (target : List O) (configuration : BankConfiguration O Q S k)
    (n radius : ℕ) (indexBound : configuration.indexHead ≤ n)
    (outputBound : configuration.output.length ≤ n)
    (headBound : ∀ j, (configuration.head j).natAbs ≤ radius) (j : Fin k) :
    (encode target configuration n radius indexBound outputBound headBound).tape j
      ((encode target configuration n radius indexBound outputBound headBound).head j) =
      configuration.tape j (configuration.head j) := by
  simp only [encode,position_coordinate]

/-- An ordinary-input decision configuration uses the two finite pointer
slots for its physical input and index heads. Its output and random position
are unobservable to the transition table. -/
def encodeOrdinary (configuration : BankConfiguration O Q S k) (n radius : ℕ)
    (inputBound : configuration.inputHead ≤ n) (indexBound : configuration.indexHead ≤ n)
    (headBound : ∀ j, (configuration.head j).natAbs ≤ radius) : RegionConfiguration Q S k n radius := {
  state := configuration.state
  indexHead := ⟨configuration.inputHead,by omega⟩
  outputHead := ⟨configuration.indexHead,by omega⟩
  mismatch := false
  head := fun j => coordinate radius (configuration.head j) (headBound j)
  tape := fun j index => configuration.tape j (position radius index) }

theorem encodeOrdinary_scanned_cell (configuration : BankConfiguration O Q S k) (n radius : ℕ)
    (inputBound : configuration.inputHead ≤ n) (indexBound : configuration.indexHead ≤ n)
    (headBound : ∀ j, (configuration.head j).natAbs ≤ radius) (j : Fin k) :
    (encodeOrdinary configuration n radius inputBound indexBound headBound).tape j
      ((encodeOrdinary configuration n radius inputBound indexBound headBound).head j) =
      configuration.tape j (configuration.head j) := by
  simp only [encodeOrdinary,position_coordinate]

theorem encodeOrdinary_instruction_eq {I A : Type} (B : TapeBank I A O Q S k) (data : InputData I A)
    (first second : BankConfiguration O Q S k) (n radius : ℕ)
    (firstInput : first.inputHead ≤ n) (firstIndex : first.indexHead ≤ n)
    (firstHeads : ∀ j, (first.head j).natAbs ≤ radius)
    (secondInput : second.inputHead ≤ n) (secondIndex : second.indexHead ≤ n)
    (secondHeads : ∀ j, (second.head j).natAbs ≤ radius)
    (auxiliary : first.auxiliaryHead=second.auxiliaryHead)
    (same : encodeOrdinary first n radius firstInput firstIndex firstHeads =
      encodeOrdinary second n radius secondInput secondIndex secondHeads) :
    B.instruction data first=B.instruction data second := by
  have states := congrArg RegionConfiguration.state same
  have inputs := congrArg (fun code => code.indexHead.val) same
  have indices := congrArg (fun code => code.outputHead.val) same
  have heads (j : Fin k) : first.head j=second.head j := by
    have equal := congrArg (fun code => position radius (code.head j)) same
    simpa only [encodeOrdinary,position_coordinate] using equal
  have cells (j : Fin k) : first.tape j (first.head j)=second.tape j (second.head j) := by
    have equal := congrArg (fun code => code.tape j (code.head j)) same
    simpa only [encodeOrdinary,position_coordinate] using equal
  change first.state=second.state at states
  change first.inputHead=second.inputHead at inputs
  change first.indexHead=second.indexHead at indices
  have scanned := cells (B.select second.state)
  rw [heads] at scanned
  simp only [TapeBank.instruction]
  rw [states,inputs,indices,auxiliary,heads,scanned]

private def regionEquiv (Q S : Type) (k n radius : ℕ) :
    RegionConfiguration Q S k n radius ≃
      Q × Fin (n+1) × Fin (n+1) × Bool × (Fin k → Fin (2*radius+1)) ×
        (Fin k → Fin (2*radius+1) → S) where
  toFun c := (c.state,c.indexHead,c.outputHead,c.mismatch,c.head,c.tape)
  invFun c := ⟨c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [Fintype Q] [Fintype S] (n radius : ℕ) :
    Fintype (RegionConfiguration Q S k n radius) :=
  Fintype.ofEquiv _ (regionEquiv Q S k n radius).symm

theorem region_card [Fintype Q] [Fintype S] (n radius : ℕ) :
    Fintype.card (RegionConfiguration Q S k n radius) =
      2*Fintype.card Q*(n+1)^2*(2*radius+1)^k*(Fintype.card S)^(k*(2*radius+1)) := by
  rw [Fintype.card_congr (regionEquiv Q S k n radius)]
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_fun]
  rw [← pow_mul]
  ring

private theorem le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have positive : 0 < 2^n := pow_pos (by decide) _
    rw [pow_succ]
    omega

/-- A linear-in-space width for an exponential configuration clock. -/
def clockWidth [Fintype Q] [Fintype S] (n radius : ℕ) : ℕ :=
  Fintype.card Q+2*Nat.clog 2 (n+1)+2*(Fintype.card S+1)*k*(radius+1)+2

theorem region_card_le_clock [Fintype Q] [Fintype S] (n radius : ℕ) :
    Fintype.card (RegionConfiguration Q S k n radius) ≤ 2^(clockWidth (Q := Q) (S := S) (k := k) n radius) := by
  rw [region_card]
  have indexBound := Nat.le_pow_clog (by decide : 1 < 2) (n+1)
  have headBound : 2*radius+1 ≤ 2^(2*(radius+1)) :=
    (le_two_pow (2*radius+1)).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have symbolBound := le_two_pow (Fintype.card S)
  calc
    _ ≤ 2*2^(Fintype.card Q)*(2^(Nat.clog 2 (n+1)))^2*
        (2^(2*(radius+1)))^k*(2^(Fintype.card S))^(k*(2*radius+1)) := by
      gcongr
      · exact le_two_pow (Fintype.card Q)
    _ = 2^(1+Fintype.card Q+2*Nat.clog 2 (n+1)+2*k*(radius+1)+Fintype.card S*k*(2*radius+1)) := by
      simp only [← pow_mul]
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [clockWidth]
      nlinarith

theorem clockWidth_linear [Fintype Q] [Fintype S] (n radius : ℕ) :
    clockWidth (Q := Q) (S := S) (k := k) n radius ≤
      (Fintype.card Q+2*(Fintype.card S+1)*k+4)*(radius+Nat.clog 2 (n+1)+1) := by
  let total := radius+Nat.clog 2 (n+1)+1
  have base : Fintype.card Q+2 ≤ (Fintype.card Q+2)*total :=
    Nat.le_mul_of_pos_right _ (by dsimp [total]; omega)
  have logarithm : 2*Nat.clog 2 (n+1) ≤ 2*total :=
    Nat.mul_le_mul_left _ (by dsimp [total]; omega)
  have work : 2*(Fintype.card S+1)*k*(radius+1) ≤ 2*(Fintype.card S+1)*k*total :=
    Nat.mul_le_mul_left _ (by dsimp [total]; omega)
  change _ ≤ (Fintype.card Q+2*(Fintype.card S+1)*k+4)*total
  calc
    _ ≤ (Fintype.card Q+2)*total+2*total+2*(Fintype.card S+1)*k*total := by
      dsimp only [clockWidth]
      omega
    _ = _ := by ring

/-- Removing a repeated vertex preserves the endpoints of a directed walk. -/
theorem exists_simple_chain {C : Type} {R : C → C → Prop} {source target : C}
    (reachable : Relation.ReflTransGen R source target) :
    ∃ tail : List C, (source::tail).IsChain R ∧ (source::tail).Nodup ∧
      (source::tail).getLast (by simp) = target := by
  classical
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[],.singleton _,by simp,rfl⟩
  | @head source next edge rest ih =>
    obtain ⟨tail,chain,nodup,last⟩ := ih
    by_cases repeated : source ∈ next::tail
    · obtain ⟨before,after,equal⟩ := List.mem_iff_append.mp repeated
      refine ⟨after,?_,?_,?_⟩
      · rw [equal] at chain
        exact chain.right_of_append
      · rw [equal] at nodup
        exact nodup.of_append_right
      · simpa [equal] using last
    · exact ⟨next::tail,.cons_cons edge chain,by simpa using And.intro repeated nodup,by simpa using last⟩

theorem exists_short_chain {C : Type} [Fintype C] {R : C → C → Prop} {source target : C}
    (reachable : Relation.ReflTransGen R source target) :
    ∃ tail : List C, (source::tail).IsChain R ∧ tail.length < Fintype.card C ∧
      (source::tail).getLast (by simp) = target := by
  obtain ⟨tail,chain,nodup,last⟩ := exists_simple_chain reachable
  exact ⟨tail,chain,by have small := nodup.length_le_card; simp only [List.length_cons] at small; omega,last⟩

theorem exists_short_region_chain [Fintype Q] [Fintype S] (n radius : ℕ)
    (R : RegionConfiguration Q S k n radius → RegionConfiguration Q S k n radius → Prop)
    {source target : RegionConfiguration Q S k n radius}
    (reachable : Relation.ReflTransGen R source target) :
    ∃ tail : List (RegionConfiguration Q S k n radius),
      (source::tail).IsChain R ∧
      tail.length < 2^(clockWidth (Q := Q) (S := S) (k := k) n radius) ∧
      (source::tail).getLast (by simp) = target := by
  obtain ⟨tail,chain,small,last⟩ := exists_short_chain reachable
  exact ⟨tail,chain,small.trans_le (region_card_le_clock n radius),last⟩

end ComplexityOfGenerators.Multitape.SpaceConfigurations
