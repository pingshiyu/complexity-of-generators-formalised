import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

theorem singleton_addCases {α : Type} (first second : α) :
    (Fin.addCases (motive:=fun _ => α) (fun _ : Fin 1 => first) (fun _ : Fin 1 => second) : Fin 2→α)=
      Fin.cases (motive:=fun _ : Fin 2 => α) first (fun _ => second) := by
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · change Fin.addCases (motive:=fun _ => α) (fun _ : Fin 1 => first) (fun _ : Fin 1 => second)
      (Fin.castAdd 1 (0 : Fin 1))=first
    rw [Fin.addCases_left]
  · have zero : index=0 := Fin.eq_zero index
    subst index
    change Fin.addCases (motive:=fun _ => α) (fun _ : Fin 1 => first) (fun _ : Fin 1 => second)
      (Fin.natAdd 1 (0 : Fin 1))=second
    rw [Fin.addCases_right]

theorem reset_seekEnd (copies radius : ℕ) (data : InputData I A) (choices : BitString)
    (length digits : List Bool) (inputPosition : ℕ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) (heads : ∀ j,(ctor.head j).natAbs≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data choices radius
      (configuration C copies .seekEnd length [] digits inputPosition 0 0 ctor) (data.input.length-inputPosition)
      (configuration C copies .seekEnd length [] digits data.input.length 0 0 ctor) := by
  let start := (configuration (O:=O) C copies .seekEnd length [] digits inputPosition 0 0 ctor).mapState (fun _ => ())
  have bounded : (InputEnd.bank I A O (Symbol (S:=S)) (C.blank,((fun _ => none),none)) (counter (k:=k))).Bounded data radius start := by
    have bound := configuration_bounded (O:=O) C copies radius data .seekEnd length [] digits inputPosition 0 0 ctor input heads (by simp) (by simp)
    exact ⟨bound.input,bound.auxiliary,bound.index,bound.head⟩
  have path := InputEnd.scan_regionSteps (C.blank,((fun _ => none),none)) (counter (k:=k)) data choices radius start bounded
    (data.input.length-inputPosition) (by dsimp [start,configuration,BankConfiguration.mapState];omega)
  have mapped := path.mapState (InputEnd.bank I A O (Symbol (S:=S)) (C.blank,((fun _ => none),none)) (counter (k:=k)))
    (bank (I:=I) (A:=A) (O:=O) C copies) (fun _ => Phase.seekEnd)
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux index emit table
      cases i <;> simp [InputEnd.bank] at table
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := table
      rfl)
    (by
      intro state i a x origin cell no yes table
      cases i <;> simp [InputEnd.bank] at table)
  exact mapped

theorem reset_go (copies radius : ℕ) (data : InputData I A) (choices : BitString)
    (state next : Phase Q copies) (length temporary digits : List Bool) (inputPosition : ℕ)
    (ctor : BankConfiguration Unit Q S k) (input : inputPosition≤data.input.length)
    (heads : ∀ j,(ctor.head j).natAbs≤radius)
    (table : (bank (I:=I) (A:=A) (O:=O) C copies).instruction data
      (configuration (O:=O) C copies state length temporary digits inputPosition 0 0 ctor)=
      .step next ((configuration (O:=O) C copies state length temporary digits inputPosition 0 0 ctor).tape
        ((bank (I:=I) (A:=A) (O:=O) C copies).select state)
        ((configuration (O:=O) C copies state length temporary digits inputPosition 0 0 ctor).head
          ((bank (I:=I) (A:=A) (O:=O) C copies).select state))) .stay .stay .stay .stay none) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data choices radius
      (configuration C copies state length temporary digits inputPosition 0 0 ctor) 1
      (configuration C copies next length temporary digits inputPosition 0 0 ctor) := by
  apply TapeBank.RegionSteps.step _ next _ .stay .stay .stay .stay none 0 _
    (configuration_bounded C copies radius data state length temporary digits inputPosition 0 0 ctor input heads (by simp) (by simp)) table
  rw [configuration_stay C copies data state next length temporary digits inputPosition 0 0 ctor input]
  exact .refl _ (configuration_bounded C copies radius data next length temporary digits inputPosition 0 0 ctor input heads (by simp) (by simp))

theorem reset_copy (copies radius : ℕ) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (ctor : BankConfiguration Unit Q S k) (heads : ∀ j,(ctor.head j).natAbs≤radius)
    (space : 2*Nat.clog 2 (data.input.length+1)+2≤radius) :
    (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data choices radius
      (configuration C copies (.copy .copy) (increment^[data.input.length] []) [] digits data.input.length 0 0 ctor)
      (2*((increment^[data.input.length] []).length+1))
      (configuration C copies (.copy .done) (increment^[data.input.length] []) (increment^[data.input.length] []) digits data.input.length 0 0 ctor) := by
  have path := (copy_framed (O:=O) (0 : Fin 3) (2 : Fin 3) (by decide) (fun _ _ => none) data choices
    (Context.mk data.input.length 0 0 0 []) (by exact ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩)
    (increment^[data.input.length] []) (iterate_canonical _) data.input.length (by simp [iterate_value])).mono
    (Copy.bank I A O (0 : Fin 3) (2 : Fin 3)) space
  have counterLift := LeftBankEmbedding.regionSteps_lift (Copy.bank I A O (0 : Fin 3) (2 : Fin 3))
    (encodeCounter C) (fun cell => cell.2.1) (by intro;rfl) (fun _ : Fin 1 => 0)
    (fun _ position => (C.blank,((fun _ => none),digitTape digits position)))
    (by intro;simp) path
  have lifted := BankEmbedding.regionSteps_lift
    (LeftBankEmbedding.bank (Copy.bank I A O (0 : Fin 3) (2 : Fin 3)) 1 (encodeCounter C) (fun cell => cell.2.1))
    id id (by intro;rfl) ctor.head (fun tape position => (ctor.tape tape position,((fun _ => none),none)))
    heads counterLift
  have mapped := lifted.mapState (copyBank (I:=I) (A:=A) (O:=O) C) (bank (I:=I) (A:=A) (O:=O) C copies) Phase.copy
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux index emit table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.copy (.rewindInput .check) cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.copy (.rewindInput .check) cell) table)
  convert mapped using 1 <;> apply BankConfiguration.ext <;> try rfl
  all_goals funext index
  all_goals try (funext position)
  all_goals refine Fin.addCases (fun j => ?_) (fun j => ?_) index
  all_goals simp only [configuration,BankEmbedding.lift,LeftBankEmbedding.lift,Context.frame,Copy.encoded,Copy.memory,
    Prelude.memory,BankConfiguration.mapState,encodeCounter,id_eq,Fin.addCases_left,Fin.addCases_right]
  all_goals refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp only [singleton_addCases,Fin.cases_zero,Fin.cases_succ]
  all_goals norm_num

theorem reset_rewind (copies radius : ℕ) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (ctor : BankConfiguration Unit Q S k) (heads : ∀ j,(ctor.head j).natAbs≤radius)
    (space : 2*Nat.clog 2 (data.input.length+1)+4≤radius) :
    ∃ time, (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data choices radius
      (configuration C copies (.rewindInput .check) (increment^[data.input.length] []) (increment^[data.input.length] []) digits data.input.length 0 0 ctor)
      time (configuration C copies (.rewindInput .check) (increment^[data.input.length] []) [] digits 0 0 0 ctor) := by
  obtain ⟨time,path⟩ := InputRewind.rewind_steps (O:=O) (2 : Fin 3)
    (fun position => Function.update (fun _ => none) 0 (digitTape (increment^[data.input.length] []) position))
    data choices data.input.length data.input.length le_rfl le_rfl
  have bounded := path.mono (InputRewind.bank I A O (2 : Fin 3)) space
  have counterLift := LeftBankEmbedding.regionSteps_lift (InputRewind.bank I A O (2 : Fin 3))
    (encodeCounter C) (fun cell => cell.2.1) (by intro;rfl) (fun _ : Fin 1 => 0)
    (fun _ position => (C.blank,((fun _ => none),digitTape digits position)))
    (by intro;simp) bounded
  have lifted := BankEmbedding.regionSteps_lift
    (LeftBankEmbedding.bank (InputRewind.bank I A O (2 : Fin 3)) 1 (encodeCounter C) (fun cell => cell.2.1))
    id id (by intro;rfl) ctor.head (fun tape position => (ctor.tape tape position,((fun _ => none),none)))
    heads counterLift
  have mapped := lifted.mapState (rewindBank (I:=I) (A:=A) (O:=O) C) (bank (I:=I) (A:=A) (O:=O) C copies) Phase.rewindInput
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux index emit table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.rewindInput .done cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Phase.rewindInput .done cell) table)
  refine ⟨time,?_⟩
  simpa only [configuration,BankEmbedding.lift,LeftBankEmbedding.lift,InputRewind.configuration,
    Prelude.memory,BankConfiguration.mapState,singleton_addCases,encodeCounter,id_eq] using mapped

theorem reset_regionSteps (copies ctorRadius : ℕ) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (inputPosition : ℕ) (ctor : BankConfiguration Unit Q S k)
    (input : inputPosition≤data.input.length) (heads : ∀ j,(ctor.head j).natAbs≤ctorRadius) :
    ∃ time, (bank (I:=I) (A:=A) (O:=O) C copies).RegionSteps data choices
      (max ctorRadius (2*Nat.clog 2 (data.input.length+1)+4))
      (configuration C copies .seekEnd (increment^[data.input.length] []) [] digits inputPosition 0 0 ctor) time
      (configuration C copies .done (increment^[data.input.length] []) [] digits 0 0 0 ctor) := by
  let radius := max ctorRadius (2*Nat.clog 2 (data.input.length+1)+4)
  have bound : ∀ j,(ctor.head j).natAbs≤radius := fun j => (heads j).trans (Nat.le_max_left _ _)
  have seeking := reset_seekEnd (O:=O) C copies radius data choices (increment^[data.input.length] []) digits inputPosition ctor input bound
  have toCopy := reset_go (O:=O) C copies radius data choices .seekEnd (.copy .copy) (increment^[data.input.length] []) [] digits
    data.input.length ctor le_rfl bound (by simp [TapeBank.instruction,bank,configuration])
  have copying := reset_copy (O:=O) C copies radius data choices digits ctor bound (by dsimp [radius];omega)
  have toRewind := reset_go (O:=O) C copies radius data choices (.copy .done) (.rewindInput .check)
    (increment^[data.input.length] []) (increment^[data.input.length] []) digits data.input.length ctor le_rfl bound rfl
  obtain ⟨time,rewinding⟩ := reset_rewind (O:=O) C copies radius data choices digits ctor bound (Nat.le_max_right _ _)
  have finish := reset_go (O:=O) C copies radius data choices (.rewindInput .check) .done
    (increment^[data.input.length] []) [] digits 0 ctor (Nat.zero_le _) bound (by
      simp [TapeBank.instruction,bank,rewindBank,BankEmbedding.bank,LeftBankEmbedding.bank,
        InputRewind.bank,InputRewind.transition,configuration,Prelude.continueInstruction,
        counter,encodeCounter,Prelude.memory,digitTape,BankEmbedding.instruction])
  exact ⟨data.input.length-inputPosition+1+2*((increment^[data.input.length] []).length+1)+1+time+1,
    ((((seeking.trans _ toCopy).trans _ copying).trans _ toRewind).trans _ rewinding).trans _ finish⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
