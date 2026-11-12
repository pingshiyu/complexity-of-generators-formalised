import ComplexityOfGenerators.Simulation.NativeSourceCall.Basic

/-! Pointwise invariants for the bounded packet and the suspended work tracks.
The packet coordinates are relative to the source work head, not the physical
origin. In particular, none of these bounds depend on the source's work radius. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The block has `length+1` cells, including the right blank index cell. -/
def packet (length head : ℕ) (anchor position : ℤ) : Option IndexMark :=
  if anchor ≤ position ∧ position ≤ anchor+length then
    some ⟨decide (position=anchor), decide (position=anchor+length), decide (position=anchor+head)⟩
  else none

@[simp] theorem packet_at (length head position : ℕ) (anchor : ℤ) (within : position ≤ length) :
    packet length head anchor (anchor+position) =
      some ⟨decide (position=0), decide (position=length), decide (position=head)⟩ := by
  simp [packet, within]

@[simp] theorem packet_first (length head : ℕ) (anchor : ℤ) :
    (packet length head anchor anchor).any IndexMark.first = true := by simp [packet]

@[simp] theorem packet_last (length head : ℕ) (anchor : ℤ) :
    (packet length head anchor (anchor+length)).any IndexMark.last = true := by simp [packet]

theorem packet_first_iff (length head : ℕ) (anchor position : ℤ) :
    (packet length head anchor position).any IndexMark.first = true ↔ position=anchor := by
  unfold packet
  split_ifs with inside <;> simp_all
  omega

theorem packet_last_iff (length head : ℕ) (anchor position : ℤ) :
    (packet length head anchor position).any IndexMark.last = true ↔ position=anchor+length := by
  unfold packet
  split_ifs with inside <;> simp_all
  omega

theorem packet_head_iff (length head : ℕ) (anchor position : ℤ) (within : head ≤ length) :
    (packet length head anchor position).any IndexMark.head = true ↔ position=anchor+head := by
  unfold packet
  split_ifs with inside <;> simp_all
  omega

@[simp] theorem packet_at_head (length head : ℕ) (anchor : ℤ) (within : head ≤ length) :
    packet length head anchor (anchor+head) =
      some ⟨decide (head=0), decide (head=length), true⟩ := by
  simpa using packet_at length head head anchor within

theorem indexMove_correct (length head : ℕ) (within : head ≤ length) (anchor : ℤ) (move : Move) :
    (indexMove ⟨decide (head=0), decide (head=length), true⟩ move).onInt (anchor+head) =
      anchor+(move.onInput length head : ℕ) := by
  cases move with
  | left =>
      by_cases zero : head=0 <;> simp [indexMove, Move.onInt, Move.onInput, zero] <;> omega
  | stay => simp [indexMove, Move.onInt, Move.onInput, Nat.min_eq_left within]
  | right =>
      by_cases last : head=length <;> simp [indexMove, Move.onInt, Move.onInput, last] <;> omega

theorem packet_shift (length head : ℕ) (anchor position shift : ℤ) :
    packet length head (anchor+shift) position = packet length head anchor (position-shift) := by
  unfold packet
  have interval : (anchor+shift≤position ∧ position≤anchor+shift+length) ↔
      (anchor≤position-shift ∧ position-shift≤anchor+length) := by omega
  simp only [interval]
  split_ifs <;> congr 2 <;> apply Bool.eq_iff_iff.mpr <;> simp only [decide_eq_true_eq] <;> omega

variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

/-- Decode invariants allow harmless noncanonical encodings of the ambient
blank tape. Actual writes still use finite alphabet symbols. -/
def Memory (fixed : ℤ → F) (source : ℤ → Option (Fin M.symbols)) (visited : Finset ℤ)
    (block : ℤ → Option IndexMark)
    (memory : ℤ → Option (Fin (Fintype.card (Cell F M.symbols)))) : Prop :=
  ∀ position, read M (memory position) =
    ⟨fixed position, source position, decide (position=0), decide (position∈visited), block position⟩

/-- A packet-only write changes no source, visit, origin, or controller cell. -/
theorem Memory.packet_write {fixed source visited block memory} (position : ℤ)
    (mark : Option IndexMark) (represented : Memory (F := F) M fixed source visited block memory) :
    Memory M fixed source visited (Function.update block position mark)
      (Function.update memory position (some (alphabet M {read M (memory position) with packet := mark}))) := by
  unfold Memory at represented ⊢
  intro x
  by_cases same : x=position
  · subst x
    simp only [Function.update_self, read_write, represented]
  · simp only [Function.update_of_ne same, represented]

/-- Native source writes preserve all bounded-controller/index tracks. -/
theorem Memory.source_write {fixed source visited block memory} (position : ℤ)
    (symbol : Option (Fin M.symbols)) (represented : Memory (F := F) M fixed source visited block memory) :
    Memory M fixed (Function.update source position symbol) visited block
      (Function.update memory position (some (alphabet M {read M (memory position) with source := symbol}))) := by
  unfold Memory at represented ⊢
  intro x
  by_cases same : x=position
  · subst x
    simp only [Function.update_self, read_write, represented]
  · simp only [Function.update_of_ne same, represented]

theorem Memory.visit_write {fixed source visited block memory} (position : ℤ)
    (represented : Memory (F := F) M fixed source visited block memory) :
    Memory M fixed source (insert position visited) block
      (Function.update memory position (some (alphabet M {read M (memory position) with visited := true}))) := by
  unfold Memory at represented ⊢
  intro x
  by_cases same : x=position
  · subst x
    simp only [Function.update_self, read_write, represented, Finset.mem_insert_self, decide_true]
  · simp only [Function.update_of_ne same, represented, Finset.mem_insert, same, false_or]

/-- Cleanup can erase a source symbol even though the native instruction set
cannot write a physical blank: it writes an explicit blank on the source track. -/
theorem Memory.erase_write {fixed source visited block memory} (position : ℤ)
    (represented : Memory (F := F) M fixed source visited block memory) :
    Memory M fixed (Function.update source position none) (visited.erase position) block
      (Function.update memory position (some (alphabet M
        {read M (memory position) with source := none, visited := false}))) := by
  unfold Memory at represented ⊢
  intro x
  by_cases same : x=position
  · subst x
    simp [represented, Finset.mem_erase]
  · simp [Function.update_of_ne same, represented, Finset.mem_erase, same]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
