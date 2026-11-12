import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Words

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Comparison

set_option backward.isDefEq.respectTransparency false

abbrev Cell := Option Bool×Option Bool

def paired : List Bool→List Bool→List Cell
  | [],[] => []
  | first::left,[] => (some first,none)::paired left []
  | [],second::right => (none,some second)::paired [] right
  | first::left,second::right => (some first,some second)::paired left right

def update (prior : Bool) (cell : Cell) : Bool :=
  if cell.1.getD false=cell.2.getD false then prior else cell.2.getD false

def scan : List Cell→Bool→Bool
  | [],prior => prior
  | cell::rest,prior => scan rest (update prior cell)

theorem paired_length (left right : List Bool) : (paired left right).length=max left.length right.length := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [paired]
      | cons bit rest ih => simp [paired,ih]
  | cons bit rest ih => cases right <;> simp [paired,ih] <;> omega

theorem paired_nonblank (left right : List Bool) : ∀ cell∈paired left right,cell≠(none,none) := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [paired]
      | cons bit rest ih => simpa [paired] using ih
  | cons bit rest ih => cases right <;> simpa [paired] using ih _

/-- A later, more significant, unequal digit supersedes the previous order. -/
theorem scan_paired (left right : List Bool) (prior : Bool) :
    scan (paired left right) prior=
      if FixedBitBlocks.decode left=FixedBitBlocks.decode right then prior
      else decide (FixedBitBlocks.decode left<FixedBitBlocks.decode right) := by
  induction left generalizing right prior with
  | nil =>
      induction right generalizing prior with
      | nil => simp [paired,scan,FixedBitBlocks.decode]
      | cons bit rest ih =>
          rw [paired,scan,ih]
          clear ih
          cases bit <;> simp only [update,Option.getD_some,Option.getD_none,Bool.false_eq_true,↓reduceIte,
            FixedBitBlocks.decode,Bool.toNat_false,Bool.toNat_true,reduceCtorEq]
          all_goals split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
            (try simp only [Bool.false_eq_true,decide_eq_true_eq,true_iff,false_iff]) <;> omega
  | cons first left ih =>
      cases right with
      | nil =>
          rw [paired,scan,ih []]
          clear ih
          cases first <;> simp only [update,Option.getD_some,Option.getD_none,Bool.false_eq_true,↓reduceIte,
            FixedBitBlocks.decode,Bool.toNat_false,Bool.toNat_true,reduceCtorEq]
          all_goals split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
            (try simp only [Bool.false_eq_true,decide_eq_true_eq,true_iff,false_iff]) <;> omega
      | cons second right =>
          rw [paired,scan,ih right]
          clear ih
          cases first <;> cases second <;>
            simp only [update,Option.getD_some,Bool.false_eq_true,↓reduceIte,FixedBitBlocks.decode,
              Bool.toNat_false,Bool.toNat_true,reduceCtorEq]
          all_goals split_ifs <;> apply Bool.eq_iff_iff.mpr <;>
            (try simp only [Bool.false_eq_true,decide_eq_true_eq,true_iff,false_iff]) <;> omega

theorem paired_lookup (left right : List Bool) (position : ℕ) :
    (paired left right)[position]?.getD (none,none)=(left[position]?,right[position]?) := by
  induction left generalizing right position with
  | nil =>
      induction right generalizing position with
      | nil => simp [paired]
      | cons bit rest ih => cases position <;> simp [paired,ih]
  | cons first left ih => cases right <;> cases position <;> simp [paired,ih]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Comparison
