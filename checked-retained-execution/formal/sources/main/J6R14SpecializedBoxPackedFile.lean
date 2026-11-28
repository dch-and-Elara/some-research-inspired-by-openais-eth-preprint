import J6R14SpecializedBoxParentFile
import J7R13Physical

/-! Reindex, without recalculating or substituting a tensor, the actual
J8-oriented source tables into the very network behind the preserved
R13 source packing. All columns still have their original owners,
physical assignment, and creation precision. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial J6R9Recursive J6R10Repack
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout

section Reindex
variable {E E' A B : Type*}
variable {N : Network E A B} {N' : Network E' A B}
variable (wire : E ≃ E') (hr : ∀ e, N'.row (wire e)=N.row e)
variable (hc : ∀ e, N'.col (wire e)=N.col e)

def pushPort (v : A⊕B) : ParentPorts N v → ParentPorts N' v
  | ⟨.inl e,he⟩ => ⟨.inl (wire e),(congrArg Sum.inl (hr e)).trans he⟩
  | ⟨.inr e,he⟩ => ⟨.inr (wire e),(congrArg Sum.inr (hc e)).trans he⟩

def reindexedFile {f : ℤ[X]} {ell : ℕ} (F : EntryFile f ell N) : EntryFile f ell N' :=
  fun v => (F v).reindex (fun y => y ∘ pushPort wire hr hc v)

theorem reindexed_reads_same {f : ℤ[X]} {ell : ℕ} (F : EntryFile f ell N)
    (hf : f.Monic) (x : E'→Bool) (v : A⊕B) :
    (reindexedFile wire hr hc F v).frozen hf (assignment N' x v) =
      (F v).frozen hf (assignment N (x ∘ wire) v) := by
  rw [reindexedFile,CreatedEntry.reindex_frozen]
  apply congrArg ((F v).frozen hf)
  funext u
  rcases u with ⟨e,he⟩
  cases e <;> rfl

theorem reindexed_creation_same {f : ℤ[X]} {ell : ℕ} (F : EntryFile f ell N) (v : A⊕B) :
    (reindexedFile wire hr hc F v).created = (F v).created := rfl
end Reindex

section Actual
variable {A Pair Row Col W : Type} [LinearOrder A]
variable [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W→Row) (col : W→OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2)
variable (z : DState A Pair Row Col t)
variable (j : Wire Pair W ↪ P11FullPacking.Physical (t+1) b A)
variable (preserve : ∀ w, P11FullPacking.physicalCell (J7SeatPacking.balancedMask (t+1) b) (j w)
  = J7SeatSource.wordLabel row col z w)

local notation "d₀" => physicalLayout row col two z j preserve
local notation "e₀" => rowWire (Pair:=Pair) row two

set_option linter.unusedSectionVars false in
/-- Original J7 parent entries on the exact R13 packing network. -/
noncomputable def sameSeatFile (f : ℤ[X]) (ell p : ℕ)
    (F : J8Physical.OldTables d₀) (sign : Pin Pair→Bool) :
    EntryFile f ell (J7R13.network row col) :=
  reindexedFile e₀ (rowWire_owner row two)
    (fun e => (owner_layout row col two z j preserve e).symm)
    (orientedEntryFile d₀ f ell p F sign)

set_option linter.unusedSectionVars false in
theorem sameSeatFile_retained (f : ℤ[X]) (ell p : ℕ)
    (F : J8Physical.OldTables d₀) (sign : Pin Pair→Bool) (hf : f.Monic)
    (x : Wire Pair W→Bool) (v : Subdivision Pair Row⊕(Pin Pair⊕OrdinaryColumn Pair Col)) :
    (sameSeatFile row col two z j preserve f ell p F sign v).frozen hf (assignment (J7R13.network row col) x v) =
      (orientedEntryFile d₀ f ell p F sign v).frozen hf
        (assignment (orientedNetwork d₀) (x ∘ e₀) v) :=
  reindexed_reads_same e₀ (rowWire_owner row two)
    (fun e => (owner_layout row col two z j preserve e).symm) _ hf x v

set_option linter.unusedSectionVars false in
theorem sameSeatFile_tag (f : ℤ[X]) (ell p : ℕ)
    (F : J8Physical.OldTables d₀) (sign : Pin Pair→Bool)
    (v : Subdivision Pair Row⊕(Pin Pair⊕OrdinaryColumn Pair Col)) :
    (sameSeatFile row col two z j preserve f ell p F sign v).created = p := rfl
end Actual

#print axioms pushPort
#print axioms reindexed_reads_same
#print axioms reindexed_creation_same
#print axioms sameSeatFile
#print axioms sameSeatFile_retained
#print axioms sameSeatFile_tag
end J6R14SpecializedBox
