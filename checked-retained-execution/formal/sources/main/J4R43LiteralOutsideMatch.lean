import J4R43LiteralOutsideGeometry
import V8NativeMessageN7LiteralSupportCube

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6800000

/-! A change of indexing of the actual non-wrapping partial shift:
an active row factor appears once at its real matched column. The
bijections are over tagged real edges, not just group cardinalities. -/
namespace J4R43LiteralOutside
open P11FullPacking J6R10Repack V8NativeMessage.N7LiteralSupport J6R9PacketTiles
open scoped Classical BigOperators

noncomputable section
variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B} (P : PhysicalPacking N a G) (t : ℤ)

def matchedRows : Matching P t ≃ {r // rowHit P t r} :=
  Equiv.ofBijective (fun x => ⟨x.val.1,⟨x.val.2,x.property⟩⟩) (by
    constructor
    · intro x y h
      have hrow : x.val.1=y.val.1 := congrArg Subtype.val h
      apply Subtype.ext
      exact Prod.ext hrow (match_unique_col P x.property (hrow.symm ▸ y.property))
    · rintro ⟨r,q,m⟩
      exact ⟨⟨(r,q),m⟩,rfl⟩)

def matchedColumns : Matching P t ≃ {q // columnHit P t q} :=
  Equiv.ofBijective (fun x => ⟨x.val.2,⟨x.val.1,x.property⟩⟩) (by
    constructor
    · intro x y h
      have hcol : x.val.2=y.val.2 := congrArg Subtype.val h
      apply Subtype.ext
      exact Prod.ext (match_unique_row P x.property (hcol.symm ▸ y.property)) hcol
    · rintro ⟨q,r,m⟩
      exact ⟨⟨(r,q),m⟩,rfl⟩)

theorem real_matched_columns_card [Fintype E] :
    Fintype.card (Matching P t) =
      ((Finset.univ : Finset E).filter (columnHit P t)).card := by
  refine (Fintype.card_congr (matchedColumns P t)).trans ?_
  let e : {q // columnHit P t q} ≃
      ↥((Finset.univ : Finset E).filter (columnHit P t)) :=
    Equiv.subtypeEquivRight (fun q => by simp)
  rw [Fintype.card_congr e,Fintype.card_coe]

variable [Fintype E] {R : Type} [CommRing R]

def sourceRowWeight (κ : R) (y : E→Bool) (r : E) : R :=
  1 - κ * wholeShiftBit P R t (Sum.elim (fun _=>false) y) r

def sourceColumnWeight (κ : R) (y : E→Bool) (q : E) : R :=
  if columnHit P t q then 1-κ*bit R (y q) else 1

theorem row_weight_at_match (κ : R) (y : E→Bool) (m : Matching P t) :
    sourceRowWeight P t κ y m.val.1 = 1 - κ * bit R (y m.val.2) := by
  rw [sourceRowWeight,literal_port_bit_unique P t _ _ _ m.property]
  rfl

theorem row_weight_at_missing (κ : R) (y : E→Bool) {r : E} (miss : ¬ rowHit P t r) :
    sourceRowWeight P t κ y r=1 := by
  rw [sourceRowWeight,literal_unmatched_port_zero P t _ r (fun q m=>miss ⟨q,m⟩),
    mul_zero,sub_zero]

theorem row_product_over_matches (κ : R) (y : E→Bool) :
    (∏ r : E,sourceRowWeight P t κ y r) =
      ∏ m : Matching P t, (1 - κ * bit R (y m.val.2)) := by
  let f := sourceRowWeight P t κ y
  let s := (Finset.univ : Finset E).filter (rowHit P t)
  calc
    _ = ∏ r ∈ s, f r := by
      symm
      exact Finset.prod_subset (Finset.subset_univ _) (fun r _ hr =>
        row_weight_at_missing P t κ y (fun yes=>hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,yes⟩)))
    _ = ∏ r : {r // rowHit P t r},f r.val := Finset.prod_subtype s (by simp [s]) f
    _ = _ := by
      symm
      apply Fintype.prod_equiv (matchedRows P t)
      intro m
      exact (row_weight_at_match P t κ y m).symm

theorem match_product_over_columns (κ : R) (y : E→Bool) :
    (∏ m : Matching P t, (1 - κ * bit R (y m.val.2))) =
      ∏ q : E,sourceColumnWeight P t κ y q := by
  let f := fun q : E=>1-κ*bit R (y q)
  let s := (Finset.univ : Finset E).filter (columnHit P t)
  calc
    _ = ∏ q : {q // columnHit P t q}, f q.val := by
      apply Fintype.prod_equiv (matchedColumns P t)
      intro m
      rfl
    _ = ∏ q∈s,f q := (Finset.prod_subtype s (by simp [s]) f).symm
    _ = _ := Finset.prod_filter (columnHit P t) f

#print axioms matchedRows
#print axioms matchedColumns
#print axioms real_matched_columns_card
#print axioms row_weight_at_match
#print axioms row_weight_at_missing
#print axioms row_product_over_matches
#print axioms match_product_over_columns

end
end J4R43LiteralOutside


