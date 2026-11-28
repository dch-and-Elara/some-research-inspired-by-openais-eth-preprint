import J5R41LiteralChildCostVisits
import J5R41LiteralChildCostAlgebra

/-! Extract precisely the original finite moment vector of the
source-only mode list, from the actual retained child column bits. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R11Blueprint J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
open J6R10RowAffine J6R10PacketAssembly

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

theorem partition_group_product {X G K R : Type*} [Fintype X] [Fintype K] [DecidableEq G] [DecidableEq K] [CommMonoid R]
    (group : X→G) (page : X→K) (g : G) (f : X→R) :
    (∏ k : K, ∏ x ∈ Finset.univ.filter (fun x=>group x=g ∧ page x=k),f x) =
    ∏ x ∈ Finset.univ.filter (fun x=>group x=g),f x := by
  classical
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun x _=>?_ )
  by_cases h : group x=g
  · simp only [h,true_and,if_true]
    rw [Finset.prod_eq_single (page x)]
    · simp
    · intro k _ hk
      exact if_neg (Ne.symm hk)
    · simp
  · simp [h]

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)

abbrev RowHalf := {e : E // rowGroup P.mask i (P.seat e)=g}
abbrev ColHalf := {e : E // colGroup P.mask i (P.seat e)=g}

def extendCol (X : ColHalf P i g→Bool) (e : E) : Bool :=
  if h : colGroup P.mask i (P.seat e)=g then X ⟨e,h⟩ else false

variable {p : ℕ}

def sourceStat (X : ColHalf P i g→Bool) (m : Mode i p P.mask) : ℕ :=
  ∑ e ∈ tileWires P i (modeTile P i m),
    if extendCol P i g X e then (ordinal P i e).val^m.order.val else 0

theorem actual_mode_columns (m : Mode i p P.mask) :
    columns (fun e : E=>(P.seat e).1) (fun e=>(P.seat e).2.val) i.val m.page m.tile.val =
      tileWires P i (modeTile P i m) := by
  ext e
  simp only [columns,tileWires,Finset.mem_filter,Finset.mem_univ,true_and]
  change _ ↔ (((P.seat e).1,⟨tile i.val (P.seat e).2.val,(tile_coordinates _ _).1⟩) :
      Tile P i) = (m.page,m.tile)
  rw [Prod.mk.injEq]
  refine and_congr_right fun _=>?_ 
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    exact congrArg Fin.val h

theorem col_moment_is_actual_nonnegative_index (v : PhysicalState P i g)
    (m : Mode i p P.mask) (hs : source P.mask i m=g) :
    stateMoment (R:=Residue f ell p) P i g p v m = (sourceStat P i g v.2 m:Residue f ell p) := by
  subst g
  simp only [stateMoment,dif_pos rfl]
  let X := extendCol P i (source P.mask i m) v.2
  have he : (fun q : ColHalf P i (source P.mask i m)=>X q.val)=v.2 := by
    funext q
    exact dif_pos q.prop
  calc
    _ = moment (fun e=>P.seat e) P.mask i m (fun q=>X q.val) := by simp [he]
    _ = _ := (moment_exact (fun e=>P.seat e) P.mask i m X).trans (by
      simp only [L,sourceStat,actual_mode_columns,Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _=>?_
      change (coord i.val (P.seat e).2.val : Residue f ell p)^m.order.val *
        bit (Residue f ell p) (X e) = (if X e then (coord i.val (P.seat e).2.val)^m.order.val else 0 : ℕ)
      cases h : X e <;> simp [bit,h])

variable {t : ℤ} (pt : ℕ) (hnil : (2:Residue f ell pt)^pt=0)

def affineAt (v : PhysicalState P i g) (r : RowHalf P i g) : Residue f ell pt :=
  LiteralPortCompiler.affine (v.1 r)
    (groupBase (fun q=>P.seat q) (fun q=>P.seat q) P.mask i t pt hnil 0 g v r.val)

theorem row_product_partition (v : PhysicalState P i g) :
    (∏ k,packetRows (t:=t) P i pt hnil g k v) =
      ∏ r : RowHalf P i g,affineAt (t:=t) P i g pt hnil v r := by
  let w := fun e : E => LiteralPortCompiler.affine
    (groupBit (fun q=>P.seat q) (fun q=>P.seat q) P.mask i g v e)
    (groupBase (fun q=>P.seat q) (fun q=>P.seat q) P.mask i t pt hnil 0 g v e)
  change (∏ k,∏ e ∈ actualRows (childBlock P i) g k,w e)=_
  have h : ∀ k,actualRows (childBlock P i) g k =
      Finset.univ.filter (fun e=>rowGroup P.mask i (P.seat e)=g ∧ (P.seat e).1=k) := by
    intro k
    ext e
    simp [actualRows,childBlock,rowBlock,Prod.swap,Prod.mk.injEq]
  simp only [h]
  rw [partition_group_product (fun e : E=>rowGroup P.mask i (P.seat e))
    (fun e : E=>(P.seat e).1) g w]
  trans (∏ e : RowHalf P i g,w e.val)
  · exact Finset.prod_subtype _ (by simp) _
  · refine Finset.prod_congr rfl fun e _=>?_
    simp only [w,groupBit,dif_pos e.prop,affineAt]

variable (β : ModeTuple P i pt) (req : Finset (Mode i pt P.mask))
variable (allSource : ∀ m ∈ req,source P.mask i m=g)
variable (covers : ∀ m,source P.mask i m=g → β m≠0 → m∈req)

include allSource covers in
theorem source_product_partition (v : PhysicalState P i g) :
    (∏ k,packetMoments P i pt β g k v) =
    ∏ m ∈ req,(sourceStat P i g v.2 m:Residue f ell pt)^β m := by
  have h : ∀ k, (Finset.univ.filter (fun m : Mode i pt P.mask=>childSource P i m=(g,k))) =
      Finset.univ.filter (fun m=>source P.mask i m=g ∧ m.page=k) := by
    intro k
    ext m
    simp [childSource,Prod.mk.injEq]
  unfold packetMoments
  simp only [h]
  rw [partition_group_product (fun m : Mode i pt P.mask=>source P.mask i m)
    (fun m : Mode i pt P.mask=>m.page) g
    (fun m=> (stateMoment (R:=Residue f ell pt) P i g pt v m)^β m)]
  let s : Finset (Mode i pt P.mask) := Finset.univ.filter (fun m=>source P.mask i m=g)
  let w := fun m : Mode i pt P.mask => (stateMoment (R:=Residue f ell pt) P i g pt v m)^β m
  change (∏ m ∈ s,w m)=_
  have hs : req⊆s := fun m hm=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,allSource m hm⟩
  rw [←Finset.prod_subset hs (fun m hm hn=>by
    have he : β m=0 := by
      by_contra hβ
      exact hn (covers m (Finset.mem_filter.mp hm).2 hβ)
    simp [w,he])]
  apply Finset.prod_congr rfl
  intro m hm
  dsimp only [w]
  rw [col_moment_is_actual_nonnegative_index P i g v m (allSource m hm)]

variable (ht : t≠0) (hv : padicValInt 2 t=i.val) (old : EntryFile f ell N) (hf : f.Monic)

include allSource in
theorem actual_child_real_support
    (β₀ : LegalTuple P i pt) (noTarget : HasNoTarget P i pt β₀.val g)
    (covers₀ : ∀ m,source P.mask i m=g → β₀.val m≠0 → m∈req) :
    physicalReply P i ht hv pt hnil old hf β₀.val g =
      ∑ v : PhysicalState P i g, oldState P i g pt old hf v *
        ((∏ r : RowHalf P i g,affineAt (t:=t) P i g pt hnil v r) *
         ∏ m ∈ req,(sourceStat P i g v.2 m:Residue f ell pt)^β₀.val m) := by
  rw [actual_source_only_child P i ht hv pt hnil old hf g β₀ noTarget]
  simp only [row_product_partition,source_product_partition P i g pt β₀.val req allSource covers₀]

#print axioms partition_group_product
#print axioms actual_mode_columns
#print axioms col_moment_is_actual_nonnegative_index
#print axioms row_product_partition
#print axioms source_product_partition
#print axioms actual_child_real_support
end
end J5R41LiteralChildCost
