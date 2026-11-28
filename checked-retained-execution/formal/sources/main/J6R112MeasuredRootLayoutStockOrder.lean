import J6R112MeasuredRootLayoutStockAddress

/-! The reverse owner-scope index is re-read in the order of the
same physical half-tape used by R94. Correctness is not an assumption
about how the two independent source orders happen to sort. -/
namespace J6R112MeasuredRootLayoutStock
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R36ChildFramedRoute J6R27OriginalGate
open J6OrientedHost J6Mesh J6R10Repack J6R11Repack J6R21Leaf
open J6R24LegalLayout J6R28GeneratedRootFrame
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R53OldOwnerRoot J6R53TerminalGate J6R54ExteriorOwner
open J6R94ExteriorDebit

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4300
set_option Elab.async false
noncomputable section

def bookInPhysicalOrder (m : ℕ) {own : ℕ} (candidate : HalfBook m own) :
    List (PortRow (rootHalfWidth m))→Meter (Option (HalfBook m own))
  | []=>⟨some [],3⟩
  | r::rs=>
    let hit := locate r.address candidate
    match hit.result with
    | none=>⟨none,hit.steps+4⟩
    | some name=>
      let k := copyFixed r.address
      let v := copyFixed name
      let tail := bookInPhysicalOrder m candidate rs
      ⟨tail.result.map (⟨k.result,v.result⟩::·),hit.steps+k.steps+v.steps+tail.steps+6⟩

theorem book_read_exact_order {H : Type*} (m : ℕ) {own : ℕ}
    (candidate : HalfBook m own) (wire : H→PortRow (rootHalfWidth m))
    (name : H→Word own) (xs : List H)
    (hits : ∀ h∈xs,(locate (wire h).address candidate).result=some (name h)) :
    (bookInPhysicalOrder m candidate (xs.map wire)).result=
      some (xs.map (fun h=>⟨(wire h).address,name h⟩)) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    have good := hits x List.mem_cons_self
    have rest := ih (fun h hh=>hits h (List.mem_cons_of_mem _ hh))
    simp only [List.map_cons,bookInPhysicalOrder,good,rest,copy_fixed_exact,Option.map_some]

variable {V : Type} [Fintype V] {m n : ℕ} (P : Plant V m n)
private abbrev addrOf (h : Port (RootWire m)) := (expectedHalfRow P (oddAxis m) h).address
variable {own : ℕ} (name : (SourceVertex P)→Word own)

def candidateNames (order : List (SourceVertex P)) : HalfBook m own :=
  order.flatMap (fun u=>scopedHalfNames P (name u) u)

theorem true_owner_from_complete_original_scopes (order : List (SourceVertex P)) (all : ∀ u,u∈order)
    (h : Port (RootWire m)) :
    (locate (addrOf P h) (candidateNames P name order)).result=some (name (physicalSourceOwner P h)) := by
  let u := physicalSourceOwner P h
  apply locate_hit
  · apply List.mem_flatMap.mpr
    refine ⟨u,all u,?_⟩
    obtain ⟨i,hi⟩ := original_local_scope_covers_each_physical_half P h
    apply List.mem_ofFn.mpr
    refine ⟨i,?_⟩
    change RefRow.mk (addrOf P ((rootLocalGate P u).port i).val) (name u)=RefRow.mk (addrOf P h) (name u)
    rw [hi]
  · intro row mem same
    obtain ⟨v,_,hm⟩ := List.mem_flatMap.mp mem
    obtain ⟨i,hr⟩ := List.mem_ofFn.mp hm
    let e := (rootLocalGate P v).port i
    have er : RefRow.mk (addrOf P e.val) (name v)=row := hr
    have addresses : addrOf P e.val=addrOf P h := (congrArg RefRow.address er).trans same
    have isHalf : e.val=h := half_addresses_unique P (oddAxis m) addresses
    have isOwner : physicalSourceOwner P e.val=v := e.property
    rw [isHalf] at isOwner
    exact (congrArg RefRow.payload er).symm.trans (congrArg name isOwner.symm)

theorem original_physical_order_enumerates_same_words (order : List (SourceVertex P)) (all : ∀ u,u∈order)
    (candidate : HalfBook m own) (same : candidate=candidateNames P name order)
    (physical : List (PortRow (rootHalfWidth m)))
    (actual : physical=(rootHalfOrder m).map (expectedHalfRow P (oddAxis m))) :
    (bookInPhysicalOrder m candidate physical).result=
      some ((rootHalfOrder m).map (fun h=>⟨addrOf P h,name (physicalSourceOwner P h)⟩)) := by
  rw [actual,same]
  apply book_read_exact_order
  intro h _
  exact true_owner_from_complete_original_scopes P name order all h

#print axioms book_read_exact_order
#print axioms true_owner_from_complete_original_scopes
#print axioms original_physical_order_enumerates_same_words
end
end J6R112MeasuredRootLayoutStock

