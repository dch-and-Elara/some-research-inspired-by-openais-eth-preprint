import J5R41LiteralChildCostPorts

/-! The coordinate vector of the dense table is the one actually
seen by the same native children, not a free supplied profile. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R11Blueprint J6R9Recursive
open J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)
variable {p : ℕ} (req : Finset (Mode i p P.mask))

theorem tile_wire_source (m : Mode i p P.mask) (e : E)
    (he : e∈tileWires P i (modeTile P i m)) :
    colGroup P.mask i (P.seat e)=source P.mask i m := by
  rw [←actual_mode_columns P i m] at he
  exact column_source_group (fun e=>P.seat e) P.mask i m e he

def sourceWeight (b : ColVertex P i g) (q : ColPort P i g b) (u : Axis P i req) : ℕ :=
  if tileOf P i q.val=modeTile P i u.val then (ordinal P i q.val).val^u.val.order.val else 0

variable (allSource : ∀ m∈req, source P.mask i m=g)

include allSource in
theorem source_limit_actual (u : Axis P i req) :
    J45Cost.sourceLimit (sourceWeight P i g req) u=spanAt P i req u := by
  unfold J45Cost.sourceLimit spanAt H
  let W := fun e : E=>if tileOf P i e=modeTile P i u.val then (ordinal P i e).val^u.val.order.val else 0
  let K := fun q : Σ b : ColVertex P i g,ColPort P i g b =>
    sourceWeight P i g req q.1 q.2 u
  calc
    _=(∑ q,K q) := (Fintype.sum_sigma K).symm
    _=(∑ q : ColHalf P i g,W q.val) := by
      apply Fintype.sum_equiv (colChart P i g)
      intro x
      rfl
    _=∑ e ∈ Finset.univ.filter (fun e : E=>colGroup P.mask i (P.seat e)=g),W e :=
      (Finset.sum_subtype _ (fun _=>by simp) _).symm
    _=∑ e∈tileWires P i (modeTile P i u.val),(ordinal P i e).val^u.val.order.val := by
      simp only [tileWires,Finset.sum_filter, W]
      refine Finset.sum_congr rfl fun e _=>?_
      by_cases h : tileOf P i e=modeTile P i u.val
      · have he := (tile_wire_source P i u.val e (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)).trans
          (allSource u.val u.prop)
        rw [if_pos he,if_pos h]
      · simp [h]

theorem source_coordinate_exact (X : ColAssignments P i g) (u : Axis P i req) :
    (∑ b, J45Cost.sourceIncrement (sourceWeight P i g req) b (X b)) u =
      sourceStat P i g ((colAssignmentsEquiv P i g) X) u.val := by
  simp only [Finset.sum_apply,J45Cost.sourceIncrement]
  let X₀ := (colAssignmentsEquiv P i g) X
  let W := fun e : E=>if tileOf P i e=modeTile P i u.val then (ordinal P i e).val^u.val.order.val else 0
  let K := fun q : Σ b : ColVertex P i g,ColPort P i g b =>
    if X q.1 q.2 then sourceWeight P i g req q.1 q.2 u else 0
  calc
    _=(∑ q,K q) := (Fintype.sum_sigma K).symm
    _=(∑ q : ColHalf P i g,if X₀ q then W q.val else 0) := by
      apply Fintype.sum_equiv (colChart P i g)
      rintro ⟨b,q⟩
      rw [show X₀ (colChart P i g ⟨b,q⟩)=X b q from new_state_col_reads P i g (fun _ _=>false) X b q]
      rfl
    _=∑ e : E, if extendCol P i g X₀ e then W e else 0 := by
      let b : Finset E := Finset.univ.filter (fun e : E=>colGroup P.mask i (P.seat e)=g)
      let d := fun e : E=> if extendCol P i g X₀ e then W e else 0
      calc
        _=(∑ e : ColHalf P i g,d e.val) := by
          refine Finset.sum_congr rfl fun e _=>?_
          simp [d,extendCol,e.prop]
        _=∑ e∈b,d e := (Finset.sum_subtype b (fun _=>by simp [b]) d).symm
        _=_ := by
          simp only [b,Finset.sum_filter]
          refine Finset.sum_congr rfl fun e _=>?_
          by_cases h : colGroup P.mask i (P.seat e)=g <;> simp [d,extendCol,h]
    _=_ := by
      simp only [sourceStat,tileWires,Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _=>?_
      by_cases h : tileOf P i e=modeTile P i u.val <;> simp [W,h,X₀]

def momentRead (β : Mode i p P.mask →₀ ℕ) (x : Axis P i req→ℤ) : Residue f ell p :=
  ∏ u,(x u:Residue f ell p)^β u.val

theorem actual_coordinate_readout (β : Mode i p P.mask→₀ℕ) (X : ColAssignments P i g) :
    momentRead (f:=f) (ell:=ell) P i req β
      (∑ b,J45Cost.intInc (J45Cost.sourceIncrement (sourceWeight P i g req)) b (X b)) =
    ∏ m∈req,(sourceStat P i g ((colAssignmentsEquiv P i g) X) m:Residue f ell p)^β m := by
  unfold momentRead
  let K := fun m : Mode i p P.mask => (sourceStat P i g ((colAssignmentsEquiv P i g) X) m:Residue f ell p)^β m
  trans (∏ u : Axis P i req,K u.val)
  swap
  · exact (Finset.prod_subtype req (fun _=>Iff.rfl) K).symm
  refine Finset.prod_congr rfl fun u _=>?_
  dsimp only [K]
  have h : (∑ b, J45Cost.intInc (J45Cost.sourceIncrement (sourceWeight P i g req)) b (X b)) u =
      (sourceStat P i g ((colAssignmentsEquiv P i g) X) u.val : ℤ) := by
    simp only [Finset.sum_apply,J45Cost.intInc, ←Nat.cast_sum]
    have e := source_coordinate_exact P i g req X u
    simp only [Finset.sum_apply] at e
    exact_mod_cast e
  rw [h,Int.cast_natCast]

#print axioms tile_wire_source
#print axioms source_limit_actual
#print axioms source_coordinate_exact
#print axioms actual_coordinate_readout
end
end J5R41LiteralChildCost

