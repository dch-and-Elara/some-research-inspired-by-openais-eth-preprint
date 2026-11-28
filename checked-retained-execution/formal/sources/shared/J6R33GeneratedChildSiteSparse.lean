import J6R32ChildResidentTransferLiteralFull
import J6R25PreparedSupplyProducer
import J6R27OriginalGateSourceSupport
import J6R31RootResidentTablesJoin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000

/-! A descendant's installed R32 chart, roster, and precision carry the
meaning of the native R17/R25 multiplicity stream. There is no
unordered or zero-only substitute for its actual event bytes. -/
namespace J6R33GeneratedChildSite
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6R10Repack P11FullPacking J6R9PacketScopes J6R16ModeCost
open J6R27OriginalGate J6R31RootResidentTables J6R32ChildResidentTransfer

variable {E A B : Type} {N : Network E A B} {a q p : ℕ}

/-- This is the checked output of the paid preparation, not an
additional input to the actual packet compiler. -/
structure ResidentReceipt (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (p : ℕ) (R : ChildResidents a q) where
  edges : List E
  edgesUnique : edges.Nodup
  edgesAll : ∀ e,e∈edges
  edgesFit : edges.length<2^q
  copiesFit : P.copies≤2^(q-a)
  copyValue : R.raw.copies.val=P.copies
  seats : R.seats=edges.map (physicalSeatField P i (childPageKey (q-a)))
  masks : R.raw.masks=(orderedChildPages a P.copies).map (encodeMaskRow P.mask)
  modes : List (PacketMode i P.copies (2^(i.val+1)) p)
  modesUnique : modes.Nodup
  modesAll : ∀ u,u∈modes
  rawModes : R.raw.roster.modes=modes.map (encodeMode i)
  rawUnique : R.raw.roster.modes.Nodup
  weights : R.raw.roster.weights.map Word.val=modes.map modeWeight
  prec : R.raw.roster.precision.val=p

variable {P : PhysicalPacking N a (Fin 64)} {i : Fin a}
  {R : ChildResidents a q} (H : ResidentReceipt P i p R)

abbrev NativeModes := J6R9PacketScopes.Mode i p P.mask

abbrev Legal (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (p : ℕ) :=
  ↥(J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask))

noncomputable def RosterIndex : Fin H.modes.length≃PacketMode i P.copies (2^(i.val+1)) p :=
  rosterIndex H.modes H.modesUnique H.modesAll

theorem roster_index_mapped :
    R.raw.roster.modes=List.ofFn (fun j=>encodeMode i (RosterIndex H j)) := by
  have h : List.ofFn (RosterIndex H) = H.modes := List.ofFn_get H.modes
  calc
    _ = H.modes.map (encodeMode i) := H.rawModes
    _ = (List.ofFn (RosterIndex H)).map (encodeMode i) := congrArg _ h.symm
    _ = _ := List.map_ofFn ..

theorem raw_roster_clock : R.raw.roster.modes.length=H.modes.length := by
  rw [H.rawModes,List.length_map]

include H in
theorem resident_raw_valid (hp : 0<p) : RawValid R.raw.roster := by
  refine ⟨Nat.succ_pos q,H.prec.symm ▸ hp,?_,?_⟩
  · intro w hw
    have z := List.mem_map_of_mem (f:=Word.val) hw
    rw [H.weights] at z
    obtain ⟨m,_,hm⟩ := List.mem_map.mp z
    exact hm ▸ (modeWeight_bounds m).1
  · have z := congrArg List.length H.weights
    simpa only [H.rawModes,List.length_map] using z

theorem resident_tuple_iff (v : List ℕ) :
    v∈strictTuples (R.raw.roster.weights.map Word.val) R.raw.roster.precision.val ↔
      ∃! β : Legal P i p,
        H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m))=v := by
  rw [H.weights,H.prec]
  exact exact_legal_vector (packet_mode_equiv P.mask i p) (J6R10RowAffine.weight i p P.mask)
    modeWeight (fun _=>rfl) (fun m=>(modeWeight_bounds m).1) H.modes H.modesUnique H.modesAll p v

def emitted (hp : 0<p) : Meter (Batch (q+1)) :=
  emitBatch a R.raw.roster (resident_raw_valid H hp).posWidth (resident_raw_valid H hp).posPrec
    (resident_raw_valid H hp).posWeights

/-- Every exact legal source mode has a genuinely emitted word vector.
The reader of one particular vector is not a free lookup. -/
theorem every_legal_mode_emitted (hp : 0<p) (β : Legal P i p) :
    ∃ v∈(emitted H hp).result.vectors,
      v.map Word.val=H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m)) := by
  let D := resident_raw_valid H hp
  obtain ⟨_,reads,_,_⟩ := emit_batch_exact a R.raw.roster D.posWidth D.posPrec D.posWeights D.sameLength
  change ((emitted H hp).result.vectors.map (List.map Word.val))=_ at reads
  let k := H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m))
  have hm : k∈strictTuples (R.raw.roster.weights.map Word.val) R.raw.roster.precision.val := by
    apply (resident_tuple_iff H k).mpr
    refine ⟨β,rfl,?_⟩
    intro γ hg
    apply Subtype.ext
    ext u
    have e := List.map_inj_left.mp hg ((packet_mode_equiv P.mask i p) u)
      (H.modesAll ((packet_mode_equiv P.mask i p) u))
    simpa only [Equiv.symm_apply_apply] using e
  rw [←reads] at hm
  exact List.mem_map.mp hm

/-- The event scan serializes the actual multiplicities over the same
complete ordered paid mode roster. Each raw weight, orientation, and
copy key is preserved; omitted entries are exactly the zeros. -/
theorem sparse_for_real_event (hp : 0<p) (v : List (Word (q+1)))
    (occurs : v∈(emitted H hp).result.vectors) :
    ∃ β : Legal P i p, ∃ es : Fin H.modes.length→Word (q+1),
      (∀ j,(es j).val=β.val ((packet_mode_equiv P.mask i p).symm (RosterIndex H j))) ∧
      v=List.ofFn es ∧
      (emitSupport a R.raw.roster.modes v).result=some (supportSpec R.raw.roster.modes v) ∧
      (emitSupport a R.raw.roster.modes v).steps=H.modes.length*dispatchStride a (q+1)+4 ∧
      some (supportSpec R.raw.roster.modes v)∈(emitted H hp).result.support := by
  let D := resident_raw_valid H hp
  obtain ⟨_,reads,supp,_⟩ := emit_batch_exact a R.raw.roster D.posWidth D.posPrec D.posWeights D.sameLength
  change ((emitted H hp).result.vectors.map (List.map Word.val))=_ at reads
  change (emitted H hp).result.support=(emitted H hp).result.vectors.map _ at supp
  have hm : v.map Word.val∈strictTuples (R.raw.roster.weights.map Word.val) R.raw.roster.precision.val := by
    rw [←reads]
    exact List.mem_map_of_mem occurs
  obtain ⟨β,hβ,_⟩ := (resident_tuple_iff H _).mp hm
  have vL : v.length=H.modes.length := by
    have z := congrArg List.length hβ
    simpa only [List.length_map] using z.symm
  let es : Fin H.modes.length→Word (q+1) := fun j=>v.get (Fin.cast vL.symm j)
  have he : v=List.ofFn es := by
    apply List.ext_getElem
    · rw [List.length_ofFn]
      exact vL
    · intro x hx hy
      rw [List.getElem_ofFn]
      rfl
  have values (j : Fin H.modes.length) :
      (es j).val=β.val ((packet_mode_equiv P.mask i p).symm (RosterIndex H j)) := by
    have f : j.val<(v.map Word.val).length := by rw [List.length_map,vL]; exact j.isLt
    have f' : j.val<(H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m))).length := by
      rw [List.length_map]
      exact j.isLt
    have z := List.getElem_of_eq hβ.symm f
    rw [List.getElem_map,List.getElem_map] at z
    exact z
  obtain ⟨out,cost⟩ := emitSupport_exact a R.raw.roster.modes v ((raw_roster_clock H).trans vL.symm)
  refine ⟨β,es,values,he,out,by rw [cost,raw_roster_clock H],?_⟩
  rw [supp]
  exact List.mem_map_of_mem occurs

/-- If the incoming vector is the event of a fixed actual source slot,
the zipper uses this same exponent, rather than choosing an arbitrary
one which happens to be legal. -/
theorem fixed_event_exponents (β : Legal P i p) (v : List (Word (q+1)))
    (reads : v.map Word.val=H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m))) :
    ∃ es : Fin H.modes.length→Word (q+1), v=List.ofFn es ∧
      ∀ j,(es j).val=β.val ((packet_mode_equiv P.mask i p).symm (RosterIndex H j)) := by
  have vL : v.length=H.modes.length := by
    have z := congrArg List.length reads
    simpa only [List.length_map] using z
  let es : Fin H.modes.length→Word (q+1) := fun j=>v.get (Fin.cast vL.symm j)
  refine ⟨es,?_,?_⟩
  · apply List.ext_getElem
    · rw [List.length_ofFn]
      exact vL
    · intro x hx hy
      rw [List.getElem_ofFn]
      rfl
  · intro j
    have h : j.val<(v.map Word.val).length := by rw [List.length_map,vL]; exact j.isLt
    have z := List.getElem_of_eq reads h
    rw [List.getElem_map,List.getElem_map] at z
    exact z

/-- Cardinal fee for the real batch (only charged once; not per page). -/
theorem native_batch_fee (hp : 0<p) :
    (emitted H hp).steps≤emitBatchCap a (q+1) R.raw.roster.weights.length H.modes.length
      (strictTuples (H.modes.map modeWeight) p).length := by
  let D := resident_raw_valid H hp
  have h := (emit_batch_exact a R.raw.roster D.posWidth D.posPrec D.posWeights D.sameLength).2.2.2
  rw [H.weights,H.prec,raw_roster_clock H] at h
  exact h

#print axioms roster_index_mapped
#print axioms resident_raw_valid
#print axioms resident_tuple_iff
#print axioms every_legal_mode_emitted
#print axioms sparse_for_real_event
#print axioms fixed_event_exponents
#print axioms native_batch_fee
end J6R33GeneratedChildSite
