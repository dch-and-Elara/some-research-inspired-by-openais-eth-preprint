import J6R41StructuredAllPathsExterior
import J6R53OldOwnerRootBasis
import J6R49SourceLayoutOwners

/-! The bootstrap row types are the actual retained rows and the actual
physical page columns of the same fixed prescribed exterior call. Neither
a present half-port nor a nonempty page payload is needed for membership. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule
open J6R32ChildResidentTransfer J6R27OriginalGate
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 3900
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

theorem group_after_transport {E A B S : Type} [LinearOrder S] [Fintype S]
    {a b : ℕ} {N : Network E A B} (P : PhysicalPacking N a S) (h : a=b)
    (i : Fin a) (j : Fin b) (same : j.val=i.val) (x : A⊕B) :
    atGroup (cast (congrArg (fun k=>PhysicalPacking N k S) h) P) j x=atGroup P i x := by
  cases h
  have e : i=j := Fin.ext same.symm
  subst j
  rfl

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Src" => (SourceVertex P)

def actualGroup (v : Src) : Fin 64 :=
  atGroup (packing (G.selector ell) (G.ready ell))
    (centerIndex (G.ready ell) (G.centre ell X.centre)) v

theorem actual_group_of_every_root_owner (x : Src) :
    actualGroup X x=owner (constantRootWord m) (oddAxis m) x := by
  let size := (mesh_root_bits m native G.nativeFits).symm
  obtain ⟨packingLaw,axisLaw,_,_⟩ := odd_site_matches_geometry G ell X.centre
  unfold actualGroup
  rw [packingLaw]
  refine (group_after_transport (rootChart P) size (oddAxis m)
    (centerIndex (G.ready ell) (G.centre ell X.centre)) axisLaw x).trans ?_
  cases x <;> rfl

def stageOldOrder (all : List Src) : List (Ext).host.Row :=
  scanSubtype (fun v=>actualGroup X v=X.group) all

theorem stage_old_order_exact (all : List Src) (hn : all.Nodup) (hc : ∀ u,u∈all) :
    (stageOldOrder X all).Nodup ∧ ∀ v,v∈stageOldOrder X all := by
  constructor
  · exact scan_subtype_nodup _ _ hn
  · intro v
    exact (scan_subtype_mem _ _ v).mpr (hc v.val)

def stagePageOrder : List (Ext).host.Col :=
  (orderedChildPages (a m) (K m)).map (canonicalPageEquiv G ell X.centre)

theorem stage_page_order_exact :
    (stagePageOrder X).Nodup ∧ ∀ k,k∈stagePageOrder X := by
  obtain ⟨hn,hc,_⟩ := child_pages_complete (a m) (K m)
  let e := canonicalPageEquiv G ell X.centre
  exact ⟨hn.map e.injective,fun k=>List.mem_map.mpr ⟨e.symm k,hc _,e.apply_symm_apply k⟩⟩

def stageOwnerOrder (all : List Src) : List ((Ext).host.Row⊕(Ext).host.Col) :=
  (stageOldOrder X all).map Sum.inl++(stagePageOrder X).map Sum.inr

theorem stage_owner_order_exact (all : List Src) (hn : all.Nodup) (hc : ∀ u,u∈all) :
    (stageOwnerOrder X all).Nodup ∧ ∀ v,v∈stageOwnerOrder X all := by
  obtain ⟨hnL,hcL⟩ := stage_old_order_exact X all hn hc
  obtain ⟨hnR,hcR⟩ := stage_page_order_exact X
  unfold stageOwnerOrder
  refine ⟨List.nodup_append.mpr ⟨hnL.map Sum.inl_injective,hnR.map Sum.inr_injective,?_⟩,?_⟩
  · intro x p y q eq
    subst y
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp p
    obtain ⟨w,_,e⟩ := List.mem_map.mp q
    cases e
  · intro u
    cases u with
    | inl w=>exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨w,hcL w,rfl⟩))
    | inr w=>exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨w,hcR w,rfl⟩))

def gateTag (gate : Stamp key prec) (pad : ℕ) (_ : Src) :
    Origin key prec (pageKeyWidth m+pad) := ⟨gate,none⟩

def bootPageKey (pad : ℕ) (k : (Ext).host.Col) : Word (pageKeyWidth m+pad) :=
  (widened pad (residentPageKey m ((canonicalPageEquiv G ell X.centre).symm k))).result

theorem boot_page_key_injective (pad : ℕ) : Function.Injective (bootPageKey X pad) :=
  (widened_distinct pad).comp ((resident_page_key_injective m).comp (canonicalPageEquiv G ell X.centre).symm.injective)

def exteriorData (gate : Stamp key prec) (pad : ℕ) (u : (Ext).host.Row⊕(Ext).host.Col) :
    OwnerData (SuffixWordWidth m) key prec (pageKeyWidth m+pad) :=
  match u with
  | .inl old=>actualOwnerValue (rootLocalGate P) (rootOperand P) (gateTag (P:=P) gate pad) old.val
  | .inr k=>freshOwnerData (X.seed pad).immutable.payload.stamp (bootPageKey X pad k)

theorem exterior_data_origin (gate : Stamp key prec) (pad : ℕ) (u : (Ext).host.Row⊕(Ext).host.Col) :
    (exteriorData X gate pad u).origin=initialOrigin X gate pad u := by
  cases u <;> rfl

theorem mounted_owner_matches_first_payload
    (gate : Stamp key prec) (pad : ℕ) (gateWidth : gate.created.val=base)
    (u : (Ext).host.Row⊕(Ext).host.Col) (p : PortAt (J6R34ChildPath.point (Ext).host u)) :
    (initialPayload X gate pad p.val).1=(exteriorData X gate pad u).origin :=
  (exact_real_root_tag_at_port X gate pad gateWidth u p).trans (exterior_data_origin X gate pad u).symm

theorem exterior_page_matches_installed_key (gate : Stamp key prec) (pad : ℕ) (k : (Ext).host.Col) :
    let x := exteriorData X gate pad (.inr k)
    x.gateCode=none ∧ x.origin.pageKey=some (bootPageKey X pad k) ∧
    x.origin.stamp=(X.seed pad).immutable.payload.stamp ∧
    x.origin.stamp.created.val=(Ext).prec ∧
    (locate (bootPageKey X pad k) (X.seed pad).immutable.payload.payload.pages).result=
      some (X.chosenFields ((canonicalPageEquiv G ell X.centre).symm k)) := by
  have H := true_seed_payload_page X pad ((canonicalPageEquiv G ell X.centre).symm k)
  have b : (X.seed pad).immutable.payload.stamp.created.val=(Ext).prec := by
    rw [actual_outer_stamp]
    exact (stable_exterior_header X).2.2
  exact ⟨rfl,rfl,rfl,b,H⟩

#print axioms group_after_transport
#print axioms actual_group_of_every_root_owner
#print axioms stage_owner_order_exact
#print axioms boot_page_key_injective
#print axioms exterior_data_origin
#print axioms mounted_owner_matches_first_payload
#print axioms exterior_page_matches_installed_key
end
end J6R54ExteriorOwner
