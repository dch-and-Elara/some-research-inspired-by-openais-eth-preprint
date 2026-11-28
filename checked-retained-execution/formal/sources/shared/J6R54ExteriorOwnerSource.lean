import J6R54ExteriorOwnerWords
import J6R54ExteriorOwnerChart

/-! Read the exact keys from the same register/atlas that the R34
publication installed for the selected (t,j,g). The retained-owner
filter reads the complete owner table in original order, not a set of
owners touched by the exterior half file. -/
namespace J6R54ExteriorOwner
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R53OldOwner J6R53OldOwnerRoot J6R49SourceLayout J6R37StructuredRoot
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3300
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

def ownerHeader {U : Type} {own : ℕ} (name : U→Word own) (group : U→Fin 64) (u : U) :
    OwnerGroup own := ⟨name u,word (group u).val⟩

theorem group_word_eq {a b : Fin 64} : word (q:=6) a.val=word b.val↔a=b := by
  constructor
  · intro w
    have e := congrArg Word.val w
    rw [word_val a.isLt,word_val b.isLt] at e
    exact Fin.ext e
  · intro w
    rw [w]

theorem exact_filter_group_keys {U : Type} {own : ℕ}
    (name : U→Word own) (group : U→Fin 64) (g : Fin 64) (order : List U) :
    (List.filter (fun h : OwnerGroup own=>decide (word (q:=6) g.val=h.group))
      (order.map (ownerHeader name group))).map OwnerGroup.key =
    (scanSubtype (fun u=>group u=g) order).map (fun u=>name u.val) := by
  induction order with
  | nil => rfl
  | cons u us ih =>
    have e : word (q:=6) g.val=word (group u).val↔group u=g :=
      group_word_eq.trans eq_comm
    unfold scanSubtype at *
    by_cases h : group u=g
    · simp only [List.map_cons,List.filter_cons,List.filterMap_cons,ownerHeader,decide_eq_true (e.mpr h),
        if_true,dif_pos h,ih]
    · simp only [List.map_cons,List.filter_cons,List.filterMap_cons,ownerHeader,decide_eq_false (fun w=>h (e.mp w)),
        Bool.false_eq_true,if_false,dif_neg h,ih]

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Src" => (SourceVertex P)
local notation "Left" => ((Ext).host.Row)
local notation "Right" => ((Ext).host.Col)
local notation "Raw" => (OwnerData (SuffixWordWidth m) key prec Pg)

abbrev RootRoster (name : Src→Word own) :=
  CompleteRoster name (actualOwnerValue (rootLocalGate P) (rootOperand P) (gateTag (P:=P) gate pad))

theorem actual_exterior_group_word : X.address.group=word (q:=6) X.group.val :=
  (valued_word X.address.group).symm.trans (congrArg word X.groupOK)

theorem read_actual_old_gate_words (name : Src→Word own)
    (root : RootRoster (P:=P) gate pad name) (headers : List (OwnerGroup own))
    (aligned : headers=root.order.map (ownerHeader name (actualGroup X)))
    (inj : Function.Injective name) :
    (gatherOwners root.raw (selectOwnerKeys X.address.group headers).result).result=
      some ((stageOldOrder X root.order).map (fun u=>exteriorData X gate pad (.inl u))) := by
  have filtered : (selectOwnerKeys X.address.group headers).result =
      (stageOldOrder X root.order).map (fun u=>name u.val) := by
    rw [aligned,actual_exterior_group_word X,select_owner_keys_exact]
    exact exact_filter_group_keys name (actualGroup X) X.group root.order
  rw [filtered]
  have all (u : Left) (_ : u∈stageOldOrder X root.order) :
      (locate (name u.val) root.raw).result=some (exteriorData X gate pad (.inl u)) :=
    complete_owner_hit root inj u.val
  exact congrArg Meter.result (gather_owner_words_exact root.raw
    (fun u : Left=>name u.val) (fun u=>exteriorData X gate pad (.inl u)) (stageOldOrder X root.order) all)

theorem true_mount_has_ordered_physical_keys :
    ((X.seed pad).immutable.payload.payload.pages.map RefRow.address)=
      (stagePageOrder X).map (bootPageKey X pad) := by
  change ((rootTable X.chosenFields).map (mappedRow pad)).map RefRow.address=_
  unfold rootTable stagePageOrder
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro k _
  change (widened pad (residentPageKey m k)).result=
    (widened pad (residentPageKey m
      ((canonicalPageEquiv G ell X.centre).symm (canonicalPageEquiv G ell X.centre k)))).result
  rw [Equiv.symm_apply_apply]

theorem read_same_live_exterior_page_words (B : PageBank f ell key prec tw bw Pg)
    (live : IsLive (X.seed pad) B) :
    let read := readMountedOwners B (X.seed pad).identifier
    read.result=some ((X.seed pad).immutable.payload.stamp,(stagePageOrder X).map (bootPageKey X pad)) ∧
    read.steps=(locate (X.seed pad).identifier B.records).steps+
      (3+(3*Pg+7)*(stagePageOrder X).length)+5 := by
  have entry := read_mounted_owners_exact B (X.seed pad).identifier (X.seed pad).immutable.payload live.2
  have addresses := true_mount_has_ordered_physical_keys X pad
  have count : (X.seed pad).immutable.payload.payload.pages.length=(stagePageOrder X).length := by
    have p := congrArg List.length addresses
    simpa only [List.length_map] using p
  dsimp only
  rw [entry,addresses,count]
  exact ⟨rfl,rfl⟩

#print axioms exact_filter_group_keys
#print axioms read_actual_old_gate_words
#print axioms true_mount_has_ordered_physical_keys
#print axioms read_same_live_exterior_page_words
end
end J6R54ExteriorOwner
