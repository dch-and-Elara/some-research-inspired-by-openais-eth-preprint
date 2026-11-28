import J6R58BootScopeBits
import J6R54ExteriorOwnerMount
import J6R57ScopeFeeCaps

/-! The original read-only exterior-owner mount is priced by the count
of supplied raw owners, the original local gate degree, and the actual
number of pages in the installed root record. No bound on the previous
mount routine's fee is a premise. -/
namespace J6R58BootScope
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6Mesh J6OrientedHost J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R35RootOrigins J6R36ChildFramedRoute J6R34RootAtlas J6R41StructuredAllPaths
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R57ScopeFee J6R51Peak
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R32RootGeneratedRegistryInputs J6R12Blueprint J6R37StructuredRoot
open J6ActiveRun J6ActiveSchedule J6R10Repack J6R30ProducedGateRegistry
open J6R27PrescribedProbe J6R24LegalLayout J6R52CacheSource J6R32ChildResidentTransfer J6R27OriginalGate J6R32StatefulArithmetic
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own next : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable {name : (exteriorChild G ell X.centre X.sample X.group).host.Row⊕
    (exteriorChild G ell X.centre X.sample X.group).host.Col→Word next}
variable (K : KeyInputs X gate pad root name)
variable (bootBank : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) bootBank)
variable (inj : Function.Injective rootName)

theorem original_root_local_gate_fits (d : ℕ) (fit : ∀ u,P.degree u≤d)
    (x : SourceVertex P) : (rootLocalGate P x).degree≤max d 2 := by
  rcases x with ((⟨u,k⟩|⟨p,b⟩)|v)
  · exact (fit u).trans (Nat.le_max_left _ _)
  · exact (show 1≤2 by decide).trans (Nat.le_max_right _ _)
  · exact Nat.le_max_right _ _

def bootMountGeometry (own next gateWidth key prec pg owners pages bankRows maxDegree : ℕ) :=
  (3+owners*(6*own+78))+
  (3+owners*(locateFee own owners+rootGateWidthFee gateWidth key prec pg maxDegree+8))+
  (locateFee key bankRows+3+(3*pg+7)*pages+5)+
  ((3+pages*(originWidthFee key prec pg+11))+(4*owners+3)+
    (3+(3*next+6)*(owners+pages))+5)+8

include bootBank live inj in
theorem actual_boot_mount_count_from_live_records :
    (chosenFirstRaw X gate pad root bootBank name K).result=some (outputRosterRows X gate pad root name) ∧
    (mountFirstOwners X gate pad root bootBank live K inj).result.raw.length≤
      root.order.length+(stagePageOrder X).length := by
  have raw := (mountFirstOwners X gate pad root bootBank live K inj).result.exactRows
  have headers := List.length_filter_le (fun v : OwnerGroup own=>decide (X.address.group=v.group)) K.headers.result
  have len := congrArg List.length (exact_filter_group_keys rootName (actualGroup X) X.group root.order)
  simp only [List.length_map] at len
  rw [K.headerExact,actual_exterior_group_word X] at headers
  simp only [List.length_map] at headers
  have oldLen : (stageOldOrder X root.order).length≤root.order.length := by
    change (scanSubtype (fun v=>actualGroup X v=X.group) root.order).length≤_
    exact len ▸ headers
  have trueLen : (mountFirstOwners X gate pad root bootBank live K inj).result.raw.length=
      (stageOldOrder X root.order).length+(stagePageOrder X).length := by
    rw [raw]
    change ((stageOwnerOrder X root.order).map _).length=_
    simp only [List.length_map,stageOwnerOrder,List.length_append]
  exact ⟨local_exterior_raw_rows X gate pad root bootBank live name K inj,
    trueLen.le.trans (Nat.add_le_add_right oldLen _)⟩

include bootBank live inj in
theorem actual_live_boot_mount_ceiling (d : ℕ) (fit : ∀ u,P.degree u≤d) :
    (mountFirstOwners X gate pad root bootBank live K inj).steps≤
      K.headers.steps+K.dest.steps+
      bootMountGeometry own next (SuffixWordWidth m) key prec Pg root.order.length
        (stagePageOrder X).length bootBank.records.length (max d 2) := by
  let U := (Ext).host.Row
  let Q := (Ext).host.Col
  let us := stageOldOrder X root.order
  let ps := stagePageOrder X
  let oldKey : U→Word own := fun u=>rootName u.val
  let oldVal : U→OwnerData (SuffixWordWidth m) key prec Pg := fun u=>exteriorData X gate pad (.inl u)
  let rows := K.headers.result
  let address := X.address.group
  let stored := (X.seed pad).immutable.payload.stamp
  let freshKey := bootPageKey X pad
  let left : U→Word next := fun u=>name (.inl u)
  let right : Q→Word next := fun k=>name (.inr k)
  let outOrder : List (U⊕Q) := us.map Sum.inl++ps.map Sum.inr
  have sameName : Sum.elim left right=name := by
    funext x
    cases x <;> rfl
  have destSame : K.dest.result=outOrder.map (Sum.elim left right) := by
    rw [sameName]
    exact K.destExact
  have rootsLen : root.raw.length=root.order.length := by rw [root.exactRows,List.length_map]
  have headerLen : rows.length=root.order.length := by rw [show rows=K.headers.result from rfl,K.headerExact,List.length_map]
  have selectSame : (selectOwnerKeys address rows).result=us.map oldKey := by
    change (selectOwnerKeys X.address.group K.headers.result).result=_
    rw [K.headerExact,actual_exterior_group_word X,select_owner_keys_exact]
    exact exact_filter_group_keys rootName (actualGroup X) X.group root.order
  have oldLe : us.length≤root.order.length := by
    have h : (selectOwnerKeys address rows).result.length≤rows.length := by
      rw [select_owner_keys_exact]
      dsimp only
      rw [List.length_map]
      exact List.length_filter_le _ _
    rw [selectSame,List.length_map,headerLen] at h
    exact h
  have lookup (u : U) (_ : u∈us) :
      (locate (oldKey u) root.raw).result=some (oldVal u) :=
    complete_owner_hit root inj u.val
  have oldExact : gatherOwners root.raw (selectOwnerKeys address rows).result=
      ⟨some (us.map oldVal),3+(us.map
        (fun u=>(locate (oldKey u) root.raw).steps+ownerDataFee (oldVal u)+8)).sum⟩ := by
    rw [selectSame]
    exact gather_owner_words_exact root.raw oldKey oldVal us lookup
  have oldSame := congrArg Meter.result oldExact
  have pageExact := read_same_live_exterior_page_words X pad bootBank live
  dsimp only at pageExact
  have mountExact := mount_words_from_actual_reads bootBank (X.seed pad).identifier address rows root.raw
    K.dest stored freshKey oldVal left right us ps oldSame pageExact.1 destSame
  dsimp only at mountExact
  have rawExact := congrArg Meter.steps mountExact
  dsimp only at rawExact
  have selectBound := select_key_fee_by_actual_length address rows
  rw [headerLen] at selectBound
  have gatherBound :
      (gatherOwners root.raw (selectOwnerKeys address rows).result).steps≤
        3+root.order.length*(locateFee own root.order.length+
          rootGateWidthFee (SuffixWordWidth m) key prec Pg (max d 2)+8) := by
    rw [oldExact]
    dsimp only
    apply Nat.add_le_add_left
    refine (uniform_sum_bound _ _ _ (fun u _=>?_)).trans (Nat.mul_le_mul_right _ oldLe)
    have a := locate_bound (oldKey u) root.raw
    rw [rootsLen] at a
    have b : ownerDataFee (oldVal u)≤_ :=
      original_encoded_gate_fee (gateTag (P:=P) gate pad u.val)
        (rootOperand P u.val ∘ (rootLocalGate P u.val).port) (rootLocalGate P u.val).gate
        (original_root_local_gate_fits d fit u.val)
    omega
  have pageBound : (readMountedOwners bootBank (X.seed pad).identifier).steps≤
      locateFee key bootBank.records.length+3+(3*Pg+7)*ps.length+5 := by
    have bill : (readMountedOwners bootBank (X.seed pad).identifier).steps=
        (locate (X.seed pad).identifier bootBank.records).steps+(3+(3*Pg+7)*ps.length)+5 :=
      pageExact.2
    rw [bill]
    have h := locate_bound (X.seed pad).identifier bootBank.records
    omega
  have writeBound : (writeMountedOwners stored (ps.map freshKey) (us.map oldVal) K.dest.result).steps≤
      (3+ps.length*(originWidthFee key prec Pg+11))+(4*root.order.length+3)+
        (3+(3*next+6)*(root.order.length+ps.length))+5 := by
    rw [destSame,write_mounted_owners_exact]
    dsimp only
    have sumEq : (ps.map (fun k=>ownerDataFee
        (freshOwnerData (gate:=SuffixWordWidth m) stored (freshKey k))+4)).sum=
        ps.length*(originWidthFee key prec Pg+11) := by
      have eq : (ps.map (fun k=>ownerDataFee
          (freshOwnerData (gate:=SuffixWordWidth m) stored (freshKey k))+4))=
          ps.map (fun _=>originWidthFee key prec Pg+11) := by
        apply List.map_congr_left
        intro k _
        rw [fresh_owner_width_fee]
      rw [eq]
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    rw [sumEq]
    simp only [List.length_append,List.length_map]
    have w := Nat.mul_le_mul_left (3*next+6) (Nat.add_le_add_right oldLe ps.length)
    have o := Nat.mul_le_mul_left 4 oldLe
    omega
  change K.headers.steps+(chosenFirstRaw X gate pad root bootBank name K).steps≤_
  change K.headers.steps+(mountWords bootBank (X.seed pad).identifier address rows root.raw K.dest).steps≤_
  rw [rawExact]
  unfold bootMountGeometry
  change _≤K.headers.steps+K.dest.steps+
    ((3+root.order.length*(6*own+78))+
    (3+root.order.length*(locateFee own root.order.length+rootGateWidthFee
      (SuffixWordWidth m) key prec Pg (max d 2)+8))+
    (locateFee key bootBank.records.length+3+(3*Pg+7)*ps.length+5)+
    ((3+ps.length*(originWidthFee key prec Pg+11))+(4*root.order.length+3)+
      (3+(3*next+6)*(root.order.length+ps.length))+5)+8)
  omega

end
#print axioms original_root_local_gate_fits
#print axioms actual_boot_mount_count_from_live_records
#print axioms actual_live_boot_mount_ceiling
end J6R58BootScope
