import J6R94ExteriorDebitBits
import J6R55BootBodiesLanes
import J6R41StructuredAllPathsExterior

/-! The order is the actual R30/R31 half-port serialization followed
by the exact marked R37 group filter. The column key is the same
canonical Page owned by the published atlas even at the last prescribed
non-prefix probe. -/
namespace J6R94ExteriorDebit
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R19Retained
open J6R25PreparedSupply J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R31RootResidentTables J6R27OriginalGate J6Mesh J6R49SourceLayout
open J6R54ExteriorOwner J6R55BootBodies J6R41StructuredAllPaths
open J6R30GeneratedRootLayout J6R28GeneratedRootFrame J6R26StablePreparedRoot
open J6R37StructuredRoot J6R35RootOrigins J6R34ChildPath J6R36ChildFramedRoute
open J6R10Repack J6R11Repack J6OrientedHost J6R24LegalLayout J6R26DescriptorTree

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4300
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n : ℕ} (P : Plant V m n)

def physicalSourceOwner (h : Port (RootWire m)) : SourceVertex P :=
  J6R10Repack.owner (rootNetwork (b:=K m) (l:=printedHalf m) P (constantRootWord m)) h

/-- Literal input stock for the next layout, independent of the external
slot request and of the chosen sample. It includes isolated old owners.
No arbitrary fee is claimed for supplying these complete ordered tapes. -/
structure RootLayoutStock {own : ℕ} (name : SourceVertex P→Word own) where
  order : List (SourceVertex P)
  nodup : order.Nodup
  complete : ∀ u,u∈order
  roles : List (Word own×BootRole)
  rolesExact : roles=order.map (fun u=>(name u,trueRootRole u))
  names : List (RefRow (rootHalfWidth m) (Word own))
  namesExact : names=(rootHalfOrder m).map (fun h=>
    ⟨(expectedHalfRow P (oddAxis m) h).address,name (physicalSourceOwner P h)⟩)
  nameInj : Function.Injective name

theorem actually_locate_stock_owner {own : ℕ} {name : SourceVertex P→Word own}
    (S : RootLayoutStock P name) (h : Port (RootWire m)) :
    (locate (expectedHalfRow P (oddAxis m) h).address S.names).result=
      some (name (physicalSourceOwner P h)) := by
  rw [S.namesExact]
  apply locate_hit
  · exact List.mem_map.mpr ⟨h,(root_half_order_complete m).2.1 h,rfl⟩
  · intro x hx eq
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    have e : p=h := half_addresses_unique P (oddAxis m) eq
    subst p
    rfl

theorem complete_stock_uses_exact_number_of_half_ports {own : ℕ} {name : SourceVertex P→Word own}
    (S : RootLayoutStock P name) :
    S.names.length=2*M m ∧ S.roles.length=S.order.length := by
  rw [S.namesExact,S.rolesExact,List.length_map,List.length_map]
  exact ⟨(root_half_order_complete m).2.2,rfl⟩

variable {f : ℤ[X]} {base native : ℕ} {P}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co dep edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Edge" => ((Ext).host.Edge)

theorem actual_old_owner_is_parent_half (e : Edge) :
    ((Ext).host.network.row e).val=physicalSourceOwner P e.val := rfl

def realHalfField (e : Edge) : SeatField (a m) (pageKeyWidth m) :=
  physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) (edge e.val)

-- The proof tag identifies the genuine root old precision; the raw
-- sparsity/endpoint program below computes no tag and has no tag fee.
private def precisionProofTag : Stamp key prec := ⟨word 0,word base⟩

private theorem original_precision_fits (X : StableExterior G ell q ro co dep edgew tc tj key prec tw bw) :
    base<2^prec := by
  have h := val_lt X.birth
  rw [X.birthOK] at h
  have b : base≤J6SourcePrecision.printed m base := by
    unfold J6SourcePrecision.printed
    omega
  exact b.trans_lt h

theorem actual_physical_half_page_equals_live_key (pad : ℕ) (e : Edge) :
    (widened pad (realHalfField X e).page).result=
      bootPageKey X pad ((Ext).host.network.col e) := by
  let gp : Stamp key prec := precisionProofTag (base:=base)
  have g : gp.created.val=base := word_val (original_precision_fits X)
  let vtx := (Ext).host.network.col e
  let pt : PortAt (J6R34ChildPath.point (Ext).host (.inr vtx)) := ⟨.inr e,rfl⟩
  have root := exact_real_root_tag_at_port X gp pad g (.inr vtx) pt
  have names := congrArg Origin.pageKey root
  change some (widened pad (realHalfField X e).page).result=
    some (bootPageKey X pad vtx) at names
  exact Option.some.inj names

def selectActualExteriorHalfRows : Meter (List (PortRow (rootHalfWidth m))) :=
  let tape := makeHalfTape m [] X.source.raw
  let sel := selectPorts X.address.group tape.result
  ⟨sel.result,tape.steps+sel.steps+4⟩

theorem measured_selection_uses_the_original_exterior_order :
    (selectActualExteriorHalfRows X).result=(orderedExteriorEdges X).map
      (fun e=>halfPortSpec m (side e.val) (realHalfField X e)) := by
  have same := exterior_half_tape_is_parent_file X
  change (selectPorts X.address.group (makeHalfTape m [] X.source.raw).result).result=_
  rw [same,actual_exterior_group_word X,(rootParent X).physical_port_select,
    exterior_order_is_exactly_selected X,List.map_map]
  rfl

def exteriorSelectRoof (m ro co dep : ℕ) :=
  halfTapeFee m ro co dep+7+2*M m*(2*rootHalfWidth m+3*(pageKeyWidth m+a m)+81)

theorem real_exterior_half_selection_fee :
    (selectActualExteriorHalfRows X).steps≤exteriorSelectRoof m ro co dep := by
  let M0 := makeHalfTape m [] X.source.raw
  let unit := 2*rootHalfWidth m+3*(pageKeyWidth m+a m)+81
  have actual := actual_root_half_tape X.source (oddAxis m) [] rfl
  have per (h : Port (RootWire m)) :
      rowScanFee (expectedHalfRow P (oddAxis m) h)=unit := by
    let F := physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) (edge h)
    unfold rowScanFee unit
    change 2*rootHalfWidth m+3*(F.page.bits++F.slot.bits).length+81=_
    rw [List.length_append,F.page.size,F.slot.size]
  have H : (M0.result.map rowScanFee).sum≤unit*(2*M m) := by
    have good (r : PortRow (rootHalfWidth m)) (hit : r∈M0.result) : rowScanFee r≤unit := by
      rw [show M0.result=_ from actual.1] at hit
      obtain ⟨h,_,rfl⟩ := List.mem_map.mp hit
      exact (per h).le
    exact (J6R82LayoutDebit.sum_mapped_bounded M0.result rowScanFee unit good).trans_eq
      (congrArg (unit*·) actual.2.1)
  have ff := (select_ports_exact X.address.group M0.result).2
  have mfee := actual.2.2
  change M0.steps≤_ at mfee
  change M0.steps+(selectPorts X.address.group M0.result).steps+4≤_
  rw [ff]
  unfold exteriorSelectRoof
  rw [Nat.mul_comm (2*M m)]
  change _≤halfTapeFee m ro co dep+7+unit*(2*M m)
  omega

#print axioms actually_locate_stock_owner
#print axioms complete_stock_uses_exact_number_of_half_ports
#print axioms actual_old_owner_is_parent_half
#print axioms actual_physical_half_page_equals_live_key
#print axioms measured_selection_uses_the_original_exterior_order
#print axioms real_exterior_half_selection_fee
end
end J6R94ExteriorDebit
