import J6R58BootScopeBits
import J6R55TerminalOriginSite
import J6R55BootBodiesCost
import J6R55BootBodiesMachine

/-! The original first writer copies the already available two-lane
order once per true exterior edge. The true tagged reader scans the
two named lists and expressly pays its finite per-port address query. -/
namespace J6R58BootScope
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R48GeneratedAddons J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online
open J6R55TerminalOrigin J6R55BootBodies J6R57ScopeFee J6R16ModeCost J6R51Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 5900
set_option Elab.async false
noncomputable section

section read
variable {f : ℤ[X]} {ell s C key prec tw bw pg own gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw pg}
variable {name : (v.parent.host.Row⊕v.parent.host.Col)→Word own}
variable {value : (v.parent.host.Row⊕v.parent.host.Col)→OwnerData gate key prec pg}

def bootAddressBill (D : BootPortWords I name) (order : List (Port v.parent.host.Edge)) : ℕ :=
  (order.map (fun h=>(D.queries h).steps)).sum

def bootEmitGeometry (ports own d key prec pg seatWidth ownerRows seatRows : ℕ) : ℕ :=
  4+ports*(locateFee own ownerRows+locateFee seatWidth seatRows+maxAddonFee own d key prec pg+14)

theorem original_boot_tag_emit_from_word_tables (D : BootPortWords I name)
    (R : CompleteRoster name value) (order : List (Port v.parent.host.Edge)) :
    (J6R48GeneratedAddons.emit (readBootAddon D R) order).steps≤
      bootAddressBill D order+bootEmitGeometry order.length own (dim v) key prec pg
        D.seatWidth R.raw.length D.seats.result.length := by
  let proj := (projectOriginTape R.raw).result
  let rd := readBootAddon D R
  let look := locateFee own R.raw.length+locateFee D.seatWidth D.seats.result.length
  let ad := maxAddonFee own (dim v) key prec pg
  have each (h : Port v.parent.host.Edge) :
      (rd h).steps+addonFee own (dim v) key prec pg (rd h).result.oldOrigin.pageKey.isSome+4≤
        (D.queries h).steps+(look+ad+14) := by
    have find := resident_read_bound proj D.seats.result (D.queries h)
    have eq : proj.length=R.raw.length := origin_tape_same_length R.raw
    rw [eq] at find
    have copy := addon_fee_from_actual_widths own (dim v) key prec pg
      (rd h).result.oldOrigin.pageKey.isSome
    change _≤ad at copy
    change (residentRead proj D.seats.result (D.queries h)).steps+2+_+4≤_
    have paid : (residentRead proj D.seats.result (D.queries h)).steps≤
        (D.queries h).steps+look+8 := by
      dsimp only [look]
      omega
    omega
  have batch := sum_with_explicit_query_bill order
    (fun h=>(rd h).steps+addonFee own (dim v) key prec pg (rd h).result.oldOrigin.pageKey.isSome+4)
    (fun h=>(D.queries h).steps) (look+ad+14) (fun h _=>each h)
  rw [(emit_exact _ _).2]
  change 4+(order.map (fun h=>(rd h).steps+
    addonFee own (dim v) key prec pg (rd h).result.oldOrigin.pageKey.isSome+4)).sum≤
      (order.map (fun h=>(D.queries h).steps)).sum+(4+order.length*(look+ad+14))
  omega

theorem boot_native_half_port_count (I : OccurrenceInput T v key prec tw bw pg) :
    (compileOccurrence I).native.physical.order.length=2*v.parent.edges := by
  letI : Fintype v.parent.host.Edge := v.parent.host.finiteEdge
  let B := compileOccurrence I
  have c := full_roster_length B.native.physical.order B.native.physical.nodup B.native.physical.complete
  change B.native.physical.order.length=Nat.card (v.parent.host.Edge⊕v.parent.host.Edge) at c
  have m : Fintype.card v.parent.host.Edge=v.parent.edges := (ticketReady T v).edgeCount
  have k : Nat.card v.parent.host.Edge=v.parent.edges := Nat.card_eq_fintype_card.trans m
  have n : Nat.card (v.parent.host.Edge⊕v.parent.host.Edge)=2*v.parent.edges := by
    rw [Nat.card_sum,k]
    omega
  exact c.trans n

theorem boot_emit_geometry_monotone {n N ow Ow d D key prec pg w W o O t Tₙ : ℕ}
    (hN : n≤N) (hOw : ow≤Ow) (hD : d≤D) (hW : w≤W) (hO : o≤O) (hT : t≤Tₙ) :
    bootEmitGeometry n ow d key prec pg w o t≤bootEmitGeometry N Ow D key prec pg W O Tₙ := by
  unfold bootEmitGeometry
  refine Nat.add_le_add_left (Nat.mul_le_mul hN ?_) _
  have oFee : locateFee ow o≤locateFee Ow O := by
    unfold locateFee
    exact Nat.add_le_add_right (Nat.mul_le_mul hO (by omega)) _
  have sFee : locateFee w t≤locateFee W Tₙ := by
    unfold locateFee
    exact Nat.add_le_add_right (Nat.mul_le_mul hT (by omega)) _
  unfold maxAddonFee
  omega
end read

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))

variable (A : FirstBodyProgram X gate pad T)

theorem actual_first_writer_uses_exact_resident_geometry (w : RootSlot) :
    let writer := readFirstPhysical X gate pad A.lanes (A.seats w)
    writer.steps=(A.seats w).made.steps+8+(Ext).edges*
      bootCopyStride m (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) (Ext).depth) (A.width w) := by
  letI : Fintype (Ext).host.Edge := (Ext).host.finiteEdge
  let t := (Path.root : Path sel Ext Ext).ticket w
  have hc := full_roster_length (orderedExteriorEdges X) (reviewed_exterior_order X).1 (reviewed_exterior_order X).2
  have edge : Fintype.card (Ext).host.Edge=(Ext).edges := (ticketReady T t).edgeCount
  rw [Nat.card_eq_fintype_card,edge] at hc
  let S := A.seats w
  change (bootRaw X gate pad A.lanes S.made).steps=_
  rw [actual_boot_body_copy_uniform_fee X gate pad A.lanes S.made _ S.exact,hc]

end
#print axioms bootAddressBill
#print axioms original_boot_tag_emit_from_word_tables
#print axioms boot_native_half_port_count
#print axioms boot_emit_geometry_monotone
#print axioms actual_first_writer_uses_exact_resident_geometry
end J6R58BootScope
