import J6R37StructuredRootFields
import J6R35RootOriginsReader

/-! Certify the bodies that were actually initialized by the exterior
writer. The left lane retains the planted R31 half-port body; the new
right lane points to exactly the immutable exterior Page and uses its
own initial R21 raw trace address (not that of another chart). -/
namespace J6R37StructuredRoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R34RootAtlas J6R36ChildFramedRoute J6R35GatewayPreparation J6R35RootOrigins
open J6R27OriginalGate J6R27PrescribedProbe J6R30GeneratedRootLayout J6R26StablePreparedRoot
open J6Mesh J6OrientedHost J6R24LegalLayout J6R11Repack J6R10Repack J6R9PacketScopes
open J6R20Ancestor J6R21Leaf J6R11Blueprint J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

theorem canonical_group_to_exterior (h : Port (RootWire m))
    (grp : retainedGroup (rootNetwork (b:=K m) (l:=printedHalf m) T
      (J6R28GeneratedRootFrame.constantRootWord m)) (atGroup (rootChart T) (oddAxis m)) h=X.group) :
    physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group := by
  apply Fin.ext
  exact (root_half_groups_actual G ell X.centre h).symm.trans
    ((half_row_groups T (oddAxis m) h).trans (congrArg Fin.val grp))

noncomputable def rootGateBody (u : SourceVertex T)
    (x : PortAt (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u)) : List Bool :=
  (expectedHalfRow T (oddAxis m) x.val).body

noncomputable abbrev firstRetained
    (u : exteriorRows (G.selector ell) (G.ready ell) (G.centre ell X.centre) X.group) :=
  retainedFromExterior (G.selector ell) (G.ready ell) (G.centre ell X.centre) (rootPreset G ell)
    X.sample X.group u

theorem actual_kept_root_seed (gate : Stamp key prec) (fits : gate.created.val=base) (pad : ℕ)
    (u : exteriorRows (G.selector ell) (G.ready ell) (G.centre ell X.centre) X.group)
    (x : PortAt (firstRetained X u).next) :
    let M := firstRetained X u
    let tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) M.next :=
      Trace.keep Trace.start M
    let h := (M.back x).val
    let A := actualLane X gate pad h
    A∈(outerLanes X gate pad).result.lanes ∧
      A.gate.body=tr.literal (rootGateBody u.val) x ∧
      A.gate.origin=⟨gate,none⟩ ∧ A.gate.origin.stamp.created.val=(entry M.next).created := by
  let M := firstRetained X u
  let tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) M.next :=
    Trace.keep Trace.start M
  let h := (M.back x).val
  have grp : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group :=
    (congrArg M.group (M.back x).property).trans M.keeps
  have hdr : (actualLane X gate pad h).gate.body=tr.literal (rootGateBody u.val) x := by
    change false::(expectedHalfRow T (oddAxis m) h).body=
      side x.val::(expectedHalfRow T (oddAxis m) h).body
    rw [M.side_left x]
  have created : (entry (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val)).created=base := by
    generalize u.val=v
    cases v <;> rfl
  exact ⟨selected_root_lane X gate pad h grp,hdr,rfl,fits.trans (tr.tag.trans created).symm⟩

noncomputable abbrev packetRootHalf (k : CanonicalPage m)
    (x : PortAt (stableBorn X k)) : Port (RootWire m) :=
  (edge x.val).val

theorem actual_exterior_packet_seed (gate : Stamp key prec) (pad : ℕ) (k : CanonicalPage m)
    (x : PortAt (stableBorn X k)) :
    let h := packetRootHalf X k x
    let A := actualLane X gate pad h
    let bank := X.seed pad
    A∈(outerLanes X gate pad).result.lanes ∧
      A.packet.body=originSeed (rootChart T) (oddAxis m) X.group k x ∧
      A.packet.origin.stamp=bank.immutable.payload.stamp ∧
      A.packet.origin.stamp.creator=bank.identifier ∧
      A.packet.origin.stamp.created.val=(entry (stableBorn X k)).created ∧
      A.packet.origin.pageKey=some (widened pad (residentPageKey m k)).result ∧
      (locate (widened pad (residentPageKey m k)).result bank.immutable.payload.payload.pages).result=
        some (X.chosenFields k) := by
  let h := packetRootHalf X k x
  have grp : retainedGroup (rootNetwork (b:=K m) (l:=printedHalf m) T
      (J6R28GeneratedRootFrame.constantRootWord m)) (atGroup (rootChart T) (oddAxis m)) h=X.group :=
    (edge x.val).property
  have pg : ((rootChart T).seat (edge h)).1=k := by
    obtain ⟨x,hx⟩ := x
    cases x with
    | inl e => cases hx
    | inr e => exact Sum.inr.inj hx
  have hdr : (actualLane X gate pad h).packet.body=originSeed (rootChart T) (oddAxis m) X.group k x := by
    obtain ⟨x,hx⟩ := x
    cases x with
    | inl e => cases hx
    | inr e => rfl
  have old : (entry (stableBorn X k)).created=J6SourcePrecision.printed m base := rfl
  refine ⟨selected_root_lane X gate pad h (canonical_group_to_exterior X h grp),hdr,rfl,rfl,?_,?_,
    true_seed_payload_page X pad k⟩
  · change X.birth.val=(entry (stableBorn X k)).created
    exact X.birthOK.trans old.symm
  · change some (widened pad (residentPageKey m ((rootChart T).seat (edge h)).1)).result=
      some (widened pad (residentPageKey m k)).result
    rw [pg]

#print axioms canonical_group_to_exterior
#print axioms actual_kept_root_seed
#print axioms actual_exterior_packet_seed
end J6R37StructuredRoot