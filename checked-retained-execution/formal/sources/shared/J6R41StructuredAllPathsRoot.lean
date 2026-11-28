import J6R41StructuredAllPathsRootTransport

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3100

/-! The exterior ingress uses the same original half-wire/side as
the emitted R37 seed, including at the canonical physically widened
Page. This is a proof-side projection of already written bytes. -/
namespace J6R41StructuredAllPaths
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R20Ancestor J6R10Repack J6R11Blueprint J6R26DescriptorTree
open J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R31RootResidentTables J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R35RootOrigins
open J6R11Repack J6R12Blueprint J6R25PreparedSupply J6ActiveSchedule J6ActiveRun J6R14ZeroMode
open J6R37StructuredRoot J6R36ChildFramedRoute J6R15ModeCost

abbrev Payload (key prec page : ℕ) := Origin key prec page × List Bool

def lanePayload {w key prec page : ℕ} (a : Lane w key prec page) : Payload key prec page :=
  (a.origin,a.body)

theorem carry_payload_exact {w key prec page : ℕ} (a : Lane w key prec page) (nextGroup : Word 6) :
    ((carryLane a nextGroup).result.2,(carryLane a nextGroup).result.1.body)=lanePayload a := by
  rw [carry_keeps_body_and_stamp]
  rfl

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)

local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)

noncomputable def initialPayload (h : Port (exteriorChild G ell X.centre X.sample X.group).host.Edge) :
    Payload key prec (pageKeyWidth m+pad) :=
  let r := actualLane X gate pad (edge h).val
  lanePayload (if side h then r.packet else r.gate)

noncomputable def exteriorPageOrigin (k : CanonicalPage m) : Origin key prec (pageKeyWidth m+pad) :=
  ⟨(X.seed pad).immutable.payload.stamp,some (widened pad (residentPageKey m k)).result⟩

noncomputable def initialOrigin (u : (ext).host.Row⊕(ext).host.Col) : Origin key prec (pageKeyWidth m+pad) :=
  match u with
  | .inl _=> ⟨gate,none⟩
  | .inr k=> exteriorPageOrigin X pad ((canonicalPageEquiv G ell X.centre).symm k)

theorem initial_gate_is_written (gateWidth : gate.created.val=base)
    (u : (ext).host.Row) :
    ∃ tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val)
        (J6R34ChildPath.point (ext).host (.inl u)),∀ x,
      initialPayload X gate pad x.val=
        (initialOrigin X gate pad (.inl u),tr.literal (rootGateBody (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) x) := by
  let M := firstRetained X u
  let E : J6R34ChildPath.point (ext).host (.inl u)=M.next :=
    (retained_prescribed_point (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group u).symm
  let tr0 : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) M.next := .keep .start M
  refine ⟨E.symm ▸ tr0,?_⟩
  intro x
  let y := castPort E x
  have H : edge y.val=edge x.val := (cast_port_edge E x).trans rfl
  have old : (M.back y).val=(edge x.val).val :=
    (M.back_val y).trans (congrArg Subtype.val H)
  have left : side x.val=false := (cast_port_preserves_side E x).symm.trans (M.side_left y)
  obtain ⟨_,body,origin,_⟩ := actual_kept_root_seed X gate gateWidth pad u y
  rw [move_cast_literal E tr0]
  change lanePayload (if side x.val then (actualLane X gate pad (edge x.val).val).packet
    else (actualLane X gate pad (edge x.val).val).gate)= (⟨gate,none⟩,tr0.literal _ y)
  rw [left,←old]
  change lanePayload (actualLane X gate pad (M.back y).val).gate=_
  exact Prod.ext origin body

theorem initial_packet_is_written (k : CanonicalPage m) :
    let K := canonicalPageEquiv G ell X.centre k
    ∃ tr : Trace (stableBorn X k) (J6R34ChildPath.point (ext).host (.inr K)),
      (locate (widened pad (residentPageKey m k)).result
        (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) ∧
      ∀ x,initialPayload X gate pad x.val=(initialOrigin X gate pad (.inr K),
        tr.literal (originSeed (rootChart T) (oddAxis m) X.group k) x) := by
  let K := canonicalPageEquiv G ell X.centre k
  let p := J6R34ChildPath.point (ext).host (.inr K)
  let E : p=stableBorn X k := stable_exterior_exact_born X k
  let τ : Trace (stableBorn X k) p := E.symm ▸ Trace.start
  refine ⟨τ,true_seed_payload_page X pad k,?_⟩
  intro x
  let y := castPort E x
  have h : (edge y.val).val=(edge x.val).val := canonical_exterior_cast_keeps_wire X k x
  have right : side x.val=true := by
    rw [←cast_port_preserves_side E x]
    change side y.val=true
    obtain ⟨x,hx⟩ := y
    cases x with
    | inl e => cases hx
    | inr e => rfl
  obtain ⟨_,body,stamp,_,_,page,_⟩ := actual_exterior_packet_seed X gate pad k y
  have moved : (E.symm ▸ Trace.start : Trace (stableBorn X k) p).literal
      (originSeed (rootChart T) (oddAxis m) X.group k) x=
        originSeed (rootChart T) (oddAxis m) X.group k y :=
    move_cast_literal E (Trace.start : Trace (stableBorn X k) (stableBorn X k))
      (originSeed (rootChart T) (oddAxis m) X.group k) x
  have actual : initialPayload X gate pad x.val=
      (initialOrigin X gate pad (.inr K),originSeed (rootChart T) (oddAxis m) X.group k y) := by
    change lanePayload (if side x.val then (actualLane X gate pad (edge x.val).val).packet
      else (actualLane X gate pad (edge x.val).val).gate)=
        (exteriorPageOrigin X pad ((canonicalPageEquiv G ell X.centre).symm K),originSeed
          (rootChart T) (oddAxis m) X.group k y)
    rw [right,←h,(canonicalPageEquiv G ell X.centre).symm_apply_apply k]
    change lanePayload (actualLane X gate pad (edge y.val).val).packet=_
    refine Prod.ext ?_ body
    change (actualLane X gate pad (edge y.val).val).packet.origin=exteriorPageOrigin X pad k
    unfold exteriorPageOrigin
    let U := (actualLane X gate pad (edge y.val).val).packet.origin
    have eta : U=Origin.mk U.stamp U.pageKey := by cases U; rfl
    exact eta.trans (congrArg₂ Origin.mk stamp page)
  change initialPayload X gate pad x.val=(initialOrigin X gate pad (.inr K),
    τ.literal (originSeed (rootChart T) (oddAxis m) X.group k) x)
  exact actual.trans (congrArg (Prod.mk _) moved.symm)

#print axioms carry_payload_exact
#print axioms initial_gate_is_written
#print axioms initial_packet_is_written
end J6R41StructuredAllPaths