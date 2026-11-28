import J6R20AncestorLiteral
import J6R19RetainedHost
import J6R18ChildWriteGeometric

/-! One real creation -> retention path. The descendant's raw local
bit assignment is routed back to the stored original packet chart,
which is evaluated at creation precision; that frame is then read and
promoted. No old numeric entry is an input. No sibling is called. -/
namespace J6R20Ancestor
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 AOracleCoordinates
open J6R18ChildWrite J6R19Retained J6R10Repack J6R11Blueprint
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild

def runAncestor {p q ell a w oldWidth newWidth : ℕ}
    (hp : 0<p) {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (fromTag : J6R15ModeCost.Word oldWidth) (toTag : J6R15ModeCost.Word newWidth)
    (z : UVBlock old ell) (t : ℤ) (i : Fin a) (b : ℕ)
    (rowSlots colSlots : List (J6R15ModeCost.Word a)) (modes : List (ModeInput a p i w))
    (raw : List Raw) (suffix : List Bool) : Meter (List Bool×List Bool) :=
  let bits := routePacket rowSlots colSlots raw
  let d := packetResult hp he hEll z t i b bits.result.1 bits.result.2 modes
  let input := writeEntry fromTag d.result
  let current := promoteFrame (ell:=ell) (oldWidth:=oldWidth) hD toTag (input.result++suffix)
  ⟨current.result,bits.steps+d.steps+input.steps+4+current.steps+4⟩

def ancestorFee (a e ell p q i w b n r c m oldWidth newWidth : ℕ) (hp : 0<p) :=
  routeFee a n r c+packetFee a e ell p i w b r c m hp+
    packetFramingFee e ell p oldWidth+promoteFee e ell p q oldWidth newWidth+4

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

set_option maxHeartbeats 1700000 in
theorem run_created_then_retained {H K : Type} {p q ell m w oldWidth newWidth : ℕ}
    (hp : 0<p) (hq : 0<q) {f : ℤ[X]} (hf : f.Monic) (heF : 0<f.natDegree)
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (he : 0<old.length) (hEll : 0<ell)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=i.val)
    (z : UVBlock old ell) (oldFile : EntryFile f ell N)
    (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i w)
    (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r,r∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c,c∈cs)
    (b : ℕ) (hw : 0<w) (hb : m+1≤2^b) (hCount : rs.length<2^w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (fromTag : J6R15ModeCost.Word oldWidth) (hFrom : fromTag.val=p)
    (toTag : J6R15ModeCost.Word newWidth) (hTo : toTag.val=q)
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K) (stay : grp (.inr k)=h)
    (descPacket : ∀ k' : K,(PacketPorts (OriginNet P i g) grp pkt h k'→Bool)→Residue f ell q)
    (assign : HopPorts grp pkt k stay→Bool) (ports : List (HopPorts grp pkt k stay))
    (hall : ∀ x,x∈ports) (raw : List Raw)
    (hTape : raw=ports.map (fun x=>literalPort grp pkt k stay x (assign x)))
    (rowSlots colSlots : List (J6R15ModeCost.Word a))
    (hRows : rowSlots=rs.map (fun r=>slotWord P r.val))
    (hCols : colSlots=cs.map (fun c=>slotWord P c.val))
    (suffix : List Bool) :
    let nil := J6R10Integral.box_two_nil p f ell
    let root := actualPacketHost P i ht0 hv p nil (castBox hO (uvRead hp old ell z)) oldFile β g
    let target := compileChild (OriginNet P i g) grp pkt h root.file q descPacket (.inl (keptVertex grp k stay))
    let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let op := runAncestor hp he hEll hD fromTag toTag z t i b rowSlots colSlots (List.ofFn ms) raw suffix
    ∃ u : UVBlock new ell,
      op.result=((writeEntry toTag u).result,suffix) ∧
      fromTag.val=target.created ∧ toTag.val=q ∧
      frameRead newWidth q new.length ell op.result.1=(toTag.bits,u.val.map (fun row=>row.val.map Subtype.val)) ∧
      castBox hN (uvRead hq new ell u)=target.read hf q assign ∧
      op.steps≤ancestorFee a old.length ell p q i.val w b ports.length rs.length cs.length m oldWidth newWidth hp := by
  let nil := J6R10Integral.box_two_nil p f ell
  let root := actualPacketHost P i ht0 hv p nil (castBox hO (uvRead hp old ell z)) oldFile β g
  let created := root.file (.inr k)
  let rootBits := assign ∘ (hop grp pkt k stay).symm
  let v := originState P i g k rootBits
  let rows := rs.map (realRow P i v)
  let cols := cs.map (realCol P i v)
  let route := routePacket rowSlots colSlots raw
  let d := packetResult hp he hEll z t i b rows cols (List.ofFn ms)
  let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let current := promoteFrame (ell:=ell) (oldWidth:=oldWidth) hD toTag ((writeEntry fromTag d.result).result++suffix)
  let op := runAncestor hp he hEll hD fromTag toTag z t i b rowSlots colSlots (List.ofFn ms) raw suffix
  have rawEq := hTape.trans (literalTape_is_payload grp pkt k stay assign ports)
  obtain ⟨hRoute,hRouteCost⟩ := route_packet_exact P i g k grp pkt stay assign ports hall rs cs raw rawEq
    rowSlots colSlots hRows hCols
  have hRoute' : route.result=(rows,cols) := hRoute
  obtain ⟨hEval,hEvalCost⟩ := real_packet_word hp he hEll P i ht ht0 hv z g k v rs hnR haR cs hnC haC
    ξ β ms hMode b hw hb hCount hCodes
  have hEntry : castBox hO (uvRead hp old ell d.result)=created.table rootBits := by
    change castBox hO (uvRead hp old ell d.result)=actualPacket P i ht0 hv p nil
      (castBox hO (uvRead hp old ell z)) β g k v
    rw [show uvRead hp old ell d.result=_ from hEval,packet_change_ring]
  obtain ⟨u,hOut,hTag,hTo',hFrame,hValue,hCurrent⟩ :=
    promote_frame_native hf heF hq created hp hO hN fromTag hFrom toTag hTo rootBits d.result hEntry suffix
  have outEq : op.result=current.result := by
    dsimp only [op,runAncestor]
    rw [show (routePacket rowSlots colSlots raw).result=(rows,cols) from hRoute']
  refine ⟨u,outEq.trans hOut,hTag,hTo',?_,hValue,?_⟩
  · change frameRead newWidth q new.length ell op.result.1=_
    rw [outEq]
    exact hFrame
  · change op.steps≤_
    have hSteps : op.steps=route.steps+d.steps+(writeEntry fromTag d.result).steps+4+current.steps+4 := by
      dsimp only [op,runAncestor]
      rw [show (routePacket rowSlots colSlots raw).result=(rows,cols) from hRoute']
    have hWrite := (write_roundtrip fromTag d.result).2.2
    change (writeEntry fromTag d.result).steps=_ at hWrite
    change route.steps≤_ at hRouteCost
    change d.steps≤_ at hEvalCost
    change current.steps≤_ at hCurrent
    rw [← size_of_monic_words hp hf hO] at hCurrent
    change current.steps≤promoteFee old.length ell p q oldWidth newWidth at hCurrent
    rw [hSteps,hWrite,ancestorFee,packetFramingFee]
    omega

#print axioms run_created_then_retained
end J6R20Ancestor




