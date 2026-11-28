import J6R21AncestorRoute
import J6R19RetainedBox
import J6R18ChildWriteHost

/-! One actual creation-time coefficient calculation, reused through an
arbitrary finite number of real retentions. The current evaluator
returns native U/V words directly to the leaf multiplier. No supplied
numeric old entry and no composed chain of old numeric routines. -/
namespace J6R21Ancestor
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 AOracleCoordinates
open J6R18ChildWrite J6R19Retained J6R10Repack J6R11Blueprint J6R20Ancestor
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild

def invokeTrace {p q ell a w : ℕ}
    (hp : 0<p) {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (z : UVBlock old ell) (t : ℤ) (i : Fin a) (b depth : ℕ)
    (rowSlots colSlots : List (J6R15ModeCost.Word a)) (modes : List (ModeInput a p i w))
    (raw : List Raw) : Meter (UVBlock new ell) :=
  let qbits := routeTrace depth rowSlots colSlots raw
  let orig := packetResult hp he hEll z t i b qbits.result.1 qbits.result.2 modes
  let out := resizeUV hD orig.result
  ⟨out.result,qbits.steps+orig.steps+out.steps+4⟩

def invokeFee (a e ell p q i w b depth n r c m : ℕ) (hp : 0<p) :=
  traceRouteFee a depth n r c+packetFee a e ell p i w b r c m hp+boxFee e ell p q+4

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

noncomputable def generatedPoint {f : ℤ[X]} {ell p : ℕ}
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht0 : t≠0) (hv : padicValInt 2 t=i.val)
    (z : Residue f ell p) (oldFile : EntryFile f ell N)
    (β : Mode i p P.mask→₀ℕ) (g : G) (k : Page a P.copies G) : Point f ell :=
  ⟨actualPacketHost P i ht0 hv p (J6R10Integral.box_two_nil p f ell) z oldFile β g,.inr k⟩

set_option maxHeartbeats 1800000 in
theorem invoke_history_native {f : ℤ[X]} {p q ell m w : ℕ}
    (hf : f.Monic) (heF : 0<f.natDegree) (hp : 0<p) (hq : 0<q)
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
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox hO (uvRead hp old ell z)) oldFile β g k) cur)
    (bits : PortAt cur→Bool) (ports : List (PortAt cur)) (hall : ∀ x,x∈ports)
    (raw : List Raw) (hTape : raw=ports.map (fun x=>(tr.literal (originSeed P i g k) x,bits x)))
    (rowSlots colSlots : List (J6R15ModeCost.Word a))
    (hRows : rowSlots=rs.map (fun r=>slotWord P r.val))
    (hCols : colSlots=cs.map (fun c=>slotWord P c.val)) :
    let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let op := invokeTrace hp he hEll hD z t i b tr.depth rowSlots colSlots (List.ofFn ms) raw
    castBox hN (uvRead hq new ell op.result)=(entry cur).read hf q bits ∧
      (entry cur).created=p ∧
      op.steps ≤ invokeFee a old.length ell p q i.val w b tr.depth ports.length rs.length cs.length m hp := by
  let root := generatedPoint P i ht0 hv (castBox hO (uvRead hp old ell z)) oldFile β g k
  let rootBits := bits ∘ tr.back.symm
  let v := originState P i g k rootBits
  let rows := rs.map (realRow P i v)
  let cols := cs.map (realCol P i v)
  let route := routeTrace tr.depth rowSlots colSlots raw
  let d := packetResult hp he hEll z t i b rows cols (List.ofFn ms)
  let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let out := resizeUV hD d.result
  let op := invokeTrace hp he hEll hD z t i b tr.depth rowSlots colSlots (List.ofFn ms) raw
  obtain ⟨hRoute,hRC⟩ := route_trace_exact tr P i g k (Equiv.refl _) bits ports hall raw hTape
    rs cs rowSlots colSlots hRows hCols
  have routed : (routeTrace tr.depth rowSlots colSlots raw).result=(rows,cols) := hRoute
  obtain ⟨hEval,hEC⟩ := real_packet_word hp he hEll P i ht ht0 hv z g k v rs hnR haR cs hnC haC
    ξ β ms hMode b hw hb hCount hCodes
  have hEntry : castBox hO (uvRead hp old ell d.result)=(entry root).table rootBits := by
    change castBox hO (uvRead hp old ell d.result)=actualPacket P i ht0 hv p
      (J6R10Integral.box_two_nil p f ell) (castBox hO (uvRead hp old ell z)) β g k v
    rw [show uvRead hp old ell d.result=_ from hEval,packet_change_ring]
  obtain ⟨hOut,hOC⟩ := native_resize_read hf heF hq (entry root) hp hO hN rootBits d.result hEntry
  refine ⟨?_,tr.tag,?_⟩
  · change castBox hN (uvRead hq new ell op.result)=(entry cur).read hf q bits
    rw [tr.read hf q bits]
    have hOp : op.result=out.result := by
      dsimp only [op,invokeTrace]
      rw [routed]
    rw [hOp]
    exact hOut
  · change op.steps≤_
    have hSteps : op.steps=route.steps+d.steps+out.steps+4 := by
      dsimp only [op,invokeTrace]
      rw [routed]
    change route.steps≤_ at hRC
    change d.steps≤_ at hEC
    change out.steps≤boxFee f.natDegree ell p q at hOC
    rw [←size_of_monic_words hp hf hO] at hOC
    rw [hSteps,invokeFee]
    omega

#print axioms invoke_history_native
end J6R21Ancestor


