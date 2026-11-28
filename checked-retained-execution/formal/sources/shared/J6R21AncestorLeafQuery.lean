import J6R21AncestorRegistry
import J6R21AncestorGather

/-! The prepared ancestor descriptor is selected by a paid directory
search. The CURRENT full edge-assignment tape is physically scanned
for this vertex's required bits. The selected actual origin program
is run once, and the result is a U/V block for the true leaf multiplier.
No old coefficient is passed in. -/
namespace J6R21Ancestor
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 AOracleCoordinates
open J6R18ChildWrite J6R19Retained J6R10Repack J6R11Blueprint J6R20Ancestor
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild

def leafRequest {p q ell a w aw : ℕ}
    (hp : 0<p) {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (he : 0<old.length) (hEll : 0<ell) (hD : old.length=new.length)
    (t : ℤ) (i : Fin a) (b depth : ℕ) (addr : J6R15ModeCost.Word aw)
    (bank : List (RefRow aw (OriginFields a p ell w old i))) (wires : List WireRead) (x : List Bool) :
    Meter (Option (UVBlock new ell)) :=
  let got := gather (depth+a+2) wires x
  let out := invokeLocated hp he hEll hD t i b depth addr bank got.result
  ⟨out.result,got.steps+out.steps+4⟩

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

set_option maxHeartbeats 1800000 in
theorem actual_generated_leaf_request {f : ℤ[X]} {p q ell m w aw M : ℕ}
    (hf : f.Monic) (heF : 0<f.natDegree) (hp : 0<p) (hq : 0<q)
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (he : 0<old.length) (hEll : 0<ell)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=i.val)
    (z : UVBlock old ell) (oldFile : EntryFile f ell N) (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i w)
    (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r,r∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c,c∈cs)
    (b : ℕ) (hw : 0<w) (hb : m+1≤2^b) (hCount : rs.length<2^w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox hO (uvRead hp old ell z)) oldFile β g k) cur)
    (order : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ x,x∈ports)
    (wires : List WireRead)
    (hWire : wires=ports.map (fun u=>⟨tr.literal (originSeed P i g k) u,
      List.replicate (order.symm (edge u.val)).val true⟩))
    (addr : J6R15ModeCost.Word aw) (bank : List (RefRow aw (OriginFields a p ell w old i)))
    (fields : OriginFields a p ell w old i) (hz : fields.probe=z)
    (hRows : fields.rows=rs.map (fun r=>slotWord P r.val))
    (hCols : fields.cols=cs.map (fun r=>slotWord P r.val))
    (hM : fields.modes=List.ofFn ms)
    (hit : (⟨addr,fields⟩ : RefRow aw (OriginFields a p ell w old i))∈bank)
    (unique : ∀ r∈bank,r.address=addr → r.payload=fields) :
    let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let op := leafRequest hp he hEll hD t i b tr.depth addr bank wires (List.ofFn bits)
    ∃ out, op.result=some out ∧
      castBox hN (uvRead hq new ell out)=(entry cur).read hf q
        (assignment cur.host.network (bits ∘ order.symm) cur.vertex) ∧
      op.steps≤gatherFee (tr.depth+a+2) M ports.length+locateFee aw bank.length+
        invokeFee a old.length ell p q i.val w b tr.depth ports.length rs.length cs.length m hp+8 := by
  let key := tr.literal (originSeed P i g k)
  let ord (u : PortAt cur) := order.symm (edge u.val)
  let d := gather (tr.depth+a+2) wires (List.ofFn bits)
  let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let fwd := invokeTrace hp he hEll hD z t i b tr.depth fields.rows fields.cols (List.ofFn ms) d.result
  have hk (u : PortAt cur) : (key u).length=tr.depth+a+2 := by
    apply literal_address_width tr
    intro v
    simp only [originSeed,List.length_cons,(originKey P i g k v).slot.size]
  obtain ⟨hGate,hCost⟩ := gather_ordinals bits ports key ord _ (fun u _=>hk u) wires hWire
  have rawOk : d.result=ports.map (fun u=>(key u,assignment cur.host.network (bits ∘ order.symm) cur.vertex u)) := hGate
  obtain ⟨hAns,_hTag,hInv⟩ := invoke_history_native hf heF hp hq hO hN he hEll
    P i ht ht0 hv z oldFile g k ξ β ms hMode rs hnR haR cs hnC haC b hw hb hCount hCodes
    tr (assignment cur.host.network (bits ∘ order.symm) cur.vertex) ports hall d.result rawOk fields.rows fields.cols hRows hCols
  obtain ⟨hRead,hReadFee⟩ := invoke_located_exact hp he hEll hD t i b tr.depth addr bank d.result fields hit unique
  change (invokeLocated hp he hEll hD t i b tr.depth addr bank d.result).result=
    some (invokeTrace hp he hEll hD fields.probe t i b tr.depth fields.rows fields.cols fields.modes d.result).result at hRead
  rw [hz,hM] at hRead hReadFee
  refine ⟨fwd.result,hRead,hAns,?_⟩
  change d.steps+(invokeLocated hp he hEll hD t i b tr.depth addr bank d.result).steps+4≤_
  change d.steps≤_ at hCost
  change fwd.steps≤_ at hInv
  change (invokeLocated hp he hEll hD t i b tr.depth addr bank d.result).steps≤locateFee aw bank.length+fwd.steps+4 at hReadFee
  omega

#print axioms actual_generated_leaf_request
end J6R21Ancestor

