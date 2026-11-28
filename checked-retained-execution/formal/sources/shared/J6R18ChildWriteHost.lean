import J6R18ChildWriteMeaning
import J6R10IntegralFinite

/-! The framed bit output is one exact entry of the actual child
host at that host's creation precision. This is an implicit-entry
routine: no full table and no whole recursive answer is emitted. -/
namespace J6R18ChildWrite
open scoped Polynomial BigOperators Classical
open MvPolynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open A1R10 A1R11 A1R12
open J6R11Blueprint J6R10Repack P11FullPacking P1DyadicGrid
open J6R9PacketScopes J6R9PacketChild J6R10RowAffine J6R10RowIdentity J6R10PacketAssembly

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

omit [Fintype A] [Fintype B] in
set_option maxHeartbeats 900000 in
theorem real_packet_word {p ell m q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hEll : 0<ell)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hval : padicValInt 2 t=i.val)
    (z : UVBlock fw ell) (g : G) (k : Page a P.copies G) (v : PhysicalState P i g)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r,r∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c,c∈cs)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q)
    (hMode : ModeMeaning P i g k ξ β ms)
    (b : ℕ) (hq : 0<q) (hb : m+1≤2^b) (hR : rs.length<2^q)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val) :
    let rows := rs.map (realRow P i v)
    let cols := cs.map (realCol P i v)
    let d := packetResult hp he hEll z t i b rows cols (List.ofFn ms)
    let z' := uvRead hp fw ell z
    let hnil := AOracleSuccinctPhysical.double_quotient_two_nilpotent (Modulus p hp fw) ell
    uvRead hp fw ell d.result=actualPacket P i ht0 hval p hnil z' β g k v ∧
      d.steps≤packetFee a fw.length ell p i.val q b rs.length cs.length m hp := by
  let rows := rs.map (realRow P i v)
  let cols := cs.map (realCol P i v)
  let z' := uvRead hp fw ell z
  let hnil := AOracleSuccinctPhysical.double_quotient_two_nilpotent (Modulus p hp fw) ell
  let f := fun r=>(typedRowWords hp he hEll z t i cols ms r).map (termMeaning hp)
  let rowsR := rowsPoly (rows.map f)
  have hRow : rows.length<2^q := by simpa only [rows,List.length_map] using hR
  obtain ⟨hE,hC⟩ := packetResult_exact hp he hEll z t ht i b hq hb rows cols hRow ms hCodes
  refine ⟨?_,by simpa only [rows,cols,List.length_map] using hC⟩
  rw [hE]
  change coeff (requestedProfile ms) rowsR*((List.ofFn ms).map (sourcedValue cols)).prod=_
  have perRow (r : RowsOf P i g k) :
      rename ξ (rowPoly (f (realRow P i v r))) =
        J6RecursiveModes.row (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r.val)
          (groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p hnil z' g v r.val)
          (fun s=>scaledRow P.mask i ht0 hval p hnil z' (P.seat r.val) s) := by
    unfold f
    rw [typedRow_poly hp he hEll z t ht i b cols ms hCodes,realRow_bit,
      localMeaning_physical P i p hnil t z' v r cs hnC haC]
    exact rename_signed_row ξ _ _ _ _ (raw_cross_is_packet P i g k ξ β ms hMode ht ht0 hval hnil z' v r)
  have hRename : rename ξ rowsR =
      ∏ r ∈ actualRows (childBlock P i) g k,
        J6RecursiveModes.row (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r)
          (groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p hnil z' g v r)
          (fun s=>scaledRow P.mask i ht0 hval p hnil z' (P.seat r) s) := by
    let V (r : E) := J6RecursiveModes.row (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r)
          (groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p hnil z' g v r)
          (fun s=>scaledRow P.mask i ht0 hval p hnil z' (P.seat r) s)
    change rename ξ rowsR=∏ r ∈ actualRows (childBlock P i) g k,V r
    unfold rowsR rowsPoly rows
    rw [map_list_prod,List.map_map,List.map_map,List.map_map]
    have h : rs.map (fun r=>rename ξ (rowPoly (f (realRow P i v r))))=rs.map (fun r=>V r.val) :=
      List.map_congr_left (fun r _=>perRow r)
    change (rs.map (fun r=>rename ξ (rowPoly (f (realRow P i v r))))).prod=_
    rw [h,prod_ordered rs hnR haR]
    exact (Finset.prod_subtype (p:=fun r : E=>childBlock P i r=(g,k))
      (F:=(inferInstance : Fintype (RowsOf P i g k))) _ (by simp [actualRows]) V).symm
  unfold actualPacket J6RecursiveModes.packet
  rw [raw_source_is_packet P i g k ξ β ms hMode v cs hnC haC,
    ← hRename,← raw_profile_is_target P i g k ξ β ms hMode]
  have H := coeff_rename_embDomain ξ.toEmbedding rowsR (requestedProfile ms)
  change coeff ((requestedProfile ms).embDomain ξ.toEmbedding) (rename ξ rowsR)=_ at H
  rw [H]

def castBox {p ell : ℕ} {F H : (ZMod (2^p))[X]} (h : F=H) :
    Truncated F ell→Truncated H ell :=
  cast (congrArg (fun f=>Truncated f ell) h)

omit [Fintype A] [Fintype B] in
theorem packet_change_ring {p ell : ℕ} {F H : (ZMod (2^p))[X]} (h : F=H)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (z : Truncated F ell) (β : Mode i p P.mask→₀ℕ) (g : G) (k : Page a P.copies G)
    (v : PhysicalState P i g) :
    castBox h (actualPacket P i ht hv p (AOracleSuccinctPhysical.double_quotient_two_nilpotent F ell) z β g k v)=
      actualPacket P i ht hv p (AOracleSuccinctPhysical.double_quotient_two_nilpotent H ell)
        (castBox h z) β g k v := by
  subst H
  rfl

set_option maxHeartbeats 1000000 in
theorem write_actual_child_entry {p ell m q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    {f : ℤ[X]} (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (he : 0<fw.length) (hEll : 0<ell)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=i.val)
    (z : UVBlock fw ell) (old : EntryFile f ell N) (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ) (ms : Fin m→ModeInput a p i q)
    (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r,r∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c,c∈cs)
    (b : ℕ) (hq : 0<q) (hb : m+1≤2^b) (hR : rs.length<2^q)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (tag : J6R15ModeCost.Word q) (hTag : tag.val=p) :
    let hnil : (2:Residue f ell p)^p=0 := J6R10Integral.box_two_nil p f ell
    let host := actualPacketHost P i ht0 hv p hnil
      (castBox (ell:=ell) hPoly (uvRead hp fw ell z)) old β g
    ∀ bits : ParentPorts host.network (.inr k)→Bool,
      let portBits := bits ∘ (packetReindex N (atGroup P i) (atPacket P) g k).symm
      let v := stateEquiv P i g (fillPacket P i g k portBits)
      let u := packedEntry hp he hEll tag z t i b (rs.map (realRow P i v)) (cs.map (realCol P i v)) (List.ofFn ms)
      ∃ word : UVBlock fw ell,
        frameRead q p fw.length ell u.result=(tag.bits, word.val.map (fun v=>v.val.map Subtype.val)) ∧
        tag.val=(host.file (.inr k)).created ∧
        castBox hPoly (uvRead hp fw ell word)=(host.file (.inr k)).table bits ∧
        u.steps≤packetFee a fw.length ell p i.val q b rs.length cs.length m hp+(4*q+6*ell*(fw.length*p+1)+16)+4 := by
  intro hNil host bits
  let portBits := bits ∘ (packetReindex N (atGroup P i) (atPacket P) g k).symm
  let v := stateEquiv P i g (fillPacket P i g k portBits)
  let ar := rs.map (realRow P i v)
  let ac := cs.map (realCol P i v)
  let d := packetResult hp he hEll z t i b ar ac (List.ofFn ms)
  obtain ⟨hD,hC⟩ := real_packet_word hp he hEll P i ht ht0 hv z g k v rs hnR haR cs hnC haC
    ξ β ms hMode b hq hb hR hCodes
  obtain ⟨_,hFrame,hCost⟩ := write_roundtrip tag d.result
  refine ⟨d.result,hFrame,hTag,?_,?_⟩
  · change castBox hPoly (uvRead hp fw ell d.result)=
      actualPacket P i ht0 hv p (J6R10Integral.box_two_nil p f ell)
        (castBox hPoly (uvRead hp fw ell z)) β g k v
    rw [show uvRead hp fw ell d.result=_ from hD,packet_change_ring]
  · change d.steps+(writeEntry tag d.result).steps+4≤_
    rw [hCost]
    exact Nat.add_le_add_right (Nat.add_le_add_right hC _) _

#print axioms real_packet_word
#print axioms packet_change_ring
#print axioms write_actual_child_entry
end J6R18ChildWrite


