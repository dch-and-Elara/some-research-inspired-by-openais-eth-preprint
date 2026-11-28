import J6R20AncestorWiring

/-! At one actual retention, the two local tapes are matched by
ancestor site slot+side. A descendant's bit is read by a boolean
search. No supplied new-to-old permutation or ring entry is used. -/
namespace J6R20Ancestor
open AOracleMachineTime A1R12 J6R15ModeCost
open J6R18ChildWrite J6R10Repack P11FullPacking J6R9PacketScopes

theorem fillSlots_chart {D : Type*} {a : ℕ} (s : Bool) (xs : List (Key a×Bool))
    (slots : List D) (addr : D→Word a) (val : D→Bool)
    (h : ∀ w∈slots,(⟨s,addr w⟩,val w)∈xs ∧ ∀ z,(⟨s,addr w⟩,z)∈xs→z=val w) :
    (fillSlots s xs (slots.map addr)).result=slots.map (fun w=>⟨addr w,val w⟩) ∧
      (fillSlots s xs (slots.map addr)).steps≤slotFee a xs.length slots.length := by
  let fn (w : Word a) : Meter (SlotBit a) :=
    let z := findBit ⟨s,w⟩ xs; ⟨⟨w,z.result⟩,z.steps⟩
  obtain ⟨hr,hc⟩ := mapMeter_exact fn (a+1) (findFee a xs.length) (slots.map addr) (fun w _=>findBit_cost _ _)
  constructor
  · unfold fillSlots
    change (mapMeter fn (a+1) (slots.map addr)).result=_
    rw [hr,List.map_map]
    apply List.map_congr_left
    intro j hj
    obtain ⟨ht,hu⟩ := h j hj
    change SlotBit.mk (addr j) (findBit ⟨s,addr j⟩ xs).result=SlotBit.mk (addr j) (val j)
    rw [findBit_correct _ _ _ ht hu]
  · change (mapMeter fn (a+1) (slots.map addr)).steps≤_
    rw [List.length_map] at hc
    unfold slotFee
    exact hc.trans (Nat.mul_le_mul_left _ (by omega))

variable {E A B G : Type} [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

abbrev GroupMap (P : PhysicalPacking N a G) (i : Fin a) (g : G) (H : Type) :=
  (Old (atGroup P i) g ⊕ Page a P.copies G) → H

abbrev PacketMap (P : PhysicalPacking N a G) (i : Fin a) (g : G) (K : Type) :=
  ChildEdge N (atGroup P i) g → K

def keptVertex {H : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (k : Page a P.copies G) (stay : grp (.inr k)=h) : Old grp h :=
  ⟨.inr k,stay⟩

abbrev HopPorts {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h) :=
  ParentPorts (child (OriginNet P i g) grp pkt h) (.inl (keptVertex grp k stay))

def hop {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h) :
    HopPorts grp pkt k stay ≃ OriginPorts P i g k :=
  oldReindex (OriginNet P i g) grp pkt h (keptVertex grp k stay)

def portPayloads {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (assign : HopPorts grp pkt k stay→Bool) (ports : List (HopPorts grp pkt k stay)) :
    List (Key a×Bool) :=
  ports.map (fun p=>(originKey P i g k (hop grp pkt k stay p),assign p))

theorem payload_hit {H K : Type} {P : PhysicalPacking N a G} {i : Fin a} {g : G}
    {h : H} (grp : GroupMap P i g H) (pkt : PacketMap P i g K)
    (k : Page a P.copies G) (stay : grp (.inr k)=h)
    (assign : HopPorts grp pkt k stay→Bool) (ports : List (HopPorts grp pkt k stay))
    (hall : ∀ c,c∈ports) (e : OriginPorts P i g k) :
    let key := originKey P i g k e
    let b := assign ((hop grp pkt k stay).symm e)
    let xs := portPayloads grp pkt k stay assign ports
    (key,b)∈xs ∧ ∀ z,(key,z)∈xs→z=b := by
  let ρ := hop grp pkt k stay
  constructor
  · apply List.mem_map.mpr
    exact ⟨ρ.symm e,hall _,by simp [ρ]⟩
  · intro z hz
    obtain ⟨c,_,hc⟩ := List.mem_map.mp hz
    have hport : ρ c=e := originKey_inj P i g k (congrArg Prod.fst hc)
    have hc' : c=ρ.symm e := ρ.apply_eq_iff_eq_symm_apply.mp hport
    exact (congrArg Prod.snd hc).symm.trans (congrArg assign hc')

def routePacket {a : ℕ} (rowSlots colSlots : List (Word a)) (raw : List Raw) :
    Meter (List (SlotBit a) × List (SlotBit a)) :=
  let z := readTape a raw
  let r := fillSlots false z.result rowSlots
  let c := fillSlots true z.result colSlots
  ⟨(r.result,c.result),z.steps+r.steps+c.steps+4⟩

def routeFee (a n r c : ℕ) := tapeFee a n+slotFee a n r+slotFee a n c+4

set_option maxHeartbeats 850000 in
theorem route_packet_exact {H K : Type} (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (k : Page a P.copies G) {h : H}
    (grp : GroupMap P i g H) (pkt : PacketMap P i g K) (stay : grp (.inr k)=h)
    (assign : HopPorts grp pkt k stay→Bool) (ports : List (HopPorts grp pkt k stay))
    (hall : ∀ c,c∈ports) (rs : List (RowsOf P i g k)) (cs : List (ColsOf P i g k))
    (raw : List Raw) (ht : raw=(portPayloads grp pkt k stay assign ports).map nested)
    (rowSlots colSlots : List (Word a))
    (hr : rowSlots=rs.map (fun r=>slotWord P r.val))
    (hc : colSlots=cs.map (fun r=>slotWord P r.val)) :
    let v := originState P i g k (assign ∘ (hop grp pkt k stay).symm)
    let z := routePacket rowSlots colSlots raw
    z.result=(rs.map (realRow P i v),cs.map (realCol P i v)) ∧
      z.steps≤routeFee a ports.length rs.length cs.length := by
  let ρ := hop grp pkt k stay
  let b := assign ∘ ρ.symm
  let X := portPayloads grp pkt k stay assign ports
  have hX : X.length=ports.length := List.length_map _
  have hR (r : RowsOf P i g k) :=
    payload_hit grp pkt k stay assign ports hall (rowOriginPort P i r)
  have hC (r : ColsOf P i g k) :=
    payload_hit grp pkt k stay assign ports hall (colOriginPort P i r)
  obtain ⟨hRO,hRC⟩ := fillSlots_chart false X rs (fun r=>slotWord P r.val)
    (fun r=>b (rowOriginPort P i r)) (fun r _=>by simpa only [rowKey] using hR r)
  obtain ⟨hCO,hCC⟩ := fillSlots_chart true X cs (fun r=>slotWord P r.val)
    (fun r=>b (colOriginPort P i r)) (fun r _=>by simpa only [colKey] using hC r)
  have hRO' := hRO.trans (List.map_congr_left (fun r _=>(origin_row_reads P i g k b r).symm))
  have hCO' := hCO.trans (List.map_congr_left (fun r _=>(origin_col_reads P i g k b r).symm))
  change (routePacket rowSlots colSlots raw).result=_ ∧ (routePacket rowSlots colSlots raw).steps≤_
  rw [show raw=X.map nested from ht,hr,hc]
  unfold routePacket
  rw [readTape_exact]
  constructor
  · exact Prod.ext hRO' hCO'
  · rw [hX] at hRC hCC
    change tapeFee a X.length+
      (fillSlots false X (rs.map (fun r=>slotWord P r.val))).steps+
      (fillSlots true X (cs.map (fun r=>slotWord P r.val))).steps+4≤_
    rw [hX,routeFee]
    omega

#print axioms fillSlots_chart
#print axioms payload_hit
#print axioms route_packet_exact
end J6R20Ancestor

