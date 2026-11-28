import J6R21AncestorHistory
import J6R21AncestorPrefix

/-! The runtime follows raw inherited port addresses, not a supplied
permutation. Logical backtracking is used only to certify its output
against the original actual packet. -/
namespace J6R21Ancestor
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R10Repack
open J6R18ChildWrite J6R20Ancestor P11FullPacking J6R9PacketScopes

def routeTrace {a : ℕ} (d : ℕ) (rowSlots colSlots : List (Word a)) (raw : List Raw) :
    Meter (List (SlotBit a)×List (SlotBit a)) :=
  let n := normalizeTape a d raw
  let z := routePacket rowSlots colSlots n.result
  ⟨z.result,n.steps+z.steps+4⟩

def traceRouteFee (a d n r c : ℕ) := normalizeFee a d n+routeFee a n r c+4

variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}

def originSeed (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G)
    (p : OriginPorts P i g k) : List Bool :=
  let key := originKey P i g k p
  side p.val::key.side::key.slot.bits

theorem originSeed_right (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (k : Page a P.copies G) (p : OriginPorts P i g k) :
    originSeed P i g k p=true::(originKey P i g k p).side::(originKey P i g k p).slot.bits := by
  rcases p with ⟨p,h⟩
  cases p with
  | inl e => cases h
  | inr e => rfl

theorem traced_payload_hit {D : Type*} (P : PhysicalPacking N a G) (i : Fin a)
    (g : G) (k : Page a P.copies G) (ρ : D≃OriginPorts P i g k) (bits : D→Bool)
    (ports : List D) (hall : ∀ w,w∈ports) (p : OriginPorts P i g k) :
    let X := ports.map (fun y=>(originKey P i g k (ρ y),bits y))
    (originKey P i g k p,bits (ρ.symm p))∈X ∧
      ∀ z,(originKey P i g k p,z)∈X→z=bits (ρ.symm p) := by
  constructor
  · apply List.mem_map.mpr
    exact ⟨ρ.symm p,hall _,by simp⟩
  · intro z hz
    obtain ⟨y,_,hy⟩ := List.mem_map.mp hz
    have he : ρ y=p := originKey_inj P i g k (congrArg Prod.fst hy)
    have hy' : y=ρ.symm p := ρ.apply_eq_iff_eq_symm_apply.mp he
    exact (congrArg Prod.snd hy).symm.trans (congrArg bits hy')

set_option maxHeartbeats 1200000 in
theorem route_trace_exact {f : ℤ[X]} {ell : ℕ} {root cur : Point f ell}
    (tr : Trace root cur) (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G)
    (matchRoot : PortAt root≃OriginPorts P i g k)
    (bits : PortAt cur→Bool) (ports : List (PortAt cur)) (hall : ∀ y,y∈ports)
    (raw : List Raw)
    (hraw : raw=ports.map (fun y=>(tr.literal (originSeed P i g k ∘ matchRoot) y,bits y)))
    (rs : List (RowsOf P i g k)) (cs : List (ColsOf P i g k))
    (rowSlots colSlots : List (Word a))
    (hrows : rowSlots=rs.map (fun r=>slotWord P r.val))
    (hcols : colSlots=cs.map (fun c=>slotWord P c.val)) :
    let ρ := tr.back.trans matchRoot
    let v := originState P i g k (bits ∘ ρ.symm)
    let out := routeTrace tr.depth rowSlots colSlots raw
    out.result=(rs.map (realRow P i v),cs.map (realCol P i v)) ∧
      out.steps≤traceRouteFee a tr.depth ports.length rs.length cs.length := by
  let ρ := tr.back.trans matchRoot
  let b := bits ∘ ρ.symm
  let X := ports.map (fun y=>(originKey P i g k (ρ y),bits y))
  have hX : X.length=ports.length := List.length_map _
  have hrawlen : raw.length=ports.length := by rw [hraw,List.length_map]
  obtain ⟨hNR,hNC⟩ := normalizeTape_exact a tr.depth raw
  have hn : (normalizeTape a tr.depth raw).result=X.map nested := by
    rw [hNR,hraw,List.map_map]
    unfold X
    rw [List.map_map]
    apply List.map_congr_left
    intro y _
    simp only [Function.comp_apply,tr.literal_exact,originSeed_right,normalize_exact,ρ,Equiv.trans_apply]
  have hitR (r : RowsOf P i g k) := traced_payload_hit P i g k ρ bits ports hall (rowOriginPort P i r)
  have hitC (c : ColsOf P i g k) := traced_payload_hit P i g k ρ bits ports hall (colOriginPort P i c)
  obtain ⟨hr,hrC⟩ := fillSlots_chart false X rs (fun r=>slotWord P r.val)
    (fun r=>b (rowOriginPort P i r)) (fun r _=>by simpa only [rowKey] using hitR r)
  obtain ⟨hc,hcC⟩ := fillSlots_chart true X cs (fun c=>slotWord P c.val)
    (fun c=>b (colOriginPort P i c)) (fun c _=>by simpa only [colKey] using hitC c)
  have hr' := hr.trans (List.map_congr_left (fun r _=>(origin_row_reads P i g k b r).symm))
  have hc' := hc.trans (List.map_congr_left (fun c _=>(origin_col_reads P i g k b c).symm))
  dsimp only
  simp only [routeTrace,hn,hrows,hcols,routePacket,readTape_exact]
  constructor
  · exact Prod.ext hr' hc'
  · rw [hX] at hrC hcC
    rw [hrawlen] at hNC
    rw [hX,traceRouteFee,routeFee]
    omega

#print axioms originSeed_right
#print axioms traced_payload_hit
#print axioms route_trace_exact
end J6R21Ancestor

