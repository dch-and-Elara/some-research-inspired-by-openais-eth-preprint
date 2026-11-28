import J6R17ModeTapeFlags

/-! The input headers are extracted from the very same R14 packing
receipt, not reconstructed from unrelated labels. The adapter also
charges a linear bypass of attached rows; axes, wires, selector and
key traffic are included in its coarse record tariffs. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape
open J6R14LayoutCost J6R12CollisionPacking J6R12CollisionSource
open J6R11CollisionReindex P11FullPacking J6R12CollisionEdges J6R12CollisionMenu J6R12CollisionGreedyStep

def headerOf (x : ExportBox) : Header :=
  (x.key,x.flags)

def headerTraffic (a : ℕ) : ℕ := 60*a+24

def rowTraffic (kR kC b q a : ℕ) : ℕ := 4*(kR+kC+2*b+3*q+2*a+16)

def drainRows (w : ℕ) : List Seated → Meter Unit
  | [] => ⟨(),0⟩
  | _::rs => ⟨(),(drainRows w rs).steps+w⟩

theorem drainRows_exact (w : ℕ) (rs : List Seated) :
    (drainRows w rs).steps=rs.length*w := by
  induction rs with
  | nil => simp [drainRows]
  | cons r rs ih =>
    simp only [drainRows,ih,List.length_cons,Nat.succ_mul]

def extractHeaders (w a : ℕ) : List ExportBox → Meter (List Header)
  | [] => ⟨[],0⟩
  | x::xs =>
    let d := drainRows w x.rows
    let z := extractHeaders w a xs
    ⟨headerOf x::z.result,d.steps+z.steps+headerTraffic a⟩

def exportRows (xs : List ExportBox) : ℕ := (xs.flatMap ExportBox.rows).length

theorem extractHeaders_exact (w a : ℕ) (xs : List ExportBox) :
    let z := extractHeaders w a xs
    z.result=xs.map headerOf ∧ z.steps=xs.length*headerTraffic a+exportRows xs*w := by
  induction xs with
  | nil => simp [extractHeaders,exportRows]
  | cons x xs ih =>
    let z := extractHeaders w a xs
    refine ⟨?_,?_⟩
    · change headerOf x::z.result=headerOf x::(xs.map headerOf)
      rw [ih.1]
    · change (drainRows w x.rows).steps+z.steps+headerTraffic a=(xs.length+1)*headerTraffic a+
        exportRows (x::xs)*w
      rw [drainRows_exact,ih.2,show exportRows (x::xs)=x.rows.length+exportRows xs by simp [exportRows]]
      ring

theorem headers_lift {a pages q : ℕ} {bs : List (Box Tagged)} {xs : List ExportBox}
    (H : List.Forall₂ (boxFaithful a pages q) bs xs) :
    ∃ cs : List (Cell (Fin a) (Fin 64)), xs.map headerOf=cs.map encodeHeader ∧
      bs.map Box.key=cs.map wordCell ∧ exportRows xs=rowsOnTape bs := by
  induction H with
  | nil => exact ⟨[],rfl,rfl,rfl⟩
  | @cons B x bs xs hx _ ih =>
    obtain ⟨cs,h₁,h₂,h₃⟩ := ih
    obtain ⟨hk,hr,c,hc,_,hf,_⟩ := hx
    refine ⟨c::cs,?_,?_,?_⟩
    · simp only [List.map_cons,h₁]
      rw [show headerOf x=encodeHeader c from by rw [headerOf,encodeHeader,hk,hc,hf]]
    · simp only [List.map_cons,h₂,hc]
    · have ho := congrArg List.length hr
      rw [List.length_map] at ho
      have hX : exportRows (x::xs)=x.rows.length+exportRows xs := by simp [exportRows]
      have hB : rowsOnTape (B::bs)=B.rows.length+rowsOnTape bs := by simp [rowsOnTape]
      rw [hX,hB,h₃,ho]

theorem packed_header_lift {E R C : Type*} [Fintype E] {a pages q : ℕ}
    (F : Format E R C (Fin a→Fin 64)) (hb : F.b=6*a)
    (z : R⊕C→Fin a→Fin 64) {xs : List ExportBox}
    (H : List.Forall₂ (boxFaithful a pages q) (sourceBoxes F z q) xs) :
    ∃ cs : List (Cell (Fin a) (Fin 64)),
      xs.map headerOf=cs.map encodeHeader ∧ cs.Nodup ∧ (∀ c,c∈cs) ∧
      xs.length=2^(6*a)*2^(6*a) ∧ cs.length=xs.length ∧ exportRows xs=Fintype.card E := by
  obtain ⟨cs,h₁,h₂,h₃⟩ := headers_lift H
  have hk : (sourceBoxes F z q).map Box.key=allPairs F.b := by
    simp only [sourceBoxes,List.map_map]
    exact List.map_id _
  rw [hk] at h₂
  have hn : cs.Nodup := List.Nodup.of_map wordCell (h₂ ▸ allPairs_nodup F.b)
  have hAll (c : Cell (Fin a) (Fin 64)) : c∈cs := by
    have he : wordCell c∈allPairs F.b := by
      rw [allPairs_mem]
      exact ⟨(coordinateLabel_len _).trans hb.symm,(coordinateLabel_len _).trans hb.symm⟩
    rw [h₂] at he
    obtain ⟨u,hu,e⟩ := List.mem_map.mp he
    exact wordCell_injective a e ▸ hu
  have hL := congrArg List.length h₁
  rw [List.length_map,List.length_map] at hL
  have hN := congrArg List.length h₂
  rw [allPairs_len,List.length_map,hb] at hN
  exact ⟨cs,h₁,hn,hAll,hL.trans hN.symm,hL.symm,h₃.trans (sourceBoxes_counts F z q).2⟩

#print axioms drainRows_exact
#print axioms extractHeaders_exact
#print axioms headers_lift
#print axioms packed_header_lift
end J6R17ModeTape


