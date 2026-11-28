import J6R54PublicFamilySite
import J6R57PublicRequestCore

/-! Actual ordered legal external requests.  The two numeric axes are
the published positive odd centres and the complete prescribed sample
range; the third is the explicit 64-way partition.  Each pair shares
one emitted head.  No per-site recipe or existential Ready is used. -/
namespace J6R57PublicRequest
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6R54PublicFamily J6R14ZeroMode J6Mesh
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 3000
set_option Elab.async false

abbrev HeadIndex (m n : ℕ) := J6Recovery.Addr m × Fin (literalDegree m n+1)
abbrev Coordinate (m n : ℕ) := HeadIndex m n × Fin 64

def orderedHeads (m n : ℕ) : List (HeadIndex m n) :=
  (List.finRange (m+1)).product (List.finRange (literalDegree m n+1))

def orderedCoordinates (m n : ℕ) : List (Coordinate m n) :=
  (orderedHeads m n).product (List.finRange 64)

theorem legal_public_order (m n : ℕ) :
    (orderedCoordinates m n).Nodup ∧
      (∀ x, x∈orderedCoordinates m n) ∧
      (orderedCoordinates m n).length=(m+1)*(literalDegree m n+1)*64 := by
  refine ⟨?_,?_,?_⟩
  · exact List.Nodup.product (List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _))
      (List.nodup_finRange _)
  · rintro ⟨⟨i,j⟩,g⟩
    unfold orderedCoordinates orderedHeads
    exact List.mem_product.mpr ⟨List.mem_product.mpr
      ⟨List.mem_finRange i,List.mem_finRange j⟩,List.mem_finRange g⟩
  · calc
      _ = (orderedHeads m n).length*(List.finRange 64).length :=
        List.length_product (orderedHeads m n) (List.finRange 64)
      _ = _ := by
        have H : (orderedHeads m n).length=(m+1)*(literalDegree m n+1) := by
          calc
            _ = (List.finRange (m+1)).length*(List.finRange (literalDegree m n+1)).length :=
              List.length_product _ _
            _ = _ := by simp only [List.length_finRange]
        rw [H,List.length_finRange]

structure Entry {kp : ℕ} (mark : Word kp) (m n tc tj tw : ℕ) where
  coord : Coordinate m n
  head : ExactHead m n tc tj tw coord.1.1 coord.1.2
  wire : OccurrenceAddress tc tj
  id : Word (KeyWidth kp tc tj)
  exactWire : wire=(realAddress head.data coord.2).result
  exactID : id=(issueExterior mark wire).result

section Generate
variable {m n kp tc tj tw edgew : ℕ}
variable (W : Widths m n tc tj tw edgew) (mark : Word kp)

def emitEntry (ij : HeadIndex m n) (H : ExactHead m n tc tj tw ij.1 ij.2) (g : Fin 64) :
    Meter (Entry mark m n tc tj tw) :=
  let A := realAddress H.data g
  let K := issueExterior mark A.result
  ⟨⟨(ij,g),H,A.result,K.result,rfl,rfl⟩,A.steps+K.steps+4⟩

def emitAt (x : Coordinate m n) : Meter (Entry mark m n tc tj tw) :=
  emitEntry mark x.1 (prepareHead W x.1.1 x.1.2).result x.2

def emitGroupBook (ij : HeadIndex m n) : Meter (List (Entry mark m n tc tj tw)) :=
  let H := prepareHead W ij.1 ij.2
  let L := emitRows (emitEntry mark ij H.result) (List.finRange 64)
  ⟨L.result,H.steps+L.steps+4⟩

def emitCatalogue : Meter (List (Entry mark m n tc tj tw)) :=
  emitBooks (emitGroupBook W mark) (orderedHeads m n)

theorem actual_entry_wires (x : Coordinate m n) :
    let E := (emitAt W mark x).result
    E.coord=x ∧
      E.wire.centre.val=index m x.1.1 ∧ E.wire.sample.val=x.1.2.val ∧
      E.wire.group.val=x.2.val ∧
      E.id=(issueExterior mark E.wire).result ∧
      (emitAt W mark x).steps=ordinalFee 6 x.2.val+6*KeyWidth kp tc tj+17 := by
  let H := (prepareHead W x.1.1 x.1.2).result
  let A := realAddress H.data x.2
  have e := real_address_exact H.data x.2
  refine ⟨rfl, (congrArg Word.val e.1).trans H.centreOK,
    (congrArg Word.val e.2.1).trans H.sampleOK,e.2.2.1,rfl,?_⟩
  change A.steps+(issueExterior mark A.result).steps+4=_
  rw [e.2.2.2,(issued_exterior_exact _ _).2]
  omega

theorem group_book_exact (ij : HeadIndex m n) :
    let L := emitGroupBook W mark ij
    L.result=(List.finRange 64).map (fun g=>(emitAt W mark (ij,g)).result) ∧
      L.result.length=64 ∧
      L.steps=(prepareHead W ij.1 ij.2).steps+6+
        ((List.finRange 64).map fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21).sum := by
  let H := prepareHead W ij.1 ij.2
  let K := emitRows (emitEntry mark ij H.result) (List.finRange 64)
  have h := emitted_rows_exact (emitEntry mark ij H.result) (List.finRange 64)
  refine ⟨h.1,?_,?_⟩
  · change K.result.length=64
    rw [h.1,List.length_map,List.length_finRange]
  · change H.steps+K.steps+4=H.steps+6+_
    have sumEq : ((List.finRange 64).map fun g=>(emitEntry mark ij H.result g).steps+4).sum=
        ((List.finRange 64).map fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21).sum := by
      congr 1
      apply List.map_congr_left
      intro g _
      have fee := (actual_entry_wires W mark (ij,g)).2.2.2.2.2
      change (emitEntry mark ij H.result g).steps=_ at fee
      rw [fee]
    rw [h.2,sumEq]
    omega

theorem catalogue_exact_order_and_bill :
    let L := emitCatalogue W mark
    L.result=(orderedCoordinates m n).map (fun x=>(emitAt W mark x).result) ∧
      L.result.length=(m+1)*(literalDegree m n+1)*64 ∧
      L.steps=2+((orderedHeads m n).map fun ij=>(prepareHead W ij.1 ij.2).steps+203+
        ((List.finRange 64).map fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21).sum).sum := by
  let f := emitGroupBook W mark
  let L := emitCatalogue W mark
  have h := emitted_books_exact f (orderedHeads m n)
  have rows : L.result=(orderedCoordinates m n).map (fun x=>(emitAt W mark x).result) := by
    rw [show L.result=(emitBooks f (orderedHeads m n)).result from rfl,h.1]
    simp only [orderedCoordinates,List.product,List.map_flatMap,List.map_map]
    apply List.flatMap_congr
    intro ij _
    exact (group_book_exact W mark ij).1
  refine ⟨rows,?_,?_⟩
  · rw [rows,List.length_map]
    exact (legal_public_order m n).2.2
  · change (emitBooks f (orderedHeads m n)).steps=_
    have eqmap :
        ((orderedHeads m n).map fun ij=>(f ij).steps+3*(f ij).result.length+5)=
          (orderedHeads m n).map (fun ij=>(prepareHead W ij.1 ij.2).steps+203+
            ((List.finRange 64).map fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21).sum) := by
      apply List.map_congr_left
      intro ij _
      change (emitGroupBook W mark ij).steps+3*(emitGroupBook W mark ij).result.length+5=_
      obtain ⟨_,len,fee⟩ := group_book_exact W mark ij
      rw [len,fee]
      omega
    rw [h.2,eqmap]

theorem every_public_address_is_stored (x : Coordinate m n) :
    (emitAt W mark x).result∈(emitCatalogue W mark).result := by
  rw [(catalogue_exact_order_and_bill W mark).1]
  exact List.mem_map.mpr ⟨x,(legal_public_order m n).2.1 x,rfl⟩
end Generate

#print axioms legal_public_order
#print axioms actual_entry_wires
#print axioms group_book_exact
#print axioms catalogue_exact_order_and_bill
#print axioms every_public_address_is_stored
end J6R57PublicRequest
