import J6R57PublicRequestCatalogue

/-! The charged sequential lookup returns the exact stored legal
coordinate (not just a Boolean).  Success is equivalent to having a
genuine centre, sample and group in the fixed-chart catalogue. -/
namespace J6R57PublicRequest
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6R54PublicFamily J6R14ZeroMode J6Mesh
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9600000
set_option Elab.async false

section
variable {m n kp tc tj tw edgew : ℕ}
variable (W : Widths m n tc tj tw edgew) (mark : Word kp)

theorem emitted_id_injective :
    Function.Injective (fun x : Coordinate m n=>(emitAt W mark x).result.id) := by
  intro x y same
  let E := (emitAt W mark x).result
  let F := (emitAt W mark y).result
  have h : (issueExterior mark E.wire).result=(issueExterior mark F.wire).result :=
    E.exactID.symm.trans (same.trans F.exactID)
  obtain ⟨t,j,g⟩ := issued_exterior_equal_address h
  obtain ⟨_,xt,xj,xg,_,_⟩ := actual_entry_wires W mark x
  obtain ⟨_,yt,yj,yg,_,_⟩ := actual_entry_wires W mark y
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      have tv := xt.symm.trans ((congrArg Word.val t).trans yt)
      unfold index at tv
      omega
    · exact Fin.ext (xj.symm.trans ((congrArg Word.val j).trans yj))
  · exact Fin.ext (xg.symm.trans ((congrArg Word.val g).trans yg))

def readCatalogue (raw : Word (KeyWidth kp tc tj)) (rows : List (Entry mark m n tc tj tw)) :
    Meter (Option (Entry mark m n tc tj tw)) :=
  lookup Entry.id raw rows

theorem catalogue_ids_nodup :
    ((emitCatalogue W mark).result.map Entry.id).Nodup := by
  rw [(catalogue_exact_order_and_bill W mark).1,List.map_map]
  exact (legal_public_order m n).1.map (emitted_id_injective W mark)

theorem unique_catalogue_entry (raw : Word (KeyWidth kp tc tj))
    {a b : Entry mark m n tc tj tw}
    (ha : a∈(emitCatalogue W mark).result) (hb : b∈(emitCatalogue W mark).result)
    (ka : a.id=raw) (kb : b.id=raw) : a=b := by
  rw [(catalogue_exact_order_and_bill W mark).1] at ha hb
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp hb
  have keys := (emitted_id_injective W mark) (ka.trans kb.symm)
  rw [keys]

theorem catalogue_read_iff (raw : Word (KeyWidth kp tc tj)) :
    (readCatalogue mark raw (emitCatalogue W mark).result).result.isSome ↔
      ∃ x : Coordinate m n,(emitAt W mark x).result.id=raw := by
  unfold readCatalogue
  rw [lookup_success_iff,(catalogue_exact_order_and_bill W mark).1]
  constructor
  · rintro ⟨r,h,k⟩
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp h
    exact ⟨x,k⟩
  · rintro ⟨x,k⟩
    refine ⟨(emitAt W mark x).result,List.mem_map.mpr ⟨x,?_,rfl⟩,k⟩
    exact (legal_public_order m n).2.1 x

theorem actual_catalogue_hit (x : Coordinate m n) (raw : Word (KeyWidth kp tc tj))
    (keyExact : (emitAt W mark x).result.id=raw) :
    let D := emitCatalogue W mark
    let R := readCatalogue mark raw D.result
    R.result=some (emitAt W mark x).result ∧
      R.steps≤((m+1)*(literalDegree m n+1)*64)*(10*KeyWidth kp tc tj+9)+2 := by
  let D := emitCatalogue W mark
  let R := readCatalogue mark raw D.result
  have roof := lookup_roof Entry.id raw D.result
  rw [(catalogue_exact_order_and_bill W mark).2.1] at roof
  refine ⟨?_,roof⟩
  have ok : R.result.isSome := (catalogue_read_iff W mark raw).mpr ⟨x,keyExact⟩
  cases hit : R.result with
  | none =>
    rw [hit] at ok
    cases ok
  | some a =>
    have h := lookup_returns_only_written_row Entry.id raw D.result a hit
    rw [unique_catalogue_entry W mark raw h.1 (every_public_address_is_stored W mark x) h.2 keyExact]

def LegalAddress (m n : ℕ) (a : OccurrenceAddress tc tj) : Prop :=
  ∃ x : Coordinate m n,
    a.centre.val=index m x.1.1 ∧ a.sample.val=x.1.2.val ∧ a.group.val=x.2.val

theorem occurrence_address_value_ext {a b : OccurrenceAddress tc tj}
    (t : a.centre.val=b.centre.val) (s : a.sample.val=b.sample.val) (g : a.group.val=b.group.val) :
    a=b := by
  have e {width : ℕ} {x y : Word width} (h : x.val=y.val) : x=y :=
    (valued_word x).symm.trans ((congrArg word h).trans (valued_word y))
  cases a
  cases b
  congr 1 <;> exact e (by assumption)

def rawRequest (mark : Word kp) (raw : OccurrenceAddress tc tj)
    (rows : List (Entry mark m n tc tj tw)) :
    Meter (Option (Entry mark m n tc tj tw)) :=
  let key := issueExterior mark raw
  let answer := readCatalogue mark key.result rows
  ⟨answer.result,key.steps+answer.steps+4⟩

theorem native_raw_request_exact_domain (raw : OccurrenceAddress tc tj) :
    (rawRequest mark raw (emitCatalogue W mark).result).result.isSome ↔ LegalAddress m n raw := by
  change (readCatalogue mark (issueExterior mark raw).result (emitCatalogue W mark).result).result.isSome ↔ _
  rw [catalogue_read_iff W mark]
  constructor
  · rintro ⟨x,k⟩
    let E := (emitAt W mark x).result
    obtain ⟨ht,hj,hg⟩ := issued_exterior_equal_address (E.exactID.symm.trans k)
    obtain ⟨_,t,j,g,_,_⟩ := actual_entry_wires W mark x
    exact ⟨x,(congrArg Word.val ht).symm.trans t,
      (congrArg Word.val hj).symm.trans j,(congrArg Word.val hg).symm.trans g⟩
  · rintro ⟨x,t,j,g⟩
    let E := (emitAt W mark x).result
    obtain ⟨_,ht,hj,hg,_,_⟩ := actual_entry_wires W mark x
    have shape : E.wire=raw :=
      occurrence_address_value_ext (ht.trans t.symm) (hj.trans j.symm) (hg.trans g.symm)
    refine ⟨x,E.exactID.trans ?_⟩
    rw [shape]

theorem native_raw_request_hit (raw : OccurrenceAddress tc tj) (x : Coordinate m n)
    (t : raw.centre.val=index m x.1.1) (j : raw.sample.val=x.1.2.val)
    (g : raw.group.val=x.2.val) :
    let R := rawRequest mark raw (emitCatalogue W mark).result
    R.result=some (emitAt W mark x).result ∧
      R.steps≤6*KeyWidth kp tc tj+16+((m+1)*(literalDegree m n+1)*64)*(10*KeyWidth kp tc tj+9) := by
  let E := (emitAt W mark x).result
  obtain ⟨_,ht,hj,hg,_,_⟩ := actual_entry_wires W mark x
  have shape : E.wire=raw :=
    occurrence_address_value_ext (ht.trans t.symm) (hj.trans j.symm) (hg.trans g.symm)
  have key : E.id=(issueExterior mark raw).result := E.exactID.trans (by rw [shape])
  have h := actual_catalogue_hit W mark x (issueExterior mark raw).result key
  refine ⟨h.1,?_⟩
  have fee := h.2
  change (issueExterior mark raw).steps+
    (readCatalogue mark (issueExterior mark raw).result (emitCatalogue W mark).result).steps+4≤_
  rw [(issued_exterior_exact mark raw).2]
  omega
end

#print axioms emitted_id_injective
#print axioms catalogue_ids_nodup
#print axioms unique_catalogue_entry
#print axioms catalogue_read_iff
#print axioms actual_catalogue_hit
#print axioms native_raw_request_exact_domain
#print axioms native_raw_request_hit
end J6R57PublicRequest
