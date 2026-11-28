import J6R21AncestorDirectory
import J6R21AncestorRoute

/-! Local input preparation for a REQUEST, not preparation of the
whole graph. A stored port record gives a unary scan lane to the present
leaf edge position, plus the inherited literal address. All reads and
copies for this request are charged, with no random-access bit oracle. -/
namespace J6R21Ancestor
open scoped Polynomial
open AOracleMachineTime A1R12 J6R20Ancestor J6R10Repack

def readSkip : List Bool → List Bool → Meter Bool
  | [],[] => ⟨false,2⟩
  | [],x::_ => ⟨x,2⟩
  | _::_,[] => ⟨false,2⟩
  | _::n,_::xs =>
    let z := readSkip n xs
    ⟨z.result,z.steps+4⟩

theorem readSkip_exact (lane xs : List Bool) :
    (readSkip lane xs).result=xs.getD lane.length false ∧
      (readSkip lane xs).steps≤4*lane.length+2 := by
  induction lane generalizing xs with
  | nil => cases xs <;> simp [readSkip]
  | cons u lane ih =>
    cases xs with
    | nil => simp [readSkip]
    | cons x xs =>
      obtain ⟨hr,hc⟩ := ih xs
      refine ⟨hr,?_⟩
      change (readSkip lane xs).steps+4≤4*(lane.length+1)+2
      omega

structure WireRead where
  header : List Bool
  lane : List Bool

def attachBit (xs : List Bool) (p : WireRead) : Meter Raw :=
  let hdr := copyBytes p.header
  let y := readSkip p.lane xs
  ⟨(hdr.result,y.result),hdr.steps+y.steps+4⟩

theorem attachBit_exact (xs : List Bool) (p : WireRead) :
    (attachBit xs p).result=(p.header,xs.getD p.lane.length false) ∧
      (attachBit xs p).steps≤3*p.header.length+4*p.lane.length+7 := by
  obtain ⟨hV,hC⟩ := readSkip_exact p.lane xs
  have hH := copyBytes_exact p.header
  constructor
  · simp only [attachBit,hH,hV]
  · simp only [attachBit,hH]
    omega

def gather (width : ℕ) (which : List WireRead) (xs : List Bool) : Meter (List Raw) :=
  mapMeter (attachBit xs) (width+1) which

def gatherFee (width M n : ℕ) := n*(4*width+4*M+12)

theorem getD_ofFn_exact {n : ℕ} (x : Fin n→Bool) (j : Fin n) :
    (List.ofFn x).getD j.val false=x j := by
  simp [List.getD_eq_getElem?_getD,j.isLt]

theorem gather_ordinals {T : Type*} {n : ℕ}
    (x : Fin n→Bool) (selected : List T) (key : T→List Bool) (ord : T→Fin n)
    (width : ℕ) (hwidth : ∀ p∈selected,(key p).length=width) (wire : List WireRead)
    (hw : wire=selected.map (fun p=>⟨key p,List.replicate (ord p).val true⟩)) :
    (gather width wire (List.ofFn x)).result=selected.map (fun p=>(key p,x (ord p))) ∧
      (gather width wire (List.ofFn x)).steps≤gatherFee width n selected.length := by
  subst wire
  let rows : List WireRead := selected.map (fun p=>⟨key p,List.replicate (ord p).val true⟩)
  have hLen : rows.length=selected.length := List.length_map _
  have hc (w : WireRead) (hm : w∈rows) :
      (attachBit (List.ofFn x) w).steps≤3*width+4*n+7 := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have h := (attachBit_exact (List.ofFn x)
      (⟨key p,List.replicate (ord p).val true⟩ : WireRead)).2
    change _≤3*(key p).length+4*(List.replicate (ord p).val true).length+7 at h
    rw [hwidth p hp,List.length_replicate] at h
    exact h.trans (by have := (ord p).isLt; omega)
  obtain ⟨hP,hC⟩ := mapMeter_exact (attachBit (List.ofFn x)) (width+1) (3*width+4*n+7) rows hc
  constructor
  · change (mapMeter (attachBit (List.ofFn x)) (width+1) rows).result=_
    rw [hP]
    unfold rows
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    change (attachBit (List.ofFn x) ⟨key p,List.replicate (ord p).val true⟩).result=_
    rw [(attachBit_exact _ _).1,List.length_replicate,getD_ofFn_exact]
  · change (mapMeter (attachBit (List.ofFn x)) (width+1) rows).steps≤_
    rw [hLen] at hC
    exact hC.trans (Nat.mul_le_mul_left _ (by omega))

theorem literal_address_width {f : ℤ[X]} {ell a : ℕ} {root cur : Point f ell}
    (tr : Trace root cur) (base : PortAt root→List Bool) (hb : ∀ p,(base p).length=a+2)
    (p : PortAt cur) : (tr.literal base p).length=tr.depth+a+2 := by
  rw [tr.literal_exact,List.length_append,List.length_replicate,hb]
  omega

#print axioms readSkip_exact
#print axioms attachBit_exact
#print axioms getD_ofFn_exact
#print axioms gather_ordinals
#print axioms literal_address_width
end J6R21Ancestor



