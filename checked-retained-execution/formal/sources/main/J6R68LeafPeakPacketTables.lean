import J6R68LeafPeakClock
import J6R18ChildWriteRun

/-! Literal packet-entry serialization only. This measures the two
tables that the *real* entry program builds, and no full choice list. -/
namespace J6R68.LeafPeak.Packet
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12 J6R18ChildWrite J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem map_result {A B : Type*} (g : A→Meter B) (d : ℕ) (xs : List A) :
    (mapMeter g d xs).result=xs.map (fun x=>(g x).result) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (g a).result::(mapMeter g d as).result=(g a).result::_
    rw [ih]

theorem flatWidth {A B : Type*} (xs : List A) (fmt : A→List B) (w : ℕ)
    (fits : ∀ x∈xs,(fmt x).length=w) :
    (xs.flatMap fmt).length=xs.length*w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,fits x List.mem_cons_self,
      ih (fun y hy=>fits y (List.mem_cons_of_mem _ hy)),List.length_cons,Nat.succ_mul,Nat.add_comm w]

theorem prefix_width {A B : Type*} (xs : List A) (fmt : A→List B) (j : ℕ) :
    ((xs.take j).flatMap fmt).length≤(xs.flatMap fmt).length := by
  have same := congrArg (fun z : List A=>(z.flatMap fmt).length)
    (List.take_append_drop j xs)
  change ((xs.take j++xs.drop j).flatMap fmt).length=(xs.flatMap fmt).length at same
  rw [List.flatMap_append,List.length_append] at same
  exact (Nat.le_add_right _ _).trans_eq same

def termBits {p ell : ℕ} {fw : List (A1R10.Word p)} (T : Term fw ell) : List Bool :=
  T.code++leafPayload T.value

def tableBits {p ell : ℕ} {fw : List (A1R10.Word p)}
    (tab : List (List (Term fw ell))) : List Bool :=
  tab.flatMap (fun row=>row.flatMap termBits)

def checkBits (check : List Bool×List Bool) : List Bool :=
  check.1++check.2

theorem term_width {p ell : ℕ} {fw : List (A1R10.Word p)}
    (T : Term fw ell) (b : ℕ) (fit : T.code.length=b) :
    (termBits T).length=b+ell*(fw.length*p) := by
  rw [termBits,List.length_append,leaf_payload_width,fit]

theorem actual_affine_row_count_and_codes
    {p ell a q : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p) (he : 0<fw.length) (hEll : 0<ell)
    (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ) (cs : List (SlotBit a))
    (ms : List (ModeInput a p i q)) (codes : ∀ m∈ms,m.code.length=b) (x : SlotBit a) :
    let R := (affineRowWords hp he hEll z t i b cs ms x).result
    R.length=ms.length+1 ∧ ∀ u∈R,u.code.length=b := by
  let first : Term fw ell :=
    ⟨encodeBits b 0,(baseFactor hp he hEll x.assigned (localSum hp he hEll z t x cs)).result⟩
  let tail := mapMeter (variableTerm hp he hEll z t i x) (uvWidth fw.length ell p+b) ms
  change (first::tail.result).length=ms.length+1 ∧ ∀ u∈first::tail.result,u.code.length=b
  have paired : tail.result=ms.map (fun m=>(variableTerm hp he hEll z t i x m).result) :=
    map_result _ _ _
  rw [paired]
  constructor
  · rw [List.length_cons,List.length_map]
  · intro u h
    rcases List.mem_cons.mp h with eq | found
    · rw [eq]
      exact encodeBits_length _ _
    · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp found
      exact codes m hm

theorem actual_packet_has_only_its_affine_table
    {p ell a q : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p) (he : 0<fw.length) (hEll : 0<ell)
    (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ) (rs cs : List (SlotBit a))
    (ms : List (ModeInput a p i q)) (codes : ∀ m∈ms,m.code.length=b) :
    let tab := (packRows hp he hEll z t i b rs cs ms).result
    tab.length=rs.length ∧
    (∀ row∈tab,row.length=ms.length+1 ∧ ∀ v∈row,v.code.length=b) ∧
    (tableBits tab).length=rs.length*((ms.length+1)*(b+ell*(fw.length*p))) := by
  let tab := (packRows hp he hEll z t i b rs cs ms).result
  have equal : tab=rs.map (fun x=>(affineRowWords hp he hEll z t i b cs ms x).result) :=
    map_result _ _ _
  have length : tab.length=rs.length := by rw [equal,List.length_map]
  have rows : ∀ row∈tab,row.length=ms.length+1 ∧ ∀ v∈row,v.code.length=b := by
    intro r hr
    rw [equal] at hr
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
    exact actual_affine_row_count_and_codes hp he hEll z t i b cs ms codes x
  refine ⟨length,rows,?_⟩
  unfold tableBits
  rw [flatWidth tab _ ((ms.length+1)*(b+ell*(fw.length*p))) ?_,length]
  intro row h
  obtain ⟨len,width⟩ := rows row h
  rw [flatWidth row termBits (b+ell*(fw.length*p)) (fun x hx=>term_width x b (width x hx)),len]

theorem actual_packet_has_only_its_mode_tests
    {a p q : ℕ} {i : Fin a} (b : ℕ) (ms : List (ModeInput a p i q))
    (codes : ∀ m∈ms,m.code.length=b) :
    let C := (prepareChecks b ms).result
    C.length=ms.length ∧ (∀ v∈C,v.1.length=b ∧ v.2.length=q) ∧
      (C.flatMap checkBits).length=ms.length*(b+q) := by
  let C := (prepareChecks b ms).result
  have equal : C=ms.map prepareCheck := map_result _ _ _
  have len : C.length=ms.length := by rw [equal,List.length_map]
  have bits : ∀ v∈C,v.1.length=b ∧ v.2.length=q := by
    intro v hv
    rw [equal] at hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    refine ⟨codes u hu,?_⟩
    change (if u.targeted then u.beta.bits else encodeBits q 0).length=q
    split
    · exact u.beta.size
    · exact encodeBits_length _ _
  refine ⟨len,bits,?_⟩
  rw [flatWidth C checkBits (b+q) ?_,len]
  intro y hy
  simp only [checkBits,List.length_append,(bits y hy).1,(bits y hy).2]

#print axioms actual_affine_row_count_and_codes
#print axioms actual_packet_has_only_its_affine_table
#print axioms actual_packet_has_only_its_mode_tests
end J6R68.LeafPeak.Packet
