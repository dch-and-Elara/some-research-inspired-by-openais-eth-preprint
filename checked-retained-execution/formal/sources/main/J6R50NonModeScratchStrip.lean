import J6R50NonModeScratchDense
import J6R23ScheduleWeightStrip
import J6R21LeafWidth

/-! Numeric fields actually present at the high-word extraction stage of
the finite U/V strip. Scope: copied/aliased numeric fields, rather than
step counters, allocator objects, or general tracing instrumentation. -/
namespace J6R50NonModeScratch
open A1R10 AOracleMachineTime J6R21Leaf J6R22Active J6R23ScheduleWeight
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

variable {p B ell : ℕ}
variable {old : List (A1R10.Word (p+B))} {new : List (A1R10.Word p)}

def stripWordFields (x : A1R10.Word (p+B)) : List Bool :=
  x.val ++ x.val.take B ++ x.val.drop B

theorem strip_word_fields_exact (x : A1R10.Word (p+B)) :
    (stripWordFields x).length=2*(p+B) := by
  unfold stripWordFields
  simp only [List.length_append,List.length_take,List.length_drop,x.property]
  omega

theorem high_word_literal_fields (x : A1R10.Word (p+B))
    (h : (x.val.take B).all (fun b=>!b)=true) :
    ∃ out, (highWord p B x).result=some out ∧ out.val=x.val.drop B ∧
      (stripWordFields x).length=x.val.length+(x.val.take B).length+out.val.length := by
  let out : A1R10.Word p := ⟨x.val.drop B,by simp only [List.length_drop,x.property];omega⟩
  refine ⟨out,?_,rfl,?_⟩
  · unfold highWord
    rw [if_pos h]
  · unfold stripWordFields
    simp only [List.length_append,out]

theorem successful_strip_rows (eq : old.length=new.length)
    (x : UVBlock old ell) (y : UVBlock new ell)
    (ok : (stripUVLoop eq x).result=some y) :
    List.Forall₂ (fun v w=>(stripULoop eq v).result=some w) x.val y.val := by
  unfold stripUVLoop at ok
  dsimp only at ok
  split at ok
  · contradiction
  · rename_i ys h
    have same : ys=y.val := congrArg Subtype.val (Option.some.inj ok)
    rw [←same]
    exact (checkedMap_result _ _ _ _).mp h

theorem successful_strip_words (eq : old.length=new.length)
    (x : UBlock old) (y : UBlock new)
    (ok : (stripULoop eq x).result=some y) :
    List.Forall₂ (fun v w=>(highWord p B v).result=some w) x.val y.val := by
  unfold stripULoop at ok
  dsimp only at ok
  split at ok
  · contradiction
  · rename_i ys h
    have same : ys=y.val := congrArg Subtype.val (Option.some.inj ok)
    rw [←same]
    exact (checkedMap_result _ _ _ _).mp h

def rowAt {p' : ℕ} {fw : List (A1R10.Word p')}
    (x : UVBlock fw ell) (i : Fin ell) : UBlock fw :=
  x.val.get ⟨i.val,by simpa only [x.property] using i.isLt⟩

def wordAt (x : UBlock old) (j : Fin old.length) : A1R10.Word (p+B) :=
  x.val.get ⟨j.val,by simpa only [x.property] using j.isLt⟩

def stripPauseFields (x : UVBlock old ell) (y : UVBlock new ell)
    (i : Fin ell) (j : Fin old.length) : List Bool :=
  leafPayload x ++ ((y.val.take i.val).flatMap scalarPayload) ++
    (((rowAt y i).val.take j.val).flatMap Subtype.val) ++ stripWordFields (wordAt (rowAt x i) j)

theorem strip_pause_fields_exact (eq : old.length=new.length)
    (x : UVBlock old ell) (y : UVBlock new ell) (i : Fin ell) (j : Fin old.length) :
    (stripPauseFields x y i j).length=
      ell*(old.length*(p+B))+i.val*(old.length*p)+j.val*p+2*(p+B) := by
  unfold stripPauseFields
  simp only [List.length_append]
  rw [leaf_payload_width,flat_payload_exact scalarPayload (new.length*p) scalar_payload_width,
    flat_payload_exact (fun w : A1R10.Word p=>w.val) p (fun w=>w.property),strip_word_fields_exact]
  simp only [List.length_take,y.property,(rowAt y i).property,min_eq_left i.isLt.le,min_eq_left j.isLt.le,←eq]

/-- In the successful literal strip this actual output-row and
output-word prefix has already been produced under head-before-tail
evaluation. No future values are needed for either prefix observer. -/
theorem real_strip_pause (eq : old.length=new.length)
    (x : UVBlock old ell) (y : UVBlock new ell)
    (ok : (stripUVLoop eq x).result=some y) (i : Fin ell) (j : Fin old.length) :
    (checkedMap (stripULoop eq) (new.length*p) (x.val.take i.val)).result=
      some (y.val.take i.val) ∧
    (checkedMap (highWord p B) p ((rowAt x i).val.take j.val)).result=
      some ((rowAt y i).val.take j.val) ∧
    (stripPauseFields x y i j).length≤
      ell*(old.length*(p+B))+ell*(old.length*p)+old.length*p+2*(p+B) := by
  have rows := successful_strip_rows eq x y ok
  have row : (stripULoop eq (rowAt x i)).result=some (rowAt y i) :=
    rows.get (by simpa only [x.property] using i.isLt) (by simpa only [y.property] using i.isLt)
  have words := successful_strip_words eq _ _ row
  refine ⟨(checkedMap_result _ _ _ _).mpr (List.forall₂_take _ rows),
    (checkedMap_result _ _ _ _).mpr (List.forall₂_take _ words),?_⟩
  rw [strip_pause_fields_exact eq]
  have hi := Nat.mul_le_mul_right (old.length*p) (Nat.le_of_lt i.isLt)
  have hj := Nat.mul_le_mul_right p (Nat.le_of_lt j.isLt)
  omega

#print axioms strip_word_fields_exact
#print axioms high_word_literal_fields
#print axioms successful_strip_rows
#print axioms successful_strip_words
#print axioms strip_pause_fields_exact
#print axioms real_strip_pause
end J6R50NonModeScratch
