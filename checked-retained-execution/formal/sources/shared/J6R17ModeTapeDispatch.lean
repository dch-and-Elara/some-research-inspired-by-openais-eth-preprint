import J6R17ModeTapeCross
import J6R17ModeTapeTuple

/-! Raw handoff of an emitted exponent vector: advance the very same
mode tape in lockstep, scan every multiplicity word, and serialize only
the positive terms. No semantic lookup of packet locations is charged
as a free operation. This stops before constructing child entries. -/
namespace J6R17ModeTape
open AOracleMachineTime J6R14LayoutCost J6R15ModeCost

def dispatchStride (a q : ℕ) : ℕ := recordStride a q+8*q+20

def emitSupport {q : ℕ} (a : ℕ) :
    List (RawMode q) → List (Word q) → Meter (Option (List (RawMode q×Word q)))
  | [],[] => ⟨some [],4⟩
  | [],_::_ => ⟨none,4⟩
  | _::_,[] => ⟨none,4⟩
  | m::ms,e::es =>
    let f := nonzero e.bits
    let u := emitSupport a ms es
    let v := u.result.map fun rest=> if f.result then (m,e)::rest else rest
    ⟨v,u.steps+f.steps+recordStride a q+4*q+20⟩

def supportSpec {q : ℕ} (ms : List (RawMode q)) (es : List (Word q)) :
    List (RawMode q×Word q) :=
  (ms.zip es).filter (fun e=>e.2.val != 0)

theorem emitSupport_exact {q : ℕ} (a : ℕ)
    (ms : List (RawMode q)) (es : List (Word q)) (h : ms.length=es.length) :
    let z := emitSupport a ms es
    z.result=some (supportSpec ms es) ∧
    z.steps=ms.length*dispatchStride a q+4 := by
  induction ms generalizing es with
  | nil =>
    cases es with
    | nil => simp [emitSupport,supportSpec]
    | cons e es => simp at h
  | cons m ms ih =>
    cases es with
    | nil => simp at h
    | cons e es =>
      have hL : ms.length=es.length := by simpa only [List.length_cons,Nat.succ.injEq] using h
      obtain ⟨hE,hC⟩ := ih es hL
      let f := nonzero e.bits
      obtain ⟨hf,hfC⟩ := nonzero_exact e.bits
      have hF : f.result=decide (e.val≠0) := Bool.eq_iff_iff.mpr (by
        simpa only [Word.val,decide_eq_true_eq] using hf)
      have hFT : f.steps=4*q := by simpa only [e.size] using hfC
      constructor
      · change ((emitSupport a ms es).result.map (fun rest=>if f.result then (m,e)::rest else rest))=
          some (supportSpec (m::ms) (e::es))
        by_cases hZ : e.val=0 <;> simp [hE,hF,supportSpec,hZ]
      · change (emitSupport a ms es).steps+f.steps+recordStride a q+4*q+20=
          (ms.length+1)*dispatchStride a q+4
        rw [hC,hFT,dispatchStride,Nat.add_mul,one_mul]
        omega

theorem supportSpec_pos {q : ℕ} {ms : List (RawMode q)} {es : List (Word q)} {x : RawMode q×Word q}
    (h : x∈supportSpec ms es) : 0<x.2.val :=
  Nat.pos_of_ne_zero (by simpa using (List.mem_filter.mp h).2)

#print axioms emitSupport_exact
#print axioms supportSpec_pos
end J6R17ModeTape

