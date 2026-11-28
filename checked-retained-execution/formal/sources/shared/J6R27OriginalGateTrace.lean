
import J6R21AncestorHistory
import J6R21AncestorDirectory

/-! Track physical addresses, not numeric coefficients, through the
actual retaining network. Edge identifiers of children are derived
from the two independent parent half-ports. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R10Repack J6R11Blueprint

theorem word_bits_inj {w : ℕ} : Function.Injective (@Word.bits w) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ (h : x=y)
  subst y
  rfl

def withSide {w : ℕ} (sideBit : Bool) (addr : Word w) : Word (w+1) :=
  ⟨sideBit::addr.bits,by simp only [List.length_cons,addr.size]⟩

def halfKey {E : Type*} {w : ℕ} (code : E→Word w) (p : Port E) : Word (w+1) :=
  withSide (side p) (code (edge p))

theorem half_key_inj {E : Type*} {w : ℕ} {code : E→Word w}
    (h : Function.Injective code) : Function.Injective (halfKey code) := by
  rintro (x|x) (y|y) e
  all_goals have bits := congrArg Word.bits e
  all_goals simp only [halfKey,withSide,side,edge,Sum.elim_inl,Sum.elim_inr,List.cons.injEq,
    id_eq,Bool.false_eq_true,Bool.true_eq_false,false_and,true_and] at bits
  · exact congrArg Sum.inl (h (word_bits_inj bits))
  · exact congrArg Sum.inr (h (word_bits_inj bits))

variable {f : ℤ[X]} {ell w : ℕ} {root : Point f ell}

noncomputable def traceCodes (code : root.host.Edge→Word w) :
    {cur : Point f ell} → (tr : Trace root cur) → cur.host.Edge→Word (w+tr.depth)
  | _,.start => code
  | _,.keep prv _ => fun p=>halfKey (traceCodes code prv) p.val

theorem trace_codes_injective {code : root.host.Edge→Word w} (hc : Function.Injective code)
    {cur : Point f ell} (tr : Trace root cur) : Function.Injective (traceCodes code tr) := by
  induction tr with
  | start => exact hc
  | keep prv mv ih =>
    intro p q h
    exact Subtype.ext (half_key_inj ih h)

theorem trace_keys_are_literal (code : root.host.Edge→Word w)
    {cur : Point f ell} (tr : Trace root cur) (p : PortAt cur) :
    (halfKey (traceCodes code tr) p.val).bits =
      tr.literal (fun q=>(halfKey code q.val).bits) p := by
  induction tr with
  | start => rfl
  | keep prv mv ih =>
    change side p.val :: (halfKey (traceCodes code prv) (edge p.val).val).bits =
      side p.val :: prv.literal (fun q=>(halfKey code q.val).bits) (mv.back p)
    rw [←mv.back_val p,ih]

/-- Every clock cell represents one real retained hop. It is read, not
peeked or replaced by a free index computation. -/
def zeroPadRaw (seed : List Bool) : List Bool → Meter (List Bool)
  | [] => copyBytes seed
  | _::ticks =>
    let z := zeroPadRaw seed ticks
    ⟨false::z.result,z.steps+4⟩

theorem zero_pad_raw_exact (seed ticks : List Bool) :
    zeroPadRaw seed ticks=⟨List.replicate ticks.length false++seed,
      3*seed.length+1+4*ticks.length⟩ := by
  induction ticks with
  | nil => simp only [zeroPadRaw,copyBytes_exact,List.length_nil,List.replicate_zero,
      List.nil_append,Nat.mul_zero,Nat.add_zero]
  | cons t rest ih =>
    rw [zeroPadRaw,ih,List.length_cons,List.replicate_succ,List.cons_append]
    congr 1

def liftRaw (sideBit : Bool) (rootEdge : List Bool) : List Bool→Meter (List Bool)
  | [] => copyBytes rootEdge
  | _::ticks =>
    let z := zeroPadRaw (sideBit::rootEdge) ticks
    ⟨z.result,z.steps+4⟩

theorem lift_raw_exact (sideBit : Bool) (seed ticks : List Bool) :
    (liftRaw sideBit seed ticks).result=(List.replicate ticks.length false++sideBit::seed).drop 1 ∧
    (liftRaw sideBit seed ticks).steps≤3*seed.length+4*ticks.length+4 := by
  cases ticks with
  | nil => simp [liftRaw,copyBytes_exact]
  | cons t rest =>
    simp only [liftRaw,zero_pad_raw_exact,List.length_cons,List.replicate_succ,List.cons_append,
      List.drop_succ_cons,List.drop_zero,true_and]
    omega

theorem lift_raw_width (sideBit : Bool) (seed ticks : List Bool) :
    (liftRaw sideBit seed ticks).result.length=seed.length+ticks.length := by
  rw [(lift_raw_exact _ _ _).1]
  simp only [List.length_drop,List.length_append,List.length_replicate,List.length_cons]
  omega

def liftWord (sideBit : Bool) (seed : Word w) (ticks : List Bool) : Meter (Word (w+ticks.length)) :=
  let v := liftRaw sideBit seed.bits ticks
  ⟨⟨v.result,by rw [lift_raw_width,seed.size]⟩,v.steps⟩

theorem lift_word_steps (sideBit : Bool) (seed : Word w) (ticks : List Bool) :
    (liftWord sideBit seed ticks).steps≤3*w+4*ticks.length+4 := by
  simpa only [liftWord,seed.size] using (lift_raw_exact sideBit seed.bits ticks).2

theorem lift_word_is_traced (code : root.host.Edge→Word w) {cur : Point f ell}
    (tr : Trace root cur) (marks : List Bool) (depth : marks.length=tr.depth) (q : PortAt root) :
    (liftWord (side q.val) (code (edge q.val)) marks).result.bits =
      (traceCodes code tr (edge (tr.back.symm q).val)).bits := by
  change (liftRaw (side q.val) (code (edge q.val)).bits marks).result=_
  rw [(lift_raw_exact _ _ _).1,depth]
  have h := trace_keys_are_literal code tr (tr.back.symm q)
  rw [tr.literal_exact,Equiv.apply_symm_apply] at h
  have h' := congrArg (List.drop 1) h
  change (side (tr.back.symm q).val :: _).drop 1 = _ at h'
  simpa only [List.drop_succ_cons,List.drop_zero] using h'.symm

#print axioms half_key_inj
#print axioms trace_codes_injective
#print axioms trace_keys_are_literal
#print axioms zero_pad_raw_exact
#print axioms lift_raw_exact
#print axioms lift_word_steps
#print axioms lift_word_is_traced
end J6R27OriginalGate


