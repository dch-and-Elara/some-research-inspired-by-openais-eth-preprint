
import J6R27OriginalGateOrdinal
import J6R27OriginalGateTrace
import J6R21AncestorOriginReads

/-! The paid OLD-vertex constructor consumes the original local incidence
records and the genuine current edge roster. Its output positions are
computed even though the correctness proof refers to the abstract trace
inverse. In particular, no numerical array of tracedSlot is provided. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R10Repack J6R21Ancestor J6R21Leaf

def gatherOptions {A B : Type*} (stride : ℕ) (one : A→Meter (Option B)) :
    List A → Meter (Option (List B))
  | [] => ⟨some [],3⟩
  | x::xs =>
    let u := one x
    let v := gatherOptions stride one xs
    ⟨u.result.bind (fun y=>v.result.map (y::·)),u.steps+v.steps+stride+6⟩

theorem gather_options_exact {A B : Type*} (stride : ℕ) (one : A→Meter (Option B))
    (spec : A→B) (xs : List A) (h : ∀ x∈xs,(one x).result=some (spec x)) :
    gatherOptions stride one xs=⟨some (xs.map spec),
      3+(xs.map (fun x=>(one x).steps+stride+6)).sum⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [gatherOptions]
    rw [h x List.mem_cons_self,ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))]
    simp only [Option.bind_some,Option.map_some,List.map_cons,List.sum_cons]
    congr 1
    omega

theorem gather_options_bound {A B : Type*} (stride cap : ℕ) (one : A→Meter (Option B))
    (xs : List A) (h : ∀ x∈xs,(one x).steps≤cap) :
    (gatherOptions stride one xs).steps≤3+xs.length*(cap+stride+6) := by
  induction xs with
  | nil => simp [gatherOptions]
  | cons x xs ih =>
    have a := h x List.mem_cons_self
    have b := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    simp only [gatherOptions,List.length_cons,Nat.add_mul,one_mul]
    omega

structure OriginSeed (w : ℕ) where
  half : Bool
  edgeId : Word w

def seedFrom {f : ℤ[X]} {ell w : ℕ} {root : Point f ell}
    (code : root.host.Edge→Word w) (q : PortAt root) : OriginSeed w :=
  ⟨side q.val,code (edge q.val)⟩

def seekInherited {w : ℕ} (b : ℕ) (marks : List Bool) (rows : List (Word (w+marks.length)))
    (seed : OriginSeed w) : Meter (Option (Word b)) :=
  let q := liftWord seed.half seed.edgeId marks
  let r := findOrdinal b q.result rows
  ⟨r.result,q.steps+r.steps+4⟩

variable {f : ℤ[X]} {ell w n : ℕ} {root cur : Point f ell}

def clockCast (d : ℕ) (marks : List Bool) (hd : marks.length=d) (addr : Word (w+d)) :
    Word (w+marks.length) :=
  ⟨addr.bits,addr.size.trans (congrArg (w+·) hd.symm)⟩

noncomputable def indexedKeys (code : root.host.Edge→Word w) (tr : Trace root cur)
    (ord : Fin n≃cur.host.Edge) (marks : List Bool) (hd : marks.length=tr.depth) :
    Fin n→Word (w+marks.length) :=
  fun j=>clockCast tr.depth marks hd (traceCodes code tr (ord j))

theorem indexed_keys_injective {code : root.host.Edge→Word w} (hc : Function.Injective code)
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (marks : List Bool)
    (hd : marks.length=tr.depth) :
    Function.Injective (indexedKeys code tr ord marks hd) := by
  intro j k h
  have hb := congrArg (@Word.bits (w+marks.length)) h
  change (traceCodes code tr (ord j)).bits=(traceCodes code tr (ord k)).bits at hb
  exact ord.injective (trace_codes_injective hc tr (word_bits_inj hb))

def seekCap (w b d n : ℕ) : ℕ :=
  3*w+4*d+4 + n*missFee (w+d) b+hitFee (w+d) b+b+7

theorem seek_inherited_exact {b : ℕ} (hb : 0<b)
    (code : root.host.Edge→Word w) (hc : Function.Injective code)
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (marks : List Bool)
    (hd : marks.length=tr.depth) (fit : n≤2^b)
    (q : PortAt root)
    (rows : List (Word (w+marks.length)))
    (actual : rows=List.ofFn (indexedKeys code tr ord marks hd)) :
    let out := seekInherited b marks rows (seedFrom code q)
    out.result=some (word (tracedSlot tr ord q).val) ∧ out.steps≤seekCap w b marks.length n := by
  let j := tracedSlot tr ord q
  let S := seedFrom code q
  let v := liftWord S.half S.edgeId marks
  let k := indexedKeys code tr ord marks hd
  have eqKey : v.result=k j := by
    apply word_bits_inj
    change (liftWord (side q.val) (code (edge q.val)) marks).result.bits=
      (traceCodes code tr (ord j)).bits
    rw [show ord j=edge (tr.back.symm q).val from ord.apply_symm_apply _]
    exact lift_word_is_traced code tr marks hd q
  have h := find_ordinal_indexed hb k (indexed_keys_injective hc tr ord marks hd) fit j
  obtain ⟨hv,hs⟩ := congrArg (fun z : Meter (Option (Word b))=>(z.result,z.steps)) h |> Prod.mk.inj
  have hc' := lift_word_steps S.half S.edgeId marks
  have hl := Nat.mul_le_mul_right (missFee (w+marks.length) b) j.isLt.le
  change (findOrdinal b v.result rows).result=some (word j.val) ∧
    v.steps+(findOrdinal b v.result rows).steps+4≤seekCap w b marks.length n
  rw [eqKey,actual,hv,hs]
  refine ⟨rfl,?_⟩
  change v.steps≤3*w+4*marks.length+4 at hc'
  change v.steps+(j.val*missFee (w+marks.length) b+hitFee (w+marks.length) b+b+3)+4≤_
  unfold seekCap
  omega

def compileIncidences {w : ℕ} (b : ℕ) (marks : List Bool) (rows : List (Word (w+marks.length)))
    (src : List (OriginSeed w)) : Meter (Option (List (Word b))) :=
  gatherOptions b (seekInherited b marks rows) src

theorem compile_actual_traced_ordinals {b : ℕ}
    (hb : 0<b) (code : root.host.Edge→Word w) (hc : Function.Injective code)
    (tr : Trace root cur) (ord : Fin n≃cur.host.Edge) (marks : List Bool)
    (hd : marks.length=tr.depth) (fit : n≤2^b) (scope : List (PortAt root))
    (rows : List (Word (w+marks.length)))
    (actual : rows=List.ofFn (indexedKeys code tr ord marks hd)) :
    let out := compileIncidences b marks rows (scope.map (seedFrom code))
    out.result=some (scope.map (fun q=>word (tracedSlot tr ord q).val)) ∧
    out.steps≤3+scope.length*(seekCap w b marks.length n+b+6) := by
  dsimp only
  have h (q : PortAt root) := seek_inherited_exact hb code hc tr ord marks hd fit q rows actual
  have H (q : PortAt root) :
      (seekInherited b marks rows (seedFrom code q)).result=some (word (tracedSlot tr ord q).val) :=
    (h q).1
  have hdC (q : PortAt root) :
      (seekInherited b marks rows (seedFrom code q)).steps≤seekCap w b marks.length n := (h q).2
  constructor
  · unfold compileIncidences
    induction scope with
    | nil => rfl
    | cons q scope ih =>
      rw [List.map_cons,gatherOptions]
      dsimp only
      rw [H q,ih,List.map_cons]
      rfl
  · have C := gather_options_bound b (seekCap w b marks.length n)
      (seekInherited b marks rows) (scope.map (seedFrom code)) (by
        intro row hm
        obtain ⟨q,_,rfl⟩ := List.mem_map.mp hm
        exact hdC q)
    rw [List.length_map] at C
    exact C

#print axioms gather_options_exact
#print axioms gather_options_bound
#print axioms indexed_keys_injective
#print axioms seek_inherited_exact
#print axioms compile_actual_traced_ordinals
end J6R27OriginalGate



