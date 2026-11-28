import J6R21AncestorRegistry

/-! Actual fixed-width key and descriptor publication/acquisition.
The data proof is bit-level; for a legal child the per-call receipt
will identify the payload's fields with its genuine physical shape.
No semantic return value is stored in this registry. -/
namespace J6R25PreparedSupply
open AOracleMachineTime J6R15ModeCost J6R21Ancestor

def joinKey {a b : ℕ} (x : Word a) (y : Word b) : Word (a+b) :=
  ⟨x.bits++y.bits,by simp only [List.length_append,x.size,y.size]⟩

theorem join_key_equality {a b : ℕ} {x x' : Word a} {y y' : Word b}
    (e : joinKey x y=joinKey x' y') : x=x' ∧ y=y' := by
  have E := congrArg Word.bits e
  change x.bits++y.bits=x'.bits++y'.bits at E
  have hLen : x.bits.length=x'.bits.length := x.size.trans x'.size.symm
  have ht (v w : List Bool) : (v++w).take v.length=v := by simp
  have hd (v w : List Bool) : (v++w).drop v.length=w := by simp
  have hx : x.bits=x'.bits := by
    have H := congrArg (List.take x.bits.length) E
    rw [ht,hLen,ht] at H
    exact H
  have hy : y.bits=y'.bits := by
    have H := congrArg (List.drop x.bits.length) E
    rw [hd,hLen,hd] at H
    exact H
  exact ⟨by cases x; cases x'; congr,by cases y; cases y'; congr⟩

def preparedKey {a b m : ℕ} (t : Word a) (z : Word b) (u : Word m) (g : Word 6) :
    Meter (Word (a+(b+(m+6)))) :=
  let arg := joinKey t (joinKey z (joinKey u g))
  let cp := copyBytes arg.bits
  ⟨⟨cp.result,by change (copyBytes arg.bits).result.length=_; rw [copyBytes_exact]; exact arg.size⟩,cp.steps+3*(a+(b+(m+6)))+9⟩

theorem prepared_key_exact {a b m : ℕ} (t : Word a) (z : Word b) (u : Word m) (g : Word 6) :
    (preparedKey t z u g).result=joinKey t (joinKey z (joinKey u g)) ∧
    (preparedKey t z u g).steps=6*(a+(b+(m+6)))+10 := by
  let k := joinKey t (joinKey z (joinKey u g))
  refine ⟨?_,?_⟩
  · change Word.mk (copyBytes k.bits).result _=k
    simp only [copyBytes_exact]
  · change (copyBytes k.bits).steps+3*(a+(b+(m+6)))+9=_
    rw [copyBytes_exact]
    simp only [k.size]
    omega

theorem prepared_key_injective {a b m : ℕ} {t t' : Word a} {z z' : Word b} {u u' : Word m}
    {g g' : Word 6} (eq : (preparedKey t z u g).result=(preparedKey t' z' u' g').result) :
    t=t' ∧ z=z' ∧ u=u' ∧ g=g' := by
  rw [(prepared_key_exact _ _ _ _).1,(prepared_key_exact _ _ _ _).1] at eq
  obtain ⟨ht,e⟩ := join_key_equality eq
  obtain ⟨hz,e'⟩ := join_key_equality e
  exact ⟨ht,hz,join_key_equality e'⟩

def childHeaderBytes {p d e : ℕ} (prec : Word p) (depth : Word d) (edges : Word e) (body : List Bool) :=
  prec.bits++depth.bits++edges.bits++body

def writeChildHeader {p d e w : ℕ} (key : Word w)
    (prec : Word p) (depth : Word d) (edges : Word e) (body : List Bool) : Meter (DirRow w) :=
  let write := copyBytes (childHeaderBytes prec depth edges body)
  ⟨⟨key,write.result⟩,write.steps+3*(p+d+e)+2*w+8⟩

theorem child_header_write {p d e w : ℕ} (key : Word w)
    (prec : Word p) (depth : Word d) (edges : Word e) (body : List Bool) :
    let C := writeChildHeader key prec depth edges body
    C.result.id=key ∧ C.result.bytes=childHeaderBytes prec depth edges body ∧
    C.steps=6*(p+d+e)+3*body.length+2*w+9 := by
  refine ⟨rfl,?_,?_⟩
  · change (copyBytes (childHeaderBytes prec depth edges body)).result=_
    rw [copyBytes_exact]
  · change (copyBytes (childHeaderBytes prec depth edges body)).steps+3*(p+d+e)+2*w+8=_
    rw [copyBytes_exact]
    simp only [childHeaderBytes,List.length_append,prec.size,depth.size,edges.size]
    omega

def publishThenAcquire {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w)) :
    Meter (List (DirRow w)×Option (List Bool)) :=
  let staged := addImmutable entry.result bank
  let read := fetch entry.result.id staged.result
  ⟨(staged.result,read.result),entry.steps+staged.steps+read.steps+4⟩

theorem acquired_literal_child {w : ℕ} (entry : Meter (DirRow w)) (bank : List (DirRow w))
    (hf : ∀ x∈bank,x.id≠entry.result.id) :
    let O := publishThenAcquire entry bank
    O.result=(entry.result::bank,some entry.result.bytes) ∧
    O.steps≤entry.steps+fetchFee bank+3*entry.result.bytes.length+2*w+9+
      fetchFee (entry.result::bank)+4 := by
  let D := addImmutable entry.result bank
  let F := fetch entry.result.id D.result
  obtain ⟨hD,hDC⟩ := addImmutable_fresh entry.result bank hf
  have hF : F.result=some entry.result.bytes := by
    unfold F D
    rw [hD]
    apply fetch_hit entry.result.id entry.result.bytes _
    · cases entry.result
      exact List.mem_cons_self
    · intro x hx eq
      rcases List.mem_cons.mp hx with h|h
      · rw [h]
      · exact ((hf _ h) eq).elim
  have hFC : F.steps≤fetchFee (entry.result::bank) := by
    simpa only [F,D,hD] using fetch_bound entry.result.id D.result
  change (D.result,F.result)=(entry.result::bank,some entry.result.bytes) ∧
    entry.steps+D.steps+F.steps+4≤_
  exact ⟨by rw [hD,hF],by change D.steps≤_ at hDC; omega⟩

#print axioms prepared_key_exact
#print axioms prepared_key_injective
#print axioms child_header_write
#print axioms acquired_literal_child
end J6R25PreparedSupply


