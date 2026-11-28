import J6R22ActiveUnit

/-! Pack a physically supplied binary probe's raw coordinates into
the same descending U-coefficient / V-constant word frame as a
recursive reply. The order/descriptor supplying those coordinates
is external; no conversion of that payload into a numeric input is
left as an oracle. -/
namespace J6R22Active
open scoped Polynomial BigOperators
open Polynomial A1R10 A1R11 AOracleMachineTime
open NativeProbeRing

def fromBit (p : ℕ) (b : Bool) : Word p :=
  if b then wordOne p else wordZero p

theorem fromBit_read (p : ℕ) (hp : 0<p) (b : Bool) :
    wordRead (fromBit p b)=if b then (1:Base p) else 0 := by
  cases b
  · exact (wordOps p hp).zero_read
  · exact wordOne_read p hp

theorem binary_encode (p : ℕ) (hp : 0<p) {e : ℕ} (b : Fin e→Bool) :
    decode (wordOps p hp) ((List.ofFn b).reverse.map (fromBit p))=binaryPoly (Base p) b := by
  induction e with
  | zero => simp [binaryPoly,decode]
  | succ e ih =>
    rw [List.ofFn_succ,List.reverse_cons,List.map_append,decode_append]
    have hlen : ([b 0].map (fromBit p)).length=1 := rfl
    rw [hlen,ih (fun j : Fin e=>b j.succ),pow_one]
    simp only [List.map_cons,List.map_nil,decode,List.length_nil,add_zero]
    change X*binaryPoly (Base p) (fun j : Fin e=>b j.succ)+
      monomial 0 (wordRead (fromBit p (b 0)))=_
    rw [fromBit_read p hp,add_comm]
    unfold binaryPoly
    rw [Fin.sum_univ_succ (fun i : Fin (e+1)=>monomial i.val (if b i then (1:Base p) else 0)),Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [X_mul_monomial]
    rfl

def encodeProbe (hp : 0<p) {fw : List (Word p)} {ell : ℕ}
    (hv : 0<ell) (coord : {b : List Bool//b.length=fw.length}) :
    Meter (UVBlock fw ell) :=
  let u : UBlock fw := ⟨coord.val.reverse.map (fromBit p),by simp [coord.property]⟩
  let v := constantTape (uGates hp fw) ell u
  ⟨⟨v,constantTape_len _ _ hv _⟩,
    coord.val.length*(p+6)+uvWidth fw.length ell p+2⟩

theorem encodeProbe_cost (hp : 0<p) {fw : List (Word p)} {ell : ℕ}
    (hv : 0<ell) (coord : {b : List Bool//b.length=fw.length}) :
    (encodeProbe hp hv coord).steps=fw.length*(p+6)+uvWidth fw.length ell p+2 := by
  simp only [encodeProbe,coord.property]

theorem boxTransport_scalar {p ell : ℕ} {F G : (Base p)[X]} (h : F=G)
    (P : (Base p)[X]) :
    boxTransport h (AdjoinRoot.of ((X : (AdjoinRoot F)[X])^ell) (AdjoinRoot.mk F P))=
      AdjoinRoot.of ((X : (AdjoinRoot G)[X])^ell) (AdjoinRoot.mk G P) := by
  subst G
  rfl

theorem encodeProbe_is_literal {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    (hv : 0<ell) {f : ℤ[X]}
    (hF : Modulus p hp fw=liftPoly p f) (coord : {b : List Bool//b.length=fw.length})
    (b : Fin f.natDegree→Bool) (read : coord.val=List.ofFn b) :
    boxTransport hF (uvRead hp fw ell (encodeProbe hp hv coord).result)=
      J6ActiveInterpolation.scalarIn p f ell (probe p f b) := by
  let u : UBlock fw := ⟨coord.val.reverse.map (fromBit p),by simp [coord.property]⟩
  have h : u.val=((List.ofFn b).reverse.map (fromBit p)) := by simp only [u,read]
  change boxTransport hF (AdjoinRoot.mk _ (decode (uOps hp fw)
    (constantTape (uOps hp fw).toGates ell u)))=_
  rw [constantTape_read]
  change boxTransport hF (AdjoinRoot.of _ (AdjoinRoot.mk _ (decode (wordOps p hp) u.val)))=_
  rw [h,binary_encode,boxTransport_scalar]
  rfl

#print axioms binary_encode
#print axioms encodeProbe_cost
#print axioms encodeProbe_is_literal
end J6R22Active





