import A1R10Budget

/-! Exact sequential readout of the two physical residue indices.
An address is a descending tape offset. The read theorem identifies
the corresponding ascending (U,V) monomial basis index. -/

open scoped Polynomial
namespace A1R10
open AOracleMachineTime AOracleMachineTimeMul AOracleCoordinates Polynomial

variable {A R : Type*} [CommRing R]

def scanWord (g : Gates A) : ℕ → List A → Meter A
  | _,[] => ⟨g.zero,0⟩
  | 0,x::_ => ⟨x,g.move+2⟩
  | n+1,_::xs =>
    let m := scanWord g n xs
    ⟨m.result,m.steps+g.move+2⟩

theorem scanWord_exact (g : Gates A) (v : List A) (n : ℕ) :
    (scanWord g n v).result=v.getD n g.zero ∧
    (scanWord g n v).steps≤v.length*(g.move+2) := by
  induction v generalizing n with
  | nil => cases n <;> simp [scanWord]
  | cons x xs ih =>
    cases n with
    | zero =>
      refine ⟨by simp [scanWord],?_⟩
      change g.move+2≤(xs.length+1)*(g.move+2)
      rw [Nat.succ_mul xs.length]
      omega
    | succ n =>
      obtain ⟨he,hc⟩ := ih n
      refine ⟨by simpa only [scanWord,List.getD_cons_succ] using he,?_⟩
      change (scanWord g n xs).steps+g.move+2≤(xs.length+1)*(g.move+2)
      rw [Nat.succ_mul xs.length]
      omega

theorem decode_coeff_scan (o : Ops A R) (v : List A) (n : ℕ) (hn : n<v.length) :
    (decode o v).coeff (v.length-1-n)=o.read (v.getD n o.zero) := by
  induction v generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [decode,List.length_cons,Nat.add_sub_cancel,Nat.sub_zero,coeff_add,
        coeff_monomial,List.getD_cons_zero]
      rw [decode_coeff_zero o xs _ le_rfl]
      simp
    | succ n =>
      have hu : n<xs.length := by simpa using hn
      simp only [decode,List.length_cons,Nat.add_sub_cancel,coeff_add,List.getD_cons_succ]
      have hn' : xs.length-(n+1) ≠ xs.length := by omega
      rw [coeff_monomial_of_ne _ hn',zero_add,
        show xs.length-(n+1)=xs.length-1-n by omega,ih _ hu]

theorem coord_decode [Nontrivial R] (o : Ops A R)
    (f : R[X]) (hf : f.Monic) (v : List A) (h : v.length≤f.natDegree) (n : ℕ) :
    coord f hf n (AdjoinRoot.mk f (decode o v))=(decode o v).coeff n := by
  have hd : (decode o v).degree < f.degree := by
    rw [degree_eq_natDegree hf.ne_zero,degree_lt_iff_coeff_zero]
    exact fun j hj => decode_coeff_zero o v j (h.trans hj)
  rw [coord_apply,AdjoinRoot.modByMonicHom_mk,(modByMonic_eq_self_iff hf).mpr hd]

def uvScan {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (v : UVBlock f ell) (i j : ℕ) : Meter (Word p) :=
  let vj := scanWord (uGates hp f) j v.val
  let ui := scanWord (wordOps p hp).toGates i vj.result.val
  ⟨ui.result,vj.steps+ui.steps+4⟩

theorem uvScan_cost {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (v : UVBlock f ell) (i j : ℕ) :
    (uvScan hp v i j).steps≤ell*(f.length*p+2)+f.length*(p+2)+4 := by
  let z := scanWord (uGates hp f) j v.val
  have hV := (scanWord_exact (uGates hp f) v.val j).2
  have hU := (scanWord_exact (wordOps p hp).toGates z.result.val i).2
  rw [v.property] at hV
  rw [z.result.property] at hU
  exact Nat.add_le_add_right (Nat.add_le_add hV hU) _

theorem uvScan_native {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (v : UVBlock f ell) (i : Fin f.length) (j : Fin ell)
    (hf : (Modulus p hp f).Monic) (hd : (Modulus p hp f).natDegree=f.length) :
    wordRead (uvScan hp v i.val j.val).result =
      doubleCoord (Modulus p hp f) hf ell
        (⟨f.length-1-i.val,by have := i.isLt; omega⟩,⟨ell-1-j.val,by have := j.isLt; omega⟩)
        (uvRead hp f ell v) := by
  let F := Modulus p hp f
  let G := ((X : (AdjoinRoot F)[X])^ell)
  letI : Fact (1 < (2:ℕ)^p) := ⟨one_lt_pow₀ (by decide) hp.ne'⟩
  haveI : Nontrivial (AdjoinRoot F) := nontrivial_of_ne _ _
    (show (1 : AdjoinRoot F) ≠ 0 by
      have hc := AdjoinRoot.mk_ne_zero_of_natDegree_lt hf
        (show (1 : (Base p)[X]) ≠ 0 from one_ne_zero)
        (show (1 : (Base p)[X]).natDegree < F.natDegree by
          have hF : F.natDegree=f.length := hd
          rw [natDegree_one,hF]
          exact Nat.zero_lt_of_lt i.isLt)
      simpa only [map_one] using hc)
  let a := (scanWord (uGates hp f) j.val v.val).result
  have hV : v.val.length≤G.natDegree := by simp [G,v.property]
  change wordRead (scanWord (wordOps p hp).toGates i.val a.val).result =
    coord F hf (f.length-1-i.val) (coord G (monic_X_pow ell) (ell-1-j.val)
      (AdjoinRoot.mk G (decode (uOps hp f) v.val)))
  rw [coord_decode (uOps hp f) G (monic_X_pow ell) v.val hV]
  have hcv := decode_coeff_scan (uOps hp f) v.val j.val
    (by rw [v.property]; exact j.isLt)
  rw [v.property] at hcv
  rw [hcv]
  have hget : v.val.getD j.val (uOps hp f).zero = a :=
    (scanWord_exact (uGates hp f) v.val j.val).1.symm
  rw [hget]
  change wordRead (scanWord (wordOps p hp).toGates i.val a.val).result =
    coord F hf (f.length-1-i.val) (AdjoinRoot.mk F (decode (wordOps p hp) a.val))
  rw [coord_decode (wordOps p hp) F hf a.val (by rw [a.property,hd])]
  have hcu := decode_coeff_scan (wordOps p hp) a.val i.val
    (by rw [a.property]; exact i.isLt)
  rw [a.property] at hcu
  rw [hcu,← (scanWord_exact (wordOps p hp).toGates a.val i.val).1]
  rfl

#print axioms scanWord_exact
#print axioms decode_coeff_scan
#print axioms uvScan_cost
#print axioms uvScan_native
end A1R10

