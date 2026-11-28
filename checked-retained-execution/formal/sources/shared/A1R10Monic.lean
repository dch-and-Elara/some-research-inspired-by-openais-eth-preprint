import A1R10Dense

/-! Monic modulus supplied as its descending lower-coefficient tape,
with a literal implicit leading one. Eliminating a head uses one
scale/subtract per lower modulus coefficient. No division, zero tests
on ring data, or assumption of field characteristic two is used. -/

open scoped Polynomial
namespace A1R10
open AOracleMachineTime Polynomial

variable {A R : Type*} [CommRing R] (o : Ops A R)

noncomputable def modulus (f : List A) : R[X] :=
  monomial f.length 1 + decode o f

theorem modulus_degree [Nontrivial R] (f : List A) :
    (modulus o f).natDegree=f.length ∧ (modulus o f).Monic := by
  have hc : (modulus o f).coeff f.length=1 := by
    simp [modulus,coeff_add,decode_coeff_zero o f]
  have h : (modulus o f).natDegree ≤ f.length := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [modulus,coeff_add,coeff_monomial_of_ne _ (by omega),decode_coeff_zero o f _ hn.le,add_zero]
  have hd := natDegree_eq_of_le_of_coeff_ne_zero h (hc.trans_ne one_ne_zero)
  exact ⟨hd,by simpa only [Monic,leadingCoeff,hd] using hc⟩

/-- Subtract a scaled modulus tail from the matching high prefix.
The rest of the tape is reused as-is. -/
def subtractScaled (o : Gates A) (lead : A) : List A → List A → Meter (List A)
  | [],ys => ⟨ys,0⟩
  | _::_,[] => ⟨[],0⟩
  | f::fs,y::ys =>
    let m := o.mul lead f
    let q := o.sub y m.result
    let tail := subtractScaled o lead fs ys
    ⟨q.result::tail.result,m.steps+q.steps+tail.steps+4*(o.move+1)⟩

theorem subtractScaled_exact (lead : A) (fs ys : List A) (h : fs.length≤ys.length) :
    (subtractScaled o lead fs ys).result.length=ys.length ∧
    decode o (subtractScaled o lead fs ys).result =
      decode o ys - C (o.read lead)*(X^(ys.length-fs.length)*decode o fs) ∧
    (subtractScaled o lead fs ys).steps≤fs.length*(2*o.budget+4*(o.move+1)) := by
  induction fs generalizing ys with
  | nil => simp [subtractScaled,decode]
  | cons f fs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hs : fs.length≤ys.length := by simpa using h
      obtain ⟨hl,hr,hc⟩ := ih ys hs
      refine ⟨by simp only [subtractScaled,List.length_cons,hl],?_,?_⟩
      · simp only [subtractScaled,decode,List.length_cons,hl,hr,o.sub_read,o.mul_read,monomial_sub]
        rw [show ys.length+1-(fs.length+1)=ys.length-fs.length by omega]
        simp only [mul_add,X_pow_mul_monomial,C_mul_monomial,
          show fs.length+(ys.length-fs.length)=ys.length by omega]
        abel
      · change (o.mul lead f).steps+(o.sub y (o.mul lead f).result).steps+
          (subtractScaled o lead fs ys).steps+4*(o.move+1) ≤
            (fs.length+1)*(2*o.budget+4*(o.move+1))
        rw [Nat.succ_mul fs.length]
        have hm := o.mul_cost lead f
        have hb := o.sub_cost y (o.mul lead f).result
        omega

theorem subtract_head_same_class (x : A) (fs ys : List A) (h : fs.length≤ys.length) :
    AdjoinRoot.mk (modulus o fs) (decode o (subtractScaled o x fs ys).result) =
      AdjoinRoot.mk (modulus o fs) (decode o (x::ys)) := by
  have hs := (subtractScaled_exact o x fs ys h).2.1
  have hpoly :
      decode o (subtractScaled o x fs ys).result =
      decode o (x::ys) - C (o.read x)* (X^(ys.length-fs.length)*modulus o fs) := by
    rw [hs,decode,modulus]
    simp only [mul_add,X_pow_mul_monomial,C_mul_monomial,mul_one,
      show fs.length+(ys.length-fs.length)=ys.length by omega]
    abel
  rw [hpoly]
  simp [map_sub,map_mul,AdjoinRoot.mk_self]

/-- Strip exactly n high heads. Each successful recursive call has the
remaining f.length+n cells by the proved width invariant. -/
def reduce (o : Gates A) (fs : List A) : ℕ → List A → Meter (List A)
  | 0,v => ⟨v,0⟩
  | _+1,[] => ⟨[],0⟩
  | n+1,x::xs =>
    let s := subtractScaled o x fs xs
    let t := reduce o fs n s.result
    ⟨t.result,s.steps+t.steps+4*(o.move+1)⟩

theorem reduce_exact (fs : List A) (n : ℕ) (v : List A) (h : v.length=fs.length+n) :
    (reduce o fs n v).result.length=fs.length ∧
    AdjoinRoot.mk (modulus o fs) (decode o (reduce o fs n v).result)=
      AdjoinRoot.mk (modulus o fs) (decode o v) ∧
    (reduce o fs n v).steps≤n*(fs.length+1)*(2*o.budget+4*(o.move+1)) := by
  induction n generalizing v with
  | zero => simpa [reduce] using h
  | succ n ih =>
    cases v with
    | nil => simp only [List.length_nil] at h; omega
    | cons x xs =>
      have hl : xs.length=fs.length+n := by
        simp only [List.length_cons] at h
        omega
      have hf : fs.length≤xs.length := by omega
      let s := subtractScaled o x fs xs
      obtain ⟨hs,_,hc⟩ := subtractScaled_exact o x fs xs hf
      obtain ⟨hr,he,ht⟩ := ih s.result (hs.trans hl)
      refine ⟨hr,he.trans (subtract_head_same_class o x fs xs hf),?_⟩
      change s.steps+(reduce o fs n s.result).steps+4*(o.move+1) ≤ _
      let w := 2*o.budget+4*(o.move+1)
      have hw : fs.length*w+4*(o.move+1)≤(fs.length+1)*w := by
        rw [Nat.succ_mul fs.length]
        dsimp [w]
        omega
      rw [mul_assoc,Nat.succ_mul n]
      calc
        _ ≤ fs.length*w + n*((fs.length+1)*w)+4*(o.move+1) := by
          change s.steps≤fs.length*w at hc
          rw [mul_assoc] at ht
          change (reduce o fs n s.result).steps≤n*((fs.length+1)*w) at ht
          omega
        _ ≤ _ := by change _ ≤ n*((fs.length+1)*w)+(fs.length+1)*w; omega

/-- Product in the actual quotient by the supplied monic polynomial. -/
def uProduct (o : Gates A) (fs : List A) (a b : List A) : Meter (List A) :=
  let c := convolve o a b
  let m := reduce o fs fs.length c.result
  ⟨m.result,c.steps+m.steps⟩

def uBudget (o : Gates A) (e : ℕ) : ℕ := (e+1)*(2*e+1)*lane o+
      e*(e+1)*(2*o.budget+4*(o.move+1))

theorem uProduct_exact (fs a b : List A) (ha : a.length=fs.length) (hb : b.length=fs.length) :
    (uProduct o fs a b).result.length=fs.length ∧
    AdjoinRoot.mk (modulus o fs) (decode o (uProduct o fs a b).result)=
      AdjoinRoot.mk (modulus o fs) (decode o a)*AdjoinRoot.mk (modulus o fs) (decode o b) ∧
    (uProduct o fs a b).steps≤uBudget o.toGates fs.length := by
  let c := convolve o a b
  obtain ⟨hl,hv,hc⟩ := convolve_exact o a b
  have hshape : c.result.length=fs.length+fs.length := hl.trans (by rw [ha,hb])
  obtain ⟨hm,hr,ht⟩ := reduce_exact o fs fs.length c.result hshape
  refine ⟨hm,?_ ,?_⟩
  · change AdjoinRoot.mk _ (decode o (reduce o fs fs.length c.result).result)=_
    rw [hr,hv,map_mul]
  · change c.steps+(reduce o fs fs.length c.result).steps≤_
    rw [ha,hb,← two_mul] at hc
    exact Nat.add_le_add hc ht

#print axioms modulus_degree
#print axioms subtractScaled_exact
#print axioms subtract_head_same_class
#print axioms reduce_exact
#print axioms uProduct_exact
end A1R10



