import P5EscapeE2Field
import Mathlib.RingTheory.AdjoinRoot

/-! A concrete Boolean gate realization of each field multiply, in a fixed
basis over F2. Its circuit has exactly m^3 public Boolean coefficients from
the multiplication table. Each coefficient is charged as a single fixed
wire constant, not as a black-box field-operation call. -/
namespace Paper5.EscapeE2
open scoped BigOperators Polynomial
open Polynomial Module

abbrev BWord (m : ℕ) := Fin m→Bool
abbrev Bin := ZMod 2

def encode2 : Bool → Bin
  | false => 0
  | true => 1

theorem encode2_inj : Function.Injective encode2 := by decide

noncomputable def bit2Equiv : Bool ≃ Bin :=
  Equiv.ofBijective encode2 ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨encode2_inj,by simp⟩)

theorem two_encode_eq (a : Bin) : encode2 (bit2Equiv.symm a)=a :=
  bit2Equiv.apply_symm_apply _

theorem encode2_and (a b : Bool) : encode2 (a && b)=encode2 a*encode2 b := by
  cases a <;> cases b <;> decide

theorem encode2_xor_add (a b : Bool) : encode2 (a != b)=encode2 a+encode2 b := by
  cases a <;> cases b <;> decide

theorem encode2_xor_sub (a b : Bool) : encode2 (a != b)=encode2 a-encode2 b := by
  cases a <;> cases b <;> decide

def gateCoord {m : ℕ} (a b : BWord m) (c : Fin m→Fin m→Bool) :
    List (Fin m×Fin m)→Bool×ℕ
  | [] => (false,0)
  | i::is =>
    let r := gateCoord a b c is
    (r.1 != ((a i.1 && b i.2) && c i.1 i.2),r.2+3)

theorem gate_coord_eval {m : ℕ} (a b : BWord m) (c : Fin m→Fin m→Bool)
    (l : List (Fin m×Fin m)) :
    encode2 (gateCoord a b c l).1=(l.map (fun i=>encode2 (a i.1)*encode2 (b i.2)*encode2 (c i.1 i.2))).sum ∧
      (gateCoord a b c l).2=3*l.length := by
  induction l with
  | nil => simp [gateCoord,encode2]
  | cons i l ih =>
    simp only [gateCoord,encode2_xor_add,encode2_and,List.map_cons,List.sum_cons,ih.1,
      ih.2,List.length_cons,Nat.mul_succ]
    exact ⟨add_comm _ _,True.intro⟩

noncomputable def gateMul {m : ℕ} (c : Fin m→Fin m→Fin m→Bool) (a b : BWord m) :
    BWord m×ℕ :=
  let l := (Finset.univ : Finset (Fin m×Fin m)).toList
  (fun k=>(gateCoord a b (c k) l).1,∑ k : Fin m,(gateCoord a b (c k) l).2)

theorem gate_mul_coeff {m : ℕ} (c : Fin m→Fin m→Fin m→Bool) (a b : BWord m)
    (k : Fin m) :
    encode2 ((gateMul c a b).1 k)=∑ i : Fin m, ∑ j : Fin m,
      encode2 (a i)*encode2 (b j)*encode2 (c k i j) := by
  unfold gateMul
  rw [(gate_coord_eval a b (c k) _).1,Finset.sum_map_toList]
  exact Fintype.sum_prod_type _

theorem gate_mul_count {m : ℕ} (c : Fin m→Fin m→Fin m→Bool) (a b : BWord m) :
    (gateMul c a b).2=3*m^3 := by
  unfold gateMul
  simp only [(gate_coord_eval a b (c _) _).2,Finset.length_toList,Finset.card_univ,
    Fintype.card_prod,Fintype.card_fin,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
  ring

section Basis
variable {K : Type*} [Field K] [Algebra Bin K] {m : ℕ}

noncomputable def fieldTape (b : Basis (Fin m) Bin K) : BWord m ≃ K :=
  (Equiv.piCongrRight fun _=>bit2Equiv).trans b.equivFun.symm.toEquiv

theorem field_tape_value (b : Basis (Fin m) Bin K) (a : BWord m) :
    fieldTape b a=∑ i : Fin m,encode2 (a i) • b i := by
  change b.equivFun.symm (fun i=>encode2 (a i))=_
  exact b.equivFun_symm_apply _

noncomputable def fieldTable (b : Basis (Fin m) Bin K) :
    Fin m→Fin m→Fin m→Bool :=
  fun k i j => bit2Equiv.symm (b.equivFun (b i*b j) k)

theorem field_mul_bits (b : Basis (Fin m) Bin K) (x y : BWord m) :
    fieldTape b (gateMul (fieldTable b) x y).1=fieldTape b x*fieldTape b y := by
  apply b.equivFun.injective
  funext k
  have hL : b.equivFun (fieldTape b (gateMul (fieldTable b) x y).1) k =
      encode2 ((gateMul (fieldTable b) x y).1 k) := by
    change b.equivFun (b.equivFun.symm (fun i=>encode2 ((gateMul (fieldTable b) x y).1 i))) k=_
    rw [LinearEquiv.apply_symm_apply]
  have hg : fieldTape b x*fieldTape b y=∑ i : Fin m,∑ j : Fin m,
      (encode2 (x i)*encode2 (y j)) • (b i*b j) := by
    rw [field_tape_value b x,field_tape_value b y,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [hL,gate_mul_coeff,hg]
  simp only [fieldTable,two_encode_eq,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul]

def bitSub {m : ℕ} (a b : BWord m) : BWord m := fun k=>a k != b k

theorem field_sub_bits (b : Basis (Fin m) Bin K) (x y : BWord m) :
    fieldTape b (bitSub x y)=fieldTape b x-fieldTape b y := by
  simp only [field_tape_value,bitSub, encode2_xor_sub,sub_smul,Finset.sum_sub_distrib]

noncomputable def gatePower (b : Basis (Fin m) Bin K) (seed : BWord m) : ℕ→BWord m×ℕ
  | 0 => ((fieldTape b).symm 1,0)
  | j+1 =>
    let p := gatePower b seed j
    let a := gateMul (fieldTable b) p.1 p.1
    let c := gateMul (fieldTable b) a.1 seed
    (c.1,p.2+a.2+c.2)

theorem gate_power_exact (b : Basis (Fin m) Bin K) (seed : BWord m) (j : ℕ) :
    fieldTape b (gatePower b seed j).1=(mersenneRun (fieldTape b seed) j).1 ∧
      (gatePower b seed j).2=6*m^3*j := by
  induction j with
  | zero => simp [gatePower,mersenneRun]
  | succ j ih =>
    simp only [gatePower,mersenneRun,field_mul_bits,gate_mul_count,ih.1,ih.2]
    exact ⟨True.intro,by ring⟩

noncomputable def gateCached (b : Basis (Fin m) Bin K) (x y : BWord m) : BWord m×ℕ :=
  let s := bitSub x y
  let p := gatePower b s m
  (bitSub ((fieldTape b).symm 1) p.1,p.2+2*m)

theorem gate_cached_exact (b : Basis (Fin m) Bin K) (x y : BWord m) :
    fieldTape b (gateCached b x y).1=(cachedRun m (fieldTape b x) (fieldTape b y)).1 ∧
      (gateCached b x y).2=6*m^4+2*m := by
  simp only [gateCached,field_sub_bits,Equiv.apply_symm_apply,(gate_power_exact b _ _).1,
    (gate_power_exact b _ _).2,cachedRun]
  exact ⟨True.intro,by ring⟩

theorem basis_cached_equivalence (b : Basis (Fin m) Bin K) (hm : 0<m)
    (x y : BWord m) :
    fieldTape b (gateCached b x y).1=(if x=y then 1 else 0) ∧
      (gateCached b x y).2=6*m^4+2*m := by
  classical
  letI : Fintype K := Fintype.ofEquiv (BWord m) (fieldTape b)
  have hc : Fintype.card K=2^m := by
    simpa using (Fintype.card_congr (fieldTape b)).symm
  have h := gate_cached_exact b x y
  rw [cached_run_indicator m hm hc] at h
  have he : fieldTape b x=fieldTape b y ↔ x=y := (fieldTape b).injective.eq_iff
  simpa only [he] using h

noncomputable def bitMachineMatrix (b : Basis (Fin m) Bin K) :
    Matrix (BWord m) (BWord m) K :=
  Matrix.of fun x y=>fieldTape b (gateCached b x y).1

theorem bit_machine_rank_and_cost (b : Basis (Fin m) Bin K) (hm : 0<m) :
    (difference (fieldTape b) (fieldTape b)).rank≤2 ∧ (bitMachineMatrix b).rank=2^m ∧
      ∀ x y : BWord m,(gateCached b x y).2=6*m^4+2*m := by
  classical
  have h : bitMachineMatrix b=1 := by
    ext x y
    rw [bitMachineMatrix,Matrix.of_apply,Matrix.one_apply]
    exact (basis_cached_equivalence b hm x y).1
  refine ⟨difference_rank_le_two _ _,?_,fun x y=>(basis_cached_equivalence b hm x y).2⟩
  rw [h,Matrix.rank_one]
  simp [BWord]

end Basis

/-- In the polynomial basis the fixed bits are exactly the coefficients
of the ordinary monic remainders of the monomials X^{i+j}. -/
theorem monic_table_entry {f : Bin[X]} (hf : f.Monic) [Fact (Irreducible f)]
    (k i j : Fin f.natDegree) :
    encode2 (fieldTable (AdjoinRoot.powerBasisAux' hf) k i j) =
      (X^(i.val+j.val)%ₘf).coeff k := by
  simp only [fieldTable,two_encode_eq,Basis.equivFun_apply]
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  have h (v : Fin f.natDegree) :
      AdjoinRoot.powerBasisAux' hf v = (AdjoinRoot.root f)^v.val :=
    (AdjoinRoot.powerBasis' hf).basis_eq_pow v
  rw [h i,h j,←pow_add]
  rw [←AdjoinRoot.mk_X,←map_pow,AdjoinRoot.modByMonicHom_mk]

#print axioms gate_coord_eval
#print axioms gate_mul_coeff
#print axioms gate_mul_count
#print axioms field_tape_value
#print axioms field_mul_bits
#print axioms field_sub_bits
#print axioms gate_power_exact
#print axioms gate_cached_exact
#print axioms basis_cached_equivalence
#print axioms bit_machine_rank_and_cost
#print axioms monic_table_entry
end Paper5.EscapeE2