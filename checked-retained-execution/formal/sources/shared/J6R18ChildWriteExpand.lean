import J6R18ChildWriteProfile
import A1R12Combine

/-! Bit-priced DFS of affine rows over the actual double quotient.
At a leaf the explicit counter scan decides whether to keep the
accumulated product. No list of all allocations is materialized. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates AOracleWitness
open A1R9 A1R10 A1R11 A1R12

def zeroUV {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} :
    Meter (UVBlock fw ell) :=
  ⟨uvZero hp fw ell,uvWidth fw.length ell p⟩

def sumUV {A : Type*} {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (g : A→Meter (UVBlock fw ell)) : List A→Meter (UVBlock fw ell)
  | []=>zeroUV hp
  | x::xs=>addM hp (g x) (sumUV hp g xs)

theorem sumUV_exact {A : Type*} {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (g : A→Meter (UVBlock fw ell)) (F : A→Truncated (Modulus p hp fw) ell) (Z : ℕ)
    (xs : List A) (H : ∀ x∈xs,uvRead hp fw ell (g x).result=F x ∧ (g x).steps≤Z) :
    let z := sumUV hp g xs
    uvRead hp fw ell z.result=(xs.map F).sum ∧
      z.steps≤uvWidth fw.length ell p+xs.length*(Z+addCap fw.length ell p hp+2) := by
  induction xs with
  | nil => simp [sumUV,zeroUV,uvZero_read]
  | cons x xs ih =>
    obtain ⟨h₁,h₂⟩ := H x List.mem_cons_self
    obtain ⟨he,hC⟩ := ih (fun y hy=>H y (List.mem_cons_of_mem _ hy))
    refine ⟨by simp only [sumUV,addM_read,h₁,he,List.map_cons,List.sum_cons],?_⟩
    have h := addM_cost hp (g x) (sumUV hp g xs)
    change (addM hp (g x) (sumUV hp g xs)).steps≤_
    change (sumUV hp g xs).steps≤_ at hC
    rw [List.length_cons,Nat.succ_mul]
    omega

theorem sumUV_map {A B : Type*} {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (f : B→Meter (UVBlock fw ell)) (g : A→B) (xs : List A) :
    sumUV hp f (xs.map g)=sumUV hp (fun x=>f (g x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,sumUV,ih]

structure Term {p : ℕ} (fw : List (A1R10.Word p)) (ell : ℕ) where
  code : List Bool
  value : UVBlock fw ell

def termEncode {m p ell : ℕ} {fw : List (A1R10.Word p)} (b : ℕ)
    (x : Fin (m+1)×UVBlock fw ell) : Term fw ell :=
  ⟨encodeBits b x.1.val,x.2⟩

noncomputable def termMeaning {m p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (x : Fin (m+1)×UVBlock fw ell) : Option (Fin m)×Truncated (Modulus p hp fw) ell :=
  (choice x.1,uvRead hp fw ell x.2)

def evalRows {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (b q : ℕ)
    (test : List (List Bool × List Bool)) :
    List (List (Term fw ell)) → List (List Bool) → UVBlock fw ell → Meter (UVBlock fw ell)
  | [],pre,acc =>
    let c := checkModes q pre test
    let w := uvWidth fw.length ell p
    ⟨if c.result then acc else uvZero hp fw ell,c.steps+w+6⟩
  | row::rs,pre,acc =>
    sumUV hp (fun c =>
      let z := uvMul hp acc c.value
      let r := evalRows hp b q test rs (c.code::pre) z.result
      ⟨r.result,r.steps+z.steps+b+2*(uvWidth fw.length ell p)+8⟩) row

def leafFee (e ell p m r b q : ℕ) : ℕ :=
  m*(counterBudget r b q+2)+uvWidth e ell p+6

def choiceFee (e ell p b : ℕ) (hp : 0<p) : ℕ :=
  mulCap e ell p+addCap e ell p hp+b+2*uvWidth e ell p+10

def treeFee (width B leaf extra : ℕ) : ℕ→ℕ
  | 0 => leaf
  | n+1 => width+B*(treeFee width B leaf extra n+extra)

theorem treeFee_pow (width B leaf extra n : ℕ) :
    treeFee width B leaf extra n≤(B+1)^n*(leaf+width+B*extra) := by
  induction n with
  | zero => simp [treeFee]; omega
  | succ n ih =>
    let U := (B+1)^n*(leaf+width+B*extra)
    have hU : leaf+width+B*extra≤U :=
      Nat.le_mul_of_pos_left _ (by positivity)
    calc
      _≤width+B*(U+extra) := Nat.add_le_add_left (Nat.mul_le_mul_left _
        (Nat.add_le_add_right ih _)) _
      _≤U+B*U := by rw [Nat.mul_add]; omega
      _=_ := by unfold U; rw [pow_succ]; ring

theorem counterBudget_mono (b q : ℕ) {r R : ℕ} (h : r≤R) :
    counterBudget r b q≤counterBudget R b q := by
  unfold counterBudget
  gcongr

theorem evalRows_exact {m p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (b q : ℕ) (hq : 0<q) (hF : m+1≤2^b) (β : Fin m→₀ℕ) (hβ : ∀ i,β i<2^q)
    (R B : ℕ) (hR : R<2^q) (rows : List (List (Fin (m+1)×UVBlock fw ell)))
    (hB : ∀ row∈rows,row.length≤B) (pre : List (Fin (m+1)))
    (hs : pre.length+rows.length≤R) (acc : UVBlock fw ell) :
    let out := evalRows hp b q (counterTape b q β (List.finRange m))
      (rows.map (List.map (termEncode b))) (rawChoices b pre) acc
    uvRead hp fw ell out.result =
      expansion β (rows.map (List.map (termMeaning hp))) (pre.map choice) (uvRead hp fw ell acc) ∧
    out.steps≤treeFee (uvWidth fw.length ell p) B (leafFee fw.length ell p m R b q)
      (choiceFee fw.length ell p b hp) rows.length := by
  induction rows generalizing pre acc with
  | nil =>
    let C := checkModes q (rawChoices b pre) (counterTape b q β (List.finRange m))
    have hpre : pre.length≤R := by simpa using hs
    obtain ⟨h,hT⟩ := check_profile_exact b q hq hF pre (hpre.trans_lt hR) β hβ
    have hU := hT.trans (Nat.mul_le_mul_left m (Nat.add_le_add_right (counterBudget_mono b q hpre) 2))
    constructor
    · change uvRead hp fw ell (if C.result then acc else uvZero hp fw ell)=
        expansion β [] (pre.map choice) (uvRead hp fw ell acc)
      change (C.result=true ↔ _) at h
      by_cases he : exponents (pre.map choice)=β
      · rw [if_pos (h.mpr he),expansion,if_pos he]
      · have hf : ¬ C.result=true := fun e=>he (h.mp e)
        rw [if_neg hf,expansion,if_neg he,uvZero_read]
    · exact Nat.add_le_add_right (Nat.add_le_add_right hU _) _
  | cons row rs ih =>
    let Wx := uvWidth fw.length ell p
    let Cs := treeFee Wx B (leafFee fw.length ell p m R b q) (choiceFee fw.length ell p b hp) rs.length
    let T := counterTape b q β (List.finRange m)
    let f := fun c : Term fw ell =>
      let z := uvMul hp acc c.value
      let u := evalRows hp b q T (rs.map (List.map (termEncode b))) (c.code::rawChoices b pre) z.result
      (⟨u.result,u.steps+z.steps+b+2*Wx+8⟩ : Meter (UVBlock fw ell))
    let F := fun x : Fin (m+1)×UVBlock fw ell =>
      expansion β (rs.map (List.map (termMeaning hp))) (choice x.1::pre.map choice)
        (uvRead hp fw ell acc*uvRead hp fw ell x.2)
    obtain ⟨hE,hC⟩ := sumUV_exact hp (fun x=>f (termEncode b x)) F
      (Cs+mulCap fw.length ell p+b+2*Wx+8) row (by
        intro c _
        let z := uvMul hp acc c.2
        have hlen : (c.1::pre).length+rs.length≤R := by
          simp only [List.length_cons] at hs ⊢
          omega
        obtain ⟨ha,hT⟩ := ih (fun y hy=>hB y (List.mem_cons_of_mem _ hy)) (c.1::pre) hlen z.result
        have hc := uvMul_native_bit_cost hp acc c.2
        constructor
        · change uvRead hp fw ell (evalRows hp b q T (rs.map (List.map (termEncode b)))
            (rawChoices b (c.1::pre)) z.result).result=F c
          rw [ha,hc.1]
          rfl
        · change (evalRows hp b q T (rs.map (List.map (termEncode b)))
            (rawChoices b (c.1::pre)) z.result).steps+z.steps+b+2*Wx+8≤_
          exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.add_le_add hT hc.2) b) (2*Wx)) 8)
    have hM : sumUV hp f (row.map (termEncode b))=sumUV hp (fun x=>f (termEncode b x)) row :=
      sumUV_map hp f (termEncode b) row
    refine ⟨?_,?_⟩
    · change uvRead hp fw ell (sumUV hp f (row.map (termEncode b))).result=_
      rw [hM,hE]
      simp only [List.map_cons,expansion,List.map_map,F,termMeaning,Function.comp_def]
    · change (sumUV hp f (row.map (termEncode b))).steps≤Wx+B*(Cs+choiceFee fw.length ell p b hp)
      rw [hM]
      refine hC.trans ?_
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul (hB row List.mem_cons_self)
      unfold choiceFee
      omega

#print axioms sumUV_exact
#print axioms treeFee_pow
#print axioms evalRows_exact
end J6R18ChildWrite


