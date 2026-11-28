
import J6R22RootReadoutMeshPrep

/-! From the charged, ordered physical load census, evaluate the actual
positive integer normalizer. All powers have an explicit loop count.
The load tape must still be obtained from the actual padding geometry. -/
namespace J6R22RootReadout
open scoped BigOperators Polynomial Classical
open Polynomial P11FullPacking J6Mesh J6RepairedCentered J6NativeHeightMesh
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
open J9R19CompiledBits J6IntegerLayers
set_option maxHeartbeats 14000000
set_option linter.unusedSectionVars false

def padFactorFee (p : ℕ) := 3*(32*(p+1)^2)+22*p+26+4*wordMulFee p

def padFactorWord {p : ℕ} (hp : 0<p) (n d : Word p) (k : Fin 3) : Meter (Word p) :=
  let delta := subWord hp d n
  let l := powerMod d (List.replicate 2 ())
  let r := powerMod d (List.replicate (2-k.val) ())
  let s := powerMod delta.result (List.replicate k.val ())
  let a := mulWord r.result s.result
  let b := addWord l.result a.result
  ⟨b.result,delta.steps+l.steps+r.steps+s.steps+a.steps+b.steps+13*p+14⟩

theorem pad_factor_word_exact {p : ℕ} (hp : 0<p) (nw dw : Word p) (k : Fin 3) (n d : ℤ)
    (hn : wordRead nw=(n:ZMod (2^p))) (hd : wordRead dw=(d:ZMod (2^p))) :
    wordRead (padFactorWord hp nw dw k).result=(pad n d k.val:ZMod (2^p)) ∧
    (padFactorWord hp nw dw k).steps≤padFactorFee p := by
  let δ := subWord hp dw nw
  let l := powerMod dw (List.replicate 2 ())
  let r := powerMod dw (List.replicate (2-k.val) ())
  let s := powerMod δ.result (List.replicate k.val ())
  let a := mulWord r.result s.result
  let b := addWord l.result a.result
  have e0 := power_mod_exact hp dw (List.replicate 2 ())
  have e1 := power_mod_exact hp dw (List.replicate (2-k.val) ())
  have e2 := power_mod_exact hp δ.result (List.replicate k.val ())
  simp only [List.length_replicate] at e0 e1 e2
  have d0 : δ.steps≤32*(p+1)^2 := (wordOps p hp).sub_cost _ _
  have c1 : a.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
  have c2 : b.steps≤32*(p+1)^2 := (wordOps p hp).add_cost _ _
  constructor
  · have e : wordRead (powerMod (subWord hp dw nw).result (List.replicate k.val ())).result =
        (wordRead (subWord hp dw nw).result)^k.val := e2.1
    simp only [padFactorWord,addWord_read,mulWord_read,e0.1,e1.1,e,subWord_read,hn,hd,
      pad,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_sub]
  · have h0 : l.steps≤3*p+4+2*wordMulFee p := e0.2
    have h1 : r.steps≤3*p+4+(2-k.val)*wordMulFee p := e1.2
    have h2 : s.steps≤3*p+4+k.val*wordMulFee p := e2.2
    have kk : k.val≤2 := by omega
    have eq : (2-k.val)*wordMulFee p+k.val*wordMulFee p=2*wordMulFee p := by
      rw [←Nat.add_mul,Nat.sub_add_cancel kk]
    change δ.steps+l.steps+r.steps+s.steps+a.steps+b.steps+13*p+14≤_
    unfold padFactorFee
    omega

def paddingFactorTape {p : ℕ} (hp : 0<p) (n d : Word p) : List (Fin 3)→Meter (Word p)
  | [] => ⟨wordOne p,3*p+4⟩
  | k::ks =>
    let r := padFactorWord hp n d k
    let a := paddingFactorTape hp n d ks
    let x := mulWord r.result a.result
    ⟨x.result,r.steps+a.steps+x.steps+2*p+9⟩

def padTapeFee (p : ℕ) := padFactorFee p+32*(p+1)^2+2*p+9

theorem padding_factor_tape_exact {p : ℕ} (hp : 0<p) (nw dw : Word p)
    (ks : List (Fin 3)) (n d : ℤ)
    (hn : wordRead nw=(n:ZMod (2^p))) (hd : wordRead dw=(d:ZMod (2^p))) :
    wordRead (paddingFactorTape hp nw dw ks).result =
      (((ks.map (fun k=>pad n d k.val)).prod:ℤ):ZMod (2^p)) ∧
    (paddingFactorTape hp nw dw ks).steps≤3*p+4+ks.length*padTapeFee p := by
  induction ks with
  | nil => simp [paddingFactorTape,wordOne_read p hp]
  | cons k ks ih =>
    let a := padFactorWord hp nw dw k
    let b := paddingFactorTape hp nw dw ks
    let q := mulWord a.result b.result
    have h := pad_factor_word_exact hp nw dw k n d hn hd
    constructor
    · simp only [paddingFactorTape,mulWord_read,h.1,ih.1,List.map_cons,List.prod_cons,Int.cast_mul]
    · have w : q.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
      have c : a.steps≤padFactorFee p := h.2
      have t : b.steps≤3*p+4+ks.length*padTapeFee p := ih.2
      change a.steps+b.steps+q.steps+2*p+9≤3*p+4+(ks.length+1)*padTapeFee p
      rw [Nat.add_mul,one_mul]
      unfold padTapeFee at t ⊢
      omega

def computeFactor {p : ℕ} (hp : 0<p) (nw dw : Word p) (k : List (Fin 3))
    (t m q : ℕ) : Meter (Word p) :=
  let a := powerMod dw (List.replicate (t*m) ())
  let b := mulWord a.result (dyadicWord p (q*t))
  let c := paddingFactorTape hp nw dw k
  let f := mulWord b.result c.result
  ⟨f.result,a.steps+b.steps+c.steps+f.steps+6*p+16⟩

def factorTapeFee (p m t C : ℕ) :=
  12*p+24+t*m*wordMulFee p+C*padTapeFee p+2*(32*(p+1)^2)

theorem compute_factor_exact {p : ℕ} (hp : 0<p) (nw dw : Word p)
    (ks : List (Fin 3)) (t m q : ℕ) (n d : ℤ)
    (hn : wordRead nw=(n:ZMod (2^p))) (hd : wordRead dw=(d:ZMod (2^p))) :
    wordRead (computeFactor hp nw dw ks t m q).result =
      ((d^(t*m)*2^(q*t)*(ks.map fun k=>pad n d k.val).prod:ℤ):ZMod (2^p)) ∧
    (computeFactor hp nw dw ks t m q).steps≤factorTapeFee p m t ks.length := by
  let a := powerMod dw (List.replicate (t*m) ())
  let b := mulWord a.result (dyadicWord p (q*t))
  let c := paddingFactorTape hp nw dw ks
  let f := mulWord b.result c.result
  have ha := power_mod_exact hp dw (List.replicate (t*m) ())
  simp only [List.length_replicate] at ha
  have hc := padding_factor_tape_exact hp nw dw ks n d hn hd
  constructor
  · simp only [computeFactor,mulWord_read,ha.1,hd,dyadic_word_read_pow,hc.1,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Nat.cast_pow,Nat.cast_ofNat]
  · have a0 : a.steps≤3*p+4+t*m*wordMulFee p := ha.2
    have b0 : b.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
    have c0 : c.steps≤3*p+4+ks.length*padTapeFee p := hc.2
    have f0 : f.steps≤32*(p+1)^2 := (wordOps p hp).mul_cost _ _
    change a.steps+b.steps+c.steps+f.steps+6*p+16≤_
    unfold factorTapeFee
    omega

theorem padding_factor_fits (n d : ℤ) (b k : ℕ) (hb : k≤2)
    (hn : Fits b n) (hd : Fits b d) :
    Fits (2*b+3) (pad n d k) := by
  have dx : Fits (b+1) (d-n) := hd.sub hn
  have C : b*(2-k)+(b+1)*k≤2*b+2 := by
    interval_cases k <;> simp <;> omega
  have x := ((hd.pow (2-k)).mul (dx.pow k)).mono C
  have y := (hd.pow 2).mono (show b*2≤2*b+2 by omega)
  exact (y.add x).mono (by omega)

theorem pad_tape_width (ks : List (Fin 3)) (n d : ℤ) (b : ℕ) (hn : Fits b n) (hd : Fits b d) :
    Fits ((2*b+3)*ks.length) (ks.map (fun k=>pad n d k.val)).prod := by
  induction ks with
  | nil => exact Fits.one _
  | cons k ks ih =>
    have C := padding_factor_fits n d b k.val (by omega) hn hd
    simp only [List.length_cons,Nat.mul_add,mul_one,List.map_cons,List.prod_cons]
    exact (C.mul ih).mono (by omega)

theorem raw_factor_width (ks : List (Fin 3)) (n d : ℤ) (m t q b : ℕ)
    (hn : Fits b n) (hd : Fits b d) :
    Fits (b*(t*m)+q*t+(2*b+3)*ks.length) (d^(t*m)*2^(q*t)*(ks.map (fun k=>pad n d k.val)).prod) := by
  have H : Fits 1 2 := by norm_num [Fits]
  exact (((hd.pow (t*m)).mul (H.pow (q*t))).mul (pad_tape_width ks n d b hn hd)).mono (by omega)

#print axioms pad_factor_word_exact
#print axioms padding_factor_tape_exact
#print axioms compute_factor_exact
#print axioms padding_factor_fits
#print axioms pad_tape_width
#print axioms raw_factor_width
end J6R22RootReadout
