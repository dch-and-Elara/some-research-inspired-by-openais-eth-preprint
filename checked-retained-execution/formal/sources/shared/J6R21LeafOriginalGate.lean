
import J6OrientedHost
import A1R11Linear
import A1R12Combine

/-! Executable original literal gate interpreter. A stored bit address
is read through the same sequential bit-tape lookup as the native U/V
kernels. None of the original clause or equality evaluations is free. -/
namespace J6R21Leaf
open scoped BigOperators
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates AOracleSuccinct
open A1R9 A1R10 A1R11 A1R12 J6OrientedHost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

structure BitAddress (m k : ℕ) where
  code : A1R10.Word k
  inRange : bitsValue code.val<m

def encodeAddress {m k : ℕ} (fit : m≤2^k) (j : Fin m) : BitAddress m k :=
  ⟨⟨encodeBits k j.val,encodeBits_length _ _⟩,by
    rw [encodeBits_exact _ _ (j.isLt.trans_le fit)]
    exact j.isLt⟩

def addressFee (m k : ℕ) : ℕ := (10*k+5)*m+k+3

def readAddress {m k : ℕ} (a : BitAddress m k) (tape : List Bool) : Meter Bool :=
  let z := seekBlock (fun _=>1) a.code.val tape
  ⟨z.result.getD false,z.steps+a.code.val.length+3⟩

theorem read_address_exact {m k : ℕ} (fit : m≤2^k) (j : Fin m) (x : Fin m→Bool) :
    let r := readAddress (encodeAddress fit j) (List.ofFn x)
    r.result=x j ∧ r.steps≤addressFee m k := by
  dsimp only
  let a := encodeAddress fit j
  let z := seekBlock (fun _=>1) a.code.val (List.ofFn x)
  obtain ⟨hv,hc⟩ := seekBlock_exact (fun _=>1) a.code.val (List.ofFn x)
  change z.result=_ at hv
  have hx : bitsValue a.code.val=j.val := encodeBits_exact _ _ (j.isLt.trans_le fit)
  have hcol := sum_map_le_length (List.ofFn x) (fun _=>1) 1 (fun _ _=>le_rfl)
  rw [List.length_ofFn,Nat.mul_one] at hcol
  have hcost : z.steps≤(10*k+5)*m := by
    change z.steps≤_ at hc
    rw [a.code.property,List.length_ofFn] at hc
    rw [show (10*k+5)*m=(10*k+4)*m+m by ring]
    omega
  have hvalue : z.result=some (x j) := by
    rw [hv,hx,List.getElem?_ofFn]
    simp [j.isLt]
  change z.result.getD false=x j ∧ z.steps+a.code.val.length+3≤addressFee m k
  constructor
  · simp [hvalue]
  · rw [a.code.property,addressFee]
    omega

def scanWords {m k : ℕ} (bits : List Bool) : List (BitAddress m k) → Meter (List Bool)
  | [] => ⟨[],1⟩
  | i::is =>
    let x := readAddress i bits
    let r := scanWords bits is
    ⟨x.result::r.result,x.steps+r.steps+2⟩

theorem scan_words_exact {m k : ℕ} (fit : m≤2^k) (x : Fin m→Bool) (ports : List (Fin m)) :
    let r := scanWords (List.ofFn x) (ports.map (encodeAddress fit))
    r.result=ports.map x ∧ r.steps≤1+ports.length*(addressFee m k+2) := by
  dsimp only
  induction ports with
  | nil => simp [scanWords]
  | cons i is ih =>
    have h := read_address_exact fit i x
    constructor
    · simp only [List.map_cons,scanWords,h.1,ih.1]
    · simp only [List.map_cons,scanWords,List.length_cons,Nat.succ_mul]
      omega

inductive OriginalGateTape (m k : ℕ) where
  | clause (ports : List (BitAddress m k)) (signs : List Bool)
  | equal (ports : List (BitAddress m k))
  | free

def gateTape {d m k : ℕ} (fit : m≤2^k) (port : Fin d→Fin m) (G : Gate d) : OriginalGateTape m k :=
  match G with
  | .clause s => .clause ((List.ofFn port).map (encodeAddress fit)) (List.ofFn s)
  | .equal => .equal ((List.ofFn port).map (encodeAddress fit))
  | .free => .free

def localAllEqual (xs : List Bool) : Bool :=
  xs.all (fun x=>x == xs.headD false)

def runOriginalGate {m k : ℕ} (bits : List Bool) : OriginalGateTape m k→Meter Bool
  | .free => ⟨true,2⟩
  | .clause ports signs =>
    let r := scanWords bits ports
    ⟨(List.zipWith (· == ·) r.result signs).any id,r.steps+5*ports.length+4⟩
  | .equal ports =>
    let r := scanWords bits ports
    ⟨localAllEqual r.result,r.steps+5*ports.length+4⟩

def originalGateFee (m k d : ℕ) : ℕ := 5+d*(addressFee m k+7)

private theorem zip_ofFn {n : ℕ} (x y : Fin n→Bool) :
    List.zipWith (· == ·) (List.ofFn x) (List.ofFn y) =
      List.ofFn (fun i=>x i == y i) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ,List.zipWith_cons_cons,ih]

private theorem pair_any_ofFn {n : ℕ} (x y : Fin n→Bool) :
    (List.ofFn (fun i=> x i == y i)).any id=decide (∃ i,x i=y i) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨i,hi⟩,ht⟩
    exact ⟨i,beq_iff_eq.mp (hi.trans ht)⟩
  · rintro ⟨i,hi⟩
    exact ⟨true,⟨i,beq_iff_eq.mpr hi⟩,rfl⟩

private theorem localEqual_iff (xs : List Bool) :
    localAllEqual xs=true ↔ ∀ x∈xs,∀ y∈xs,x=y := by
  cases xs with
  | nil => simp [localAllEqual]
  | cons b bs =>
    simp only [localAllEqual,List.headD_cons,List.all_eq_true,beq_iff_eq]
    refine ⟨fun h x hx y hy => (h x hx).trans (h y hy).symm,?_⟩
    intro h y hy
    exact h y hy b List.mem_cons_self

private theorem all_equal_ofFn {n : ℕ} (x : Fin n→Bool) :
    localAllEqual (List.ofFn x)=decide (∀ i j,x i=x j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [localEqual_iff,List.mem_ofFn,decide_eq_true_eq]
  constructor
  · intro h i j
    exact h _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
  · rintro h y ⟨u,hu⟩ z ⟨v,hv⟩
    exact hu.symm.trans ((h u v).trans hv)

theorem original_gate_exact {d m k : ℕ} (fit : m≤2^k)
    (port : Fin d→Fin m) (G : Gate d) (x : Fin m→Bool) :
    let r := runOriginalGate (List.ofFn x) (gateTape fit port G)
    r.result=G.eval (x∘port) ∧ r.steps≤originalGateFee m k d := by
  dsimp only
  have H := scan_words_exact fit x (List.ofFn port)
  cases G with
  | free => simp [runOriginalGate,gateTape,Gate.eval,originalGateFee]; omega
  | clause s =>
    constructor
    · simp only [runOriginalGate,gateTape]
      rw [H.1,List.map_ofFn,zip_ofFn,pair_any_ofFn,Gate.eval]
    · simp only [runOriginalGate,gateTape,List.length_map,List.length_ofFn,originalGateFee]
      have h := H.2
      rw [List.length_ofFn] at h
      rw [Nat.mul_add] at h ⊢
      omega
  | equal =>
    constructor
    · simp only [runOriginalGate,gateTape]
      rw [H.1,List.map_ofFn,all_equal_ofFn,Gate.eval]
    · simp only [runOriginalGate,gateTape,List.length_map,List.length_ofFn,originalGateFee]
      have h := H.2
      rw [List.length_ofFn] at h
      rw [Nat.mul_add] at h ⊢
      omega

def uvGate {p ell m k : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hℓ : 0<ell) (A : OriginalGateTape m k) (tape : List Bool) :
    Meter (UVBlock fw ell) :=
  let g := runOriginalGate tape A
  ⟨if g.result then uvOne hp he hℓ else uvZero hp fw ell,g.steps+uvWidth fw.length ell p+4⟩

theorem uv_gate_exact {p ell d m k : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hℓ : 0<ell) (fit : m≤2^k)
    (port : Fin d→Fin m) (G : Gate d) (x : Fin m→Bool) :
    let r := uvGate hp he hℓ (gateTape fit port G) (List.ofFn x)
    uvRead hp fw ell r.result=(if G.eval (x∘port) then 1 else 0) ∧
      r.steps≤originalGateFee m k d+uvWidth fw.length ell p+4 := by
  dsimp only
  obtain ⟨a,b⟩ := original_gate_exact fit port G x
  constructor
  · simp only [uvGate,a]
    split <;> simp
  · exact Nat.add_le_add_right (Nat.add_le_add_right b _) _

#print axioms read_address_exact
#print axioms scan_words_exact
#print axioms original_gate_exact
#print axioms uv_gate_exact
end J6R21Leaf
