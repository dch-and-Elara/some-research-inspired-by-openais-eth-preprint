import J4R43LiteralOutsideInteger

/-! Lift the genuine original positive exterior slot (not a substituted
rational evaluation) and decode the Hamming statistic on its graph-known
nonempty set of real matched pin columns. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9PacketCoeff P11FullPacking J6R10Repack J6R9PacketTiles
open J6ActiveRun J6R12Blueprint J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
open V8NativeMessage.N7HighBound
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4400000
set_option maxRecDepth 2200

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ} {R T : Type} [CommRing R] [CommRing T]
local notation "N" => oldColumnNetwork F reg

theorem map_factorized_value (P : PhysicalPacking N a (Fin 64)) (φ : R→+*T)
    (t : ℤ) (κ : R) (σ : W→Bool) :
    φ (factorizedValue F reg P t κ σ)=factorizedValue F reg P t (φ κ) σ := by
  simp only [factorizedValue,localColumnValue,localColumnTerm,map_prod,map_sum,map_mul]
  refine Finset.prod_congr rfl fun u _=>Finset.sum_congr rfl fun y _=>?_
  congr 1
  · cases b : oldColumnTruth F reg σ (.inr u) y <;> simp [bit,b]
  · refine Finset.prod_congr rfl fun q _=>?_
    unfold columnArgumentWeight sourceColumnWeight
    by_cases h : columnHit P t (edge q.val) <;> cases v : y q <;> simp [bit,h,v]

theorem positive_extreme_natAbs (a : ℕ) :
    (((2^a:ℕ):ℤ)-1).natAbs=2^a-1 := by
  let L := (2:ℕ)^a
  have hL : 1≤L := Nat.succ_le_of_lt (pow_pos (by decide) _)
  change ((L:ℤ)-((1:ℕ):ℤ)).natAbs=L-1
  rw [←Nat.cast_sub hL,Int.natAbs_natCast]

variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem original_positive_extreme_is_integer (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (out : t.val=(((2^a₀:ℕ):ℤ)-1)) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    let p := registerPrecision S root t
    let C := J9FactorBounds.kernel (2^a₀)
    let Z := graphFactor F reg P t.val C*(1-C)^hitWeight F reg P t.val σ
    originalOppositeSlot F reg P d t i hv 0 0 hf σ=(Z:Residue f 1 p) ∧
      centeredBox p f hf (originalOppositeSlot F reg P d t i hv 0 0 hf σ)=Z ∧
      0<graphFactor F reg P t.val C ∧ 1<1-C := by
  let p := registerPrecision S root t
  let C : ℤ := J9FactorBounds.kernel (2^a₀)
  let Z : ℤ := graphFactor F reg P t.val C*(1-C)^hitWeight F reg P t.val σ
  have realZ : factorizedValue F reg P t.val C σ=Z :=
    literal_hamming_factorization F reg P t.val C σ
  have wide : 2^a₀-h≤t.val.natAbs := by
    rw [out,positive_extreme_natAbs]
    have H := G.positive
    omega
  have hc : rho a₀ t.val = (C:TwoLocal) := by
    rw [out]
    exact actual_kernel_at_extreme a₀ i.isLt.pos
  have edge : factorizedValue F reg P t.val (C:TwoLocal) σ=(Z:TwoLocal) := by
    calc
      _ = ((factorizedValue F reg P t.val C σ : ℤ) : TwoLocal) :=
        (map_factorized_value F reg P (Int.castRingHom TwoLocal) t.val C σ).symm
      _ = _ := congrArg (fun z : ℤ=>(z:TwoLocal)) realZ
  have same : originalOppositeSlot F reg P d t i hv 0 0 hf σ=(Z:Residue f 1 p) := by
    rw [literal_outside_value F reg P G d t i hv wide hf hd,hc,edge,map_intCast]
  have ht : |Z|≤(2:ℤ)^(7*Fintype.card (DWire F)) := by
    rw [←realZ,out]
    exact actual_integer_has_height F reg P σ
  have M : 0<Fintype.card (DWire F) := (Nat.zero_le _).trans_lt d.active
  have lift := actual_extreme_integer_lift F reg t M hf hd Z ht
  have neg : C<0 := genuine_extreme_negative a₀
  refine ⟨same,?_,actual_graph_factor_positive F reg P t.val C neg.le,by omega⟩
  rw [same]
  exact lift

theorem hamming_comparison_unique (A B : ℤ) (hA : 0<A) (hB : 1<B) :
    Function.Injective (fun m : ℕ=>A*B^m) := by
  have h := pow_right_strictMono₀ hB
  exact fun m n eq=>h.injective (mul_left_cancel₀ (ne_of_gt hA) eq)

theorem designated_pin_changes_hamming (P : PhysicalPacking N a (Fin 64))
    (t : ℤ) (v : W) (h : v∈hitPins F reg P t) :
    hitWeight F reg P t (fun _=>false)=0 ∧
      hitWeight F reg P t (fun w=>decide (w=v))=1 := by
  constructor
  · simp [hitWeight]
  · have same :
      (hitPins F reg P t).filter (fun w=>decide (w=v)=true)={v} := by
      ext w
      simp only [Finset.mem_filter,decide_eq_true_eq,Finset.mem_singleton]
      exact ⟨And.right,fun e=>⟨e ▸ h,e⟩⟩
    rw [hitWeight,same,Finset.card_singleton]

theorem positive_extreme_reports_designated_pin (P : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (out : t.val=(((2^a₀:ℕ):ℤ)-1)) (hf : f.Monic) (hd : 0<f.natDegree)
    (v : W) (last : (P.seat (literalPin F v)).2.val+1=2^a₀) :
    originalOppositeSlot F reg P d t i hv 0 0 hf (fun _=>false) ≠
      originalOppositeSlot F reg P d t i hv 0 0 hf (fun w=>decide (w=v)) := by
  have hv' : v∈hitPins F reg P t.val := by
    rw [out]
    exact last_pin_makes_set_nonempty F reg P G v last
  have counts := designated_pin_changes_hamming F reg P t.val v hv'
  obtain ⟨_,low,A,B⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd (fun _=>false)
  obtain ⟨_,high,_,_⟩ := original_positive_extreme_is_integer F reg P G d t i hv out hf hd (fun w=>decide (w=v))
  intro eq
  rw [eq,high] at low
  have e := hamming_comparison_unique _ _ A B low
  rw [counts.1,counts.2] at e
  omega

#print axioms map_factorized_value
#print axioms positive_extreme_natAbs
#print axioms original_positive_extreme_is_integer
#print axioms hamming_comparison_unique
#print axioms designated_pin_changes_hamming
#print axioms positive_extreme_reports_designated_pin
end
end J4R43LiteralOutside

