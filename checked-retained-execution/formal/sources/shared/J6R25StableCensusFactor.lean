
import J6R25StableCensusNumerator
import J6R22RootReadoutFactorSource

/-! Native public factor from exactly the enumerated physical padding
columns. A typed load census is a public acquisition boundary, but the
normalizer integer, its width, and its materialization fee are derived. -/
namespace J6R25StableCensus
open scoped BigOperators Polynomial Classical
open Polynomial P11FullPacking J6Mesh J6RepairedCentered J6NativeHeightMesh J6OrientedHost
open A1R10 A1R12 AOracleMachineTime AOracleCoordinates
open J9R19CompiledBits J6IntegerLayers J6R22RootReadout J6R23PaddingCensus
set_option maxHeartbeats 15000000
set_option linter.unusedSectionVars false

private theorem aligned_product {A B : Type*} (f : A→ℤ) (g : B→ℤ)
    {xs : List A} {ys : List B} (h : List.Forall₂ (fun a b=>f a=g b) xs ys) :
    (xs.map f).prod=(ys.map g).prod := by
  induction h with
  | nil => rfl
  | cons H h ih => simp only [List.map_cons,List.prod_cons,H,ih]

theorem legal_normalizer_pair_shape
    (m q l : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (newChart : LegalRootChart w hm hL) (i : J6Recovery.Addr m)
    (V : List (Pad w m (K m) l)) (nodup : V.Nodup) (all : V.toFinset=Finset.univ)
    (ks : List (Fin 3)) (aligned : List.Forall₂ (fun k v=>k.val=chartLoads m l w hm hL newChart i v) ks V) :
    let n := sampleNum m i
    let d := sampleDen m i
    d^(index m i*m)*2^(q*index m i)*(ks.map (fun k=>pad n d k.val)).prod =
      legalFactor m l q w hm hL newChart i := by
  dsimp only
  unfold legalFactor J6IntegerLayers.factor
  rw [Fintype.card_fin]
  let f : Fin 3→ℤ := fun k=>pad (sampleNum m i) (sampleDen m i) k.val
  let g : Pad w m (K m) l→ℤ := fun v=>
    pad (sampleNum m i) (sampleDen m i) (chartLoads m l w hm hL newChart i v)
  have R : List.Forall₂ (fun a b=>f a=g b) ks V :=
    aligned.imp fun a b h=>congrArg (pad (sampleNum m i) (sampleDen m i)) h
  rw [aligned_product f g R,←List.prod_toFinset g nodup,all]

theorem actual_legal_factor_word {p : ℕ}
    (hp : 0<p) (m q l : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (newChart : LegalRootChart w hm hL) (i : J6Recovery.Addr m)
    (V : List (Pad w m (K m) l)) (nodup : V.Nodup) (all : V.toFinset=Finset.univ)
    (ks : List (Fin 3)) (aligned : List.Forall₂ (fun k v=>k.val=chartLoads m l w hm hL newChart i v) ks V)
    (width : publicFactorWidth m q ks.length+2≤p) :
    (bitsValue (makePublicFactor hp m q i ks).result.val:ℤ)=legalFactor m l q w hm hL newChart i ∧
    (makePublicFactor hp m q i ks).steps≤
      63*p+37+(2*m+1)*meshStateFee p+factorTapeFee p m (index m i) ks.length := by
  let c := prepareMeshWords hp m i
  let r := computeFactor hp c.result.1 c.result.2 ks (index m i) m q
  let b := centered hp r.result
  obtain ⟨n,d,MH⟩ := prepare_mesh_exact hp m i
  have C := compute_factor_exact hp c.result.1 c.result.2 ks (index m i) m q
    (sampleNum m i) (sampleDen m i) n d
  have eq := legal_normalizer_pair_shape m q l w hm hL newChart i V nodup all ks aligned
  dsimp only at eq
  have rz : wordRead r.result=(legalFactor m l q w hm hL newChart i:ZMod (2^p)) :=
    C.1.trans (congrArg (fun x : ℤ=>(x:ZMod (2^p))) eq)
  obtain ⟨fn,fd⟩ := source_mesh_fits m i
  have Z := raw_factor_width ks (sampleNum m i) (sampleDen m i) m (index m i) q
    (outerMeshWidth m) fn fd
  rw [eq] at Z
  have T := (address_index m i).2.2.1
  have h1 := Nat.mul_le_mul_left (outerMeshWidth m) (Nat.mul_le_mul_right m T)
  have h2 := Nat.mul_le_mul_left q T
  have bf : Fits (publicFactorWidth m q ks.length) (legalFactor m l q w hm hL newChart i) :=
    Z.mono (by unfold publicFactorWidth; omega)
  have lift := word_lifts_int hp r.result (legalFactor m l q w hm hL newChart i) rz bf width
  refine ⟨?_,?_⟩
  · change (bitsValue b.result.magnitude.val:ℤ)=_
    rw [← abs_of_signed_value b.result,lift]
    exact Int.natAbs_of_nonneg (legal_factor_positive m l q w hm hL newChart i).le
  · have h := (centered_exact hp r.result).2
    change b.steps≤35*p+10 at h
    change c.steps+r.steps+b.steps+3≤_
    have hx := C.2
    change r.steps≤_ at hx
    change c.steps≤_ at MH
    omega

#print axioms legal_normalizer_pair_shape
#print axioms actual_legal_factor_word
end J6R25StableCensus
