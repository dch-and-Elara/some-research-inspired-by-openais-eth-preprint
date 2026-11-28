import J4R43LiteralOutsideRows
import V8NativeMessageN7LiteralSupportZero

/-! The completed zero-probe value is the product of the actual
constant-degree old-column marginals. No purported supplied child
or group scalar is used as a certificate of a value. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9PacketTiles
open J6R9PacketCoeff J6ActiveRun J6R12Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option maxHeartbeats 5500000
set_option maxRecDepth 2600
set_option Elab.async false
set_option linter.unreachableTactic false

section GlobalPorts
variable {E A B : Type} (N : Network E A B)

def allColumnPorts : (Σ b : B,ParentPorts N (.inr b)) ≃ E where
  toFun q := edge q.2.val
  invFun e := ⟨N.col e,⟨.inr e,rfl⟩⟩
  left_inv := by
    rintro ⟨b,⟨e,h⟩⟩
    cases e with
    | inl e => exact nomatch h
    | inr e =>
      have he : N.col e=b := Sum.inr.inj h
      cases he
      rfl
  right_inv _ := rfl

def globalColumnBits : (E→Bool) ≃ ((b : B)→ParentPorts N (.inr b)→Bool) where
  toFun y b q := y (edge q.val)
  invFun x e := x (N.col e) ⟨.inr e,rfl⟩
  left_inv y := by funext e; rfl
  right_inv x := by
    funext b q
    change (fun k : Σ b : B,ParentPorts N (.inr b) => x k.1 k.2)
      ((allColumnPorts N).symm ((allColumnPorts N) ⟨b,q⟩))=_
    rw [Equiv.symm_apply_apply]
end GlobalPorts

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ} {R : Type} [CommRing R]
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg
variable (P : PhysicalPacking N a (Fin 64))

def columnArgumentWeight (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (e : E) (b : Bool) : R :=
  sourceColumnWeight P t κ (fun _=>b) e

abbrev ColumnArgs (u : DOld F) := ParentPorts N (.inr u)

def localColumnTerm (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (u : DOld F)
    (x : ColumnArgs F reg u→Bool) : R :=
  bit R (oldColumnTruth F reg σ (.inr u) x) *
    ∏ q : ColumnArgs F reg u, columnArgumentWeight F reg P t κ (edge q.val) (x q)

def localColumnValue (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (u : DOld F) : R :=
  ∑ x : ColumnArgs F reg u→Bool,localColumnTerm F reg P t κ σ u x

def factorizedValue (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) : R :=
  ∏ u : DOld F,localColumnValue F reg P t κ σ u

theorem old_global_indicator (σ : W→Bool) (y : E→Bool) :
    (∏ u : DOld F,bit R (oldColumnTruth F reg σ (.inr u) (globalColumnBits N y u))) =
      if originalColumnKeep F reg σ y then 1 else 0 := by
  have flag (u : DOld F) :
      oldColumnTruth F reg σ (.inr u) (globalColumnBits N y u) =
      oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val)) := by
    have H := actual_column_flags_read_only_its_old_port F reg σ u (fun _=>false) y
    rw [←H]
    congr 1
    funext p
    obtain ⟨p,hp⟩ := p
    cases p
    · exact nomatch hp
    · rfl
  simp only [flag]
  by_cases k : ∀ u : DOld F,oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val))=true
  · have hk : originalColumnKeep F reg σ y=true := decide_eq_true k
    rw [if_pos hk]
    exact Finset.prod_eq_one (fun u _=>by rw [k u]; rfl)
  · have hk : originalColumnKeep F reg σ y=false := decide_eq_false k
    rw [if_neg (by rw [hk]; decide)]
    obtain ⟨u,hu⟩ := not_forall.mp k
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    cases b : oldRowTruth F reg σ (.inl u) (fun p=>y (edge p.val))
    · rfl
    · exact (hu b).elim

def literalColumnCube (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) : R :=
  ∑ y : E→Bool, if originalColumnKeep F reg σ y then
         ∏ q : E,sourceColumnWeight P t κ y q else 0

theorem columnTerm_product (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (y : E→Bool) :
    (∏ u : DOld F,localColumnTerm F reg P t κ σ u (globalColumnBits N y u)) =
      if originalColumnKeep F reg σ y then (∏ q : E,sourceColumnWeight P t κ y q) else 0 := by
  unfold localColumnTerm
  rw [Finset.prod_mul_distrib,old_global_indicator (R:=R) F reg σ y]
  let g := fun q : E => sourceColumnWeight P t κ y q
  have weights :
      (∏ u : DOld F,∏ q : ColumnArgs F reg u,
        columnArgumentWeight F reg P t κ (edge q.val) (globalColumnBits N y u q)) =
      ∏ q : E,g q := by
    let k := fun z : Σ u : DOld F,ColumnArgs F reg u=>g (edge z.2.val)
    calc
      _ = ∏ z,k z := (Fintype.prod_sigma k).symm
      _ = ∏ q : E,g q := Fintype.prod_equiv (allColumnPorts N) _ _ (fun _=>rfl)
  rw [weights]
  dsimp only [g]
  split_ifs <;> simp

theorem true_columns_are_independent (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) :
    literalColumnCube F reg P t κ σ = factorizedValue F reg P t κ σ := by
  let Q := fun u : DOld F=>ColumnArgs F reg u→Bool
  letI : DecidableEq (DOld F) := Classical.decEq _
  letI (b : DOld F) : Fintype (ColumnArgs F reg b) := Fintype.ofFinite _
  letI (b : DOld F) : DecidableEq (ColumnArgs F reg b) := Classical.decEq _
  letI : ∀ b : DOld F,Fintype (Q b) := fun b=>by dsimp only [Q]; exact Pi.instFintype
  letI : Fintype ((b : DOld F)→Q b) := Pi.instFintype
  let e : (E→Bool) ≃ ((b : DOld F)→Q b) := globalColumnBits N
  let H : (u : DOld F)→Q u→R := localColumnTerm F reg P t κ σ
  let cube (y : E→Bool) : R :=
    if originalColumnKeep F reg σ y then ∏ q : E,sourceColumnWeight P t κ y q else 0
  calc
    _ = (∑ x : (b : DOld F)→Q b,∏ b,H b (x b)) := by
      change (∑ y,cube y) = _
      exact Fintype.sum_equiv e cube (fun x=>∏ b,H b (x b))
        (fun y=>(columnTerm_product F reg P t κ σ y).symm)
    _ = (∏ b : DOld F,∑ x : Q b,H b x) := (Fintype.prod_sum H).symm
    _ = _ := by
      unfold factorizedValue localColumnValue
      refine Finset.prod_congr (Finset.ext (fun x=>by simp)) fun b _=>?_
      exact Finset.sum_congr (Finset.ext (fun x=>by simp)) (fun _ _=>rfl)

theorem native_exact_factorized (P : PhysicalPacking N a (Fin 64)) {h : ℕ} (G : BandCertificate P h) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (wide : 2^a-h≤t.natAbs) (σ : W→Bool) :
    exactZero P i t (oldColumnTruth F reg σ) =
      factorizedValue F reg P t (rho a t) σ := by
  rw [exactZero,full_signed_root_is_zero_polynomial,full_root_at_zero_has_literal_two_cubes P i ht hv,
    actual_flat_after_band F reg P G wide]
  exact true_columns_are_independent F reg P t (rho a t) σ

variable {f : ℤ[X]}
local notation "S" => printedParams (f:=f) (ell:=1) (Paper5.D1Literal.oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a₀" => J6ActiveRun.Shape.levelBits S 0

theorem literal_outside_value (P₀ : ColumnPacking F reg (f:=f)) {h : ℕ}
    (G : BandCertificate P₀ h) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a₀) (hv : padicValInt 2 t.val=i.val)
    (wide : 2^a₀-h≤t.val.natAbs) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    originalOppositeSlot F reg P₀ d t i hv 0 0 hf σ =
      J6ZeroTransport.reduceAt (registerPrecision S root t)
        (J6R10Integral.box_two_nil (registerPrecision S root t) f 1)
        (factorizedValue F reg P₀ t.val (rho a₀ t.val) σ) := by
  unfold originalOppositeSlot oldColumnFile
  rw [actual_zero_slot_is_reduction P₀ i (centerNonzero t) hv
    (oldColumnTruth F reg σ) (4*Fintype.card W+1) _ (by omega) hf hd]
  rw [native_exact_factorized F reg P₀ G i (centerNonzero t) hv wide]

#print axioms allColumnPorts
#print axioms globalColumnBits
#print axioms old_global_indicator
#print axioms columnTerm_product
#print axioms true_columns_are_independent
#print axioms native_exact_factorized
#print axioms literal_outside_value
end
end J4R43LiteralOutside

