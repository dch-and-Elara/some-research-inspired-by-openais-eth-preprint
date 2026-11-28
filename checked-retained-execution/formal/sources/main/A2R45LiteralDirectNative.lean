import A2R45LiteralDirectTensor
import A2R45LiteralFilledAlgebra
import A1R43LiteralGenericLayout
import A1R43LiteralShift
import J6R15PlantedIdentityCenter
import J6R12RepackBoolean

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

/-! The actual general source tensor host for the direct path gadget.
Here the *same* physical packing supplies the finite kernel and source
zero-mode child products. The paired-seat/legal-root admission remains
a separate input; no fitted abstract switched register is substituted. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler Acquisition
open A1R43Literal A1R43Literal.General J6R10Repack J6R9Recursive J6R11Integral
open J6R10Integral P11FullPacking

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) {Pad : Type}
local notation "U" => DirectWire F
local notation "R" => DirectRow F
local notation "C" => DirectCol F

def directPhysical := splitNetwork (directNetwork F) Pad
local notation "N" => directPhysical (Pad:=Pad) F

def directRowOdd (r : R) (j : Fin (directArity F r)×Bool) :
    ParentPorts N (.inl (.inl r)) := ⟨.inl (oddWire U Pad ⟨r,j⟩),rfl⟩

def directColEven (c : C) (e : {w : U//directOwner F w=c}) :
    ParentPorts N (.inr (.inl c)) :=
  ⟨.inr (evenWire U Pad e.val),congrArg (fun k : C=>Sum.inr (Sum.inl k)) e.property⟩

def actualDirectPin (p : DirectPort F) : ParentPorts N (.inr (.inl (.inr p))) :=
  directColEven F (.inr p) ⟨⟨p.1,p.2,true⟩,rfl⟩

def directDummyIndex : U⊕Pad → SplitWire U Pad
  | .inl w=>oddWire U Pad w
  | .inr p=>.inr p

def directDummyPort (z : U⊕Pad) : ParentPorts N (.inr (.inr z)) := by
  refine ⟨.inr (directDummyIndex F z),?_⟩
  cases z <;> rfl

def directPhysicalTable :
    ∀ v : SplitRow U R Pad⊕SplitCol U C Pad,(ParentPorts N v→Bool)→Bool
  | .inl (.inl r),x=>directGateTable F r (x ∘ directRowOdd F r)
  | .inl (.inr _),_=>true
  | .inr (.inl c),x=>
      decide (∀ u v : {w : U//directOwner F w=c},x (directColEven F c u)=x (directColEven F c v)) &&
        match c with
        | .inl _=>true
        | .inr p=>x (actualDirectPin F p)
  | .inr (.inr z),x=> !(x (directDummyPort F z))

def directNativeFile (f : ℤ[X]) (P0 : ℕ) : EntryFile f 1 N :=
  fun v=>⟨P0,fun x=>if directPhysicalTable F v x then 1 else 0⟩

theorem direct_native_is_binary (f : ℤ[X]) (P0 : ℕ) (hb : 0<P0)
    (hf : f.Monic) (hd : 0<f.natDegree) (v : SplitRow U R Pad⊕SplitCol U C Pad)
    (x : ParentPorts N v→Bool) :
    ((directNativeFile F f P0) v).frozen hf x=bit (directPhysicalTable F v x) := by
  unfold directNativeFile CreatedEntry.frozen bit
  exact J6R12Repack.canonical_lift_bool P0 hb f hf hd 1 (by decide) _

private theorem direct_bit_and {K : Type*} [CommRing K] (u v : Bool) :
    bit (K:=K) (u&&v)=bit u*bit v := by
  cases u <;> cases v <;> simp [bit]

private theorem direct_bit_not {K : Type*} [CommRing K] (b : Bool) :
    bit (K:=K) (!b)=(if b=false then 1 else 0) := by
  cases b <;> rfl

private theorem direct_pin_product {K : Type*} [CommRing K] (z : DirectPort F→Bool) :
    (∏ p,bit (K:=K) (z p))=directPinOnes F z := by
  unfold directPinOnes
  split
  · rename_i h
    rw [h]
    simp [bit]
  · rename_i h
    have q : ∃ i,z i=false := by
      by_contra e
      push_neg at e
      apply h
      funext i
      cases hi : z i with
      | false => exact (e i hi).elim
      | true => rfl
    obtain ⟨p,hp⟩ := q
    exact Finset.prod_eq_zero (Finset.mem_univ p) (by rw [hp]; rfl)

variable [Fintype Pad]

theorem direct_rows_exact (f : ℤ[X]) (p P0 : ℕ) (hb : 0<P0)
    (hf : f.Monic) (hd : 0<f.natDegree) (y : SplitWire U Pad→Bool) :
    reduce p f 1 (J6R11Integral.rowProduct N (directNativeFile F f P0) hf y) =
      (Acquisition.rowProduct (fun r z=>bit (directGateTable F r z)) ∘ oddBits) y := by
  rw [J6R11Integral.rowProduct,map_prod,Fintype.prod_sum_type]
  have h (r : SplitRow U R Pad) :
      reduce p f 1 (((directNativeFile F f P0) (.inl r)).frozen hf (assignment N y (.inl r))) =
        bit (directPhysicalTable F (.inl r) (assignment N y (.inl r))) := by
    rw [direct_native_is_binary F f P0 hb hf hd]
    cases directPhysicalTable F (.inl r) (assignment N y (.inl r))
    · exact map_zero _
    · exact map_one _
  simp_rw [h]
  change (∏ r : R,bit (directGateTable F r (fun j=>oddBits y ⟨r,j⟩))) *
      (∏ _ : U⊕Pad,(1:Box f 1 p)) =
    ∏ r : R, bit (directGateTable F r (fun j=>oddBits y ⟨r,j⟩))
  simp only [Finset.prod_const_one,mul_one]

theorem direct_cols_exact (f : ℤ[X]) (p P0 : ℕ) (hb : 0<P0)
    (hf : f.Monic) (hd : 0<f.natDegree) (x : SplitWire U Pad→Bool) :
    reduce p f 1 (colProduct N (directNativeFile F f P0) hf x) =
      sourceColumns (directColumnTensor F) x := by
  rw [colProduct,map_prod,Fintype.prod_sum_type]
  have receive (r : SplitCol U C Pad) :
      reduce p f 1 (((directNativeFile F f P0) (.inr r)).frozen hf (assignment N x (.inr r))) =
        bit (directPhysicalTable F (.inr r) (assignment N x (.inr r))) := by
    rw [direct_native_is_binary F f P0 hb hf hd]
    cases directPhysicalTable F (.inr r) (assignment N x (.inr r))
    · exact map_zero _
    · exact map_one _
  simp_rw [receive]
  let v (c : C) : Box f 1 p := if ∀ u w : U,directOwner F u=c→directOwner F w=c→
    evenBits x u=evenBits x w then 1 else 0
  let pin (c : C) : Box f 1 p := match c with
    | .inl _=>1
    | .inr i=>bit (evenBits x ⟨i.1,i.2,true⟩)
  have table_eq (c : C) :
      bit (K:=Box f 1 p) (directPhysicalTable F (.inr (.inl c)) (assignment N x (.inr (.inl c))))=
        v c*pin c := by
    unfold directPhysicalTable
    rw [direct_bit_and]
    have coh : (∀ u w : {q : U//directOwner F q=c}, evenBits x u.val=evenBits x w.val) ↔
        (∀ u w : U,directOwner F u=c→directOwner F w=c→evenBits x u=evenBits x w) :=
      ⟨fun h u w hu hw=>h ⟨u,hu⟩ ⟨w,hw⟩,fun h u w=>h u.val w.val u.property w.property⟩
    have eq :
      bit (K:=Box f 1 p) (decide (∀ u w : {q : U//directOwner F q=c},
        evenBits x u.val=evenBits x w.val))=v c := by
      simp only [bit,decide_eq_true_eq,coh,v]
    change bit (decide (∀ u w : {q : U//directOwner F q=c},
      evenBits x u.val=evenBits x w.val)) * _ = _
    rw [eq]
    cases c <;> rfl
  have vprod : (∏ c : C,v c)=equalityTensor (directOwner F) (evenBits x) := by
    unfold equalityTensor
    apply Finset.prod_congr rfl
    intro c _
    by_cases hc : ∀ u w : U,directOwner F u=c→directOwner F w=c→evenBits x u=evenBits x w
    · simp only [v,if_pos hc]
    · simp only [v,if_neg hc]
  have pprod : (∏ c : C,pin c)=directPinOnes F (fun q=>evenBits x ⟨q.1,q.2,true⟩) := by
    rw [Fintype.prod_sum_type]
    change (∏ _ : Occurrence F,(1:Box f 1 p))*_ = _
    rw [Finset.prod_const_one,one_mul,direct_pin_product]
  have dummy (z : U⊕Pad) :
      bit (K:=Box f 1 p) (directPhysicalTable F (.inr (.inr z)) (assignment N x (.inr (.inr z)))) =
        if x (directDummyIndex F z)=false then 1 else 0 := by
    cases z
    · exact direct_bit_not _
    · exact direct_bit_not _
  simp_rw [table_eq,Finset.prod_mul_distrib,vprod,pprod,dummy]
  rw [Fintype.prod_sum_type,←mul_assoc]
  rfl

#print axioms direct_native_is_binary
#print axioms direct_rows_exact
#print axioms direct_cols_exact
end
end A2R45Literal
