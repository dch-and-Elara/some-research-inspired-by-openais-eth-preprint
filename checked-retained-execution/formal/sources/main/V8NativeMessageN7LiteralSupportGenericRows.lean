import V8NativeMessageN7LiteralSupportBlock
import V8NativeMessageN7LiteralSupportResidue

/-! Algebraic row-fibre elimination for the actual two-cube physical
contraction. The cut is the original declared row-owner projection. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R9PacketTiles P11FullPacking
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 2300
noncomputable section

variable {E A B G R : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [CommRing R]
variable {n : ℕ} {N : Network E A B} (P : PhysicalPacking N n G)

def coefficientAt (t : ℤ) (κ : R) (y : E→Bool) (r : E) : R :=
  κ*wholeShiftBit P R t (Sum.elim (fun _=>false) y) r

def genericRowTerm (N : Network E A B)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (b : E→R) (u : A) (x : E→Bool) : R :=
  bit R (flags (.inl u) (fun p=>x (edge p.val))) *
  ∏ r : Fiber N.row u,LiteralPortCompiler.affine (x r.val) (b r.val)

def genericRowFactor (N : Network E A B)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (b : E→R) (u : A) : R :=
  localSum N.row id false (genericRowTerm N flags b) u

omit [Fintype A] [Fintype B] in
private theorem generic_row_term_is_local
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) (b : E→R) (u : A)
    (x x' : E→Bool) (same : ∀ r,N.row r=u→x r=x' r) :
    genericRowTerm N flags b u x=genericRowTerm N flags b u x' := by
  unfold genericRowTerm
  apply congrArg₂ (·*·)
  · apply congrArg (bit R)
    apply congrArg (flags (.inl u))
    funext p
    obtain ⟨p,h⟩ := p
    cases p with
    | inl r => exact same r (Sum.inl.inj h)
    | inr _ => cases h
  · refine Finset.prod_congr rfl fun r _=>?_
    rw [same _ r.property]

omit [Fintype E] [Fintype B] in
private theorem row_indicator_product (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (x : E→Bool) :
    bit R (rowKeep N flags x)=∏ u : A,bit R (flags (.inl u) (fun p=>x (edge p.val))) := by
  unfold rowKeep
  by_cases yes : ∀ u : A,flags (.inl u) (fun p=>x (edge p.val))=true
  · rw [decide_eq_true yes]
    symm
    exact Finset.prod_eq_one (fun u _=>by rw [yes u]; rfl)
  · rw [decide_eq_false yes]
    obtain ⟨u,hu⟩ := not_forall.mp yes
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    cases k : flags (.inl u) (fun p=>x (edge p.val))
    · rfl
    · exact (hu k).elim

theorem flat_row_fibres_integrate (t : ℤ) (κ : R)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) :
    flatSigned P t κ flags=
      ∑ y : E→Bool, if colKeep N flags y then
        ∏ u : A,genericRowFactor N flags (coefficientAt P t κ y) u else 0 := by
  rw [literal_cubes_sum_columns_first]
  refine Finset.sum_congr rfl fun y _=>?_
  have eqTerm (x : E→Bool) : flatTerm P t κ flags (Sum.elim x y)=
      bit R (colKeep N flags y) * ∏ u : A,genericRowTerm N flags (coefficientAt P t κ y) u x := by
    unfold flatTerm
    rw [actual_flags_on_full_side_words]
    have bmul (b c : Bool) : bit R (b&&c)=bit R b*bit R c := by cases b <;> cases c <;> simp [bit]
    rw [bmul,row_indicator_product]
    have eqA (r : E) : κ*wholeShiftBit P R t (Sum.elim x y) r=coefficientAt P t κ y r := rfl
    simp only [Sum.elim_inl,eqA]
    rw [J6BlockFactor.prod_rows N.row
      (fun r=>LiteralPortCompiler.affine (x r) (coefficientAt P t κ y r))]
    simp only [genericRowTerm,Finset.prod_mul_distrib]
    ac_rfl
  simp only [eqTerm,←Finset.mul_sum]
  rw [split_actual_bits N.row id false _ (generic_row_term_is_local flags _)]
  cases colKeep N flags y <;> simp [bit,genericRowFactor]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.flat_row_fibres_integrate
