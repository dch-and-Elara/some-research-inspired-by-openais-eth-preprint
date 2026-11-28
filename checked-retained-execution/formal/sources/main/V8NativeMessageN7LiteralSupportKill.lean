import V8NativeMessageN7LiteralSupportFlat

/-! A row factor with only physically absent required inputs excludes
the entire global value, in any commutative receiving ring. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option maxRecDepth 2200
noncomputable section

variable {E A B G R : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [CommRing R]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G)

theorem missing_required_inputs_kills_flat
    (t : ℤ) (κ : R) (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (u : A⊕B) (inputs : Finset E)
    (noMatch : ∀ r∈inputs,∀ q,¬Matches P t r q)
    (requires : ∀ w : Port E→Bool,(∀ r∈inputs,w (.inl r)=false)→
      flags u (fun p=>w p.val)=false) :
    flatSigned P t κ flags=0 := by
  unfold flatSigned
  refine Finset.sum_eq_zero fun w _=>?_
  unfold flatTerm
  by_cases h : ∀ r∈inputs,w (.inl r)=false
  · have gate : bit R (flags u (fun p=>w p.val))=0 :=
      (congrArg (bit R) (requires w h)).trans rfl
    rw [Finset.prod_eq_zero (Finset.mem_univ u) gate,zero_mul]
  · push_neg at h
    obtain ⟨r,hr,active⟩ := h
    have on : w (.inl r)=true := by
      cases q : w (.inl r)
      · exact (active q).elim
      · rfl
    have z := literal_unmatched_port_zero (R:=R) P t w r (noMatch r hr)
    have gate : LiteralPortCompiler.affine (w (.inl r)) (κ*wholeShiftBit P R t w r)=0 := by
      simp [LiteralPortCompiler.affine,on,z]
    rw [Finset.prod_eq_zero (Finset.mem_univ r) gate,mul_zero]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.missing_required_inputs_kills_flat
