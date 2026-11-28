import P5D1LiteralLocality

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000

/-! The support premise of v8 N6 is derived on the actual all-edge
Boolean cube of an old-row, four-clone Appendix D packet child. Its
retained unary table is literally reindexed, never contracted away. -/
namespace V8NativeMessage.N6D
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Blueprint J6R9Recursive J6R9PacketScopes
open P11FullPacking Paper5.D1Literal Paper5.HybridClosure
noncomputable section

theorem canonical_zero (f : ℤ[X]) (hf : f.Monic) (p ell : ℕ) :
    canonicalLift p f hf ell 0=0 := by
  simp [canonicalLift,polynomialSection]

def hostTerm {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) (hf : f.Monic)
    (x : H.Edge→Bool) : IntRing f ell :=
  letI := H.finiteRow
  letI := H.finiteCol
  ∏ v : H.Row ⊕ H.Col, (H.file v).frozen hf (assignment H.network x v)

theorem hostContract_all_terms {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) (hf : f.Monic) :
    letI := H.finiteEdge
    H.contract hf = ∑ x : H.Edge→Bool, hostTerm H hf x := rfl

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable {a : ℕ} (P : PhysicalPacking (dNetwork F cubic) a (Fin 64))
variable (i : Fin a) (g : Fin 64)
local notation "N" => dNetwork F cubic
local notation "Γ" => atGroup P i

def pinOwner (w : W) : Fin 64 := P.rowLabel (.inr (.inl w)) i

abbrev AllState (P : PhysicalPacking (dNetwork F cubic) a (Fin 64)) (i : Fin a) (g : Fin 64) :=
  ChildEdge N (atGroup P i) g → Bool

def pinVertex (w : PinSlice F cubic P i g) : Old Γ g :=
  ⟨.inl (.inr (.inl w.val)),w.property⟩

def pinPort (w : W) : ParentPorts N (.inl (.inr (.inl w))) :=
  ⟨.inl (.inl w,true),rfl⟩

def pinEdge (w : PinSlice F cubic P i g) : ChildEdge N Γ g :=
  ⟨(pinPort F cubic w.val).val,
    (congrArg Γ (pinPort F cubic w.val).property).trans (pinVertex F cubic P i g w).property⟩

omit [Fintype W] in
theorem pinEdge_injective : Function.Injective (pinEdge F cubic P i g) := by
  intro u v h
  have hv := congrArg Subtype.val h
  change (Sum.inl ((Sum.inl u.val : MainClonedCNF.Port F),true) :
    Port (DWire F))=Sum.inl (Sum.inl v.val,true) at hv
  exact Subtype.ext (Sum.inl.inj (congrArg Prod.fst (Sum.inl.inj hv)))

def pattern (x : AllState F cubic P i g) (w : PinSlice F cubic P i g) : Bool :=
  x (pinEdge F cubic P i g w)

variable {f : ℤ[X]} (hf : f.Monic) (p₀ : ℕ)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
variable (p : ℕ) (hnil : (2 : Residue f 1 p)^p=0) (z : Residue f 1 p)
variable (β : Mode i p P.mask →₀ ℕ)

def trueTerm (σ : W→Bool) (x : AllState F cubic P i g) : IntRing f 1 :=
  hostTerm (actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ σ) β g) hf x

theorem trueTerm_group_local (σ τ : W→Bool) (x : AllState F cubic P i g)
    (same : ∀ w : PinSlice F cubic P i g, σ w.val=τ w.val) :
    trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ x =
      trueTerm F cubic P i g hf p₀ ht hv p hnil z β τ x := by
  unfold trueTerm hostTerm actualPacketHost physicalChildHost physicalHost
  dsimp only
  apply Finset.prod_congr rfl
  intro v _
  cases v with
  | inl u =>
    change ((oldRowFile F cubic f p₀ σ u.val).reindex _).frozen hf _ =
      ((oldRowFile F cubic f p₀ τ u.val).reindex _).frozen hf _
    rw [oldRow_file_equal_at_group F cubic p₀ P i g σ τ same u]
  | inr k => rfl

/-- The old unary entry is exactly the indicator of the one decided
sign, evaluated at its retained physical half-port. This is its actual
creation-tagged truth, before requesting any lower precision. -/
theorem choice_from_old_table (σ : W→Bool) (x : AllState F cubic P i g)
    (w : PinSlice F cubic P i g) :
    (oldRowFile F cubic f p₀ σ (pinVertex F cubic P i g w).val).table
      (restrictOriginal N Γ g (pinVertex F cubic P i g w) x) =
      if pattern F cubic P i g x w=σ w.val then 1 else 0 := by
  simp only [oldRowFile,oldRowTruth,pinVertex,decide_eq_true_eq]
  rfl

/-- Every disagreeing local sign kills this actual complete
assignment term already in the integral carrier, even in the
presence of arbitrary remaining packet factors. -/
theorem trueTerm_zero_of_ne (σ : W→Bool) (x : AllState F cubic P i g)
    (w : PinSlice F cubic P i g) (ne : pattern F cubic P i g x w≠σ w.val) :
    trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ x=0 := by
  let v := pinVertex F cubic P i g w
  let A := actualPacket P i ht hv p hnil z β g
  let file := oldRowFile F cubic f p₀ σ
  unfold trueTerm hostTerm actualPacketHost physicalChildHost physicalHost
  dsimp only
  apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl v))
  change (compileChild N Γ (atPacket P) g file p (compiledPacket P i g p A) (.inl v)).frozen hf
    (assignment (child N Γ (atPacket P) g) x (.inl v))=0
  rw [retained_int_exact]
  change canonicalLift p₀ f hf 1 ((file v.val).table (restrictOriginal N Γ g v x))=0
  rw [choice_from_old_table F cubic P i g p₀,if_neg ne,canonical_zero]

theorem trueTerm_support (σ : W→Bool) (x : AllState F cubic P i g)
    (nonzero : trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ x≠0) :
    ∀ w : PinSlice F cubic P i g, σ w.val=pattern F cubic P i g x w := by
  intro w
  by_contra ne
  exact nonzero (trueTerm_zero_of_ne F cubic P i g hf p₀ ht hv p hnil z β σ x w (Ne.symm ne))

theorem actual_child_is_complete_sum (σ : W→Bool) :
    (actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ σ) β g).contract hf =
      ∑ x : AllState F cubic P i g, trueTerm F cubic P i g hf p₀ ht hv p hnil z β σ x := by
  rw [hostContract_all_terms]
  refine Finset.sum_congr (Finset.ext (fun x => by simp only [Finset.mem_univ])) ?_
  exact fun _ _ => rfl

#print axioms canonical_zero
#print axioms hostContract_all_terms
#print axioms pinEdge_injective
#print axioms trueTerm_group_local
#print axioms choice_from_old_table
#print axioms trueTerm_zero_of_ne
#print axioms trueTerm_support
#print axioms actual_child_is_complete_sum

end
end V8NativeMessage.N6D
