import V8NativeMessageN7LiteralSupportSourceKillOr
import P9SeatPhysical

/-! Full precision at the true zero probe on the old-row layout. The
endpoints are ordinary coordinates of the same physical P9 chart. -/
namespace J2R47P9ZeroProbe
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R12Blueprint J6R10Repack J6R9PacketScopes J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
open V8NativeMessage.N7LiteralSupport
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 12000000
set_option maxRecDepth 2400
set_option Elab.async false
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v, GraphCutMoments.degree F v=3)
local notation "N" => (dNetwork F reg)
local notation "E" => DWire F

section Geometry
variable {a : ℕ}

/-- The two positive ORs are built into the actual cloned truth table.
A positive shift cannot leave the last row seat; a negative shift
cannot leave the first. Both true ports of each OR are reserved. -/
def Reserved (Q : PhysicalPacking N a (Fin 64)) (positive negative : F) : Prop :=
  (∀ b, (Q.seat (sourceOrPort F positive b)).2=endpointIndex a true) ∧
  (∀ b, (Q.seat (sourceOrPort F negative b)).2=endpointIndex a false)

theorem endpoint_matches_no_successor (Q : PhysicalPacking N a (Fin 64)) (r q : E)
    (right : Bool) {t : ℤ}
    (ht : if right then 0<t else t<0)
    (he : (Q.seat r).2=endpointIndex a right) :
    ¬ Matches Q t r q := by
  intro m
  have pos := congrArg Fin.val he
  have col := (Q.seat q).2.isLt
  have sh := m.2
  cases right with
  | false =>
    change (Q.seat r).2.val=0 at pos
    change t<0 at ht
    omega
  | true =>
    change (Q.seat r).2.val=2^a-1 at pos
    change 0<t at ht
    omega

theorem some_reserved_or_unmatched (Q : PhysicalPacking N a (Fin 64)) (positive negative : F)
    (h : Reserved F reg Q positive negative) {t : ℤ} (ht : t≠0) :
    ∃ e : F, ∀ b : Bool, ¬ ∃ q : E, Matches Q t (sourceOrPort F e b) q := by
  rcases lt_or_gt_of_ne ht with neg|pos
  · refine ⟨negative,fun b ⟨q,m⟩=>?_⟩
    exact endpoint_matches_no_successor F reg Q _ q false neg (h.2 b) m
  · refine ⟨positive,fun b ⟨q,m⟩=>?_⟩
    exact endpoint_matches_no_successor F reg Q _ q true pos (h.1 b) m
end Geometry

section Slot
variable {a : ℕ} {f : ℤ[X]}

/-- Same actual layout and file at every signed active center, with no
restriction on the receiving exponent. This is the complete slot, not
a claim that each of its 64 children vanishes. -/
theorem reserved_endpoints_literal_full_zero (P : PhysicalPacking N a (Fin 64)) (positive negative : F)
    (reserve : Reserved F reg P positive negative) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (β : Mode i p P.mask→₀ℕ) :
    V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
      (oldRowFile F reg f (4*Fintype.card W+1) σ) hf β=0 := by
  by_cases mode : β=0
  · obtain ⟨e,absent⟩ := some_reserved_or_unmatched F reg P positive negative reserve ht
    rw [mode]
    change V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
      (V8PooledMenu.binaryFile f (4*Fintype.card W+1) (oldRowTruth F reg σ)) hf 0=0
    rw [actual_zero_slot_is_reduction P i ht hv (oldRowTruth F reg σ) _ p (by omega) hf hd,
      exactZero,full_signed_root_is_zero_polynomial,
      full_root_at_zero_has_literal_two_cubes P i ht hv,
      actual_shiftless_original_or_is_zero F reg P t _ σ e absent,map_zero]
  · exact native_zero_probe_nonzero_mode P i ht hv p _ _ hf β mode
end Slot

section Public
variable {f : ℤ[X]} (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

/-- Actual public addresses only: if the original probe roster omits
zero this theorem does not add a delivered value or change the menu. -/
theorem reserved_endpoints_public_full_zero (positive negative : F)
    (reserve : Reserved F reg P positive negative) (hf : f.Monic) (hd : 0<f.natDegree)
    (σ : W→Bool) (x : PublicSlot F reg f P d)
    (zeroProbe : siteProbe F reg d x.1 x.2.1=0) :
    wholePublic F reg P d hf σ x=0 := by
  obtain ⟨e,absent⟩ := some_reserved_or_unmatched F reg P positive negative reserve (centerNonzero x.1)
  exact literal_original_shiftless_or_excludes_every_sign F reg P d hf hd σ x zeroProbe e absent
end Public

#print axioms endpoint_matches_no_successor
#print axioms some_reserved_or_unmatched
#print axioms reserved_endpoints_literal_full_zero
#print axioms reserved_endpoints_public_full_zero
end
end J2R47P9ZeroProbe

