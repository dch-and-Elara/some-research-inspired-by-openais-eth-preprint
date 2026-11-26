import P5D1LiteralTrace

/-! Constructive finite visit ledger of the literal root products. The
value at each center/probe is the real finite grouped sample; no rational
field lift is computed by this loop. Counts still exclude lower-level and
bit-machine operations. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r" σ => (oldRowRoot F cubic f σ)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))
variable (P : RootPacking F cubic f)

noncomputable def siteLedger (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool)
    (t : PublicCenter F cubic f) (ζ : PublicProbe F cubic f) :
    List (PublicSlot F cubic f P d × Residue f 1 (registerPrecision S r* t)) :=
  (Finset.univ : Finset (PublicMenu F cubic f P d t)).toList.map
    (fun β => (⟨t,ζ,β⟩, ∏ g : Fin 64, publicReply F cubic f P d hf σ ⟨t,ζ,β,g⟩))

noncomputable def rootVisitLedger (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool) :
    List (Option (PublicSlot F cubic f P d)) :=
  (Finset.univ : Finset (PublicCenter F cubic f)).toList.flatMap (fun t =>
    (Finset.univ : Finset (PublicProbe F cubic f)).toList.flatMap (fun ζ =>
      (siteLedger F cubic f P d hf σ t ζ).map (fun e => some e.1)))

theorem siteLedger_value (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool)
    (t : PublicCenter F cubic f) (ζ : PublicProbe F cubic f) :
    ((siteLedger F cubic f P d hf σ t ζ).map Prod.snd).sum =
      ∑ β : PublicMenu F cubic f P d t, ∏ g : Fin 64,
        publicReply F cubic f P d hf σ ⟨t,ζ,β,g⟩ := by
  unfold siteLedger
  rw [List.map_map,Finset.sum_map_toList]
  rfl

theorem rootVisitLedger_covers (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool)
    (u : PublicSlot F cubic f P d) :
    some u ∈ rootVisitLedger F cubic f P d hf σ := by
  rcases u with ⟨t,ζ,β⟩
  apply List.mem_flatMap.mpr
  refine ⟨t,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨ζ,by simp,?_⟩
  unfold siteLedger
  rw [List.map_map]
  exact List.mem_map.mpr ⟨β,by simp,rfl⟩

/-- The explicitly enumerating root-product loop is itself a witness
of the separately paid trace contract (one charge per product, prior to
any non-unit interpolation arithmetic). -/
noncomputable def literalRootProductTrace (d : Ready S Δ r*) (hf : f.Monic) (σ : W → Bool) :
    FixedSchedule.Execution (PublicSlot F cubic f P d) where
  trace := rootVisitLedger F cubic f P d hf σ
  covers := rootVisitLedger_covers F cubic f P d hf σ
  charge _ := 1
  charge_pos := fun _ _ => le_rfl

#print axioms siteLedger_value
#print axioms rootVisitLedger_covers
#print axioms literalRootProductTrace
end Paper5.D1Literal
