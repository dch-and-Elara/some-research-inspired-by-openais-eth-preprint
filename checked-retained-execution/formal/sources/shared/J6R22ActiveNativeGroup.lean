import J6R22ActiveGroups
import J6R22ActiveUnit
import J6R16ModeCostSite
import J6R12BlueprintGrouped

/-! Connect the paid 64-group fold to the source's dependent legal
\beta alphabet at the same true call, centre, and chosen probe. The
roster is a verified enum transcript (no requirement to materialize
it); the per-child callback already runs on its serialized
descriptor. Producing all descriptors, and the centre-level
interpolation/Hermite combine, are separate. -/
namespace J6R22Active
open scoped BigOperators Polynomial Classical
open A1R10 AOracleMachineTime J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J6R16ModeCost J6R18ChildWrite

theorem complete_sum {B R : Type*} [Fintype B] [AddCommMonoid R]
    (ls : List B) (hn : ls.Nodup) (ha : ∀ b,b∈ls) (term : B→R) :
    (ls.map term).sum=∑ b,term b := by
  classical
  have hu : ls.toFinset=Finset.univ := by
    ext b
    simp [ha]
  rw [←hu,List.sum_toFinset term hn]

theorem complete_order_length {B : Type*} [Fintype B]
    (ls : List B) (hn : ls.Nodup) (ha : ∀ b,b∈ls) :
    ls.length=Nat.card B := by
  simpa only [Nat.card_eq_fintype_card,List.map_const',List.sum_replicate,Nat.mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using complete_sum ls hn ha (fun _=>(1:ℕ))

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

set_option maxHeartbeats 2000000 in
theorem grouped_run_reindex (c : Call (PhysicalHost f ell))
    (hc : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) :
    let B := sourceBlueprint sel r hf
    let run : Responses (paddedShape (N sel) (Childs sel) r) f ell c :=
      fun w=>B.program.run (B.program.child c w)
    letI := nativeMenuFinite (N sel) c t
    groupedSample (paddedShape (N sel) (Childs sel) r) f ell c run t z =
      ∑ β : NativeMenu (N sel) c t, ∏ g : Fin 64,
        B.program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,ha⟩) := by
  let B := sourceBlueprint sel r hf
  let H := positive_at_native sel r
  dsimp only
  unfold groupedSample
  symm
  refine Fintype.sum_equiv (nativeSlotEquiv (N sel) (Childs sel) r c hc ha t (H c hc ha t))
    _ _ (fun β=>?_ )
  apply Finset.prod_congr rfl
  intro g _
  let addr : NativeAddress (N sel) c := ⟨t,z,β,g⟩
  let w := nativeAddressEquiv (N sel) (Childs sel) r c hc ha (H c hc ha) addr
  change B.program.run ((Plan sel).child c ⟨addr,ha⟩)=B.program.run (B.program.child c w)
  have h1 : B.program.child c w=widenedChild (N sel) (Childs sel) r c hc ha (H c hc ha) w :=
    paddedBlueprint_child (N sel) (Childs sel) r H f ell (physicalEntries hf) c hc ha w
  have h2 : widenedChild (N sel) (Childs sel) r c hc ha (H c hc ha) w=
      (Plan sel).child c ⟨addr,ha⟩ :=
    widenedChild_exact (N sel) (Childs sel) r c hc ha (H c hc ha) addr
  have go (a b : Call (PhysicalHost f ell)) (e : a=b) : HEq (B.program.run a) (B.program.run b) := by
    subst b
    rfl
  exact eq_of_heq (go _ _ (h1.trans h2).symm)
set_option maxHeartbeats 2000000 in
theorem metered_native_probe (c : Call (PhysicalHost f ell))
    (hc : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c)
    (hp : 0<registerPrecision S c t) {fw : List (Word (registerPrecision S c t))}
    (he : 0<fw.length) (hE : 0<ell)
    (hF : Modulus (registerPrecision S c t) hp fw=NativeProbeRing.liftPoly (registerPrecision S c t) f)
    (ls : List (NativeMenu (N sel) c t)) (hn : ls.Nodup) (hall : ∀ b,b∈ls)
    (child : NativeMenu (N sel) c t→Fin 64→Meter (UVBlock fw ell))
    (read : ∀ β g, castBox hF (uvRead hp fw ell (child β g).result)=
      (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,ha⟩)) :
    let B := sourceBlueprint sel r hf
    let run : Responses (paddedShape (N sel) (Childs sel) r) f ell c :=
      fun w=>B.program.run (B.program.child c w)
    let v := groupedProbe hp he hE ls child
    castBox hF (uvRead hp fw ell v.result)=
      groupedSample (paddedShape (N sel) (Childs sel) r) f ell c run t z ∧
    probeEntryBill ls child≤v.steps ∧
    v.steps≤probeEntryBill ls child+
      probeExtra fw.length ell (registerPrecision S c t) 64 (Nat.card (NativeMenu (N sel) c t)) hp := by
  letI : Fintype (NativeMenu (N sel) c t) := nativeMenuFinite (N sel) c t
  let B := sourceBlueprint sel r hf
  let Q := fun β : NativeMenu (N sel) c t=>∏ g : Fin 64,uvRead hp fw ell (child β g).result
  have hlen := complete_order_length ls hn hall
  obtain ⟨bl,bu⟩ := grouped_probe_exact_bill hp he hE ls child
  refine ⟨?_,bl,?_⟩
  · rw [grouped_run_reindex sel r hf c hc ha t z,grouped_probe_value hp he hE ls child]
    change castBox hF (ls.map Q).sum=_
    rw [complete_sum ls hn hall Q]
    rw [← boxTransport_cast,map_sum]
    simp only [Q,map_prod,boxTransport_cast]
    refine Finset.sum_congr rfl fun β _=>Finset.prod_congr rfl fun g _=>?_
    exact read β g
  · rw [← hlen]
    exact bu

#print axioms complete_sum
#print axioms complete_order_length
#print axioms grouped_run_reindex
#print axioms metered_native_probe
end J6R22Active







