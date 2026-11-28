import V8R45PooledLiteralSchedule
import V8R45PooledLiteralDegree
import V8R45PooledLiteralDispatch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5600000
set_option maxRecDepth 3000

/-! Derive actual child well-formedness from the root incidence and the
same supplied legal packing. The source solver is run at the printed
high precisions; its final integer readout is independently the C6 count. -/
namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy
open P11FullPacking J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
open J6R9Recursive J6R12Repack J1PPrinted

noncomputable section

theorem printed_root_delta_at_least_three (V : Type) [Fintype V] (hu : 0<rootU V) :
    3 ≤ sourceDelta (rootSize V) := by
  have ha : 1≤rootA V := by unfold rootA; omega
  have hl : 2≤(2:ℕ)^rootA V := by
    exact (show 2=(2:ℕ)^1 by decide) ▸ Nat.pow_le_pow_right (by decide) ha
  have h := (printed_root_packet_guards V hu).2.2
  omega

variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}

theorem literal_root_stable (G : Graph V E) (p : ThreePorts G) (f : ℤ[X])
    (hu : 0<rootU V) (s : V → Bool) : Stable (rootSize V) 3 (originCall G p f s) := by
  refine stable_root _ _ _ rfl (literal_root_edgeCount G p f s) ?_
    (literal_root_creation_tags G p f s) (printed_root_edges_linear V)
  have d := literal_root_degree_three G p f s
  have h := printed_root_delta_at_least_three V hu
  exact ⟨fun v => (d.1 v).trans h,fun v => (d.2 v).trans h⟩

variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)

theorem legal_exterior_children_stable (W : Probes V f) (s : V → Bool)
    (t : Site V) (q : Address P hu huM t) (g : Fin 64) :
    Stable (rootSize V) 3 (exteriorChild P hu huM W s t q g) := by
  let c := exteriorChild P hu huM W s t q g
  let H := rawHost G p f s
  have base := literal_root_stable G p f hu s
  have hP : rootPrec V ≤ high t := (printed_site_increases V t).le
  have hM : 0 < H.edgeCount :=
    (literal_root_edgeCount G p f s).symm ▸ printed_root_positive_edges V
  have child := J6R12Repack.generated_invariants (H:=H) P (rootIndex hu huM t)
    (nonzero_site hu huM t) (rootIndex_val hu huM t) (rootPrec V) (high t)
    (J6R10Integral.box_two_nil (high t) f 1) (readProbe f _ (W.word t q.probeIdx))
    q.beta g (sourceDelta (rootSize V)) (Fintype.card_fin 64)
    hM base.degree (printed_root_packet_guards V hu).2.2 base.tags hP
  change GoodDegree c.host (sourceDelta (rootSize V)) ∧ GoodTags c.host (high t) ∧
    32*c.host.edgeCount ≤ 3*H.edgeCount ∧ c.host.edgeCount < H.edgeCount at child
  refine ⟨rfl,child.1,child.2.1,?_⟩
  have hh : H.edgeCount = wireSize V := literal_root_edgeCount G p f s
  have hb : wireSize V ≤ 3*rootSize V := printed_root_edges_linear V
  have hc := child.2.2.1
  rw [hh] at hc
  change 8^1*c.host.edgeCount ≤ 3*rootSize V
  norm_num only [pow_one]
  omega

#print axioms printed_root_delta_at_least_three
#print axioms literal_root_stable
#print axioms legal_exterior_children_stable
end
end V8R45PooledLiteral