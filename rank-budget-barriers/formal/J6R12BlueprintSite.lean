import J6R11RepackSelect
import J6R9RecursiveWeights
import J6R10RowAffine

/-! Preparation of one actual active site from numerical and physical
invariants. It chooses a certified layout from the exact edge graph.
There is no layout, degree or probe-count assertion on arbitrary raw
Call records. The selected mode type depends on the call and centre. -/
namespace J6R12Blueprint
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R11Blueprint
  J6R11Repack J6R10Repack J6R9PacketScopes P11FullPacking

variable {f : ℤ[X]} {ell : ℕ}
abbrev H := PhysicalHost f ell
abbrev Params := Shape (H (f:=f) (ell:=ell)) Unit

structure Ready (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (c : Call (H (f:=f) (ell:=ell))) : Prop where
  active : S.cutoff < c.edges
  edgeCount : c.host.edgeCount = c.edges
  degree : GoodDegree c.host Δ
  tags : GoodTags c.host c.prec
  collision : 2*(J9PrintedSchedule.arrayCard (S.levelBits c.depth))^2*Δ ≤ c.edges
  paddedSlots : 2^(S.levelBits c.depth)*J9PrintedSchedule.arrayCard (S.levelBits c.depth) ≤ c.edges
  packetDegree : 2*2^(S.levelBits c.depth) ≤ Δ
  widthFits : S.levelWidth c.depth ≤ S.levelBits c.depth
  fit : ProofFit S f c

variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ} {c : Call (H (f:=f) (ell:=ell))}

abbrev Selector (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) :=
  ∀ c : Call (H (f:=f) (ell:=ell)), Ready S Δ c →
    PhysicalPacking c.host.network (S.levelBits c.depth) (Fin 64)

noncomputable def defaultSelector (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) : Selector S Δ :=
  fun c d => Classical.choose (host_can_repack c.host (S.levelBits c.depth) Δ
    (Fintype.card_fin 64) d.degree (d.edgeCount.symm ▸ d.collision)
    (d.edgeCount.symm ▸ d.paddedSlots))

def packing (sel : Selector S Δ) (d : Ready S Δ c) :
    PhysicalPacking c.host.network (S.levelBits c.depth) (Fin 64) := sel c d

/-- The valuation is strictly less than the bit-word length on every
positive-multiplicity centre. -/
theorem active_level_lt (d : Ready S Δ c) (t : Center S c) :
    padicValInt 2 t.val < S.levelBits c.depth := by
  have ht := active_order_pos (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t.val t.property
  unfold order at ht
  have hn : S.levelWidth c.depth-padicValInt 2 t.val ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at ht
    omega
  exact (Nat.sub_pos_iff_lt.mp (Nat.pos_of_ne_zero hn)).trans_le d.widthFits

def centerIndex (d : Ready S Δ c) (t : Center S c) : Fin (S.levelBits c.depth) :=
  ⟨padicValInt 2 t.val,active_level_lt d t⟩

theorem centerNonzero (t : Center S c) : t.val ≠ 0 :=
  (active_grid _ _ _ t.property).2

theorem register_positive (d : Ready S Δ c) (t : Center S c) :
    0 < registerPrecision S c t :=
  (Nat.zero_le c.prec).trans_lt
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt d.active))

abbrev SiteMode (sel : Selector S Δ) (d : Ready S Δ c) (t : Center S c) :=
  Mode (centerIndex d t) (registerPrecision S c t) (packing sel d).mask

def siteWeight (sel : Selector S Δ) (d : Ready S Δ c) (t : Center S c) (m : SiteMode sel d t) : ℕ :=
  J6R10RowAffine.weight (centerIndex d t) (registerPrecision S c t) (packing sel d).mask m

theorem siteWeight_pos (sel : Selector S Δ) (d : Ready S Δ c) (t : Center S c) (m : SiteMode sel d t) :
    0 < siteWeight sel d t m := m.order.val.succ_pos

#print axioms defaultSelector
#print axioms active_level_lt
#print axioms centerNonzero
#print axioms register_positive
#print axioms siteWeight_pos
end J6R12Blueprint