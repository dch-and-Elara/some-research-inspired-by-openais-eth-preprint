import J6R11Collision
import J6R10RepackRounded

/-!
# Physical reindexing and unconditional label choice for active repacking

The collision sample stores a pair of complete vertex words. The
released R10 packing stores one ordered pair per coordinate.
This is a literal bijection, preserving every fibre and the entire
variance score. The packing follows from the source's numeric
collision and slot assumptions, not a supplied variance witness.
-/

open scoped BigOperators Classical

namespace J6R11CollisionReindex
open J6R11Collision J6R10Repack P11FullPacking J1MainSourceCollision
noncomputable section

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ}

def pairedWords (a : ℕ) (G : Type*) :
    ((Fin a→G)×(Fin a→G)) ≃ Cell (Fin a) G where
  toFun p := fun i => (p.1 i,p.2 i)
  invFun c := (fun i => (c i).1,fun i => (c i).2)
  left_inv p := by cases p; rfl
  right_inv p := by
    funext i
    exact Prod.ext rfl rfl

theorem card_filter_fibre {S : Type*} (ends : E → S) (v : S) :
    (fibre ends v).card=Nat.card {e : E // ends e=v} := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

theorem card_fibre_load {S : Type*} (label : E → S) (c : S) :
    (Nat.card {e : E // label e=c}:ℚ)=load label c := by
  classical
  rw [← card_filter_fibre, fibre,Finset.card_filter,Nat.cast_sum]
  unfold load indicator
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : label e=c <;> simp [h]

omit [Fintype A] [Fintype B] [LinearOrder G] in
theorem declared_variance_eq (N : Network E A B)
    (z : Sample A B (Fin a→G)) :
    varianceScore (declaredCell N z.1 z.2)=deviation (edgeCell N.row N.col z) := by
  let f := pairedWords a G
  have hc : Nat.card (Cell (Fin a) G)=Fintype.card ((Fin a→G)×(Fin a→G)) := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_congr f).symm
  have hd (c : (Fin a→G)×(Fin a→G)) :
      load (declaredCell N z.1 z.2) (f c)=load (edgeCell N.row N.col z) c := by
    unfold load
    apply Finset.sum_congr rfl
    intro e _
    change indicator (f (edgeCell N.row N.col z e)=f c)=_
    rw [Equiv.apply_eq_iff_eq]
  unfold varianceScore
  rw [← Equiv.sum_comp f]
  simp only [card_fibre_load,Nat.card_eq_fintype_card (α:=E),hc,hd]
  rfl

omit [LinearOrder G] in
/-- With actual per-vertex indexed degree bounds, score existence
is proved in precisely the physical declaredCell interface. -/
theorem declared_variance_witness (N : Network E A B) (Δ : ℕ) [Nonempty G]
    (hr : ∀ v, Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e=v}≤Δ) :
    ∃ rowLabel : A→Fin a→G, ∃ colLabel : B→Fin a→G,
      varianceScore (declaredCell N rowLabel colLabel)≤2*(Nat.card E:ℚ)*Δ := by
  have hra : ∀ v, (fibre N.row v).card≤Δ := fun v => (card_filter_fibre N.row v).trans_le (hr v)
  have hcb : ∀ v, (fibre N.col v).card≤Δ := fun v => (card_filter_fibre N.col v).trans_le (hc v)
  obtain ⟨z,hz⟩ := exists_labeling (A:=Fin a→G) N.row N.col Δ hra hcb
  refine ⟨z.1,z.2,?_⟩
  rw [declared_variance_eq N z,Nat.card_eq_fintype_card]
  exact hz

/-- Every such active child graph admits the actual new physical
packing, with the original quotient's rounded height and no external
label-existence or variance hypothesis. -/
theorem child_simple_exists_Pack (N : Network E A B) (Δ : ℕ)
    (hG : Fintype.card G=64)
    (hr : ∀ v, Nat.card {e : E // N.row e=v}≤Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e=v}≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card E) :
    ∃ P : PhysicalPacking N a G,
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) := by
  letI : Nonempty G := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨rl,cl,hvar⟩ := declared_variance_witness (G:=G) (a:=a) N Δ hr hc
  obtain ⟨p,hrl,hcl,hp⟩ := actual_rounded_packing N hG rl cl Δ hvar hcollision hslots
  exact ⟨p,by rw [hrl,hcl,hp]⟩

#print axioms card_filter_fibre
#print axioms card_fibre_load
#print axioms declared_variance_eq
#print axioms declared_variance_witness
#print axioms child_simple_exists_Pack

end
end J6R11CollisionReindex

