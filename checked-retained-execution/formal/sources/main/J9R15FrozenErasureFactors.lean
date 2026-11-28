import J9R15FrozenErasureTables
import J6R10IntegralFinite

/-! Factor the exact retained packed file by untouched original owners.
Unprotected tables use only their own real endpoints, not a tail callback. -/
namespace J9R15FrozenErasure
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J6R14SpecializedBox
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube

noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

variable {A Pair Row Col W : Type} [LinearOrder A]
variable [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W → Row) (col : W → OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2) (state : DState A Pair Row Col t)
variable (seat : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (J7SeatPacking.balancedMask (t+1) b) (seat w)
  = wordLabel row col state w)

local notation "E" => Wire Pair W
local notation "V" => Pin Pair ⊕ OrdinaryColumn Pair Col
local notation "N" => J7R13.network row col
local notation "D" => physicalLayout row col two state seat preserve
local notation "D'" => nativeSeats (fun e => seat e) (fun e => seat e)
local notation "old" => cloneHosts (Pair:=Pair) (Col:=Col)
local notation "OWN" => seatOwner col seat
variable {n : ℤ}
local notation "K" => kept D' old OWN n
local notation "PR" => protectedOwner D' old OWN n
local notation "SEL" => select col seat (n:=n)

theorem protected_has_owner (u : FreeOwner D' old OWN n) : ∃ v : V, SEL v=some u := by
  letI : DecidableEq (Option V) := Classical.decEq _
  obtain ⟨p,hp⟩ := (mem_cloneHosts_iff u.val).mp (Finset.mem_sdiff.mp u.property).1
  refine ⟨.inr (.inl p),?_⟩
  unfold select
  rw [dif_pos (hp ▸ u.property)]
  exact congrArg some (Subtype.ext hp.symm)

theorem protected_owner_iff {u : FreeOwner D' old OWN n} {v : V}
    (hv : SEL v=some u) (e : E) : PR e=some u ↔ colNode col e=v := by
  rw [protected_select]
  exact ⟨fun he => select_inj col seat he hv,fun he => he.symm ▸ hv⟩

theorem unlift_untouched_reads (F : J8Physical.OldTables D) (sign : Pin Pair → Bool)
    (v : V) (hv : SEL v=none) (X : E → Bool) :
    rawFlag row col two state seat preserve F sign (.inr v) (unlift PR (restrict PR X)) =
      rawFlag row col two state seat preserve F sign (.inr v) X := by
  apply colFlag_congr
  intro e he
  have hn : PR e=none := by rw [protected_select,he,hv]
  simp [unlift,hn,restrict]

/-- Accept an arbitrary syntax for the original clone gates if, on their
own local port cube, they are exactly the pure common-bit truth table. -/
def CloneTruth (F : J8Physical.OldTables D) : Prop :=
  ∀ (p : Pin Pair) (x : Ports col (.inl p) → Bool),
    (LiteralPortCompiler.truth (F ((D).colLabel (.inl p)) ⟨.inl p,rfl⟩) x:ℕ) =
      if ∀ u v, x u=x v then 1 else 0

theorem canonical_clone_truth (F : J8Physical.OldTables D) :
    CloneTruth row col two state seat preserve (canonicalOld row col two state seat preserve F) := by
  intro p x
  exact canon_exact_eq row col two state seat preserve F p x (R:=ℕ)

theorem clone_raw_iff (F : J8Physical.OldTables D) (hF : CloneTruth row col two state seat preserve F)
    (sign : Pin Pair → Bool) (p : Pin Pair) (X : E → Bool) :
    rawFlag row col two state seat preserve F sign (.inr (.inr (.inl p))) X = true ↔
      ∀ e e', colNode col e=.inr (.inl p) → colNode col e'=.inr (.inl p) → X e=X e' := by
  let ER := rowWire (Pair:=Pair) row two
  let u : Ports col (.inl p) → Bool := fun i => X (ER (J8Physical.ordinaryWire D ⟨.inl p,i⟩))
  have hh : ∀ i : Ports col (.inl p), ER (J8Physical.ordinaryWire D ⟨.inl p,i⟩)=i.val := by
    intro i
    change ER ((ER.trans (colWire col).symm).symm (.inr ⟨.inl p,i⟩))=_
    simp only [Equiv.symm_trans_apply,Equiv.apply_symm_apply]
    rfl
  have hl := hF p u
  have hiff : (∀ i j : Ports col (.inl p), X i.val=X j.val) ↔
      ∀ e e', colNode col e=.inr (.inl p) → colNode col e'=.inr (.inl p) → X e=X e' :=
    ⟨fun h e e' he he' => h ⟨e,he⟩ ⟨e',he'⟩,fun h i j => h i.val j.val i.property j.property⟩
  change ((if rawFlag row col two state seat preserve F sign (.inr (.inr (.inl p))) X
    then 1 else 0):ℕ) = _ at hl
  simp only [u,hh] at hl
  by_cases h : ∀ i j : Ports col (.inl p), X i.val=X j.val
  · rw [if_pos h] at hl
    have hr : rawFlag row col two state seat preserve F sign (.inr (.inr (.inl p))) X = true := by
      by_contra hn
      simp [hn] at hl
    exact ⟨fun _ => hiff.mp h,fun _ => hr⟩
  · rw [if_neg h] at hl
    exact ⟨fun hr => by simp [hr] at hl,fun hs => (h (hiff.mpr hs)).elim⟩

def restValid (F : J8Physical.OldTables D) (sign : Pin Pair → Bool)
    (Y : E → Bool) (X : Rest PR → Bool) : Prop :=
  (∀ r : Subdivision Pair Row, rawFlag row col two state seat preserve F sign (.inl r) Y=true) ∧
    ∀ v : V, SEL v=none  → 
      rawFlag row col two state seat preserve F sign (.inr v) (unlift PR X)=true

def restWeight (F : J8Physical.OldTables D) (sign : Pin Pair → Bool)
    (Y : E → Bool) (X : Rest PR → Bool) : TwoLocal :=
  if restValid row col two state seat preserve (n:=n) F sign Y X then 1 else 0

theorem split_flags (F : J8Physical.OldTables D) (hF : CloneTruth row col two state seat preserve F)
    (sign : Pin Pair → Bool) (Y X : E → Bool) :
    ((∀ r : Subdivision Pair Row, rawFlag row col two state seat preserve F sign (.inl r) Y=true) ∧
      ∀ v : V, rawFlag row col two state seat preserve F sign (.inr v) X=true) ↔
      Tied PR X ∧ restValid row col two state seat preserve F sign Y (restrict PR X) := by
  constructor
  · rintro ⟨hrow,hcol⟩
    refine ⟨?_,hrow,?_⟩
    · intro u e e' he he'
      obtain ⟨v,hv⟩ := protected_has_owner col seat u
      obtain ⟨p,rfl⟩ := selected_clone col seat hv
      exact (clone_raw_iff row col two state seat preserve F hF sign p X).mp (hcol _)
        e e' ((protected_owner_iff col seat hv e).mp he) ((protected_owner_iff col seat hv e').mp he')
    · intro v hv
      rw [unlift_untouched_reads row col two state seat preserve F sign v hv]
      exact hcol v
  · rintro ⟨hTie,hrow,hRest⟩
    refine ⟨hrow,fun v => ?_⟩
    cases hv : SEL v with
    | none =>
      exact (unlift_untouched_reads row col two state seat preserve F sign v hv X) ▸ hRest v hv
    | some u =>
      obtain ⟨p,rfl⟩ := selected_clone col seat hv
      apply (clone_raw_iff row col two state seat preserve F hF sign p X).mpr
      intro e e' he he'
      exact hTie u e e' ((protected_owner_iff col seat hv e).mpr he) ((protected_owner_iff col seat hv e').mpr he')

private theorem prod_flags {R I : Type*} [CommRing R] [Fintype I] (p : I → Prop) [∀ i,Decidable (p i)] [Decidable (∀ i,p i)] :
    (∏ i : I, if p i then (1:R) else 0) = if ∀ i, p i then 1 else 0 := by
  by_cases h : ∀ i, p i
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i _ => if_pos (h i))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem mul_flags {R : Type*} [CommRing R] (p q : Prop) [Decidable p] [Decidable q] [Decidable (p ∧ q)] :
    (if p then (1:R) else 0)*(if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

theorem frozen_factors (F : J8Physical.OldTables D) (hF : CloneTruth row col two state seat preserve F)
    (sign : Pin Pair → Bool) (f : ℤ[X]) (ell p₀ p : ℕ)
    (hf : f.Monic) (hp₀ : 0<p₀) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (Y X : E → Bool) :
    let file := sameSeatFile row col two state seat preserve f ell p₀ F sign
    reduce p f ell (rowProduct N file hf Y) * reduce p f ell (colProduct N file hf X) =
      guardWeight PR X * J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f ell)
        (restWeight row col two state seat preserve (n:=n) F sign Y (restrict PR X)) := by
  dsimp only
  rw [rowProduct,colProduct,map_prod,map_prod]
  simp_rw [frozen_flag row col two state seat preserve F sign f ell p₀ hf hp₀ hd hℓ,apply_ite,map_one,map_zero]
  rw [prod_flags (fun r : Subdivision Pair Row => rawFlag row col two state seat preserve F sign (.inl r) Y=true),
    prod_flags (fun v : V => rawFlag row col two state seat preserve F sign (.inr v) X=true),
    guard_weight,restWeight,apply_ite (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f ell)),map_one,map_zero,mul_flags,mul_flags]
  have h := split_flags row col two state seat preserve (n:=n) F hF sign Y X
  by_cases hh : Tied PR X ∧ restValid row col two state seat preserve F sign Y (restrict PR X)
  · rw [if_pos (h.mpr hh),if_pos hh]
  · rw [if_neg (fun h' => hh (h.mp h')),if_neg hh]

#print axioms protected_has_owner
#print axioms protected_owner_iff
#print axioms unlift_untouched_reads
#print axioms canonical_clone_truth
#print axioms clone_raw_iff
#print axioms split_flags
#print axioms frozen_factors

end
end J9R15FrozenErasure
