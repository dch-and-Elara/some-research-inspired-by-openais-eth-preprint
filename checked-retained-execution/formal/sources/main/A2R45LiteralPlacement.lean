
import A2R45LiteralSlot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 1900
set_option linter.unusedSectionVars false

/-! Instantiate the frozen A2 abstract Placement from the actual same
finite page and slot labels, restricted to the simulated pairs. The
omitted physical positions are precisely actual pinned-zero fillers,
already accounted for by the literal contraction theorem. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial FixedHostAcquisition Acquisition A1R43Literal
open A1R43Literal.General J6R10Repack J6R9Recursive J6R11Integral P11FullPacking

noncomputable section
variable {n a b : ℕ} (W : General.PairPlan (simulated n) a b)
local notation "T" => simulated n
local notation "P" => General.fullPacking T W
local notation "PP" => General.Spare T W

abbrev pair (n : ℕ) := Wire n×Bool

def restrictedPredRel (x y : pair n) : Prop :=
  unitPredecessor P (Sum.inl x) (Sum.inl y)

def restrictedPred (x : pair n) : Option (pair n) :=
  if h : ∃ y,restrictedPredRel W x y then some (Classical.choose h) else none

theorem restrictedPred_exact (x y : pair n) :
    restrictedPred W x=some y ↔ restrictedPredRel W x y := by
  unfold restrictedPred
  split
  · rename_i h
    have ht := Classical.choose_spec h
    constructor
    · intro e
      rwa [←Option.some.inj e]
    · intro e
      exact congrArg some (Sum.inl.inj (unitPredecessor_unique P _ _ _ ht e))
  · rename_i h
    constructor
    · intro e
      cases e
    · intro e
      exact (h ⟨y,e⟩).elim

theorem restricted_odd_predecessor (u : Wire n) :
    restrictedPred W (u,true)=some (u,false) :=
  (restrictedPred_exact W _ _).2 (General.full_seat_predecessor T W u)

theorem real_seat_parity (u : Wire n) (r : Bool) :
    ((P).seat (Sum.inl (u,r))).2.val =
      2*(General.shortSeat T W u).2.val+(if r then 1 else 0) := rfl

theorem restricted_even_predecessor (u v : Wire n) (r : Bool)
    (h : restrictedPred W (u,false)=some (v,r)) : r=true := by
  have e := ((restrictedPred_exact W _ _).1 h).2
  change ((P).seat (Sum.inl (v,r))).2.val+1 =
    ((P).seat (Sum.inl (u,false))).2.val at e
  rw [real_seat_parity W v r,real_seat_parity W u false] at e
  cases r <;> simp at e ⊢
  omega

def actualEarlier (u : Wire n) : Option (Wire n) :=
  (restrictedPred W (u,false)).map Prod.fst

def realPlacement : Placement n (Page (a+1) b (Fin 64)) where
  packet z := ((P).seat (Sum.inl z)).1
  position z := (((P).seat (Sum.inl z)).2.val:ℤ)
  earlier := actualEarlier W
  predecessor := restrictedPred W
  exact_predecessor x y := by
    rw [restrictedPred_exact]
    unfold restrictedPredRel unitPredecessor
    constructor
    · rintro ⟨e,h⟩
      exact ⟨e,by exact_mod_cast h⟩
    · rintro ⟨e,h⟩
      exact ⟨e,by exact_mod_cast h⟩
  odd := restricted_odd_predecessor W
  even u := by
    unfold actualEarlier
    cases e : restrictedPred W (u,false) with
    | none => rfl
    | some p =>
      obtain ⟨i,r⟩ := p
      have h := restricted_even_predecessor W u i r e
      cases h
      rfl

theorem physical_slot_is_abstract_mesh (i : Fin (a+1)) (hi : i.val=0)
    (w : Input n) (f : ℤ[X]) (base p : ℕ)
    (hb : 0<base) (hp : 0<p) (hf : f.Monic) (hd : 0<f.natDegree) :
    (J6R14ZeroMode.polynomial P i (-1) p (file (Pad:=PP) w f base) hf).eval 0 =
      (fixedMeshSlot (K:=Box f 1 p) (2^(a+1)) (realPlacement W) w.enabled) := by
  rw [J6R15PlantedIdentity.zero_eq_parentJet P i (minus_one_mem_grid (a+1))
    (by decide : (-1:ℤ)≠0) (minus_one_odd_index _ i hi) p hp (file w f base) hf]
  rw [physical_parent_is_shifted P w f base p hb hf hd
    (General.full_seat_predecessor T W) (realPlacement W).earlier]
  rw [fixedMeshSlot,pairedMeshRegister_eq _ _ _ (by positivity : 0<(2:ℕ)^(a+1))
    (realPlacement W).packet (realPlacement W).position
    (realPlacement W).earlier (realPlacement W).predecessor
    (realPlacement W).exact_predecessor (realPlacement W).odd (realPlacement W).even]
  rfl

theorem actual_scalar_mesh_decode (w : Input n) (p : ℕ) (hn : 0<n) (hp : n+1<p) :
    (fixedMeshSlot (K:=ZMod (2^p)) (2^(a+1)) (realPlacement W) w.enabled).val =
      count w.enabled :=
  fixedMeshSlot_decode hn _ (by positivity) (realPlacement W) w.enabled hp

#print axioms restrictedPred_exact
#print axioms restricted_odd_predecessor
#print axioms real_seat_parity
#print axioms restricted_even_predecessor
#print axioms realPlacement
#print axioms physical_slot_is_abstract_mesh
#print axioms actual_scalar_mesh_decode
end
end A2R45Literal
