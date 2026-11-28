import J7R43LiteralIntegral

/-! A genuine physical (page, parity) tile supplies its singleton source
moment. The same ordinary-column coordinates and the same unary pins
occur in the already-audited J8 and J9 pose, but no derivative or
completed product is needed here. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6R9PacketChild
open J8Physical J8J9Grouped J6R14SpecializedBox NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

section State
variable {E A B G K : Type*} [Fintype E] [LinearOrder G] [Fintype G] [CommRing K]
variable {a : ℕ} {N : Network E A B} (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ)

theorem read_source_moment_as_global (m : Mode i p P.mask) {g : G}
    (hm : source P.mask i m=g) (v : PhysicalState P i g) (X : E→Bool)
    (hx : ∀ q : {q : E // colGroup P.mask i (P.seat q)=g}, X q.val = v.2 q) :
    (stateMoment P i g p v m : K) = moment (fun e => P.seat e) P.mask i m (fun q => X q.val) := by
  subst g
  rw [stateMoment,dif_pos rfl]
  dsimp only
  congr 1
  funext q
  exact (hx q).symm
end State

variable {G R S V : Type} [LinearOrder G] {U : V→Type} {a b : ℕ}
variable (d : Layout (Page a b G) R S V G U (2^a))
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [∀ v, Fintype (U v)]
variable (mask : MaskFamily a b G)
variable (wordsR : R→Fin a→G) (wordsC : S⊕V→Fin a→G)
variable (hC : ∀ w : Wire R, physicalCell mask (d.seat w) =
  declaredCell (orientedNetwork d) wordsR wordsC w)
variable (hB : Nat.card (Cell (Fin a) G) * (b*2^a) ≤ 3*Nat.card (Wire R))
local notation "Q" => (seatedParentPacking d mask wordsR wordsC hC hB)
variable (i : Fin a)
variable (hr : ∀ w, rowGroup mask i (d.seat w)=d.rowLabel w.1)
variable (hc : ∀ w, colGroup mask i (d.seat w)=actualColLabel d w)
variable (hrow : ∀ r, wordsR r i=d.rowLabel r)
variable (hpin : ∀ s, wordsC (.inl s) i=d.pinLabel s)
variable (hold : ∀ v, wordsC (.inr v) i=d.colLabel v)
variable {f : ℤ[X]} {ell : ℕ}
variable (p created : ℕ) (F : OldTables d) (sign : S→Bool)
variable (hf : f.Monic) (hc0 : 0<created) (hf0 : 0<f.natDegree) (hell : 0<ell)
variable (e : EndpointSeating d) (even : Even (2^a))
local notation "D" => Box f ell p
local notation "file" => orientedEntryFile d f ell created F sign
local notation "L" => (2^a : ℕ)
local notation "E" => groupedPhysicalStateEquiv d mask i hr hc

set_option maxHeartbeats 4600000 in
theorem zero_moment_uses_actual_tile (hi : i.val=0) (s : S)
    (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (Fintype.card (PinTile d s))) (hn : n.val<p-1)
    (v : PhysicalState Q i (d.pinLabel s)) :
    let m := anchoredMode d mask i hr hc s off (⟨n.val,hn⟩ : Fin (p-1))
    stateMoment Q i (d.pinLabel s) p v m = (feature d s n (E (d.pinLabel s) v).2 : D) := by
  let m := anchoredMode d mask i hr hc s off (⟨n.val,hn⟩ : Fin (p-1))
  let X := extendCol d mask i (d.pinLabel s) v.2
  have hsource : source mask i m=d.pinLabel s := anchored_source d mask i hr hc s off _
  have hread := read_source_moment_as_global (K:=D) Q i p m hsource v X
    (fun q => extendCol_at d mask i (d.pinLabel s) v.2 q.val q.prop)
  change stateMoment Q i (d.pinLabel s) p v m = _
  rw [hread]
  have hmoment := actual_tile_moment_box d mask i hr hc hi p ell f (0:Scalar p f) s off X n hn
  dsimp only at hmoment
  calc
    _ = _ := hmoment
    _ = _ := by
      apply evalBox_int_const p
      rw [Polynomial.coeff_C_zero]
      exact (feature_cast d s n _).symm

set_option maxHeartbeats 4400000 in
include hrow hpin hold hc0 hf0 hell in
theorem seated_singleton_integer (hi : i.val=0)
    (ht : (L:ℤ)-1≠0) (hv : padicValInt 2 ((L:ℤ)-1)=i.val) (s : S)
    (off : d.rowLabel (pinWire d s).1 ≠ d.pinLabel s)
    (n : Fin (Fintype.card (PinTile d s))) (hn : n.val<p-1) :
    let m := anchoredMode d mask i hr hc s off (⟨n.val,hn⟩ : Fin (p-1))
    reduce p f ell (actualChildTruth Q i ht hv p 0 file hf (Finsupp.single m 1) (d.pinLabel s)) =
      (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s n) : D) := by
  let m := anchoredMode d mask i hr hc s off (⟨n.val,hn⟩ : Fin (p-1))
  have hs : source mask i m=d.pinLabel s := anchored_source d mask i hr hc s off _
  have hchild (g : G) (hg : source mask i m=g) :
      reduce p f ell (actualChildTruth Q i ht hv p 0 file hf (Finsupp.single m 1) g) =
        ∑ v : PhysicalState Q i g,
          actualBaselineWeight Q i (t:=(L:ℤ)-1) p (0:D) file hf g v * stateMoment Q i g p v m := by
    subst g
    apply (literal_singleton_child Q i p (0:D) file hf ht hv m).trans
    exact sum_univ_congr_instance _ _ _ _ (fun _ => rfl)
  have H := baselineFeature_exact d mask wordsR wordsC hC hB i hr hc hrow hpin hold p created
    F sign hf hc0 hf0 hell e even (d.pinLabel s) (feature d s n)
  apply (hchild _ hs).trans
  symm
  apply H.symm.trans
  apply sum_univ_congr_instance
  intro v
  rw [zero_moment_uses_actual_tile d mask wordsR wordsC hC hB i hr hc p hi s off n hn]
#print axioms read_source_moment_as_global
#print axioms zero_moment_uses_actual_tile
#print axioms seated_singleton_integer
end
end J7R43Literal