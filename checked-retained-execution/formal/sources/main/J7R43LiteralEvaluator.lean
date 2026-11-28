import J7R43LiteralMoment
import J7R43LiteralBaseline
import J7R43LiteralNoDivision

/-! One true selected group at zeta=0 equals its wholly integral local
column evaluator: the two row rails are summed through their literal
equality truth tables, not by accessing or multiplying other children. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral J6R11Integral
open J6R9PacketScopes J6R9PacketChild J6R10PacketAssembly J6R10RowAffine
open J8Physical J8J9Grouped J6R14SpecializedBox NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

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
local notation "T" => LiteralPortCompiler.truth
local notation "aff" => LiteralPortCompiler.affine
local notation "E" => groupedPhysicalStateEquiv d mask i hr hc

variable (hL : 0<(2^a:ℕ))

set_option maxHeartbeats 3800000 in
include hr hc hrow hpin hold hc0 hf0 hell hL in
theorem physical_baseline_no_division (ht : (L:ℤ)-1≠0) (hv : padicValInt 2 ((L:ℤ)-1)=i.val) (g : G) :
    reduce p f ell (actualChildTruth Q i ht hv p 0 file hf 0 g) =
      (integerBaseline d e even F g : D) := by
  have h := seated_baseline_integer d mask wordsR wordsC hC hB i hr hc hrow hpin hold
    p created F sign hf hc0 hf0 hell e even ht hv g
  have hI := literal_baseline_no_division d e even hL F sign g
  have hDec : (fun x y : G => Classical.propDecidable (x=y)) =
      (fun x y : G => LinearOrder.toDecidableEq x y) := Subsingleton.elim _ _
  rw [hDec] at hI
  exact h.trans (congrArg (fun n : ℤ => (n:D)) hI)

set_option maxHeartbeats 4300000 in
include hrow hpin hold hc0 hf0 hell hL in
theorem physical_source_no_division (hi : i.val=0)
    (ht : (L:ℤ)-1≠0) (hv : padicValInt 2 ((L:ℤ)-1)=i.val)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (n : Fin (Fintype.card (PinTile d s))) (hn : n.val<p-1)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true) :
    let m := anchoredMode d mask i hr hc s off (⟨n.val,hn⟩ : Fin (p-1))
    reduce p f ell (actualChildTruth Q i ht hv p 0 file hf (Finsupp.single m 1) (d.pinLabel s)) =
      (integerSourceEvaluation d e even F sign s n.val : D) := by
  have h := seated_singleton_integer d mask wordsR wordsC hC hB i hr hc hrow hpin hold p created
    F sign hf hc0 hf0 hell e even hi ht hv s off n hn
  have hI := literal_source_no_division d e even hL F sign s n sat
  have hDec : (fun x y : G => Classical.propDecidable (x=y)) =
      (fun x y : G => LinearOrder.toDecidableEq x y) := Subsingleton.elim _ _
  rw [hDec] at hI
  exact h.trans (congrArg (fun n : ℤ => (n:D)) hI)

#print axioms physical_baseline_no_division
#print axioms physical_source_no_division
end
end J7R43Literal