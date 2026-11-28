import J7R43LiteralIntegral

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

/- Integer image of the true, separately compiled baseline slot. -/
set_option maxHeartbeats 2000000 in
include hr hc hrow hpin hold hc0 hf0 hell in
theorem seated_baseline_integer (ht : (L:ℤ)-1≠0) (hv : padicValInt 2 ((L:ℤ)-1)=i.val) (g : G) :
    reduce p f ell (actualChildTruth Q i ht hv p 0 file hf 0 g) =
      (J8J9Grouped.child d e even F sign g none (fun _ => 1) : D) := by
  let m : Assignment d g → ℤ := fun _ => 1
  let f0 : PhysicalState Q i g → D :=
    actualBaselineWeight Q i (t:=(L:ℤ)-1) p (0:D) file hf g
  have h₁ := literal_baseline_child Q i p (0:D) file hf ht hv g
  have h₂ := baselineFeature_exact d mask wordsR wordsC hC hB i hr hc hrow hpin hold p created
    F sign hf hc0 hf0 hell e even g m
  apply h₁.trans
  symm
  apply h₂.symm.trans
  apply sum_univ_congr_instance
  intro v
  change f0 v * ((1:ℤ):D) = f0 v
  rw [Int.cast_one,mul_one]
#print axioms seated_baseline_integer
end
end J7R43Literal