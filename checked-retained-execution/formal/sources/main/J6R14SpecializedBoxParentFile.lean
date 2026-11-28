import J6R14SpecializedBoxFactors
import J6R12RepackBoolean

/-! Construct the original J7/J8-oriented parent EntryFile from its
actual incidences, rather than try to identify this opposite
orientation with the Boolean J6 Plant specialization. The original
subdivision is a row; each old clause or unary pin is a column.
Theorems are pointwise at the same physical wire assignments and at
the immutably tagged creation precision. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial J6R9Recursive J6R10Repack
open J8Physical J8EndToEnd LiteralPortCompiler

noncomputable section
variable {Packet R S V G : Type} {P : V → Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def orientedNetwork : Network (Wire R) R (S⊕V) where
  row := Prod.fst
  col := colOwner d

def rowIncidence (r : R) (b : Bool) : ParentPorts (orientedNetwork d) (.inl r) :=
  ⟨.inl (r,b),rfl⟩

def pinIncidence (p : S) : ParentPorts (orientedNetwork d) (.inr (.inl p)) :=
  ⟨.inr (pinWire d p),by simp [owner,orientedNetwork,colOwner]⟩

def oldIncidence (v : V) (i : P v) : ParentPorts (orientedNetwork d) (.inr (.inr v)) :=
  ⟨.inr (ordinaryWire d ⟨v,i⟩),by simp [owner,orientedNetwork,colOwner]⟩

def orientedFlag (F : OldTables d) (sign : S→Bool)
    (v : R⊕(S⊕V)) (y : ParentPorts (orientedNetwork d) v→Bool) : Bool :=
  match v with
  | .inl r => decide (y (rowIncidence d r false) = y (rowIncidence d r true))
  | .inr (.inl p) => decide (y (pinIncidence d p) = sign p)
  | .inr (.inr v) => satisfied (F (d.colLabel v) ⟨v,rfl⟩) (fun i => y (oldIncidence d v i))

def orientedEntryFile (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool) :
    EntryFile f ell (orientedNetwork d) :=
  fun v => ⟨p,fun y => if orientedFlag d F sign v y then 1 else 0⟩

theorem oriented_creation_tag (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (v : R⊕(S⊕V)) :
    (orientedEntryFile d f ell p F sign v).created = p := rfl

theorem oriented_entry_read (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (v : R⊕(S⊕V)) (y : ParentPorts (orientedNetwork d) v→Bool) :
    (orientedEntryFile d f ell p F sign v).read hf p y =
      if orientedFlag d F sign v y then 1 else 0 :=
  (orientedEntryFile d f ell p F sign v).read_created hf y

theorem oriented_row_truth (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (x : Wire R→Bool) (r : R) :
    (orientedEntryFile d f ell p F sign (.inl r)).frozen hf
      (assignment (orientedNetwork d) x (.inl r)) =
       (truth (equality false true) (fun b => x (r,b)) : IntRing f ell) := by
  rw [truth_equality]
  change canonicalLift p f hf ell (if decide (x (r,false)=x (r,true)) then 1 else 0) = _
  simp only [decide_eq_true_eq]
  by_cases h : x (r,false)=x (r,true)
  · simp only [if_pos h,J6R12Repack.canonical_lift_one p hp f hf hF ell hℓ]
  · simp only [if_neg h,J6R12Repack.canonical_lift_zero]

theorem oriented_pin_truth (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (x : Wire R→Bool) (g : G) (s : LocalPin d g) :
    (orientedEntryFile d f ell p F sign (.inr (.inl s.val))).frozen hf
      (assignment (orientedNetwork d) x (.inr (.inl s.val))) =
       (truth (pin s (sign s.val)) (fun i : LocalPin d g => x (pinWire d i.val)) : IntRing f ell) := by
  rw [truth_pin]
  change canonicalLift p f hf ell (if decide (x (pinWire d s.val)=sign s.val) then 1 else 0) = _
  simp only [decide_eq_true_eq]
  by_cases h : x (pinWire d s.val)=sign s.val
  · simp only [if_pos h,J6R12Repack.canonical_lift_one p hp f hf hF ell hℓ]
  · simp only [if_neg h,J6R12Repack.canonical_lift_zero]

theorem oriented_old_truth (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (x : Wire R→Bool) (g : G) (v : LocalColumn d g) :
    (orientedEntryFile d f ell p F sign (.inr (.inr v.val))).frozen hf
      (assignment (orientedNetwork d) x (.inr (.inr v.val))) =
      (truth (F g v) (fun i : P v.val => x (ordinaryWire d ⟨v.val,i⟩)) : IntRing f ell) := by
  rcases v with ⟨v,hv⟩
  subst g
  exact J6R12Repack.canonical_lift_bool p hp f hf hF ell hℓ _

#print axioms orientedEntryFile
#print axioms oriented_creation_tag
#print axioms oriented_entry_read
#print axioms oriented_row_truth
#print axioms oriented_pin_truth
#print axioms oriented_old_truth
end
end J6R14SpecializedBox
