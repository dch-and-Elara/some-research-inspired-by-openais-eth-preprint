import A1R43LiteralGraph
import J6R12RepackBoolean
import J6R11IntegralRetained

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! Literal binary NAND, equality, unary-one and pinned-zero entries.
All table arguments are the true dependent incidence ports of the
bounded-degree physical star graph. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R9Recursive J6R11Integral J6R12Repack J6R10Integral
noncomputable section

variable {V Pad : Type} [DecidableEq V]
variable (F : Finset (V × V))
local notation "N" => network F Pad

def colPort (v : V) (u : {u : Occ F // endpoint F u=v}) :
    ParentPorts N (.inr (.inl v)) :=
  (colPortsEquiv N (.inl v)) ((colFibre F Pad v).symm u)

def dummyColPort (z : Occ F ⊕ Pad) : ParentPorts N (.inr (.inr z)) := by
  refine ⟨.inr (z.elim (oddWire F Pad) Sum.inr),?_⟩
  exact congrArg Sum.inr ((dummy_col_unique F Pad z _).2 rfl)

def tableFlag :
    ∀ v : Row F Pad ⊕ Col F Pad, (ParentPorts N v→Bool) → Bool
  | .inl (.inl e), x =>
      !(x ⟨.inl (oddWire F Pad (e,false)),rfl⟩ &&
        x ⟨.inl (oddWire F Pad (e,true)),rfl⟩)
  | .inl (.inr _), _ => true
  | .inr (.inl v), x =>
      decide (∀ u u' : {u : Occ F // endpoint F u=v}, x (colPort F v u)=x (colPort F v u'))
  | .inr (.inr z), x => !(x (dummyColPort F z))

def file (f : ℤ[X]) (p : ℕ) : EntryFile f 1 N :=
  fun v=>⟨p,fun x=>if tableFlag F v x then 1 else 0⟩

theorem file_creation (f : ℤ[X]) (p : ℕ) (v : Row F Pad ⊕ Col F Pad) :
    (file F f p v).created=p := rfl

def rowFlag (y : Wire F Pad→Bool) (v : Row F Pad) : Bool :=
  tableFlag F (.inl v) (assignment N y (.inl v))

def colFlag (x : Wire F Pad→Bool) (v : Col F Pad) : Bool :=
  tableFlag F (.inr v) (assignment N x (.inr v))

theorem row_NAND (y : Wire F Pad→Bool) (e : F) :
    rowFlag F y (.inl e) =
      !(y (oddWire F Pad (e,false)) && y (oddWire F Pad (e,true))) := rfl

theorem row_dummy (y : Wire F Pad→Bool) (z : Occ F⊕Pad) :
    rowFlag F y (.inr z)=true := rfl

theorem col_eq (x : Wire F Pad→Bool) (v : V) :
    colFlag F x (.inl v)=true ↔
      ∀ u u' : {u : Occ F // endpoint F u=v},
        x (evenWire F Pad u.val)=x (evenWire F Pad u'.val) := by
  change decide (∀ u u' : {u : Occ F // endpoint F u=v},
    x (evenWire F Pad u.val)=x (evenWire F Pad u'.val))=true ↔ _
  rw [decide_eq_true_eq]

theorem col_dummy (x : Wire F Pad→Bool) (z : Occ F⊕Pad) :
    colFlag F x (.inr z)=true ↔ x (z.elim (oddWire F Pad) Sum.inr)=false := by
  change (! x (z.elim (oddWire F Pad) Sum.inr))=true ↔ _
  simp

def spin {R : Type*} [Zero R] [One R] (b : Bool) : R :=
  if b then 1 else 0

theorem file_frozen (f : ℤ[X]) (p : ℕ) (hp : 0<p) (hf : f.Monic) (hF : 0<f.natDegree)
    (v : Row F Pad⊕Col F Pad) (x : ParentPorts N v→Bool) :
    (file F f p v).frozen hf x=spin (tableFlag F v x) := by
  unfold file CreatedEntry.frozen spin
  exact canonical_lift_bool p hp f hf hF 1 (by decide) _

variable [Fintype V] [Fintype Pad]

omit [Fintype V] in
theorem rowProduct_receives (f : ℤ[X]) (base p : ℕ) (hbase : 0<base)
    (hf : f.Monic) (hF : 0<f.natDegree) (y : Wire F Pad→Bool) :
    reduce p f 1 (rowProduct N (file F f base) hf y) =
      ∏ r : Row F Pad, (spin (rowFlag F y r) : Box f 1 p) := by
  rw [rowProduct,map_prod]
  apply Finset.prod_congr rfl
  intro r _
  rw [file_frozen F f base hbase hf hF]
  change reduce p f 1 (spin (rowFlag F y r))=spin (rowFlag F y r)
  cases rowFlag F y r
  · exact map_zero _
  · exact map_one _

theorem colProduct_receives (f : ℤ[X]) (base p : ℕ) (hbase : 0<base)
    (hf : f.Monic) (hF : 0<f.natDegree) (x : Wire F Pad→Bool) :
    reduce p f 1 (colProduct N (file F f base) hf x) =
      ∏ r : Col F Pad, (spin (colFlag F x r) : Box f 1 p) := by
  rw [colProduct,map_prod]
  apply Finset.prod_congr rfl
  intro r _
  rw [file_frozen F f base hbase hf hF]
  change reduce p f 1 (spin (colFlag F x r))=spin (colFlag F x r)
  cases colFlag F x r
  · exact map_zero _
  · exact map_one _

#print axioms file_creation
#print axioms row_NAND
#print axioms row_dummy
#print axioms col_eq
#print axioms col_dummy
#print axioms file_frozen
#print axioms rowProduct_receives
#print axioms colProduct_receives

end
end A1R43Literal
