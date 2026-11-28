import J7PrintedParamsLiteral
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort

/-! # Deterministic literal triangle replacement and the exterior matching -/
open scoped BigOperators

namespace J7LiteralGraph
open J7SourceLabels

variable {V : Type*} [LinearOrder V] (H : SimpleGraph V)

abbrev Edge (H : SimpleGraph V) := {e : V × V // e.1 < e.2 ∧ H.Adj e.1 e.2}

abbrev Half (H : SimpleGraph V) := Σ v : V, {w : V // H.Adj v w}

def orientLeg : Edge H × Bool → Half H
  | (e, false) => ⟨e.val.1, ⟨e.val.2,e.prop.2⟩⟩
  | (e, true) => ⟨e.val.2, ⟨e.val.1,H.symm e.prop.2⟩⟩

def unorientLeg : Half H → Edge H × Bool
  | ⟨v,⟨w,h⟩⟩ =>
    if hp : v < w then (⟨(v,w),hp,h⟩,false) else
      (⟨(w,v),lt_of_le_of_ne (le_of_not_gt hp) (H.ne_of_adj h).symm,H.symm h⟩,true)

/-- Sort the two distinct endpoints by the supplied vertex order. Exactly
one original edge and one of its two sides accounts for each half-edge. -/
def orientChart : Edge H × Bool ≃ Half H where
  toFun := orientLeg H
  invFun := unorientLeg H
  left_inv := by
    rintro ⟨⟨⟨v,w⟩,h,j⟩,b⟩
    cases b
    · simp [orientLeg,unorientLeg,h]
    · simp [orientLeg,unorientLeg,not_lt_of_ge h.le]
  right_inv := by
    rintro ⟨v,⟨w,h⟩⟩
    by_cases hp : v < w <;> simp [orientLeg,unorientLeg,hp]

def finSide : Bool ≃ Fin 2 :=
  ⟨fun b => if b then 1 else 0,fun i => decide (i=1),by decide,by decide⟩

def finPort : Option Bool ≃ Fin 3 :=
  ⟨fun b => match b with | none => 0 | some false => 1 | some true => 2,
    fun i => if i=0 then none else some (decide (i=2)), by decide,by decide⟩

def rot : Equiv.Perm (Fin 3) :=
  ⟨fun j => j+1,fun j => j-1,by decide,by decide⟩

def toggle (b : Bool) : Equiv.Perm (V × Fin 3) :=
  if b then Equiv.prodCongr (Equiv.refl V) rot else Equiv.refl _

/-- An exterior edge is a pre-existing base edge. An internal edge is
one of the three consecutive edges in a particular vertex cloud. -/
abbrev TEdge (H : SimpleGraph V) := Edge H ⊕ (V × Fin 3)

variable [Fintype V] [DecidableRel H.Adj]

def neighbors (v : V) : Finset V := Finset.univ.filter (H.Adj v)

def Cubic : Prop := ∀ v, (neighbors H v).card = 3

def neighborChart (cubic : Cubic H) (v : V) :
    {w : V // H.Adj v w} ≃ Fin 3 :=
  (Equiv.subtypeEquivRight (fun w => by simp [neighbors])).trans
    ((neighbors H v).orderIsoOfFin (cubic v)).symm.toEquiv

/-- First sort the neighbors inside each vertex, then place them in
the three literal vertices of its triangle. No mysterious atlas input
or input tensor sign is used by this definition. -/
def pinToTriangle (cubic : Cubic H) : Pin (Edge H) ≃ V × Fin 3 :=
  (Equiv.prodCongr (Equiv.refl _) finSide.symm).trans
    ((orientChart H).trans
      ((Equiv.sigmaCongrRight (neighborChart H cubic)).trans (Equiv.sigmaEquivProd V (Fin 3))))

def flagAtlas (cubic : Cubic H) : TEdge H × Bool ≃ Pin (Edge H) × Option Bool where
  toFun x := match x with
    | (.inl e, b) => ((e,finSide b), none)
    | (.inr q, b) => ((pinToTriangle H cubic).symm (toggle b q),some b)
  invFun x := match x with
    | (e, none) => (.inl e.1,finSide.symm e.2)
    | (p, some b) => (.inr ((toggle b).symm (pinToTriangle H cubic p)),b)
  left_inv := by rintro ⟨e|q,b⟩ <;> simp
  right_inv := by rintro ⟨⟨e,k⟩,b⟩; cases b <;> simp

/-- The actual cubic incidence atlas consumed by the v9 four-clone compiler. -/
def atlas (cubic : Cubic H) : TEdge H × Bool ≃ Pin (Edge H) × Fin 3 :=
  (flagAtlas H cubic).trans (Equiv.prodCongr (Equiv.refl _) finPort)

def endPin (cubic : Cubic H) (e : TEdge H) (b : Bool) : Pin (Edge H) :=
  (atlas H cubic (e,b)).1

@[simp] theorem outside_pin (cubic : Cubic H) (e : Edge H) (b : Bool) :
    endPin H cubic (.inl e) b = (e,finSide b) := rfl

theorem outside_is_matching (cubic : Cubic H) :
    (fun p : Edge H × Bool => endPin H cubic (.inl p.1) p.2).Bijective :=
  (Equiv.prodCongr (Equiv.refl _) finSide).bijective

theorem outside_owners (cubic : Cubic H) (e : Edge H) :
    (pinToTriangle H cubic (endPin H cubic (.inl e) false)).1 = e.val.1 ∧
    (pinToTriangle H cubic (endPin H cubic (.inl e) true)).1 = e.val.2 := by
  constructor <;> simp [pinToTriangle,orientChart,orientLeg]

theorem inside_owners (cubic : Cubic H) (q : V × Fin 3) (b : Bool) :
    pinToTriangle H cubic (endPin H cubic (.inr q) b) = toggle b q := by
  change pinToTriangle H cubic ((pinToTriangle H cubic).symm (toggle b q)) = _
  exact Equiv.apply_symm_apply _ _

theorem each_edge_has_two_distinct_ends (cubic : Cubic H) (e : TEdge H) :
    endPin H cubic e false ≠ endPin H cubic e true := by
  intro he
  cases e with
  | inl e =>
    have hh := congrArg (fun x : Pin (Edge H) => (pinToTriangle H cubic x).1) he
    dsimp only at hh
    rw [(outside_owners H cubic e).1,(outside_owners H cubic e).2] at hh
    exact (ne_of_lt e.prop.1) hh
  | inr q =>
    have hh := congrArg (pinToTriangle H cubic) he
    rw [inside_owners,inside_owners] at hh
    have hbad : ∀ i : Fin 3, i ≠ rot i := by decide
    exact hbad q.2 (congrArg Prod.snd hh)

#print axioms orientChart
#print axioms pinToTriangle
#print axioms atlas
#print axioms outside_is_matching
#print axioms outside_owners
#print axioms inside_owners
#print axioms each_edge_has_two_distinct_ends

end J7LiteralGraph
