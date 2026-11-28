import A1R43LiteralGate
import LiteralPortCompiler
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000
set_option maxRecDepth 1400

/-! Sum the independent real row ports at the signed -1 matrix.
The all-one unary rows are summed against an arbitrary incoming
argument; no suspension over their physical positions is needed. -/
namespace A1R43Literal
open scoped Classical BigOperators
open J6R10Repack LiteralPortCompiler

noncomputable section

def boolPair : (Bool→Bool) ≃ Bool × Bool where
  toFun a := (a false,a true)
  invFun p := fun b=>if b then p.2 else p.1
  left_inv a := by funext b; cases b <;> rfl
  right_inv _ := rfl

variable {R : Type*} [CommRing R]

theorem affine_mass_one (z : R) : (∑ y : Bool,affine y z)=1 := by
  simp [affine]

theorem NAND_affine (x z : R) :
    (∑ b : Bool→Bool,(spin (!(b false && b true)):R) *
      ∏ j : Bool,affine (b j) (if j then z else x))=1-x*z := by
  let h (b : Bool→Bool) : R :=
    spin (!(b false && b true)) * ∏ j : Bool,affine (b j) (if j then z else x)
  change (∑ b, h b)=_
  rw [← boolPair.symm.sum_comp h,Fintype.sum_prod_type]
  simp [h,spin,affine,boolPair]
  ring

variable {V Pad : Type} [DecidableEq V] [Fintype Pad]
variable (F : Finset (V×V))
local notation "N" => network F Pad

abbrev RF (Pad : Type) (r : Row F Pad) := {w : Wire F Pad // (network F Pad).row w=r}

def rowCube : ((r : Row F Pad) → RF F Pad r→Bool) ≃ (Wire F Pad→Bool) where
  toFun y w := y ((N).row w) ⟨w,rfl⟩
  invFun y _ w := y w.val
  left_inv y := by
    funext r w
    rcases w with ⟨w,h⟩
    cases h
    rfl
  right_inv _ := rfl

omit [DecidableEq V] [Fintype Pad] in
theorem rowCube_read (u : (r : Row F Pad) → RF F Pad r→Bool)
    (r : Row F Pad) (w : RF F Pad r) : rowCube F u w.val=u r w := by
  exact congrFun (congrFun ((rowCube F).symm_apply_apply u) r) w

def dummyRowFibre (z : Occ F⊕Pad) : RF F Pad (.inr z) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨z.elim (evenWire F Pad) Sum.inr,(dummy_row_unique F Pad z _).2 rfl⟩
  left_inv w := Subtype.ext ((dummy_row_unique F Pad z _).1 w.property).symm
  right_inv u := by cases u; rfl

def rowTerm (a : Wire F Pad→R) (r : Row F Pad) (u : RF F Pad r→Bool) : R :=
  spin (tableFlag F (.inl r) (u ∘ (rowPortsEquiv N r).symm)) *
      ∏ w : RF F Pad r, affine (u w) (a w.val)

theorem rowTerm_real (a : Wire F Pad→R) (e : F) :
    (∑ u : RF F Pad (.inl e)→Bool, rowTerm F a (.inl e) u) =
      1-a (oddWire F Pad (e,false))*a (oddWire F Pad (e,true)) := by
  let j := (rowFibre F Pad e).symm
  let v := j.arrowCongr (Equiv.refl Bool)
  rw [← v.sum_comp (rowTerm F a (.inl e))]
  refine Eq.trans (Finset.sum_congr rfl (fun b _=>?_)) (NAND_affine _ _)
  unfold rowTerm
  have eqprod :
      (∏ w : RF F Pad (.inl e),affine (v b w) (a w.val)) =
        ∏ k : Bool,affine (b k) (if k then a (oddWire F Pad (e,true)) else a (oddWire F Pad (e,false))) := by
    rw [← j.prod_comp (fun w=>affine (v b w) (a w.val))]
    apply Finset.prod_congr rfl
    intro k _
    change affine (b (j.symm (j k))) (a (j k).val) = _
    rw [j.symm_apply_apply]
    cases k <;> rfl
  rw [eqprod]
  rfl

theorem rowTerm_dummy (a : Wire F Pad→R) (z : Occ F⊕Pad) :
    (∑ u : RF F Pad (.inr z)→Bool, rowTerm F a (.inr z) u)=1 := by
  let j := (dummyRowFibre F z).symm
  let v := j.arrowCongr (Equiv.refl Bool)
  let group : (Unit→Bool) ≃ Bool :=
    ⟨fun x=>x (),fun b _=>b,by intro x; funext u; cases u; rfl,fun _=>rfl⟩
  rw [← v.sum_comp (rowTerm F a (.inr z)),← group.symm.sum_comp]
  have hh (b : Bool) : rowTerm F a (.inr z) (v (group.symm b)) =
      affine b (a (z.elim (evenWire F Pad) Sum.inr)) := by
    unfold rowTerm
    change (1:R) * _ = _
    rw [one_mul,←j.prod_comp]
    simp only [Fintype.prod_unique]
    rfl
  simp only [hh]
  exact affine_mass_one _

def rowSum (a : Wire F Pad→R) : R :=
  ∑ y : Wire F Pad→Bool,(∏ r : Row F Pad,spin (rowFlag F y r)) *
    ∏ w : Wire F Pad,affine (y w) (a w)

theorem sum_instances {X : Type*} (t : X→R) (A B : Fintype X) :
    (@Finset.univ X A).sum t=(@Finset.univ X B).sum t :=
  congrArg (fun C : Fintype X=>(@Finset.univ X C).sum t) (Subsingleton.elim _ _)

theorem rowSum_NAND (a : Wire F Pad→R) :
    rowSum F a = ∏ e : F, (1-a (oddWire F Pad (e,false))*a (oddWire F Pad (e,true))) := by
  classical
  letI : DecidableEq (Row F Pad) := Classical.decEq _
  letI (r : Row F Pad) : Fintype (RF F Pad r) := Fintype.ofFinite _
  unfold rowSum
  rw [← (rowCube (Pad:=Pad) F).sum_comp]
  calc
    _ = ∑ u : (r : Row F Pad)→RF F Pad r→Bool,∏ r : Row F Pad,rowTerm F a r (u r) := by
      apply Finset.sum_congr rfl
      intro u _
      simp only [rowTerm,Finset.prod_mul_distrib]
      congr 1
      · apply Finset.prod_congr rfl
        intro r _
        congr 1
        unfold rowFlag
        congr 1
        funext p
        rcases p with ⟨p,hp⟩
        rcases p with w|w
        · exact rowCube_read F u r ⟨w,Sum.inl.inj hp⟩
        · cases hp
      · let idx := Equiv.sigmaFiberEquiv (N).row
        rw [← idx.prod_comp (fun w=>affine (rowCube F u w) (a w)),Fintype.prod_sigma]
        apply Finset.prod_congr rfl
        intro r _
        apply Finset.prod_congr (by ext w; simp only [Finset.mem_univ])
        intro w _
        rw [show idx ⟨r,w⟩=w.val from rfl,rowCube_read F u r w]
    _ = _ := by
      rw [← Fintype.prod_sum (rowTerm F a),Fintype.prod_sum_type]
      have leftSide :
          (∏ e : F, ∑ u : RF F Pad (.inl e)→Bool,rowTerm F a (.inl e) u) =
            ∏ e : F, (1-a (oddWire F Pad (e,false)) * a (oddWire F Pad (e,true))) := by
        apply Finset.prod_congr rfl
        intro e _
        exact (sum_instances (rowTerm F a (.inl e)) _ _).trans (rowTerm_real F a e)
      have rightSide :
          (∏ z : Occ F⊕Pad, ∑ u : RF F Pad (.inr z)→Bool,rowTerm F a (.inr z) u) = 1 := by
        apply Finset.prod_eq_one
        intro z _
        exact (sum_instances (rowTerm F a (.inr z)) _ _).trans (rowTerm_dummy F a z)
      rw [leftSide,rightSide,mul_one]

#print axioms affine_mass_one
#print axioms NAND_affine
#print axioms rowCube_read
#print axioms rowTerm_real
#print axioms rowTerm_dummy
#print axioms rowSum_NAND
end
end A1R43Literal
