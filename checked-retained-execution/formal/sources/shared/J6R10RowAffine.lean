import J6R10RowIdentity
import J6SourceMoment

/-! Signed row data used literally by the child tensor. We restrict the
old global Boolean cube to group-indexed Boolean row and column cubes. -/
namespace J6R10RowAffine
open scoped BigOperators Classical
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
open J6R10RowLocal J6R10RowIdentity J6ActiveAllocation J6SourceMoment
variable {A Q S R : Type*} [Fintype Q] [LinearOrder S] [CommRing R] {a b : ℕ}

def rowBits (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (x : ∀ g, State ρ κ mask i g) (r : A) : Bool :=
  (x (rowGroup mask i (ρ r))).1 ⟨r,rfl⟩

def colBits (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (x : ∀ g, State ρ κ mask i g) (q : Q) : Bool :=
  (x (colGroup mask i (κ q))).2 ⟨q,rfl⟩

omit [Fintype Q] in theorem col_restrict (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (x : ∀ g, State ρ κ mask i g) (g : S) :
    (fun q : {q : Q // colGroup mask i (κ q)=g} => colBits ρ κ mask i x q.val) = (x g).2 := by
  funext q
  rcases q with ⟨q,hq⟩
  subst g
  rfl

noncomputable def groupBit (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (g : S) (x : State ρ κ mask i g) (r : A) : Bool :=
  if e : rowGroup mask i (ρ r)=g then x.1 ⟨r,e⟩ else false

noncomputable def groupBase (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (t : ℤ) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (g : S) (x : State ρ κ mask i g) (r : A) : R :=
  if e : rowGroup mask i (ρ r)=g then
    localValue κ mask i t p hnil z (ρ r) (fun q => x.2 ⟨q.val,q.property.trans e⟩) else 0

def weight (i : Fin a) (p : ℕ) (mask : MaskFamily a b S) (m : Mode i p mask) : ℕ :=
  m.order.val+1

theorem actual_affine_row_eq (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R) [Fintype (Page a b S)]
    (x : ∀ g, State ρ κ mask i g) (r : A) :
    LiteralPortCompiler.affine (rowBits ρ κ mask i x r) (originalRow κ t p hnil z (ρ r) (colBits ρ κ mask i x)) =
      ∑ o : Option (Mode i p mask),
        scaled (weight i p mask)
          (J6SourceMoment.insert (fun r => row ρ κ mask i ht hv p hnil z r (x (rowGroup mask i (ρ r))))
            (fun m => moment κ mask i m (x (source mask i m)).2)) r o := by
  classical
  rw [actual_row_eq κ mask i htM ht hv p hp hnil z (ρ r),col_restrict]
  simp only [col_restrict ρ κ mask i x]
  let Y := rowBits ρ κ mask i x r
  let B₀ := localValue κ mask i t p hnil z (ρ r) (x (rowGroup mask i (ρ r))).2
  let C₀ (m : Mode i p mask) := scaledRow mask i ht hv p hnil z (ρ r) m *
    moment κ mask i m (x (source mask i m)).2
  change LiteralPortCompiler.affine Y (B₀+∑ m,C₀ m) = _
  rw [Fintype.sum_option]
  have h0 : scaled (weight i p mask)
      (J6SourceMoment.insert (fun r => row ρ κ mask i ht hv p hnil z r (x (rowGroup mask i (ρ r))))
        (fun m => moment κ mask i m (x (source mask i m)).2)) r none =
      LiteralPortCompiler.affine Y B₀ := by
    simp [scaled,cost,J6SourceMoment.insert,row,Y,B₀,rowBits]
  have h1 (m : Mode i p mask) : scaled (weight i p mask)
      (J6SourceMoment.insert (fun r => row ρ κ mask i ht hv p hnil z r (x (rowGroup mask i (ρ r))))
        (fun m => moment κ mask i m (x (source mask i m)).2)) r (some m) =
      LiteralPortCompiler.slope Y*C₀ m := by
    simp [scaled,cost,weight,J6SourceMoment.insert,row,Y,C₀,rowBits,scaledRow]
    ring
  rw [h0]
  simp only [h1,← Finset.mul_sum]
  cases Y with
  | false =>
    simp [LiteralPortCompiler.affine,LiteralPortCompiler.slope]
    ring
  | true => simp [LiteralPortCompiler.affine,LiteralPortCompiler.slope]

#print axioms col_restrict
#print axioms actual_affine_row_eq
end J6R10RowAffine
