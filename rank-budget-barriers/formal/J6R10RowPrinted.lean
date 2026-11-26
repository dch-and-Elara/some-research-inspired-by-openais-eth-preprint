import J6R10RowAffine
import J6R10PrintedContraction

/-! Physical instantiation of the complete printed nonzero recursion
step. The incoming old tables are already grouped by their true vertex
symbols; the local row, the crossing coefficients and tile moments are
not supplied as abstract equality premises. -/
namespace J6R10RowPrinted
open scoped BigOperators Classical
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild
open J6R10RowLocal J6R10RowIdentity J6R10RowAffine
open J6R10PacketAssembly J6R10PrintedContraction
open J6ActiveAllocation J6SourceMoment
private noncomputable def fromGeneric {R I M G K : Type*} [CommRing R]
    [Fintype I] [Fintype M] [Fintype G] [Fintype K]
    {V : G → Type*} [∀ g, Fintype (V g)]
    (block : I → G × K) (target source : M → G × K)
    (old : ∀ g, V g → R) (L : ∀ m, V (source m).1 → R)
    (bit : ∀ g, V g → I → Bool) (base : ∀ g, V g → I → R)
    (cross : ∀ g, V g → I → M → R) (β : M →₀ ℕ) (g : G) : R :=
  J6RecursiveModes.child target source (actualRows block) old bit base cross
    (fun g y m => if h : (source m).1 = g then L m (h.symm ▸ y) else 0) β g

variable {A Q S R : Type*} [Fintype A] [Fintype Q] [LinearOrder S] [CommRing R] {a b : ℕ}
  [Fintype S] [Fintype (Page a b S)]

def block (ρ : A → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (r : A) : S × Page a b S :=
  (rowBlock mask i (ρ r)).swap

def targetGP (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) :
    S × Page a b S := (target mask i m).swap

def sourceGP (mask : MaskFamily a b S) (i : Fin a) {p : ℕ} (m : Mode i p mask) :
    S × Page a b S := (source mask i m,m.page)

noncomputable def reconstructedChild (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (old : ∀ g, State ρ κ mask i g→R) (β : Mode i p mask→₀ℕ) (g : S) : R :=
  fromGeneric (block ρ mask i) (targetGP mask i) (sourceGP mask i)
    old (fun m v => moment κ mask i m v.2)
    (groupBit ρ κ mask i) (groupBase ρ κ mask i t p hnil z)
    (fun _ _ r m => scaledRow mask i ht hv p hnil z (ρ r) m) β g

set_option maxHeartbeats 4500000 in theorem actual_source_step (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R)
    (old : ∀ g, State ρ κ mask i g → R) :
    (∑ x : ∀ g, State ρ κ mask i g, (∏ g, old g (x g)) *
      ∏ r : A,
        LiteralPortCompiler.affine (rowBits ρ κ mask i x r)
          (originalRow κ t p hnil z (ρ r) (colBits ρ κ mask i x))) =
    ∑ β ∈ J6RecursiveMenu.menu p (weight i p mask),
      ∏ g, reconstructedChild ρ κ mask i ht hv p hnil z old β g := by
  classical
  simp only [actual_affine_row_eq ρ κ mask i htM ht hv p hp hnil z]
  let wr := weight i p mask
  let bk := block ρ mask i
  let T := targetGP (p:=p) mask i
  let U := sourceGP (p:=p) mask i
  let F (r : A) (v : State ρ κ mask i (bk r).1) (m : Option (Mode i p mask)) :=
    row ρ κ mask i ht hv p hnil z r v m
  let L (m : Mode i p mask) (v : State ρ κ mask i (U m).1) : R := moment κ mask i m v.2
  have hz (r : A) (m : Mode i p mask) (v : State ρ κ mask i (bk r).1)
      (h : bk r≠T m) : F r v (some m)=0 := by
    exact row_off_target ρ κ mask i ht hv p hnil z r m v (fun e => h (congrArg Prod.swap e))
  have h0 (g : S) (y : State ρ κ mask i g) (r : A) (e : (bk r).1=g) :
      scaled wr (fun _ m => F r (e.symm ▸ y) m) r none =
        LiteralPortCompiler.affine (groupBit ρ κ mask i g y r) (groupBase ρ κ mask i t p hnil z g y r) := by
    change rowGroup mask i (ρ r)=g at e
    subst g
    change scaled wr (fun _ m => F r y m) r none = _
    simp [F,scaled,cost,row,groupBit,groupBase]
  have hm (g : S) (y : State ρ κ mask i g) (r : A) (e : (bk r).1=g) (m : Mode i p mask) :
      scaled wr (fun _ o => F r (e.symm ▸ y) o) r (some m) =
        LiteralPortCompiler.slope (groupBit ρ κ mask i g y r) * scaledRow mask i ht hv p hnil z (ρ r) m := by
    change rowGroup mask i (ρ r)=g at e
    subst g
    change scaled wr (fun _ o => F r y o) r (some m) = _
    change (2:R)^(m.order.val+1)*(LiteralPortCompiler.slope (y.1 ⟨r,rfl⟩) *
      crossNorm mask i ht hv p hnil z (ρ r) m) = _ 
    rw [groupBit,dif_pos rfl,scaledRow]
    exact mul_left_comm _ _ _
  have h := exact_source_contraction (R:=R) (P:=A) (M:=Mode i p mask)
    (G:=S) (K:=Page a b S) (V:=State ρ κ mask i)
    wr (fun m => Nat.succ_pos m.order.val) p hnil bk T U F old L
    (groupBit ρ κ mask i) (groupBase ρ κ mask i t p hnil z)
    (fun _ _ r m => scaledRow mask i ht hv p hnil z (ρ r) m) hz h0 hm
  let fty := fun g => (inferInstance : Fintype (State ρ κ mask i g))
  have hf : @Pi.instFintype S (State ρ κ mask i)
        (fun x y => Classical.propDecidable (x=y)) _ fty =
      @Pi.instFintype S (State ρ κ mask i)
        (fun x y => LinearOrder.toDecidableEq x y) _ fty :=
    Subsingleton.elim _ _
  rw [hf] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · refine Finset.sum_congr rfl (fun β _ => ?_)
    refine Finset.prod_congr rfl (fun g _ => ?_)
    rfl

#print axioms actual_source_step
end J6R10RowPrinted
