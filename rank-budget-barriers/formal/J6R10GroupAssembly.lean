import J6R10PacketAssembly

namespace J6R10GroupAssembly
open scoped Classical BigOperators
open J6ActiveAllocation J6ActiveProfile J6BlockFactor J6ChildIdentity J6SourceMoment
open J6FixedProfile J6LiteralCoeff J6NoOversizedChild J6R10PacketAssembly

variable {R P M G K : Type*} [CommRing R] [Fintype P] [Fintype M]
  [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K]
  {V : G → Type*} [∀ g, Fintype (V g)]

def packetFiber (g : G) : rows (Prod.fst : G × K → G) g ≃ K where
  toFun p := p.val.2
  invFun k := ⟨(g,k),rfl⟩
  left_inv p := by rcases p with ⟨⟨g',k⟩,e⟩; cases e; rfl
  right_inv _ := rfl

def chooseGroup [∀ g, Inhabited (V g)] (g : G) (y : V g) (h : G) : V h :=
  if e : h = g then e.symm ▸ y else default

omit [Fintype G] [∀ g, Fintype (V g)] in
@[simp] theorem chooseGroup_at [∀ g, Inhabited (V g)] (g : G) (y : V g) :
    chooseGroup g y g = y := by simp [chooseGroup]

omit [Fintype G] in
theorem fold_retained_by_packet (source : M → G × K) (g : G)
    (moment : M → R) (coeff : K → R) :
    (∏ m ∈ Finset.univ.filter (fun m => (source m).1 = g), moment m) *
      (∏ k, coeff k) =
    ∏ k, coeff k * ∏ m ∈ Finset.univ.filter (fun m => source m = (g,k)), moment m := by
  classical
  let S := (Finset.univ : Finset M).filter (fun m => (source m).1 = g)
  have h : ∏ k, ∏ m ∈ S.filter (fun m => (source m).2 = k), moment m =
      ∏ m ∈ S, moment m :=
    Finset.prod_fiberwise S (fun m => (source m).2) moment
  change (∏ m ∈ S, moment m) * _ = _
  rw [← h, mul_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have he : S.filter (fun m => (source m).2 = k) =
      Finset.univ.filter (fun m => source m = (g,k)) := by
    ext m
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
  change coeff k * (∏ m ∈ S.filter (fun m => (source m).2 = k), moment m) = _
  rw [he]

theorem exact_one_child [∀ g, Inhabited (V g)]
    (w : M → ℕ) (block : P → G × K) (target source : M → G × K)
    (row : ∀ i, V (block i).1 → Option M → R)
    (old : ∀ g, V g → R) (L : ∀ m, V (source m).1 → R)
    (bit : ∀ g, V g → P → Bool) (base : ∀ g, V g → P → R)
    (cross : ∀ g, V g → P → M → R)
    (hzero : ∀ i m v, block i ≠ target m → row i v (some m) = 0)
    (h0 : ∀ g (y : V g) i (e : (block i).1 = g),
      scaled w (fun _ v => row i (e.symm ▸ y) v) i none =
        LiteralPortCompiler.affine (bit g y i) (base g y i))
    (hm : ∀ g (y : V g) i (e : (block i).1 = g) m,
      scaled w (fun _ v => row i (e.symm ▸ y) v) i (some m) =
        LiteralPortCompiler.slope (bit g y i) * cross g y i m)
    (b : Profile P M) (g : G) :
    (∑ y : V g, old g y *
        (∏ m : rows (Prod.fst ∘ source) g, L m.val (cast (congrArg V m.property.symm) y) ^ (b m.val).val) *
        (∏ k : rows (Prod.fst : G × K → G) g,
          localizedCoeff w block target Prod.fst row b k.val (cast (congrArg V k.property.symm) y))) =
      J6RecursiveModes.child target source (actualRows block) old bit base cross
        (fun g y m => if h : (source m).1 = g then L m (h.symm ▸ y) else 0) (profileFinsupp b) g := by
  classical
  unfold J6RecursiveModes.child
  refine Finset.sum_congr rfl (fun y _ => ?_)
  let x : ∀ h, V h := chooseGroup g y
  let f : P → Option M → R := fun i => row i (x (block i).1)
  let mom (m : M) : R := if h : (source m).1 = g then L m (h.symm ▸ y) else 0
  let coeff (k : K) : R := targetCoeff w f block target b (g,k)
  have hcoeff :
      (∏ k : rows (Prod.fst : G × K → G) g,
        localizedCoeff w block target Prod.fst row b k.val (cast (congrArg V k.property.symm) y)) =
        ∏ k, coeff k := by
    refine Fintype.prod_equiv (packetFiber g) _ _ (fun kk => ?_)
    rcases kk with ⟨⟨g',k⟩,e⟩
    change g' = g at e
    subst g'
    change localizedCoeff w block target Prod.fst row b (g,k) y = coeff k
    unfold coeff f
    rw [coefficient_is_local, show x g = y from chooseGroup_at g y]
  have hmom :
      (∏ m : rows (Prod.fst ∘ source) g, L m.val (cast (congrArg V m.property.symm) y) ^ (b m.val).val) =
        ∏ m ∈ Finset.univ.filter (fun m => (source m).1 = g), mom m ^ (b m).val := by
    have h : (∏ m : rows (Prod.fst ∘ source) g, mom m.val ^ (b m.val).val) =
        ∏ m ∈ Finset.univ.filter (fun m => (source m).1 = g), mom m ^ (b m).val :=
      (Finset.prod_subtype (p := fun m => (Prod.fst ∘ source) m = g)
        (Finset.univ.filter (fun m => (source m).1 = g))
        (fun m => by simp) (fun m => mom m ^ (b m).val)).symm
    rw [← h]
    refine Finset.prod_congr rfl (fun m _ => ?_)
    have e : (source m.val).1 = g := m.property
    simp only [mom,dif_pos e]
    rcases m with ⟨m, hm⟩
    change (source m).1 = g at hm
    subst g
    rfl
  rw [hcoeff,hmom,mul_assoc,fold_retained_by_packet source g (fun m => mom m ^ (b m).val) coeff]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  change coeff k *
      (∏ m ∈ Finset.univ.filter (fun m => source m = (g,k)), mom m ^ (b m).val) = _
  apply actual_packet_entry w f block target source b g k _ _ _ mom
  · exact fun i m e => hzero i m _ e
  · intro i e
    have he := congrArg Prod.fst e
    have xe : x (block i).1 = he.symm ▸ y := by simp [x,chooseGroup,he]
    exact show scaled w f i none = _ from by
      simpa only [scaled,f,xe] using h0 g y i he
  · intro i e m
    have he := congrArg Prod.fst e
    have xe : x (block i).1 = he.symm ▸ y := by simp [x,chooseGroup,he]
    exact show scaled w f i (some m) = _ from by
      simpa only [scaled,f,xe] using hm g y i he m

#print axioms exact_one_child
end J6R10GroupAssembly
