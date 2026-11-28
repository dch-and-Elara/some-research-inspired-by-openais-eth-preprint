import A4R45PhysicalFullChart

/-! Plant real consecutive even/odd addresses in the fully occupied
diagonal ordered cell of the original packet chart. -/
namespace A4R45ActualPairs
open P11FullPacking J6R10Repack AAcquisitionCost
set_option autoImplicit false
set_option warningAsError true

variable {G : Type*} [LinearOrder G] {a copies : ℕ}

def diagCell (word : Fin a→G) : Cell (Fin a) G := fun i=>(word i,word i)

def diagKey (word : Fin a→G) : Key (Fin a) G := ⟨diagCell word,fun _=>le_rfl⟩

def address (word : Fin a→G) (p : Fin copies) (i : Fin (2^a)) :
    Physical a copies G := (⟨diagKey word,(p,fun _=>false)⟩,i)

theorem address_diagonal (mask : MaskFamily a copies G) (word : Fin a→G)
    (p : Fin copies) (i : Fin (2^a)) :
    physicalCell mask (address word p i)=diagCell word := by
  funext j
  simp [physicalCell,address,cell,diagKey,diagCell]

theorem address_injective (word : Fin a→G) :
    Function.Injective (fun z : Fin copies × Fin (2^a) => address word z.1 z.2) := by
  intro z t e
  exact Prod.ext (congrArg (fun p : Physical a copies G => p.1.2.1) e)
    (congrArg (fun p : Physical a copies G => p.2) e)

theorem original_diagonal_actual_pairs {Hard W A B : Type*}
    [Fintype Hard] [Fintype W] [Fintype G]
    (N : Network W A B) (rows : A→Fin a→G) (cols : B→Fin a→G)
    (mask : MaskFamily a copies G) (word : Fin a→G) (ha : 0<a)
    (hard : Hard×Bool ↪ W)
    (room : Fintype.card Hard≤copies*2^(a-1))
    (hard_cell : ∀ x, declaredCell N rows cols (hard x)=diagCell word)
    (load : ∀ c, Nat.card {w : W // declaredCell N rows cols w=c}=copies*2^a) :
    ∃ seat : W≃Physical a copies G, (∀ w,physicalCell mask (seat w)=declaredCell N rows cols w) ∧
      (∀ j,wirePred seat (hard (j,true))=some (hard (j,false))) := by
  classical
  let H := 2^(a-1)
  have hL : 2*H=2^a := by
    change 2 * (2:ℕ)^(a-1)=2^a
    rw [←pow_succ',Nat.sub_add_cancel ha]
  let pick (h : Hard) : Fin copies × Fin H :=
    finProdFinEquiv.symm (Fin.castLE room (Fintype.equivFin Hard h))
  have injPick : Function.Injective pick := by
    intro i j he
    apply (Fintype.equivFin Hard).injective
    apply Fin.ext
    exact congrArg (fun z : Fin (copies*H)=>z.val) (finProdFinEquiv.symm.injective he)
  let place (v : Hard×Bool) : Fin copies × Fin (2*H) :=
    A4R45PairSeats.pairSeat (pick v.1,v.2)
  have injPlace : Function.Injective place := by
    intro x y h
    have e := A4R45PairSeats.pairSeat_injective copies H h
    exact Prod.ext (injPick (congrArg (fun z : (Fin copies×Fin H)×Bool=>z.1) e))
      (congrArg (fun z : (Fin copies×Fin H)×Bool=>z.2) e)
  let src : Hard×Bool ↪ {x : W // declaredCell N rows cols x=diagCell word} :=
    ⟨fun x=>⟨hard x,hard_cell x⟩,fun u v e=>hard.injective (congrArg Subtype.val e)⟩
  let dest : Hard×Bool ↪ {p : Physical a copies G // physicalCell mask p=diagCell word} :=
    ⟨fun x=>⟨address word (place x).1 (Fin.cast hL (place x).2),address_diagonal mask _ _ _⟩,by
      intro u v eq
      have e : ((place u).1, Fin.cast hL (place u).2) =
          ((place v).1, Fin.cast hL (place v).2) := by
        apply address_injective (copies:=copies) word
        exact congrArg Subtype.val eq
      apply injPlace
      exact Prod.ext (congrArg (fun z : Fin copies×Fin (2^a)=>z.1) e)
        (Fin.ext (congrArg (fun z : Fin copies×Fin (2^a)=>z.2.val) e))⟩
  obtain ⟨P,typed,seats⟩ := A4R45PhysicalFullChart.actual_full_chart_prescribed
    N rows cols mask (diagCell word) load src dest
  refine ⟨P,typed,?_⟩
  intro h
  apply (wirePred_spec P _ _).mpr
  have hTrue : P (hard (h,true))=(dest (h,true)).val := seats (h,true)
  have hFalse : P (hard (h,false))=(dest (h,false)).val := seats (h,false)
  unfold packetOf positionOf
  rw [hTrue,hFalse]
  constructor
  · rfl
  · change ((2*(pick h).2.val:ℕ):ℤ)+1 = ((2*(pick h).2.val+1:ℕ):ℤ)
    push_cast
    rfl

#print axioms address_diagonal
#print axioms address_injective
#print axioms original_diagonal_actual_pairs
end A4R45ActualPairs
