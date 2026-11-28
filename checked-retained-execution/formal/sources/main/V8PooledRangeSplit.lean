import V8PooledRangeHost
import V8PooledRangeTreePorts

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange
namespace Split

abbrev V (k : ℕ) := Tree k ⊕ (Deficit k × Bool)
abbrev OuterEdges (k : ℕ) (E : Type*) := E ⊕ (Deficit k ⊕ Deficit k)
abbrev Edges (k : ℕ) (E : Type*) := TreeEdge k ⊕ OuterEdges k E

def coreHalf (j : Fin 3) : Bool := decide (j = 2)

def sourceIndex {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (e : E) (b : Bool) : Fin 3 :=
  p (H e b) ⟨(e,b),rfl⟩

/-- First the old core edges, then the split links, then the single
deficit spoke at each old core vertex. Old ports 0,1 go in the first
half, old port 2 and the new spoke in the other half. -/
def outside {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    Graph (V k) (OuterEdges k E)
  | .inl e, b => .inr (H e b,coreHalf (sourceIndex H p e b))
  | .inr (.inl c), b => .inr (c,b)
  | .inr (.inr c), false => .inl (deficitTarget k c)
  | .inr (.inr c), true => .inr (c,true)

abbrev graph {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    Graph (V k) (Edges k E) := hostEnds k (outside H p)

theorem outsideEdges {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    OutsideEdges k (outside H p) := by
  intro e
  rcases e with (e | (c | c))
  · exact Or.inr ⟨(H e true,coreHalf (sourceIndex H p e true)),rfl⟩
  · exact Or.inr ⟨(c,true),rfl⟩
  · exact Or.inr ⟨(c,true),rfl⟩

theorem deficit_card (k : ℕ) : Fintype.card (Deficit k) = 2*k+4 := by simp; omega

theorem order (k : ℕ) : Fintype.card (V k) = 6*k+10 := by
  simp
  omega

private abbrev LocalCore := (Fin 3 ⊕ Bool) ⊕ Unit

private def coreOpen : LocalCore → Bool × Fin 3
  | .inl (.inl j) => if j = 2 then (true,1) else if j = 1 then (false,2) else (false,1)
  | .inl (.inr b) => (b,0)
  | .inr _ => (true,2)

private def coreClose : Bool × Fin 3 → LocalCore
  | (b,j) =>
    if j = 0 then .inl (.inr b)
    else if b then
      if j = 1 then .inl (.inl 2) else .inr ()
    else
      if j = 1 then .inl (.inl 0) else .inl (.inl 1)

private theorem core_close_open (a : LocalCore) : coreClose (coreOpen a) = a := by decide +revert
private theorem core_open_close (a : Bool × Fin 3) : coreOpen (coreClose a) = a := by decide +revert

private theorem coreOpen_half (j : Fin 3) :
    (coreOpen (.inl (.inl j))).1 = coreHalf j := by decide +revert

private def treeStamp {k : ℕ} (q : TreeToken k) : V k × Fin 3 :=
  let a := openTreeHalf k q
  (.inl a.1,a.2)

private def coreStamp {k : ℕ} (c : Deficit k) (q : LocalCore) : V k × Fin 3 :=
  let a := coreOpen q
  (.inr (c,a.1),a.2)

private def edgeToken {k : ℕ} (e : TreeEdge k) (b : Bool) : TreeToken k :=
  .inl ((treeEdgeKind k e).map (fun i => (i,b)) (fun i => (i,b)))

def stamp {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    Edges k E × Bool → V k × Fin 3
  | (.inl e,b) => treeStamp (edgeToken e b)
  | (.inr (.inl e),b) => coreStamp (H e b) (.inl (.inl (sourceIndex H p e b)))
  | (.inr (.inr (.inl c)),b) => coreStamp c (.inl (.inr b))
  | (.inr (.inr (.inr c)),false) => treeStamp (.inr c)
  | (.inr (.inr (.inr c)),true) => coreStamp c (.inr ())

private def treeStub {k : ℕ} {E : Type*} : TreeToken k → Edges k E × Bool
  | .inl (.inl (i,b)) => (.inl (privateLeafEdge k i),b)
  | .inl (.inr (i,b)) => (.inl (neighboringSpineEdge k i),b)
  | .inr c => (.inr (.inr (.inr c)),false)

private def coreStub {k : ℕ} {E : Type*} {H : Graph (Deficit k) E}
    (p : ThreePorts H) (c : Deficit k) : LocalCore → Edges k E × Bool
  | .inl (.inl j) =>
    let q := ((p c).symm j).val
    (.inr (.inl q.1),q.2)
  | .inl (.inr b) => (.inr (.inr (.inl c)),b)
  | .inr _ => (.inr (.inr (.inr c)),true)

private def unstamp {k : ℕ} {E : Type*} {H : Graph (Deficit k) E} (p : ThreePorts H) :
    V k × Fin 3 → Edges k E × Bool
  | (.inl v,j) => treeStub (closeTreeHalf k (v,j))
  | (.inr (c,b),j) => coreStub p c (coreClose (b,j))

private theorem unstamp_treeStamp {k : ℕ} {E : Type*} {H : Graph (Deficit k) E} (p : ThreePorts H)
    (a : TreeToken k) : unstamp p (treeStamp a) = treeStub a := by
  change treeStub (closeTreeHalf k (openTreeHalf k a)) = treeStub a
  rw [close_openTreeHalf]

private theorem unstamp_coreStamp {k : ℕ} {E : Type*} {H : Graph (Deficit k) E} (p : ThreePorts H)
    (c : Deficit k) (a : LocalCore) : unstamp p (coreStamp c a) = coreStub p c a := by
  change coreStub p c (coreClose (coreOpen a)) = coreStub p c a
  rw [core_close_open]

private theorem stamp_treeStub {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (a : TreeToken k) : stamp H p (treeStub a) = treeStamp a := by
  rcases a with ((⟨i,b⟩ | ⟨i,b⟩) | c)
  · change treeStamp (edgeToken (privateLeafEdge k i) b) = _
    simp [edgeToken]
  · change treeStamp (edgeToken (neighboringSpineEdge k i) b) = _
    simp [edgeToken]
  · rfl

private theorem stamp_coreStub {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (c : Deficit k) (a : LocalCore) : stamp H p (coreStub p c a) = coreStamp c a := by
  rcases a with ((j | b) | u)
  · rcases he : (p c).symm j with ⟨⟨e,b⟩,h⟩
    change H e b = c at h
    have hp : p c ⟨(e,b),h⟩ = j := by rw [← he,Equiv.apply_symm_apply]
    subst c
    change stamp H p (.inr (.inl ((p (H e b)).symm j).val.1),((p (H e b)).symm j).val.2) = _
    rw [he]
    change coreStamp (H e b) (.inl (.inl (p (H e b) ⟨(e,b),rfl⟩))) = _
    rw [hp]
  · rfl
  · rfl

private theorem unstamp_stamp {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (q : Edges k E × Bool) : unstamp p (stamp H p q) = q := by
  rcases q with ⟨e,b⟩
  rcases e with (e | (e | (c | c)))
  · change unstamp p (treeStamp (edgeToken e b)) = _
    rw [unstamp_treeStamp]
    have he := treeEdge_ofKind k e
    rcases h : treeEdgeKind k e with (i | i)
    · simp only [h,Sum.elim_inl] at he
      simp [edgeToken,h,treeStub,he]
    · simp only [h,Sum.elim_inr] at he
      simp [edgeToken,h,treeStub,he]
  · change unstamp p (coreStamp (H e b) (.inl (.inl (sourceIndex H p e b)))) = _
    rw [unstamp_coreStamp]
    simp only [coreStub,sourceIndex,Equiv.symm_apply_apply]
  · change unstamp p (coreStamp c (.inl (.inr b))) = _
    rw [unstamp_coreStamp]
    rfl
  · cases b
    · change unstamp p (treeStamp (.inr c)) = _
      rw [unstamp_treeStamp]
      rfl
    · change unstamp p (coreStamp c (.inr ())) = _
      rw [unstamp_coreStamp]
      rfl

private theorem stamp_unstamp {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (q : V k × Fin 3) : stamp H p (unstamp p q) = q := by
  rcases q with ⟨v,j⟩
  rcases v with (v | ⟨c,b⟩)
  · change stamp H p (treeStub (closeTreeHalf k (v,j))) = _
    rw [stamp_treeStub]
    have h := open_closeTreeHalf k (v,j)
    exact congrArg (fun a : Tree k × Fin 3 => ((Sum.inl a.1 : V k),a.2)) h
  · change stamp H p (coreStub p c (coreClose (b,j))) = _
    rw [stamp_coreStub]
    have h := core_open_close (b,j)
    exact congrArg (fun a : Bool × Fin 3 => ((Sum.inr (c,a.1) : V k),a.2)) h

def stampEquiv {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    Edges k E × Bool ≃ V k × Fin 3 where
  toFun := stamp H p
  invFun := unstamp p
  left_inv := unstamp_stamp H p
  right_inv := stamp_unstamp H p

theorem stamp_endpoint {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (q : Edges k E × Bool) : (stamp H p q).1 = graph H p q.1 q.2 := by
  rcases q with ⟨e,b⟩
  rcases e with (e | (e | (c | c)))
  · change (treeStamp (edgeToken e b)).1 = Sum.inl (treeEnds k e b)
    have he := treeEdge_ofKind k e
    rcases h : treeEdgeKind k e with (i | i)
    · simp only [h,Sum.elim_inl] at he
      rw [← he]
      simp [edgeToken,treeStamp,openTreeHalf]
    · simp only [h,Sum.elim_inr] at he
      rw [← he]
      cases b <;> simp [edgeToken,treeStamp,openTreeHalf]
  · change Sum.inr (H e b,(coreOpen (.inl (.inl (sourceIndex H p e b)))).1) = _
    rw [coreOpen_half]
    rfl
  · rfl
  · cases b
    · rcases c with (⟨i,z⟩ | z)
      · rfl
      · cases z <;> rfl
    · rfl

/-- The actual incidence sets of the split graph have exactly three
ports, with each of the three positions used once at the prescribed vertex. -/
def ports {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    ThreePorts (graph H p) := fun v =>
  let eqv := stampEquiv H p
  { toFun := fun q => (eqv q.val).2
    invFun := fun j => ⟨eqv.symm (v,j),by
      rw [← stamp_endpoint]
      change (eqv (eqv.symm (v,j))).1 = v
      rw [Equiv.apply_symm_apply]⟩
    left_inv := fun q => Subtype.ext <| by
      change eqv.symm (v,(eqv q.val).2) = q.val
      have hv : v = (eqv q.val).1 := q.property.symm.trans (stamp_endpoint H p q.val).symm
      have huv : (v,(eqv q.val).2) = eqv q.val := Prod.ext hv rfl
      exact (congrArg eqv.symm huv).trans (eqv.symm_apply_apply q.val)
    right_inv := fun j => congrArg Prod.snd (eqv.apply_symm_apply (v,j)) }

/-- The physical endpoint values on the very same completion. -/
theorem exact_endpoint {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (w : Word k) (b : Bool) :
    satCount (graph H p) (ports H p) (hostEnabled k w b) = CaterpillarRange.output k (w,b) :=
  physical_endpoint_count k (outside H p) (outsideEdges H p) (ports H p) w b

theorem exact_pair {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    Function.Injective (fun w : Word k =>
      (satCount (graph H p) (ports H p) (hostEnabled k w false),
       satCount (graph H p) (ports H p) (hostEnabled k w true))) :=
  physical_endpoint_pair_injective k (outside H p) (outsideEdges H p) (ports H p)

theorem exact_range {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H) :
    2^k ≤ (physicalRange (graph H p) (ports H p)).card ^ 2 :=
  physical_range_square k (outside H p) (outsideEdges H p) (ports H p)

theorem exact_decoder_budget {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (B b : ℕ) {Menu : Type*} [Fintype Menu] (Side : Menu → Type*) [∀ m, Fintype (Side m)]
    (hmenu : Fintype.card Menu ≤ 2^B) (hside : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (menu : (V k → Bool) → Menu) (aux : (s : V k → Bool) → Side (menu s))
    (decode : (Σ m, Side m) → ℕ)
    (hc : ∀ s, decode ⟨menu s,aux s⟩ = satCount (graph H p) (ports H p) s) :
    Fintype.card (V k) ≤ 12*(B+b)+10 := by
  rw [order]
  have hg := physical_decoder_budget k B b (outside H p) (outsideEdges H p) (ports H p)
    Side hmenu hside menu aux decode hc
  omega

#print axioms outsideEdges
#print axioms deficit_card
#print axioms order
#print axioms stampEquiv
#print axioms stamp_endpoint
#print axioms ports
#print axioms exact_endpoint
#print axioms exact_pair
#print axioms exact_range
#print axioms exact_decoder_budget

end Split
end V8PooledRange
