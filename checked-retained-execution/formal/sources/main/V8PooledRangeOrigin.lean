import V8PooledRangeConclusion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace V8PooledRange
namespace NativeOrigin

abbrev Occ (V E : Type*) := ClauseId V E × Bool

/-- Each original occurrence has two physical wires after the App. D
subdivision. The first flag is the clause port and the second flag
distinguishes the clause side (false) from the variable side (true). -/
abbrev Edge (V E : Type*) := Occ V E × Bool

def Satisfied {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (a : Edge V E → Bool) : Prop :=
  (∀ q : Occ V E, a (q,false) = a (q,true)) ∧
  (∀ q r : Occ V E, clausePort G p s q = clausePort G p s r → a (q,true)=a (r,true)) ∧
  (∀ i, a ((i,false),false) = (clauses G p s i).1.2 ∨
    a ((i,true),false) = (clauses G p s i).2.2)

abbrev Models {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :=
  {a : Edge V E → Bool // Satisfied G p s a}

noncomputable instance {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    Fintype (Models G p s) := Fintype.ofFinite _

def originalRep {V E : Type*} (G : Graph V E) (p : ThreePorts G) (v : Variable V) : Occ V E :=
  (occurrenceChart G p).symm (.inr v)

theorem clausePort_rep {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (v : Variable V) : clausePort G p s (originalRep G p v) = v := by
  rw [← occurrenceChart_projects]
  change (((occurrenceChart G p) ((occurrenceChart G p).symm (.inr v))).elim
    (fun t => Sum.inl t.1) id) = v
  rw [Equiv.apply_symm_apply]
  rfl

private theorem occurs_eq_at_model {V E : Type*}
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (a : Models G p s) (q : Occ V E) (side : Bool) :
    a.val (q,side) = a.val (originalRep G p (clausePort G p s q),true) := by
  have h := a.property.2.1 q (originalRep G p (clausePort G p s q))
    (clausePort_rep G p s _).symm
  cases side
  · exact (a.property.1 q).trans h
  · exact h

/-- Exact source subdivision: every satisfying physical wire marking
comes from a unique original five-copy CNF assignment. -/
def subdivisionModels {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    Models G p s ≃ PhysicalModels G p s where
  toFun a := ⟨fun v => a.val (originalRep G p v,true), by
    intro i
    have h := a.property.2.2 i
    rw [occurs_eq_at_model G p s a (i,false) false,
      occurs_eq_at_model G p s a (i,true) false] at h
    exact h⟩
  invFun x := ⟨fun q => x.val (clausePort G p s q.1), by
    refine ⟨fun _ => rfl,fun q r h => congrArg x.val h,?_⟩
    intro i
    exact x.property i⟩
  left_inv a := by
    apply Subtype.ext
    funext q
    exact (occurs_eq_at_model G p s a q.1 q.2).symm
  right_inv x := by
    apply Subtype.ext
    funext v
    exact congrArg x.val (clausePort_rep G p s v)

noncomputable def originCount {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) : ℕ :=
  Fintype.card (Models G p s)

theorem originCount_eq {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    originCount G p s = satCount G p s :=
  Fintype.card_congr (subdivisionModels G p s)

theorem wires_card {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) : Fintype.card (Edge V E) = 30*Fintype.card V+4 := by
  have h := literal_ports_count G p
  simp only [Edge,Occ,Fintype.card_prod,Fintype.card_bool]
  omega

theorem split_origin_endpoint {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H) (w : Word k) (b : Bool) :
    originCount (Split.graph H p) (Split.ports H p) (hostEnabled k w b) =
      CaterpillarRange.output k (w,b) := by
  rw [originCount_eq,Split.exact_endpoint]

theorem split_origin_decoder {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (B b : ℕ) {Menu : Type*} [Fintype Menu] (Side : Menu → Type*) [∀ m, Fintype (Side m)]
    (hmenu : Fintype.card Menu ≤ 2^B) (hside : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (menu : (Split.V k → Bool) → Menu) (aux : (s : Split.V k → Bool) → Side (menu s))
    (decode : (Σ m, Side m) → ℕ)
    (hc : ∀ s, decode ⟨menu s,aux s⟩ = originCount (Split.graph H p) (Split.ports H p) s) :
    ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤ ((B+b : ℕ) : ℚ) :=
  Split.c6_decoder_lower H p B b Side hmenu hside menu aux decode
    (fun s => (hc s).trans (originCount_eq _ _ _))

#print axioms clausePort_rep
#print axioms subdivisionModels
#print axioms originCount_eq
#print axioms wires_card
#print axioms split_origin_endpoint
#print axioms split_origin_decoder

end NativeOrigin
end V8PooledRange
