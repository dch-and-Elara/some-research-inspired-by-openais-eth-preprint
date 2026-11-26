import P5HybridDUnclonedGraph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16000000

/-! Exact occurrence counts on the whole literal bipartite graph, including
the four-port tree's new bridge and the still one-wire unary pin. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators
open J6R10Repack J1MainSourceCollision

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => network F cubic

theorem subdivision_degree (e : Link F) : (varFibre (N).col e).card=2 := by
  let emb : Bool ↪ Wire F := ⟨fun b=>(e,b),fun _ _ h=>congrArg Prod.snd h⟩
  have h : varFibre (N).col e=Finset.univ.map emb := by
    ext q
    rcases q with ⟨p,b⟩
    cases b <;> simp [varFibre,network,emb]
  rw [h,Finset.card_map,Finset.card_univ,Fintype.card_bool]

def treeWire (u : Tree W) : Unit⊕Bool→Wire F
  | .inl _ => (.inr u.1,u.2)
  | .inr b => (.inl ((occSite F cubic).symm (u,b)),false)

omit [Fintype W] in
theorem tree_wire_exact_owner (u : Tree W) (i : Unit⊕Bool) : (N).row (treeWire F cubic u i)=.inl u := by
  rcases i with (_|b)
  · rfl
  · change Sum.inl ((occSite F cubic) ((occSite F cubic).symm (u,b))).1=.inl u
    rw [Equiv.apply_symm_apply]

def treeFibre (u : Tree W) : ↥(facFibre (N).row (.inl u)) ≃ Unit⊕Bool where
  toFun w := match w.val.1 with
    | .inl p => .inr (occSite F cubic p).2
    | .inr _ => .inl ()
  invFun i := ⟨treeWire F cubic u i, by simp [facFibre,tree_wire_exact_owner]⟩
  left_inv w := by
    obtain ⟨⟨p,b⟩,hp⟩ := w
    have h := (Finset.mem_filter.mp hp).2
    rcases p with p|v <;> cases b
    · apply Subtype.ext
      have hu : (occSite F cubic p).1=u := Sum.inl.inj h
      change (Sum.inl ((occSite F cubic).symm (u,(occSite F cubic p).2)),false)=
        (Sum.inl p,false)
      rw [show (u,(occSite F cubic p).2)=occSite F cubic p from Prod.ext hu.symm rfl]
      rw [Equiv.symm_apply_apply]
    · simp [network] at h
    · apply Subtype.ext
      have he : (v,false)=u := Sum.inl.inj h
      change (Sum.inr u.1,u.2)=(Sum.inr v,false)
      rw [←he]
    · apply Subtype.ext
      have he : (v,true)=u := Sum.inl.inj h
      change (Sum.inr u.1,u.2)=(Sum.inr v,true)
      rw [←he]
  right_inv i := by
    rcases i with (v|b)
    · cases v
      rfl
    · change Sum.inr ((occSite F cubic) ((occSite F cubic).symm (u,b))).2=Sum.inr b
      rw [Equiv.apply_symm_apply]

theorem tree_degree (u : Tree W) : (facFibre (N).row (.inl u)).card=3 := by
  have h := Fintype.card_congr (treeFibre F cubic u)
  simpa only [Fintype.card_sum,Fintype.card_unit,Fintype.card_bool,Fintype.card_coe] using h

omit [Fintype W] in
theorem clause_row_exact (t : Factor F) (w : Wire F) :
    (N).row w=.inr t ↔ ∃ p : Occ F,w=(.inl p,true) ∧ factorOf F p=t := by
  constructor
  · rcases w with ⟨(p|u),b⟩ <;> cases b
    · simp [network]
    · exact fun h=>⟨p,rfl,Sum.inr.inj h⟩
    · simp [network]
    · simp [network]
  · rintro ⟨p,rfl,h⟩
    exact congrArg Sum.inr h

def clauseBit : Occ F→Bool
  | .inl _ => false
  | .inr x => x.2

omit [Fintype W] [DecidableEq W] in
theorem distinct_clause_ports :
    Function.Injective (fun p : Occ F=>(factorOf F p,clauseBit F p)) := by
  rintro (p|⟨p,b⟩) (q|⟨q,c⟩) h <;> simp [factorOf,clauseBit] at h ⊢ <;> exact h

theorem clause_degree (t : Factor F) : (facFibre (N).row (.inr t)).card≤2 := by
  let a (w : ↥(facFibre (N).row (.inr t))) : Bool :=
    match w.val.1 with | .inl p=>clauseBit F p | .inr _=>false
  have ha : Function.Injective a := by
    intro p q h
    obtain ⟨x,hx,fx⟩ := (clause_row_exact F cubic t _).mp (Finset.mem_filter.mp p.property).2
    obtain ⟨y,hy,fy⟩ := (clause_row_exact F cubic t _).mp (Finset.mem_filter.mp q.property).2
    have hb : clauseBit F x=clauseBit F y := by
      unfold a at h
      rw [hx,hy] at h
      exact h
    have xy : x=y := distinct_clause_ports F (Prod.ext (fx.trans fy.symm) hb)
    exact Subtype.ext (hx.trans ((congrArg (fun p : Occ F=>((.inl p : Link F),true)) xy).trans hy.symm))
  simpa only [Fintype.card_coe,Fintype.card_bool] using Fintype.card_le_of_injective a ha

theorem old_degree (v : Old F) : (facFibre (N).row v).card≤3 := by
  cases v with
  | inl u => rw [tree_degree F cubic u]
  | inr t => exact (clause_degree F cubic t).trans (by decide)

theorem pin_has_one_wire (v : W) : (facFibre (N).row (.inr (.inl v))).card=1 := by
  have h : facFibre (N).row (.inr (.inl v))={pinWire F v} := by
    ext p
    simp [facFibre,pin_row_exact F cubic]
  rw [h,Finset.card_singleton]

#print axioms subdivision_degree
#print axioms tree_wire_exact_owner
#print axioms treeFibre
#print axioms tree_degree
#print axioms clause_row_exact
#print axioms distinct_clause_ports
#print axioms clause_degree
#print axioms old_degree
#print axioms pin_has_one_wire
end
end Paper5.HybridDUncloned
