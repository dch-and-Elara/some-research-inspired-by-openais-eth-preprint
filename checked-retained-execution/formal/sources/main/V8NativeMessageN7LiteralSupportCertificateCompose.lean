import V8NativeMessageN7LiteralSupportBlock

/-! A finite local-table certificate is sufficient. Only the displayed
component-local sign words are enumerated. This theorem measures the
number of word pairs, not the cost of finding an accepting layout. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000
noncomputable section

variable {S K E C R : Type} [Fintype S] [Fintype K] [Fintype E] [Fintype C] [CommRing R]

def localPairValue (owner : S→K) (left right : E→S) (σ : S→Bool) (k : K) : R :=
  ∏ e : Fiber (owner ∘ left) k, if σ (left e.val)||σ (right e.val) then 1 else 0

omit [Fintype S] in
theorem verified_component_local_tables_compose
    (owner : S→K) (left right : E→S)
    (colocated : ∀ e,owner (left e)=owner (right e))
    (eval : K→(S→Bool)→R)
    (locality : ∀ k σ τ,(∀ s,owner s=k→σ s=τ s)→eval k σ=eval k τ)
    (check : ∀ k (x : Fiber owner k→Bool),
      eval k (fillFiber owner k true x)=localPairValue owner left right (fillFiber owner k true x) k)
    (σ : S→Bool) :
    (∏ k,eval k σ)=∏ e : E,if σ (left e)||σ (right e) then 1 else 0 := by
  have exactAlong (k : K) : eval k σ=localPairValue owner left right σ k := by
    let σ' := fillFiber owner k true (fun j=>σ j.val)
    have matchLocal (s : S) (h : owner s=k) : σ' s=σ s :=
      fillFiber_roundtrip owner k true σ s h
    calc
      _ = eval k σ' := locality k σ σ' (fun s hs=>(matchLocal s hs).symm)
      _ = localPairValue owner left right σ' k := check k _
      _ = _ := by
        unfold localPairValue
        refine Finset.prod_congr rfl fun e _=>?_
        have first : owner (left e.val)=k := e.property
        have second : owner (right e.val)=k := (colocated e.val).symm.trans first
        rw [matchLocal _ first,matchLocal _ second]
  calc
    _ = ∏ k,localPairValue owner left right σ k := Finset.prod_congr rfl (fun k _=>exactAlong k)
    _ = _ := by
      unfold localPairValue
      symm
      exact J6BlockFactor.prod_rows (owner∘left)
        (fun e=>if σ (left e)||σ (right e) then (1:R) else 0)

omit [Fintype K] in
theorem actual_certificate_word_pair_count
    (pinOwner : S→K) (colOwner : C→K) (k : K) :
    Fintype.card ((Fiber pinOwner k→Bool)×(Fiber colOwner k→Bool))=
      2^(Fintype.card (Fiber pinOwner k)+Fintype.card (Fiber colOwner k)) := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fun,Fintype.card_bool,pow_add]

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.verified_component_local_tables_compose
#print axioms V8NativeMessage.N7LiteralSupport.actual_certificate_word_pair_count
