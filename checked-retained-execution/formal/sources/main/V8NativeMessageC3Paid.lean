import V8NativeMessageC3Rank

set_option autoImplicit false
set_option warningAsError true

namespace V8NativeMessage.C3
open scoped Classical BigOperators
noncomputable section
variable {H G : Type*} (b : H→G→ℕ)

/-- One trace slot pays for at most one distinguished block or one
private point occurrence. Repeated visits are allowed; no event is
silently introduced just because the expression exists. -/
inductive PaidEvent where
  | block (h : H)
  | point (h : H) (g : G) (q : Fin (b h g))

variable {W steps : ℕ}
    (emits : Fin steps → Fin W → Option (PaidEvent b))
    (covers : ∀ e, ∃ t w, emits t w=some e)

include covers in
theorem paid_trace_injective :
    ∃ addr : PaidEvent b → Fin steps × Fin W, Function.Injective addr := by
  have he (e : PaidEvent b) : ∃ q : Fin steps × Fin W, emits q.1 q.2=some e := by
    obtain ⟨t,w,h⟩ := covers e
    exact ⟨(t,w),h⟩
  choose q hq using he
  refine ⟨q,?_⟩
  intro e e' h
  have e₀ := (hq e).symm.trans (show emits (q e).1 (q e).2=some e' by rw [h]; exact hq e')
  exact Option.some.inj e₀

variable [Fintype H] [Fintype G]

omit [Fintype G] in
include covers in
theorem trace_bounds :
    Fintype.card H ≤ W*steps ∧ ∀ h g, b h g≤W*steps := by
  obtain ⟨q,hq⟩ := paid_trace_injective b emits covers
  refine ⟨?_,fun h g => ?_⟩
  · have h : Function.Injective (q ∘ PaidEvent.block (b:=b)) := by
      intro u v hh
      exact PaidEvent.block.inj (hq hh)
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective _ h
  · have inj : Function.Injective (fun k : Fin (b h g) => q (.point h g k)) := by
      intro u v hh
      have h' : PaidEvent.point h g u=PaidEvent.point h g v := hq hh
      cases h'
      rfl
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective _ inj

include covers in
theorem C3_trace_budget {m κmax : ℕ}
    (κ : H→ℕ) (rank : 2^m≤∑ h, κ h * ∏g, b h g)
    (depth : ∀h, κ h≤κmax) :
    2^m≤κmax*(W*steps)^(Fintype.card G+1) := by
  obtain ⟨blocks,points⟩ := trace_bounds b emits covers
  exact C3_paid_budget κ b rank blocks points depth

#print axioms paid_trace_injective
#print axioms trace_bounds
#print axioms C3_trace_budget

end
end V8NativeMessage.C3