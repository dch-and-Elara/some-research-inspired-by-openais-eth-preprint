import V8PooledRangeExpansion
import V8PooledRangeNormalized
import V8PooledRangeResults

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange
namespace Split

/-- All finite graph and exact-count conclusions for the v8 completion.
The complete native slot encoder is a separate input to the decoder bound. -/
structure C6Certificate {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H) (γ : ℚ) : Prop where
  simple : IsSimple (graph H p)
  expanded : Expansion (graph H p) (γ / (4*(γ+4)))
  order_exact : Fintype.card (V k) = 6*k+10
  binary : ∀ s i, (support (graph H p) (ports H p) s i).card = 2
  normalized_supports : ∀ s, Function.Injective (support (graph H p) (ports H p) s)
  occurrence_counts : ∀ s x,
    Nat.card {q : ClauseId (V k) (Edges k E) × Bool //
        clausePort (graph H p) (ports H p) s q = x} =
      x.elim (fun _ => 3) (fun _ => 1)
  physical_sizes :
    (2*(2*Fintype.card (ClauseId (V k) (Edges k E))) = 30*Fintype.card (V k)+4) ∧
    (Fintype.card (Variable (V k)) + Fintype.card (ClauseId (V k) (Edges k E)) =
      25*Fintype.card (V k)/2+3) ∧
    (Fintype.card (Variable (V k)) + 1 = 5*Fintype.card (V k)+3)
  exact_endpoints : ∀ w b,
    satCount (graph H p) (ports H p) (hostEnabled k w b) = CaterpillarRange.output k (w,b)
  pair_inj : Function.Injective (fun w : Word k =>
    (satCount (graph H p) (ports H p) (hostEnabled k w false),
     satCount (graph H p) (ports H p) (hostEnabled k w true)))
  range_bound :
    ((Fintype.card (V k) : ℝ)-10)/12 ≤ Real.logb 2 ((endpointRange H p).card : ℝ)
  terminal_bound : ∀ s, satCount (graph H p) (ports H p) s < 2^(5*Fintype.card (V k)+3)

/-- No input-dependent graph, chosen terminal value or completed graph
condition is supplied to the proof: it constructs the graph and all
its physical clause variables from a simple expanding cubic core at
the prescribed order. -/
theorem c6_certificate {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (hs : IsSimple H) (γ : ℚ) (hγ : 0 ≤ γ) (he : Expansion H γ) :
    C6Certificate H p γ where
  simple := isSimple H p hs
  expanded := expansion H p γ hγ he
  order_exact := order k
  binary := support_width (graph H p) (ports H p)
  normalized_supports := fun s => supports_injective (graph H p) (ports H p) s (isSimple H p hs).loopless
  occurrence_counts := variable_degree (graph H p) (ports H p)
  physical_sizes := source_register_dimensions (graph H p) (ports H p)
  exact_endpoints := exact_endpoint H p
  pair_inj := exact_pair H p
  range_bound := c6_endpoint_log_range H p
  terminal_bound := physical_terminal_precision (graph H p) (ports H p)

/-- Finite C6 consequence even with adversarial dependent side state.
The only data about the pooled C4 channel used here are its alphabet
and the per-menu cardinality bound of the additional side channel. -/
theorem c6_decoder_lower {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (B b : ℕ) {Menu : Type*} [Fintype Menu] (Side : Menu → Type*) [∀ m, Fintype (Side m)]
    (hmenu : Fintype.card Menu ≤ 2^B) (hside : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (menu : (V k → Bool) → Menu) (aux : (s : V k → Bool) → Side (menu s))
    (decode : (Σ m, Side m) → ℕ)
    (hc : ∀ s, decode ⟨menu s,aux s⟩ = satCount (graph H p) (ports H p) s) :
    ((Fintype.card (V k) : ℚ)-10)/12 ≤ ((B+b : ℕ) : ℚ) := by
  have g := exact_decoder_budget H p B b Side hmenu hside menu aux decode hc
  have h : (Fintype.card (V k) : ℚ) ≤ 12 * ((B+b : ℕ) : ℚ) + 10 := by exact_mod_cast g
  linarith

#print axioms c6_certificate
#print axioms c6_decoder_lower

end Split
end V8PooledRange
