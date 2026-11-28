import V8PooledMenuRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace V8PooledMenu
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy

private theorem sigma_cast {M : Type*} (F : M → Type*) {m n : M}
    (h : m=n) (x : F m) : (⟨n,cast (congrArg F h) x⟩ : Σ a, F a) = ⟨m,x⟩ := by
  cases h
  rfl

/-- The finite C4–C6 transfer on one literal graph. Menu, side state and
exact integer target all refer to the same switch input. -/
theorem actual_pooled_decoder {k : ℕ} {E : Type} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (P : Packing (Split.graph H p) (Split.ports H p))
    (hu : 0<rootU (Split.V k)) (huM : rootU (Split.V k)≤wireSize (Split.V k))
    (L : PublicPrecision (Split.V k)) {f : ℤ[X]}
    (pr : Probes (Split.V k) f) (hf : f.Monic) (hd : 0<f.natDegree)
    (b : ℕ) (Side : WholeMenu f P hu huM L → Type*) [∀ m, Fintype (Side m)]
    (hSide : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (aux : (s : Split.V k → Bool) → Side (nativeMenu P hu huM L pr hf s))
    (decode : (Σ m, Side m) → ℕ)
    (correct : ∀ s, decode ⟨nativeMenu P hu huM L pr hf s,aux s⟩ =
      NativeOrigin.originCount (Split.graph H p) (Split.ports H p) s) :
    ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤
      ((pooledBits (rootA (Split.V k)) (rootU (Split.V k)) L.prec + b : ℕ) : ℚ) := by
  let Code := PublicTape hu huM L
  let enc := encodeWhole P hu huM L
  let recv := decodeWhole P hu huM L pr
  let F (m : Code) := Side (recv m)
  letI (m : Code) : Fintype (F m) := inferInstanceAs (Fintype (Side (recv m)))
  let asSide (s : Split.V k → Bool) : F (enc s) :=
    cast (congrArg Side (nativeMenu_eq P hu huM L pr hf hd s)) (aux s)
  let d (st : Σ m, F m) : ℕ := decode ⟨recv st.1,st.2⟩
  refine NativeOrigin.split_origin_decoder H p _ b F
    (le_of_eq (tape_budget hu huM L)) (fun m => hSide (recv m)) enc asSide d ?_
  intro s
  change decode ⟨recv (enc s),asSide s⟩ = _
  exact (congrArg decode (sigma_cast Side (nativeMenu_eq P hu huM L pr hf hd s) (aux s))).trans (correct s)

#print axioms actual_pooled_decoder

end V8PooledMenu
