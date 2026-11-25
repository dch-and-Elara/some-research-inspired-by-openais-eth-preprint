import ReceiverOrderGroupcast
import Mathlib.Data.Fintype.BigOperators

open Reconstruction.ColorAlphabet

namespace Reconstruction.ReleaseColor

noncomputable section

variable {T : Type*} {A : T → Type*} {X B : Type*}

/-- Each physical demand is recovered by an arbitrary function of the
common broadcast and its receiver's known messages. -/
def GroupcastDecodes (send : (Word A → X) → B) : Prop :=
  ∀ (u : Word A) (t : T), ∃ d : B → ({v : Word A // (v t).1 = (u t).2} → X) → X,
    ∀ z, d (send z) (fun v => z v.val) = z u

/-- Revealing all messages outside a generalized-independent collection leaves
an injective broadcast on the messages inside. The broadcast need not be linear. -/
theorem groupcast_injective_on_independent (send : (Word A → X) → B)
    (hdec : GroupcastDecodes send) (S : Finset (Word A)) (hS : GeneralizedIndependent S)
    {z w : Word A → X} (hsend : send z = send w) (hrest : ∀ v ∉ S, z v = w v) : z = w := by
  classical
  by_contra hn
  let U := S.filter (fun v => z v ≠ w v)
  have hU : U.Nonempty := by
    by_contra h
    apply hn
    funext v
    by_cases hv : v ∈ S
    · by_contra hd
      exact h ⟨v, Finset.mem_filter.mpr ⟨hv,hd⟩⟩
    · exact hrest v hv
  obtain ⟨x, ⟨u,hu,hxu⟩, hk⟩ := hS U (Finset.filter_subset _ _) hU
  obtain ⟨d,hd⟩ := hdec u x.1
  have he : (fun v : {v : Word A // (v x.1).1 = (u x.1).2} => z v.val) =
      fun v => w v.val := by
    funext v
    by_cases hv : v.val ∈ S
    · by_contra hh
      exact hk v.val (Finset.mem_filter.mpr ⟨hv,hh⟩) (v.property.trans hxu)
    · exact hrest v.val hv
  exact (Finset.mem_filter.mp hu).2 ((hd z).symm.trans (by rw [hsend,he,hd]))

/-- The corresponding finite-alphabet broadcast cardinality bound, with the
complement of the selected messages fixed. -/
theorem groupcast_broadcast_card [Fintype X] [Fintype B] (base : X)
    (send : (Word A → X) → B) (hdec : GroupcastDecodes send)
    (S : Finset (Word A)) (hS : GeneralizedIndependent S) :
    Fintype.card X ^ S.card ≤ Fintype.card B := by
  classical
  let fill (x : S → X) (v : Word A) : X := if hv : v ∈ S then x ⟨v,hv⟩ else base
  let f (x : S → X) : B := send (fill x)
  have hf : Function.Injective f := by
    intro x y h
    have he := groupcast_injective_on_independent send hdec S hS h
      (fun v hv => by simp [fill,hv])
    funext v
    simpa [fill,v.property] using congrFun he v.val
  have hh := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_fun] using hh

end
end Reconstruction.ReleaseColor
