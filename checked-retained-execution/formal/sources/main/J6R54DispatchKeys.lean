import J6R53DispatchRawProbe

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 13800000
set_option maxRecDepth 3300
set_option linter.unusedSectionVars false

/-! A raw callback does not take a decoded mode. It charges one current
route discovery, allocates a LocalLoad from the actual emitted raw
vector, and performs the actual scoped continuation. Layout discovery
is a metered input; it cannot be replaced by free typed-mode decoding. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R25PreparedSupply
open J6R53Dispatch
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion
open J6R48DFS J6R49DFS
noncomputable section

variable {f : ℤ[X]} {ell q Δ : ℕ} {SP : Params (f:=f) (ell:=ell)} {c : Call (PhysicalHost f ell)}
variable {sel : Selector SP Δ}
local notation "W" => J6R15ModeCost.Word q
local notation "M" => (shape SP Δ sel)

theorem literal_raw_decodes_its_key
    {d : Ready SP Δ c} {t : Center SP c}
    (I : SiteTape sel d t q) (β : NativeMenu M c t) (raw : List W)
    (h : raw.map Word.val=vectorKey sel d t I β) :
    decodeAt I raw=some β := by
  have same : raw=(vectorKey sel d t I β).map (word (q:=q)) :=
    (canonical_tuple_words raw).symm.trans (congrArg (List.map (word (q:=q))) h)
  rw [same]
  exact decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)

theorem same_selected_mode_from_same_incoming
    {d d' : Ready SP Δ c} {t t' : Center SP c}
    (tc : t'=t)
    (I : SiteTape sel d t q) (I' : SiteTape sel d' t' q) (same : HEq I' I)
    (raw : List W) (α : NativeMenu M c t') (β : NativeMenu M c t)
    (rawEq : raw.map Word.val=vectorKey sel d' t' I' α) (decoded : decodeAt I raw=some β) :
    HEq α β := by
  cases tc
  have tape : I'=I := eq_of_heq same
  subst I'
  have h : decodeAt I raw=some α := literal_raw_decodes_its_key I α raw rawEq
  exact heq_of_eq (Option.some.inj (h.symm.trans decoded))

theorem native_field_ext
    (w : NativeAddress M c)
    (t : Center SP c) (z : Probe SP c) (β : NativeMenu M c t) (g : Fin 64)
    (ht : w.1=t) (hz : w.2.1=z) (hβ : HEq w.2.2.1 β) (hg : w.2.2.2=g) :
    w=⟨t,z,β,g⟩ := by
  rcases w with ⟨t0,z0,b0,g0⟩
  dsimp only at ht hz hβ hg
  subst t
  subst z
  subst g
  have mode : b0=β := eq_of_heq hβ
  subst β
  rfl

#print axioms literal_raw_decodes_its_key
#print axioms same_selected_mode_from_same_incoming
#print axioms native_field_ext
end
end J6R54Dispatch

