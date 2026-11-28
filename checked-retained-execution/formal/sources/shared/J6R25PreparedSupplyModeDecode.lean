import J6R17ModeTapeTuple
import J6R16ModeCostMeter


/-! Unique typed meaning of the byte stream emitted by the literal
source mode weights. This list of dependent NativeMenu tags is for
the existing proof interface only. Raw sparse support records are
actually written by emitSupport. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial J6R15ModeCost J6R16ModeCost J6R17ModeTape
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint

theorem choose_in_order {A B : Type*} (key : B→A) (xs : List A)
    (every : ∀ v∈xs,∃ b,key b=v) : ∃ bs : List B,bs.map key=xs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨v,hv⟩ := every x List.mem_cons_self
    obtain ⟨vs,hvs⟩ := ih (fun u hu=>every u (List.mem_cons_of_mem _ hu))
    exact ⟨v::vs,by simp only [List.map_cons,hv,hvs]⟩

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}
variable (d : J6R12Blueprint.Ready S Δ c) (t : Center S c)
variable (I : SiteTape sel d t q)

def vectorKey (β : NativeMenu (shape S Δ sel) c t) : List ℕ :=
  I.modes.map (fun m=>β.val ((site_mode_equiv sel d t).symm m))

theorem vector_key_inj : Function.Injective (vectorKey sel d t I) := by
  intro β γ h
  apply Subtype.ext
  ext a
  have e := List.map_inj_left.mp h ((site_mode_equiv sel d t) a) (I.allModes _)
  simpa only [Equiv.symm_apply_apply] using e

theorem native_mode_order :
    ∃ order : List (NativeMenu (shape S Δ sel) c t),
      order.Nodup ∧ (∀ β,β∈order) ∧
      order.map (vectorKey sel d t I)=strictTuples (I.modes.map modeWeight) (registerPrecision S c t) := by
  let xs := strictTuples (I.modes.map modeWeight) (registerPrecision S c t)
  let key := vectorKey sel d t I
  have fit (v : List ℕ) (hv : v∈xs) : ∃ β,key β=v :=
    ((native_tuple_iff sel d t I.modes I.nodup I.allModes v).mp hv).exists
  obtain ⟨modes,hModes⟩ := choose_in_order key xs fit
  have pos (w : ℕ) (hw : w∈I.modes.map modeWeight) : 0<w := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hw
    exact (modeWeight_bounds m).1
  have hN : (modes.map key).Nodup := hModes ▸ (strictTuples_exact _ _ pos).1
  refine ⟨modes,hN.of_map _,?_,hModes⟩
  intro β
  have hb : key β∈xs := by
    apply (native_tuple_iff sel d t I.modes I.nodup I.allModes (key β)).mpr
    refine ⟨β,rfl,fun mu h=>vector_key_inj sel d t I h⟩
  rw [←hModes] at hb
  obtain ⟨mu,hmu,e⟩ := List.mem_map.mp hb
  exact (vector_key_inj sel d t I e) ▸ hmu

#print axioms vector_key_inj
#print axioms native_mode_order
end J6R25PreparedSupply


