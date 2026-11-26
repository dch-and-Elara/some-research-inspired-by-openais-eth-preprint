import P5D1LiteralDecoder
import J6R9RecursiveAssemble

/-! Literal R9 receiving addresses with the child representatives
chosen *before* multiplication. Only the fixed decoder basis is
lifted; the post-decoding residue section is not used. -/
namespace Paper5.D1Literal
open scoped BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive

section Restrict

variable {B : Type*} [CommRing B]

def pickFin (k : ℕ) : (ℕ → B) →ₗ[B] (Fin k → B) where
  toFun b j := b j.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Restrict

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

abbrev Terms (S : Shape Host Mode) (c : Call Host) (t : Center S c) :=
  ↥(J6RecursiveMenu.menu (registerPrecision S c t) (S.weight c t.val))

abbrev Orders (S : Shape Host Mode) (c : Call Host) (t : Center S c) :=
  Fin (order c.edges (S.levelWidth c.depth) t.val)

noncomputable def receivingDecoder
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X]) :
    (Probe S c → Box f ell (registerPrecision S c t)) →ₗ[Box f ell (registerPrecision S c t)]
      (Orders S c t → Box f ell (registerPrecision S c t)) :=
  let k := order c.edges (S.levelWidth c.depth) t.val
  (pickFin k).comp (nativeDecoder (sampleNode S f ell c fit t) k normal)

noncomputable def liftedReply
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X]) (j : Orders S c t) :
    IntRing f ell :=
  let rep := representative (registerPrecision S c t) f ell
  liftedCoefficient (receivingDecoder S f ell c fit t normal) rep
    (fun z => liftedChildSum rep (fun (β : Terms S c t) (g : Fin 64) => answers ⟨t,z,β,g⟩)) j

theorem liftedReply_reduce
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X]) (j : Orders S c t) :
    reduce (registerPrecision S c t) f ell (liftedReply S f ell c fit answers t normal j) =
      (quotientAt S f ell c fit answers t normal).coeff j.val := by
  unfold liftedReply
  rw [reduce_liftedChild_decode _ _ _ (representative_spec _ _ _)]
  rfl

noncomputable def replyWeight
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X])
    (w : Orders S c t → RatRing f ell) (z : Probe S c) : RatRing f ell :=
  publicWeight (receivingDecoder S f ell c fit t normal)
    (representative (registerPrecision S c t) f ell) (embed f ell) w z

/-- No extra retained-coefficient index is introduced into the actual
root product menu. The weight depends on (t,z), not on beta or g. -/
theorem liftedReply_one_product_per_address
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c)
    (normal : (Box f ell (registerPrecision S c t))[X])
    (w : Orders S c t → RatRing f ell) :
    (∑ j, w j * embed f ell (liftedReply S f ell c fit answers t normal j)) =
      ∑ z : Probe S c, ∑ β : Terms S c t, replyWeight S f ell c fit t normal w z *
        ∏ g : Fin 64, embed f ell (representative (registerPrecision S c t) f ell
          (answers ⟨t,z,β,g⟩)) := by
  exact one_term_per_native_slot (receivingDecoder S f ell c fit t normal)
    (representative (registerPrecision S c t) f ell) (embed f ell) w
    (fun z (β : Terms S c t) (g : Fin 64) => answers ⟨t,z,β,g⟩)

#print axioms liftedReply_reduce
#print axioms liftedReply_one_product_per_address
end Paper5.D1Literal

