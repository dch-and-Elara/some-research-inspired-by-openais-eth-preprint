import P11R12ProbabilityProjection
import P11R12ProbabilityPicked
import Mathlib.Tactic

/-! Reindex actual unordered types once, retaining the same heterogeneous
sample at each key. A finite ordinal is only needed by the existing tail
theorem; the packing itself still uses its original key type. -/
namespace P11R12Probability
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11SourceGeometry RandomEndpoint
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b n : ℕ}

abbrev Indexed (b : ℕ) (e : Fin n ≃ Key (Fin a) K) (j : Fin n) := TypeDraw b (e j)

noncomputable def sampleWeight (b : ℕ) (e : Fin n ≃ Key (Fin a) K) (j : Fin n) :
    Indexed b e j→ℚ := uniform _

omit [Fintype W] in theorem sampleWeight_prob (b : ℕ) (e : Fin n ≃ Key (Fin a) K)
    (j : Fin n) : PacketVariance.prob (sampleWeight b e j) := by
  letI : Nonempty (Indexed b e j) := ⟨(fun _ => false,fun _ => Equiv.refl _)⟩
  exact uniform_prob _

def toDraw (e : Fin n ≃ Key (Fin a) K) (x : ∀ j, Indexed b e j) : Draw a b K :=
  Equiv.piCongrLeft (TypeDraw b) e x

omit [Fintype W] in theorem toDraw_at (e : Fin n ≃ Key (Fin a) K)
    (x : ∀ j, Indexed b e j) (j : Fin n) : toDraw e x (e j) = x j :=
  Equiv.piCongrLeft_apply_apply (TypeDraw b) e x j

omit [Fintype W] in theorem toDraw_receives (e : Fin n ≃ Key (Fin a) K)
    (x : ∀ j, Indexed b e j) (k : Key (Fin a) K) :
    toDraw e x k = cast (congrArg (TypeDraw b) (e.apply_symm_apply k)) (x (e.symm k)) :=
  Equiv.piCongrLeft_apply_eq_cast x k

def legType (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K) (w : W) : Fin n :=
  e.symm (key (f w))

def fromCoordinate (e : Fin n ≃ Key (Fin a) K) (f : W→Cell (Fin a) K)
    (w : W) : Indexed b e (legType e f w) ≃ TypeDraw b (key (f w)) :=
  Equiv.cast (congrArg (TypeDraw b) (e.apply_symm_apply (key (f w))))

noncomputable def hit (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (right : Bool) (w : W)
    (z : Indexed b e (legType e f w)) : Bool :=
  decide (realEvent f cap w right (fromCoordinate e f w z))

theorem chart (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (right : Bool)
    (x : ∀ j, Indexed b e j) (w : W) :
    (seat (toDraw e x) f cap w).2.val = GuardedPacking.endpoint (2^a) right ↔
      hit e f cap right w (x (legType e f w)) = true := by
  change (seat (toDraw e x) f cap w).2.val = (endpointIndex a right).val ↔ _
  rw [← Fin.ext_iff, sampled_endpoint_is_local,toDraw_receives]
  simp [hit,fromCoordinate,legType]

omit [Fintype W] in theorem fromCoordinate_transport (e : Fin n ≃ Key (Fin a) K) (f : W → Cell (Fin a) K)
    (w w' : W) (h : legType e f w=legType e f w') (x : Indexed b e (legType e f w)) :
    fromCoordinate e f w' (cast (congrArg (Indexed b e) h) x) =
      cast (congrArg (TypeDraw b) (e.symm.injective h)) (fromCoordinate e f w x) := by
  simp only [fromCoordinate,Equiv.cast_apply,cast_cast]

theorem uniform_transport {U V : Type*} [Fintype U] [Fintype V]
    (e : U≃V) (P : U→Prop) (Q : V→Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q (e x)) :
    probability (uniform U) P = probability (uniform V) Q := by
  unfold uniform
  rw [uniform_event_card,uniform_event_card,
    Nat.card_congr (Equiv.subtypeEquiv e h),Nat.card_congr e]

#print axioms sampleWeight_prob
#print axioms toDraw_at
#print axioms toDraw_receives
#print axioms chart
#print axioms fromCoordinate_transport
#print axioms uniform_transport
end P11R12Probability
