import AffineEdgeEncoder

open scoped BigOperators Polynomial

namespace AffineCost

open AffineEdge

inductive Match (q : ℕ)
  | zero
  | one (t : Fin q)
  | two (s t : Fin q)
  deriving DecidableEq

def Match.ofList {q : ℕ} : List (Fin q) → Match q
  | [] => .zero
  | [t] => .one t
  | s :: t :: _ => .two s t

def scan {q : ℕ} (u v : Word q) : Match q :=
  Match.ofList ((List.finRange q).filter (fun t => v.1 t == u.2 t))

theorem scan_spec {q : ℕ} (u v : Word q) :
    match scan u v with
    | .zero => ∀ t, v.1 t ≠ u.2 t
    | .one s => ∀ t, v.1 t = u.2 t ↔ t = s
    | .two s t => s ≠ t ∧ v.1 s = u.2 s ∧ v.1 t = u.2 t := by
  let l := (List.finRange q).filter (fun t => v.1 t == u.2 t)
  have hm (t : Fin q) : t ∈ l ↔ v.1 t = u.2 t := by simp [l]
  have hn : l.Nodup := (List.nodup_finRange q).filter _
  change match Match.ofList l with
    | .zero => ∀ t, v.1 t ≠ u.2 t
    | .one s => ∀ t, v.1 t = u.2 t ↔ t = s
    | .two s t => s ≠ t ∧ v.1 s = u.2 s ∧ v.1 t = u.2 t
  rcases l with _ | ⟨s, _ | ⟨t, tl⟩⟩
  · intro t ht
    exact List.not_mem_nil ((hm t).mpr ht)
  · intro t
    exact (hm t).symm.trans List.mem_singleton
  · exact ⟨fun h => (List.nodup_cons.mp hn).1 (by simp [h]),
      (hm s).mp (by simp), (hm t).mp (by simp)⟩

theorem compl_invol {q : ℕ} (a : Bits q) : complement (complement a) = a := by
  funext t
  simp [complement]

theorem eq_compl_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem first_of_zero {q : ℕ} {u v : Word q} (h : scan u v = .zero) :
    v.1 = complement u.2 := by
  have hs := scan_spec u v
  rw [h] at hs
  exact funext fun t => eq_compl_of_ne (hs t)

theorem first_of_one {q : ℕ} {u v : Word q} {s : Fin q} (h : scan u v = .one s) :
    v.1 = flip s (complement u.2) := by
  have hs := scan_spec u v
  rw [h] at hs
  funext t
  by_cases ht : t = s
  · subst t
    simpa [complement] using (hs s).2 rfl
  · rw [flip_other ht]
    exact eq_compl_of_ne (fun hv => ht ((hs t).1 hv))

theorem hard_zero {q : ℕ} {v : Word q} (h : scan v v = .zero) :
    hardWord v.1 none = v := by
  refine Prod.ext rfl ?_
  simpa [hardWord, step, compl_invol] using congrArg complement (first_of_zero h)

theorem hard_one {q : ℕ} {v : Word q} {s : Fin q} (h : scan v v = .one s) :
    hardWord v.1 (some s) = v := by
  refine Prod.ext rfl ?_
  simpa [hardWord, step, Function.comp_apply, flip_complement, compl_invol, flip_flip] using
    congrArg (flip s ∘ complement) (first_of_one h)

theorem hard_not_two {q : ℕ} {v : Word q} {s t : Fin q} (h : scan v v = .two s t) :
    ¬ ∃ k, hardWord v.1 k = v := by
  have hs := scan_spec v v
  rw [h] at hs
  rintro ⟨_ | k, hv⟩
  · have he := congrFun (congrArg Prod.snd hv) s
    have hf : v.1 s = !(v.1 s) := hs.2.1.trans he.symm
    exact (by cases v.1 s <;> decide : v.1 s ≠ !(v.1 s)) hf
  · have aux (i : Fin q) (hi : v.1 i = v.2 i) : i = k := by
      by_contra hn
      have he := congrFun (congrArg Prod.snd hv) i
      change flip k (complement v.1) i = v.2 i at he
      rw [flip_other hn] at he
      have hf : v.1 i = !(v.1 i) := hi.trans he.symm
      exact (by cases v.1 i <;> decide : v.1 i ≠ !(v.1 i)) hf
    exact hs.1 ((aux s hs.2.1).trans (aux t hs.2.2).symm)

/-- The other element of the consecutive pair containing the slot, if present. -/
def partner {q : ℕ} (t : Fin q) : Option (Fin q) :=
  let s := if t.val % 2 = 0 then t.val+1 else t.val-1
  if h : s < q then some ⟨s,h⟩ else none

theorem partner_ne {q : ℕ} {t s : Fin q} (h : partner t = some s) : s ≠ t := by
  let k := if t.val % 2 = 0 then t.val+1 else t.val-1
  change (if hk : k < q then some ⟨k,hk⟩ else none) = some s at h
  by_cases hk : k < q
  · rw [dif_pos hk] at h
    have he := congrArg Fin.val (Option.some.inj h)
    change k = s.val at he
    dsimp [k] at he
    split at he <;> intro eq <;> have := congrArg Fin.val eq <;> omega
  · simp [hk] at h

theorem partner_of_bucket {q : ℕ} {s t : Fin q}
    (he : bucket s = bucket t) (hne : s ≠ t) : partner t = some s := by
  have he' := congrArg Fin.val he
  change s.val/2 = t.val/2 at he'
  have hn' : s.val ≠ t.val := fun h => hne (Fin.ext h)
  have hv : (if t.val % 2 = 0 then t.val+1 else t.val-1) = s.val := by
    split <;> omega
  unfold partner
  simp [hv, s.isLt]

variable {q : ℕ} {F : Type*} [Field F]

def bitDiff (a b : Bool) : F := bitScalar a - bitScalar b

theorem bitDiff_square (x : Bool) : bitDiff (F := F) (!x) x * bitDiff (!x) x = 1 := by
  cases x <;> simp [bitDiff, bitScalar]

def scale (sites : Fin q → F) (a : Bits q) (t : Fin q) : F × F :=
  let d : F := bitDiff (!(a t)) (a t)
  match partner t with
  | none => (d, 0)
  | some s =>
    let c := d * sites t / (sites t - sites s)
    (c, sites s * c)

theorem scale_selected (sites : Fin q → F) (hi : Function.Injective sites)
    (a : Bits q) (t : Fin q) :
    ((scale sites a t).2 - sites t * (scale sites a t).1) *
      bitDiff (!(a t)) (a t) = -sites t := by
  cases h : partner t with
  | none =>
    simp only [scale, h, zero_sub, neg_mul, mul_assoc, bitDiff_square, mul_one]
  | some s =>
    have hn : sites t - sites s ≠ 0 := sub_ne_zero.mpr
      (fun hst => partner_ne h (hi hst).symm)
    simp only [scale, h]
    let d : F := bitDiff (!(a t)) (a t)
    let c := d * sites t / (sites t - sites s)
    change (sites s * c - sites t * c) * d = _
    have hh : (sites t - sites s) * c = d * sites t := by
      dsimp [c]
      field_simp
    calc
      _ = -(((sites t-sites s)*c)*d) := by ring
      _ = -(sites t * (d*d)) := by rw [hh]; ring
      _ = _ := by rw [show d*d = 1 from bitDiff_square (a t), mul_one]

theorem scale_partner (sites : Fin q → F) (a : Bits q) {s t : Fin q}
    (hs : bucket s = bucket t) (hne : s ≠ t) :
    (scale sites a t).2 = sites s * (scale sites a t).1 := by
  simp [scale, partner_of_bucket hs hne]

def coeffPair (sites : Fin q → F) (u v : Word q) : F × F :=
  let a := complement u.2
  match scan u u, scan v v with
  | .zero, .zero => (if parity v.1 = parity a then 1 else 0, 0)
  | .one t, .one s =>
    let d : F := if bucket s = bucket t then bitDiff (v.1 s) (a s) else 0
    ((scale sites a t).1 * d, (scale sites a t).2 * d)
  | _, _ => (0,0)

def selector (u v : Word q) : F := if u = v then 1 else 0

def bucketWeight (a : Bits q) (t : Fin q) (j : EncoderRow q) : F :=
  match j with
  | .inl s => if bucket s = bucket t then -bitScalar (a s) else 0
  | .inr (.inl b) => if b = bucket t then 1 else 0
  | .inr (.inr _) => 0

def weights (sites : Fin q → F) (u : Word q) (j : EncoderRow q) : F × F :=
  let a := complement u.2
  match scan u u with
  | .zero => (if j = .inr (.inr (parity a)) then 1 else 0, 0)
  | .two _ _ => (0,0)
  | .one t => ((scale sites a t).1 * bucketWeight a t j, (scale sites a t).2 * bucketWeight a t j)

theorem column_scan (v : Word q) (j : EncoderRow q) :
    binaryEncoder (F := F) q j v =
      match scan v v with
      | .zero => encoderColumn v.1 none j
      | .one s => encoderColumn v.1 (some s) j
      | .two _ _ => 0 := by
  cases h : scan v v
  · exact (hard_zero h) ▸ binaryEncoder_hardWord v.1 none j
  · exact (hard_one h) ▸ binaryEncoder_hardWord v.1 (some _) j
  · exact binaryEncoder_zero_other v (hard_not_two h) j

private theorem sum_zero_weight (a c : Bits q) (k : Kind q) :
    (∑ j : EncoderRow q,
      (if j = .inr (.inr (parity a)) then (1:F) else 0) * encoderColumn c k j) =
      if k = none ∧ parity c = parity a then 1 else 0 := by
  classical
  cases k <;> simp [encoderColumn, eq_comm, ite_mul]

private theorem sum_bucket_weight (a c : Bits q) (t : Fin q) (k : Kind q) :
    (∑ j : EncoderRow q, bucketWeight (F := F) a t j * encoderColumn c k j) =
      match k with
      | none => 0
      | some s => if bucket s = bucket t then bitDiff (c s) (a s) else 0 := by
  classical
  cases k with
  | none => simp [Fintype.sum_sum_type, bucketWeight, encoderColumn]
  | some s =>
    simp only [Fintype.sum_sum_type, bucketWeight, encoderColumn, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, add_zero]
    by_cases h : bucket s = bucket t
    · simp [h, bitDiff]
      ring
    · simp [h]

theorem weights_sum (sites : Fin q → F) (u v : Word q) :
    (∑ j : EncoderRow q, (weights sites u j).1 * binaryEncoder q j v) =
      (coeffPair sites u v).1 ∧
    (∑ j : EncoderRow q, (weights sites u j).2 * binaryEncoder q j v) =
      (coeffPair sites u v).2 := by
  classical
  cases hu : scan u u <;> cases hv : scan v v <;>
    simp only [weights, coeffPair, hu, hv, column_scan, mul_assoc, ← Finset.mul_sum,
      sum_bucket_weight, sum_zero_weight, zero_mul, mul_zero,
      Finset.sum_const_zero, and_self, eq_self, true_and, reduceCtorEq, false_and, if_false]

end AffineCost
