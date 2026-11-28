import J6R21AncestorHistory

/-! Retention trace composition. This concatenates actual typed moves;
no reindexing proof, raw port read, or machine times are supplied. -/
namespace J6R35RootOrigins
open scoped Polynomial
open J6R21Ancestor

variable {f : ℤ[X]} {ell : ℕ} {a b : Point f ell}

noncomputable def concatenate (head : Trace a b) :
    {c : Point f ell} → Trace b c → Trace a c
  | _, .start => head
  | _, .keep old move => .keep (concatenate head old) move

theorem concatenate_depth (head : Trace a b) {c : Point f ell} (tail : Trace b c) :
    (concatenate head tail).depth = head.depth + tail.depth := by
  induction tail with
  | start => simp [concatenate, Trace.depth]
  | keep prev move ih => simp [concatenate, Trace.depth, ih, Nat.add_assoc]

theorem concatenate_back (head : Trace a b) {c : Point f ell} (tail : Trace b c) :
    (concatenate head tail).back = tail.back.trans head.back := by
  induction tail with
  | start => simp [concatenate, Trace.back]
  | keep prev move ih =>
    change move.back.trans (concatenate head prev).back =
      (move.back.trans prev.back).trans head.back
    rw [ih, Equiv.trans_assoc]

theorem concatenate_old_tag (head : Trace a b) {c : Point f ell} (tail : Trace b c) :
    (entry c).created = (entry a).created :=
  (concatenate head tail).tag

end J6R35RootOrigins

#print axioms J6R35RootOrigins.concatenate_depth
#print axioms J6R35RootOrigins.concatenate_back
#print axioms J6R35RootOrigins.concatenate_old_tag
