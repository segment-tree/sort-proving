import Mathlib.Tactic.Lemma    --For lemma keyword
import Mathlib.Data.Nat.Basic  --For basic theorems about inequalities
import Mathlib.Data.List.Basic     --For list permutations

-- Predicate for a list being sorted
def sorted : List Nat -> Prop
  -- An empty list is sorted
  | [] => True
  -- A list containing a single element is sorted
  | [_] => True
  -- A list with more than 2 elements is only sorted if all
  -- elements are ordered.
  | h1 :: h2 :: t => h1 ≤ h2 ∧ sorted (h2 :: t)


def filter' : (α → Bool) → List α → List α := List.filter

lemma sort_termination (x : ℕ) (xs : List ℕ) :
                        (filter' (fun x_1 ↦ decide (x_1 ≤ x)) xs).length < (x :: xs).length ∧
                        (filter' (fun x_1 ↦ decide (x_1 > x)) xs).length < (x :: xs).length := by
  constructor
  all_goals
    rw [filter']
    let lst := x :: xs
    have h0 : xs.length < lst.length := by exact Nat.lt_add_one xs.length
    have h : (f : ℕ → Bool) → (List.filter f xs).length ≤ xs.length := by
      exact λ f => List.length_filter_le f xs
    have h1 : (List.filter (·≤x) xs).length < lst.length := by
      exact Nat.lt_of_le_of_lt (h (·≤x)) h0
    have h2 : (List.filter (·>x) xs).length < lst.length := by
      exact Nat.lt_of_le_of_lt (h (·>x)) h0
    assumption

def qsort (lst : List Nat) : List Nat :=
  match lst with
  | [] => []
  | x::xs => qsort (filter' (·≤x) xs) ++ [x] ++ qsort (filter' (·>x) xs)
  termination_by lst.length
  decreasing_by
    exact (sort_termination x xs).1
    exact (sort_termination x xs).2

lemma sorted_concat (l : List Nat) (r : List Nat)
                    (sortL : sorted l) (sortR : sorted r)
                    (mid : Nat) :
                    (∀ e ∈ l, e ≤ mid) → (∀ e ∈ r, e ≥ mid) → (sorted $ l++r) :=
  match l with
  | []  => (λ _ _ => sortR)
  | x::y::xs =>
      have le : x ≤ y := sortL.1
      have ha : (∀ e ∈ x::y::xs, e ≤ mid) → (∀ e ∈ y::xs, e ≤ mid) :=
        fun h e he => h e (by simp [he])
      (λ el er => And.intro le $
        (sorted_concat (y::xs) r sortL.2 sortR mid) (ha el) er)
  | [x] => (match r with
    | [] => (λ _ _ => sortL)
    | y :: ys => (λ el er =>
      have le : x ≤ y := calc
        x ≤ mid := el x (List.mem_singleton.mpr rfl)
        _ ≤ y   := er y List.mem_cons_self
      And.intro le $ sortR))

lemma sorted_concat_one (r : List Nat) (sortR : sorted r) (x : Nat) :
                        (∀ e ∈ r, e ≥ x) → (sorted $ x::r)
  | er =>
  sorted_concat [x] r (by simp[sorted]) sortR x (by simp) er

#check List.filter_append_perm
#check List.Perm.append
#check (!·)
/-
lemma filter_perm (l : List α) (f : α → Bool) : List.Perm (l.filter f ++ l.filter (λ x => not $ f x)) l := by
  apply List.filter_append_perm
-/
local infixl:50 " ~ " => List.Perm

theorem qsort_perm (l : List Nat) : l.Perm (qsort l) :=
  match l with
  | [] => by simp [qsort]
  | x :: xs => by
    simp [qsort,filter']
    have h : List.Perm (x::xs) (qsort (List.filter (·≤x) xs) ++ [x] ++ qsort (List.filter (·>x) xs)) :=
      (calc
        x :: xs ~ x :: ((List.filter (·≤x) xs) ++ (List.filter (·>x) xs)) := by
                  apply List.Perm.cons x
                  have hh : List.filter (fun y => decide (y > x)) xs = List.filter (fun y => !decide (y ≤ x)) xs := by
                    ext y
                    grind
                  simp [hh]
                  exact (List.filter_append_perm (fun y => decide (y ≤ x)) xs).symm
              _ ~ x :: (qsort (List.filter (·≤x) xs) ++ qsort (List.filter (·>x) xs)) := by
                  have hl : (List.filter (·≤x) xs) ~ qsort (List.filter (·≤x) xs) := qsort_perm _
                  have hr : (List.filter (·>x) xs) ~ qsort (List.filter (·>x) xs) := qsort_perm _
                  simp
                  exact List.Perm.append hl hr
              _ = (x :: qsort (List.filter (·≤x) xs)) ++ qsort (List.filter (·>x) xs) := by simp
              _ ~ qsort (List.filter (·≤x) xs) ++ [x] ++ qsort (List.filter (·>x) xs) := by grind)
    grind
    termination_by l.length
    decreasing_by
    all_goals
      rw [show List.filter = filter' from rfl]
    apply (sort_termination x xs).1
    apply (sort_termination x xs).2



#check List.mem_filter
#check List.of_mem_filter
theorem qsort_sorted (l : List Nat) : sorted (qsort l) :=
  match l with
  | [] => by simp [qsort,sorted]
  | x::xs => by
    simp [qsort]
    rw [filter']
    --have lem e p (h : e ∈ qsort (List.filter (fun y ↦ decide (p y)) xs)) : p e := sorry
    have lem : ∀ (e : ℕ) (p : ℕ → Prop) [DecidablePred p],
    e ∈ qsort (List.filter (fun y ↦ decide (p y)) xs) → p e := by
      intro e p _ h
      apply (List.Perm.mem_iff (a := e) (qsort_perm _)).2 at h
      apply List.of_mem_filter (a := e) (p := (fun y ↦ decide (p y))) at h
      apply of_decide_eq_true at h
      assumption
    apply sorted_concat _ _ _ _ x
    · /- intro e h
      apply (List.Perm.mem_iff (a := e) (qsort_perm _)).2 at h
      apply List.of_mem_filter (a := e) (p := (·≤x)) at h
      apply of_decide_eq_true at h
      assumption -/
      intro e h
      apply lem e (·≤x) h
    · intro e h0
      have := List.mem_cons.mp h0
      apply Or.elim this
      · grind
      · intro h
        exact Nat.le_of_succ_le (lem e (x.succ≤·) h)
    · apply qsort_sorted
    · apply sorted_concat_one
      · apply qsort_sorted
      · intro e h
        exact Nat.le_of_succ_le (lem e (LE.le x.succ) h)
    termination_by l.length
    decreasing_by
    all_goals
      rw [show List.filter = filter' from rfl]
    apply (sort_termination x xs).1
    apply (sort_termination x xs).2


#eval qsort [1,3,2,6,5,7]
/-
lemma perm_preserves_forall {α : Type} {f : α → Prop} {l : List α}
    (h : ∀ x ∈ l, f x) (l' : List α) (hperm : List.Perm l l') :
    ∀ x ∈ l', f x := by
  intro x hx
  -- 使用排列的性质：如果 x 在 l' 中，那么它也在 l 中（因为它们是排列）
  have : x ∈ l := (List.Perm.mem_iff hperm).mpr hx
  -- 应用原假设
  exact h x this
-/
