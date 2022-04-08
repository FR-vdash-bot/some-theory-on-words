
import tactic

import data.list.basic
import data.list.infix

universe u
variables {α : Type u} [decidable_eq α]

namespace list

def is_lcp (l l₁ l₂ : list α) : Prop := l <+: l₁ ∧ l <+: l₂ ∧ ∀ t, t <+: l₁ → t <+: l₂ → t <+: l

lemma lcp_unique {l l' l₁ l₂ : list α} : l.is_lcp l₁ l₂ → l'.is_lcp l₁ l₂ → l = l' := by
{ rintros ⟨hl₁, hl₂, hl⟩ ⟨hl'₁, hl'₂, hl'⟩,
  specialize hl l' hl'₁ hl'₂,
  specialize hl' l hl₁ hl₂,
  exact antisymm hl' hl, }

/-- Longest common prefix. -/
def lcp : list α → list α → list α
| []      _       := []
| _       []      := []
| (a::as) (b::bs) := if a = b then a::(lcp as bs) else []

lemma lcp_spec : ∀ (l₁ l₂ : list α), (lcp l₁ l₂).is_lcp l₁ l₂
| []      []      := ⟨prefix_rfl, nil_prefix _, λ _ h _, h⟩
| []      (b::bs) := ⟨prefix_rfl, nil_prefix _, λ _ h _, h⟩
| (a::as) []      := ⟨nil_prefix _, prefix_rfl, λ _ _ h, h⟩
| (a::as) (b::bs) := if h : a = b then by
{ rw [lcp, if_pos h, is_lcp],
  simp [cons_prefix_iff, h],
  rcases lcp_spec as bs with ⟨ha, hb, h⟩,
  refine ⟨ha, hb, λ t ha' hb', _⟩,
  cases t with hd tl, { exact nil_prefix _, },
  rw [cons_prefix_iff] at *,
  exact ⟨ha'.1, h tl ha'.2 hb'.2⟩, }
else by
{ rw [lcp, if_neg h],
  refine ⟨nil_prefix _, nil_prefix _, λ t ha hb, _⟩,
  cases t with hd tl, { exact prefix_rfl, },
  { rw [cons_prefix_iff] at *,
    exact absurd (ha.1.symm.trans hb.1) h, }, }

def psigma_lcp (l₁ l₂ : list α) : Σ' (l : list α), l.is_lcp l₁ l₂ :=
⟨lcp l₁ l₂, lcp_spec l₁ l₂⟩

lemma exists_lcp (l₁ l₂ : list α) : ∃ (l : list α), l.is_lcp l₁ l₂ :=
⟨lcp l₁ l₂, lcp_spec l₁ l₂⟩

lemma exists_unique_lcp (l₁ l₂ : list α) : ∃! (l : list α), l.is_lcp l₁ l₂ := by
{ cases exists_lcp l₁ l₂ with l hl,
  use l, dsimp, exact ⟨hl, λ t ht, lcp_unique ht hl⟩, }

lemma lcp_is_prefix_left {l₁ l₂ : list α} : lcp l₁ l₂ <+: l₁ :=
(lcp_spec l₁ l₂).1

lemma lcp_is_prefix_right {l₁ l₂ : list α} : lcp l₁ l₂ <+: l₂ :=
(lcp_spec l₁ l₂).2.1

lemma prefix_of_lcp {l₁ l₂ l₃ : list α} : l₁ <+: l₂ → l₁ <+: l₃ → l₁ <+: lcp l₂ l₃ :=
(lcp_spec l₂ l₃).2.2 l₁

def with_prefix (α : Type*) := list α

namespace with_prefix

instance : partial_order (with_prefix α) :=
{ le          := is_prefix,
  le_refl     := prefix_refl,
  le_trans    := λ _ _ _, is_prefix.trans,
  le_antisymm := λ _ _ h₁ h₂, eq_of_prefix_of_length_eq h₁ $ h₁.length_le.antisymm h₂.length_le }

instance : order_bot (with_prefix α) := ⟨[], nil_prefix⟩
instance : inhabited (with_prefix α) := ⟨⊥⟩

instance : semilattice_inf (with_prefix α) :=
{ inf              := lcp,
  inf_le_left      := λ _ _, lcp_is_prefix_left,
  inf_le_right     := λ _ _, lcp_is_prefix_right,
  le_inf           := λ _ _ _, prefix_of_lcp,
  ..(by apply_instance : partial_order (with_prefix α)) }

end with_prefix

instance with_prefix.has_le : has_le (with_prefix α) := ⟨is_prefix⟩


def is_lcs (l l₁ l₂ : list α) : Prop := l <:+ l₁ ∧ l <:+ l₂ ∧ ∀ t, t <:+ l₁ → t <:+ l₂ → t <:+ l

lemma lcs_unique {l l' l₁ l₂ : list α} : l.is_lcs l₁ l₂ → l'.is_lcs l₁ l₂ → l = l' := by
{ rintros ⟨hl₁, hl₂, hl⟩ ⟨hl'₁, hl'₂, hl'⟩,
  specialize hl l' hl'₁ hl'₂,
  specialize hl' l hl₁ hl₂,
  exact antisymm hl' hl, }

/-- Longest common suffix. -/
def lcs (l₁ l₂ : list α) : list α :=
(lcp l₁.reverse l₂.reverse).reverse

lemma lcs_spec (l₁ l₂ : list α) : (lcs l₁ l₂).is_lcs l₁ l₂ := by
{ unfold is_lcs lcs,
  simp_rw [← reverse_prefix, reverse_reverse],
  convert lcp_spec l₁.reverse l₂.reverse, ext,
  refine ⟨λ h t, _, λ h t, h t.reverse⟩,
  convert h t.reverse, simp_rw [reverse_reverse], }

def psigma_lcs (l₁ l₂ : list α) : Σ' (l : list α), l.is_lcs l₁ l₂ :=
⟨lcs l₁ l₂, lcs_spec l₁ l₂⟩

lemma exists_lcs (l₁ l₂ : list α) : ∃ (l : list α), l.is_lcs l₁ l₂ :=
⟨lcs l₁ l₂, lcs_spec l₁ l₂⟩

lemma exists_unique_lcs (l₁ l₂ : list α) : ∃! (l : list α), l.is_lcs l₁ l₂ := by
{ cases exists_lcs l₁ l₂ with l hl,
  use l, dsimp, exact ⟨hl, λ t ht, lcs_unique ht hl⟩, }

lemma lcs_is_suffix_left {l₁ l₂ : list α} : lcs l₁ l₂ <:+ l₁ :=
(lcs_spec l₁ l₂).1

lemma lcs_is_suffix_right {l₁ l₂ : list α} : lcs l₁ l₂ <:+ l₂ :=
(lcs_spec l₁ l₂).2.1

lemma suffix_of_lcs {l₁ l₂ l₃ : list α} : l₁ <:+ l₂ → l₁ <:+ l₃ → l₁ <:+ lcs l₂ l₃ :=
(lcs_spec l₂ l₃).2.2 l₁

def with_suffix (α : Type*) := list α

namespace with_suffix

instance : partial_order (with_suffix α) :=
{ le          := is_suffix,
  le_refl     := suffix_refl,
  le_trans    := λ _ _ _, is_suffix.trans,
  le_antisymm := λ _ _ h₁ h₂, eq_of_suffix_of_length_eq h₁ $ h₁.length_le.antisymm h₂.length_le }

instance : order_bot (with_suffix α) := ⟨[], nil_suffix⟩
instance : inhabited (with_suffix α) := ⟨⊥⟩

instance : semilattice_inf (with_suffix α) :=
{ inf              := lcs,
  inf_le_left      := λ _ _, lcs_is_suffix_left,
  inf_le_right     := λ _ _, lcs_is_suffix_right,
  le_inf           := λ _ _ _, suffix_of_lcs,
  ..(by apply_instance : partial_order (with_suffix α)) }

end with_suffix


def reverse_order_iso : with_prefix α ≃o with_suffix α :=
{ to_equiv := ⟨reverse, reverse, reverse_reverse, reverse_reverse⟩,
  map_rel_iff' := λ l₁ l₂, reverse_suffix }


def is_border (l₁ l₂ : list α) : Prop :=
l₁.is_prefix l₂ ∧ l₁.is_suffix l₂

lemma nil_border (l : list α) : [].is_border l := ⟨nil_prefix l, nil_suffix l⟩

@[refl] lemma border_refl (l : list α) : l.is_border l := ⟨prefix_refl l, suffix_refl l⟩

lemma border_rfl {l : list α} : l.is_border l := border_refl _

@[trans] lemma is_border.trans :
  ∀ {l₁ l₂ l₃ : list α}, l₁.is_border l₂ → l₂.is_border l₃ → l₁.is_border l₃
| _ _ _ ⟨hp₁, hs₁⟩ ⟨hp₂, hs₂⟩ := ⟨hp₁.trans hp₂, hs₁.trans hs₂,⟩

protected lemma is_border.sublist {l₁ l₂ : list α}
  (h : l₁.is_border l₂) : l₁ <+ l₂ := h.1.is_infix.sublist

@[simp] lemma reverse_border {l₁ l₂ : list α} :
  (reverse l₁).is_border (reverse l₂) ↔ l₁.is_border l₂ :=
⟨ λ h, ⟨reverse_suffix.mp h.2, reverse_prefix.mp h.1⟩,
  λ h, ⟨reverse_prefix.mpr h.2, reverse_suffix.mpr h.1⟩ ⟩

lemma is_border.length_le {l₁ l₂ : list α}
  (h : l₁.is_border l₂) : l₁.length ≤ l₂.length := length_le_of_sublist h.sublist

lemma eq_of_border_of_length_eq {l₁ l₂ : list α}
  (h : l₁.is_border l₂) : l₁.length = l₂.length → l₁ = l₂ :=
eq_of_sublist_of_length_eq h.sublist

instance : is_partial_order (list α) is_border :=
{ refl     := border_refl,
  trans    := λ _ _ _, is_border.trans,
  antisymm := λ _ _ h₁ h₂, eq_of_border_of_length_eq h₁ $ h₁.length_le.antisymm h₂.length_le }

instance decidable_border (l₁ l₂ : list α) : decidable (l₁.is_border l₂) := and.decidable


lemma drop_border_of_take_border (l : list α) {p : ℕ} (h : (l.take p).is_border l) :
  (l.drop (l.length - p)).is_border l :=
if hp : p ≤ l.length then by
{ have h' := suffix_iff_eq_drop.mp h.2,
  rwa [h', length_take, min_eq_left hp] at h, }
else by rw [tsub_eq_zero_of_le (le_of_not_ge hp), drop]

lemma take_border_of_drop_border (l : list α) {p : ℕ} (h : (l.drop p).is_border l) :
  (l.take (l.length - p)).is_border l := by
{ have h' := prefix_iff_eq_take.mp h.1,
  rwa [h', length_drop] at h, }

lemma take_border_iff_drop_border (l : list α) {p : ℕ} :
  (l.take p).is_border l ↔ (l.drop (l.length - p)).is_border l :=
⟨ l.drop_border_of_take_border, λ h, if hp : p ≤ l.length then
    by convert l.take_border_of_drop_border h; rw [tsub_tsub_cancel_of_le hp]
  else by rw [take_all_of_le (le_of_not_ge hp)] ⟩

lemma drop_border_iff_take_border (l : list α) {p : ℕ} :
  (l.drop p).is_border l ↔ (l.take (l.length - p)).is_border l :=
⟨ l.take_border_of_drop_border, λ h, if hp : p ≤ l.length then
    by convert l.drop_border_of_take_border h; rw [tsub_tsub_cancel_of_le hp]
  else by rw [drop_eq_nil_of_le (le_of_not_ge hp)]; exact nil_border _ ⟩


def longest_prefix_suffix : list α → list α → list α
| l []      := []
| l (b::bs) := if b::bs <+: l then b::bs else l.longest_prefix_suffix bs

lemma longest_prefix_suffix_spec : ∀ (l₁ l₂ : list α),
  longest_prefix_suffix l₁ l₂ <+: l₁ ∧ longest_prefix_suffix l₁ l₂ <:+ l₂ ∧
  ∀ (l : list α), l <+: l₁ ∧ l <:+ l₂ → l.is_border (longest_prefix_suffix l₁ l₂)
| _ []  := by rw [longest_prefix_suffix]; exact ⟨nil_prefix _, suffix_rfl,
                                                 λ l hl, by rw [suffix_nil_iff.mp hl.2]⟩
| l₁ (b::bs) := if h : b::bs <+: l₁ then by
{ rw [longest_prefix_suffix, if_pos h],
  refine ⟨h, suffix_rfl, λ l hl, ⟨prefix_of_prefix_length_le hl.1 h hl.2.length_le, hl.2⟩⟩, }
else by
{ rw [longest_prefix_suffix, if_neg h],
  obtain ⟨h₁, h₂, h'⟩ := longest_prefix_suffix_spec l₁ bs,
  refine ⟨h₁, suffix_cons_iff.mpr (or.inr h₂), λ l hl, _⟩,
  refine h' l ⟨hl.1, (suffix_cons_iff.mp hl.2).resolve_left _⟩,
  rintro rfl, exact h hl.1, }


def is_proper_border (l₁ l₂ : list α) : Prop :=
l₁.is_border l₂ ∧ ¬ l₂.is_border l₁

def longest_proper_border : list α → list α
| []      := []
| (a::as) := longest_prefix_suffix (a::as) as

lemma longest_proper_border_lenght_lt : ∀ (l : list α) (h : l ≠ []),
  l.longest_proper_border.length < l.length
| []      h := absurd rfl h
| (a::as) _ := (longest_prefix_suffix_spec (a::as) as).2.1.length_le.trans_lt
  (lt_of_add_lt_add_right (lt_add_of_le_of_pos (length_cons a as).ge zero_lt_one))

lemma longest_proper_border_spec : ∀ (l : list α), l = [] ∨
  l.longest_proper_border.is_proper_border l ∧
  ∀ (t : list α), t.is_proper_border l → t.is_border l.longest_proper_border
| []      := or.inl rfl
| (a::as) := by
{ obtain ⟨h₁, h₂, h⟩ := longest_prefix_suffix_spec (a::as) as,
  refine or.inr ⟨_, λ t ht, _⟩,
  { refine ⟨⟨h₁, suffix_cons_iff.mpr (or.inr h₂)⟩, _⟩,
    intro h, have hle := h.length_le,
    have hlt := longest_proper_border_lenght_lt (a::as) (λ h, list.no_confusion h),
    exact hlt.not_le hle, },
  { refine h t ⟨ht.1.1, _⟩,
    refine (suffix_cons_iff.mp ht.1.2).resolve_left _,
    rintro rfl, exact ht.2 border_rfl, } }


def is_lcb (l l₁ l₂ : list α) : Prop :=
  l.is_border l₁ ∧ l.is_border l₂ ∧ ∀ t : list α, t.is_border l₁ → t.is_border l₂ → t.is_border l

lemma lcb_unique {l l' l₁ l₂ : list α} : l.is_lcb l₁ l₂ → l'.is_lcb l₁ l₂ → l = l' := by
{ rintros ⟨hl₁, hl₂, hl⟩ ⟨hl'₁, hl'₂, hl'⟩,
  specialize hl l' hl'₁ hl'₂,
  specialize hl' l hl₁ hl₂,
  exact antisymm hl' hl, }

/-- Longest common border. -/
def lcb (l₁ l₂ : list α) : list α :=
longest_prefix_suffix (lcp l₁ l₂) (lcs l₁ l₂)

lemma lcb_spec (l₁ l₂ : list α) : (lcb l₁ l₂).is_lcb l₁ l₂ := by
{ obtain ⟨h₁, h₂, h⟩ := longest_prefix_suffix_spec (lcp l₁ l₂) (lcs l₁ l₂),
  obtain ⟨hp₁, hp₂, hp⟩ := lcp_spec l₁ l₂,
  obtain ⟨hs₁, hs₂, hs⟩ := lcs_spec l₁ l₂,
  refine ⟨⟨h₁.trans hp₁, h₂.trans hs₁⟩, ⟨h₁.trans hp₂, h₂.trans hs₂⟩, λ t ht₁ ht₂, _⟩,
  exact h t ⟨hp t ht₁.1 ht₂.1, hs t ht₁.2 ht₂.2⟩, }

lemma exists_lcb (l₁ l₂ : list α) : ∃ (l : list α), l.is_lcb l₁ l₂ :=
⟨lcb l₁ l₂, lcb_spec l₁ l₂⟩

lemma exists_unique_lcb (l₁ l₂ : list α) : ∃! (l : list α), l.is_lcb l₁ l₂ := by
{ cases exists_lcb l₁ l₂ with l hl,
  use l, dsimp, exact ⟨hl, λ t ht, lcb_unique ht hl⟩, }

lemma lcb_is_border_left {l₁ l₂ : list α} : (lcb l₁ l₂).is_border l₁ :=
(lcb_spec l₁ l₂).1

lemma lcb_is_border_right {l₁ l₂ : list α} : (lcb l₁ l₂).is_border l₂ :=
(lcb_spec l₁ l₂).2.1

lemma border_of_lcb {l₁ l₂ l₃ : list α} :
  l₁.is_border l₂ → l₁.is_border l₃ → l₁.is_border (lcb l₂ l₃) :=
(lcb_spec l₂ l₃).2.2 l₁

def with_border (α : Type*) := list α

namespace with_border

instance : partial_order (with_border α) :=
{ le          := is_border,
  le_refl     := border_refl,
  le_trans    := λ _ _ _, is_border.trans,
  le_antisymm := λ _ _ h₁ h₂, eq_of_border_of_length_eq h₁ $ h₁.length_le.antisymm h₂.length_le }

instance : order_bot (with_border α) := ⟨[], nil_border⟩
instance : inhabited (with_border α) := ⟨⊥⟩

instance : semilattice_inf (with_border α) :=
{ inf              := lcb,
  inf_le_left      := λ _ _, lcb_is_border_left,
  inf_le_right     := λ _ _, lcb_is_border_right,
  le_inf           := λ _ _ _, border_of_lcb,
  ..(by apply_instance : partial_order (with_border α)) }

end with_border


def has_period (l : list α) (p : ℕ) : Prop :=
p ≤ l.length ∧ ∀ (i j : ℕ) (hij : i + p = j) (hi hj),
  l.nth_le i hi = l.nth_le j hj

lemma period_zero (l : list α) : l.has_period 0 :=
⟨zero_le _, λ i j h _ _, by simp_rw [← h, add_zero]⟩

@[refl] lemma period_length (l : list α) : l.has_period l.length :=
⟨le_rfl, λ i j h hi hj, by rw [← h] at hj; exact absurd hj le_add_self.not_lt ⟩

lemma period_of_border {l : list α} {l' : list α} (h : l'.is_border l) :
  l.has_period (l.length - l'.length) := by
{ refine ⟨nat.sub_le _ _, λ i j hij _ hj, _⟩,
  have hi : i < l'.length :=
    by rwa [← hij, ← lt_tsub_iff_right, tsub_tsub_cancel_of_le h.length_le] at hj,
  rw [add_comm] at hij,
  simp_rw [hij.symm, l.nth_le_take _ hi, nth_le_drop,
    (prefix_iff_eq_take.mp h.1).symm, (suffix_iff_eq_drop.mp h.2).symm], }

lemma drop_border_of_period {l : list α} {p : ℕ} (h : l.has_period p) :
  (l.drop p).is_border l := by
{ refine ⟨_, l.drop_suffix p⟩, convert l.take_prefix (l.length - p),
  apply list.ext_le, rw [l.length_take _, l.length_drop _, min_eq_left (nat.sub_le _ _)],
  intros n h₁ h₂, simp_rw [nth_le_take', nth_le_drop', add_comm p n],
  rw [h.2 n], refl, }

lemma take_border_of_period {l : list α} {p : ℕ} (h : l.has_period p) :
  (l.take (l.length - p)).is_border l := by
{ have h' := drop_border_of_period h,
  have x := prefix_iff_eq_take.mp h'.1,
  rwa [x, length_drop] at h', }

lemma period_iff_drop_border {l : list α} {p : ℕ} (h : p ≤ l.length) :
  l.has_period p ↔ (l.drop p).is_border l :=
⟨ drop_border_of_period, λ hl, by
  { convert period_of_border hl,
    simp_rw [length_drop, tsub_tsub_cancel_of_le h], }⟩

lemma period_iff_take_border {l : list α} {p : ℕ} (h : p ≤ l.length) :
  l.has_period p ↔ (l.take (l.length - p)).is_border l :=
by convert period_iff_drop_border h using 1; rw [drop_border_iff_take_border]

lemma reverse_period {l : list α} {p : ℕ} (h : l.has_period p) :
  l.reverse.has_period p := by
{ have hp : p = l.reverse.length - (l.drop p).reverse.length :=
    by simp_rw [length_reverse, length_drop, tsub_tsub_assoc le_rfl h.1, tsub_self, zero_add],
  rw [hp], apply period_of_border, rw [reverse_border],
  exact drop_border_of_period h, }

lemma reverse_period_iff (l : list α) (p : ℕ) :
  l.reverse.has_period p ↔ l.has_period p :=
⟨λ h, by rw [← l.reverse_reverse]; exact reverse_period h, reverse_period⟩

lemma take_period {l : list α} {p : ℕ} (h : l.has_period p)
  {n : ℕ} (hn : n ≤ l.length) (hnp : p ≤ n) : (l.take n).has_period p := by
{ refine ⟨by rwa [length_take, min_eq_left hn], λ i j hij hi hj, _⟩,
  simp_rw [nth_le_take'], rwa [h.2], }

lemma prefix_period {l : list α} {p : ℕ} (h : l.has_period p)
  {l' : list α} (hl : l' <+: l) (hp : p ≤ l'.length) : l'.has_period p :=
by rw [prefix_iff_eq_take.mp hl]; exact take_period h hl.length_le hp

lemma drop_period {l : list α} {p : ℕ} (h : l.has_period p)
  {n : ℕ} (hn : n ≤ l.length) (hnp : p ≤ n) : (l.drop (l.length - n)).has_period p := by
{ refine ⟨by rwa [length_drop, tsub_tsub_cancel_of_le hn], λ i j hij hi hj, _⟩,
  simp_rw [nth_le_drop'], exact h.2 (l.length - n + i) (l.length - n + j)
                            (by rw [← hij, add_assoc]) _ _, }

lemma suffix_period {l : list α} {p : ℕ} (h : l.has_period p)
  {l' : list α} (hl : l' <:+ l) (hp : p ≤ l'.length) : l'.has_period p := by
by rw [suffix_iff_eq_drop.mp hl]; exact drop_period h hl.length_le hp

lemma infix_period {l : list α} {p : ℕ} (h : l.has_period p)
  {l' : list α} (hl : l' <:+: l) (hp : p ≤ l'.length) : l'.has_period p := by
{ rw [infix_iff_prefix_suffix] at hl, obtain ⟨t, ht₁, ht₂⟩ := hl,
  apply prefix_period _ ht₁ hp,
  exact suffix_period h ht₂ (hp.trans ht₁.length_le), }

lemma drop_period_sub_of_period_period {l : list α} {p q : ℕ}
  (hp : l.has_period p) (hq : l.has_period q) (h : p ≤ q) : (l.drop p).has_period (q - p) := by
{ refine ⟨by rw [length_drop]; exact tsub_le_tsub_right hq.1 p, λ n m hnm hn hm, _⟩,
  simp_rw [nth_le_drop', p.add_comm],
  have hnp := hn, have hnq := hm,
  rw [length_drop, lt_tsub_iff_right] at hnp hnq,
  simp_rw [hnm.symm, add_assoc, tsub_add_cancel_of_le h] at hnq ⊢,
  have hp' := hp.2 n (n + p) rfl (lt_of_add_lt_of_nonneg_left hnp p.zero_le) hnp,
  have hq' := hq.2 n (n + q) rfl (lt_of_add_lt_of_nonneg_left hnq q.zero_le) hnq,
  simp_rw [← hp', ← hq'], }

lemma take_period_sub_of_period_period {l : list α} {p q : ℕ}
  (hp : l.has_period p) (hq : l.has_period q) (h : p ≤ q) :
  (l.take (l.length - p)).has_period (q - p) := by
{ rw [← l.reverse_reverse, reverse_take, l.reverse_reverse, reverse_period_iff],
  rw [← reverse_period_iff] at hp hq,
  convert drop_period_sub_of_period_period hp hq h,
  rw [reverse_period_iff] at hp hq,
  rwa [length_reverse, tsub_tsub_cancel_of_le hp.1],
  simp_rw [length_reverse, tsub_le_self], }

lemma period_iff_forall_mod_eq (l : list α) (p : ℕ) : l.has_period p ↔
  ∃ (hp : p ≤ l.length), ∀ (i : ℕ) (hi), l.nth_le i hi = l.nth_le (i % p)
  ( if p0 : p = 0 then (by rwa [p0, nat.mod_zero])
    else (i.mod_lt (pos_iff_ne_zero.mpr p0)).trans_le hp ) := by
{ split,
  { cases dec_em (p = 0) with p0 p0, { simp [p0], },
    replace p0 := pos_iff_ne_zero.mpr p0,
    rintro ⟨h₁, h₂⟩, use h₁,
    intros i hi,
    induction i using nat.strong_rec_on with i h,
    { cases dec_em (i < p) with hip hip, { simp_rw [nat.mod_eq_of_lt hip], },
      { replace hip := le_of_not_gt hip,
        simp_rw [nat.mod_eq_sub_mod hip],
        have hip' : i - p < l.length := tsub_le_self.trans_lt hi,
        convert ← h (i - p) (tsub_lt_self (p0.trans_le hip) p0) hip' using 1,
        apply h₂, exact tsub_add_cancel_of_le hip, }, }, },
  { rintro ⟨h₁, h₂⟩, use h₁,
    intros i j hij hi hj, simp_rw [h₂ i hi, h₂ j hj, ← hij,
      nat.mod_eq_sub_mod (self_le_add_left p i), add_tsub_cancel_right], }, }

lemma nth_le_prefix {l : list α} {l' : list α} (hl : l' <+: l) {i : ℕ} (h : i < l'.length) :
  l'.nth_le i h = l.nth_le i (h.trans_le hl.length_le) :=
by rw [prefix_iff_eq_take] at hl; conv_lhs { congr, rw [hl], }; rwa [← nth_le_take]

lemma period_of_prefix_period_dvd {l : list α} {p : ℕ} (p0 : 0 < p) (hp : l.has_period p)
  {l' : list α} (hl : l' <+: l) (hpl : p ≤ l'.length)
  {d : ℕ} (hd : l'.has_period d) (hdp : d ∣ p) :
  l.has_period d := by
{ rw [period_iff_forall_mod_eq] at *,
  use hd.fst.trans hl.length_le,
  intros i hi, rw [hp.snd],
  convert hd.snd (i % p) ((i.mod_lt p0).trans_le hpl) using 1,
  rw [nth_le_prefix hl], simp_rw [nth_le_prefix hl, i.mod_mod_of_dvd hdp], }

lemma period_of_take_period_dvd {l : list α} {p : ℕ} (p0 : 0 < p) (hp : l.has_period p)
  {n : ℕ} (hpn : p ≤ n) {d : ℕ} (hd : (l.take n).has_period d) (hdp : d ∣ p) :
  l.has_period d :=
if hnl : n ≤ l.length then
  period_of_prefix_period_dvd p0 hp (l.take_prefix n)
    (by rwa [length_take, min_eq_left hnl]) hd hdp
else by rwa [take_all_of_le (le_of_not_ge hnl)] at hd

lemma period_of_suffix_period_dvd {l : list α} {p : ℕ} (p0 : 0 < p) (hp : l.has_period p)
  {l' : list α} (hl : l' <:+ l) (hpl : p ≤ l'.length)
  {d : ℕ} (hd : l'.has_period d) (hdp : d ∣ p) :
  l.has_period d := by
{ rw [← reverse_period_iff],
  exact period_of_prefix_period_dvd p0 (reverse_period hp) (reverse_prefix.mpr hl)
    (by rwa [length_reverse]) (reverse_period hd) hdp, }

lemma period_of_drop_period_dvd {l : list α} {p : ℕ} (p0 : 0 < p) (hp : l.has_period p)
  {n : ℕ} (hpn : p ≤ n) {d : ℕ} (hd : (l.drop (l.length - n)).has_period d) (hdp : d ∣ p) :
  l.has_period d :=
if hnl : n ≤ l.length then
  period_of_suffix_period_dvd p0 hp (l.drop_suffix (l.length - n))
    (by rwa [length_drop, tsub_tsub_cancel_of_le hnl]) hd hdp
else by rwa [tsub_eq_zero_of_le (le_of_not_ge hnl)] at hd

lemma period_of_infix_period_dvd {l : list α} {p : ℕ} (p0 : 0 < p) (hp : l.has_period p)
  {l' : list α} (hl : l' <:+: l) (hpl : p ≤ l'.length)
  {d : ℕ} (hd : l'.has_period d) (hdp : d ∣ p) :
  l.has_period d := by
{ rw [infix_iff_prefix_suffix] at hl, obtain ⟨t, ht₁, ht₂⟩ := hl,
  have hpt : p ≤ t.length := hpl.trans ht₁.length_le,
  apply period_of_suffix_period_dvd p0 hp ht₂ hpt _ hdp,
  exact period_of_prefix_period_dvd p0 (suffix_period hp ht₂ hpt) ht₁ hpl hd hdp, }

lemma periodicity_lemma_aux (l : list α) (p q : ℕ) (hp : l.has_period p) (hq : l.has_period q)
  (h : p + q ≤ l.length + p.gcd q) (k : ℕ) (k_def : p / p.gcd q + q / p.gcd q = k)
  (hk : ∀ (m : ℕ), m < k → ∀ {l : list α} {p q : ℕ},
    p + q ≤ l.length + p.gcd q → l.has_period p → l.has_period q →
    p / p.gcd q + q / p.gcd q = m → l.has_period (p.gcd q))
  (p0 : 0 < p) (q0 : 0 < q) (d0 : 0 < p.gcd q) (hpq : p < q) : l.has_period (p.gcd q) := by
{ have dvd_p : p.gcd q ∣ p := p.gcd_dvd_left q,
  have dvd_q : p.gcd q ∣ q := p.gcd_dvd_right q,
  have dvd_sub := nat.dvd_sub' dvd_q dvd_p,
  have : p ≤ l.length - p := by
  { apply le_tsub_of_add_le_left, rw [← add_le_add_iff_right (p.gcd q)],
    apply trans _ h, rw [add_assoc, add_le_add_iff_left],
    apply add_le_of_le_tsub_left_of_le hpq.le,
    exact nat.le_of_dvd (tsub_pos_of_lt hpq) dvd_sub, },
  have hp' : (drop (l.length - (l.length - p)) l).has_period p :=
    drop_period hp tsub_le_self this,
  rw [tsub_tsub_cancel_of_le hp.1] at hp',
  have hq' := drop_period_sub_of_period_period hp hq hpq.le,
  have gcd_eq : p.gcd (q - p) = p.gcd q :=
    by rw [← nat.gcd_add_self_right, tsub_add_cancel_of_le hpq.le],
  have h' : p + (q - p) ≤ (drop p l).length + p.gcd (q - p) :=
    by rwa [length_drop, add_tsub_cancel_of_le hpq.le, gcd_eq,
      tsub_add_eq_add_tsub hp.1, le_tsub_iff_left (hp.1.trans le_self_add)],
  have hm : p / p.gcd q + (q - p) / p.gcd q < k := by
  { rw [← k_def, add_lt_add_iff_left], apply lt_of_mul_lt_mul_right _ d0.le,
    simp_rw [nat.div_mul_cancel dvd_q, nat.div_mul_cancel dvd_sub],
    exact tsub_lt_self q0 p0, },
  specialize hk (p / p.gcd q + (q - p) / p.gcd q) hm h' hp' hq' _;
  simp_rw [gcd_eq] at ⊢ hk,
  refine period_of_drop_period_dvd p0 hp this _ dvd_p,
  convert hk, rw [tsub_tsub_cancel_of_le hp.1], }

lemma periodicity_lemma {l : list α} {p q : ℕ} (hp : l.has_period p) (hq : l.has_period q)
  (h : p + q ≤ l.length + p.gcd q) : l.has_period (p.gcd q) := by
{ induction k_def : p / (p.gcd q) + q / (p.gcd q) using nat.strong_rec_on with k hk
                                                  generalizing l p q h,
  dsimp at hk,
  cases dec_em (p = 0) with p0 p0, rwa [p0, nat.gcd_zero_left],
  cases dec_em (q = 0) with q0 q0, rwa [q0, nat.gcd_zero_right],
  replace p0 := pos_iff_ne_zero.mpr p0,
  replace q0 := pos_iff_ne_zero.mpr q0,
  have d0 := nat.gcd_pos_of_pos_left q p0,
  rcases nat.lt_trichotomy p q with (hpq | hpq | hpq),
  { exact periodicity_lemma_aux l p q hp hq h k k_def hk p0 q0 d0 hpq, },
  { rwa [hpq, nat.gcd_self] at *, },
  { rw [nat.gcd_comm] at *, rw [add_comm] at h k_def,
    exact periodicity_lemma_aux l q p hq hp h k k_def hk q0 p0 d0 hpq, }, }

end list
