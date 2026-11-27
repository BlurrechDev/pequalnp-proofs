import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27450

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def lv : ℕ → List Gate → ℕ → Bool
  | n, [], k => k == n - 1
  | n, g :: rest, k => g.inputs.contains k || lv (n + 1) rest k

def shape (n : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a, b])

def NFs : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: rest => shape n g ∧ lv (n + 1) rest n = true ∧ NFs (n + 1) rest

def tab (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => tab p n ||| (if p n then 2 ^ n else 0)

def opOf (o : ℕ) : GateOp :=
  if o = 0 then GateOp.and else if o = 1 then GateOp.or else GateOp.not

def mkGate (c : ℕ × List ℕ) : Gate := ⟨opOf c.1, c.2⟩

def gateTab (M : ℕ) (look : ℕ → ℕ) (c : ℕ × List ℕ) : ℕ :=
  if c.1 = 0 then c.2.foldr (fun i a => look i &&& a) M
  else if c.1 = 1 then c.2.foldr (fun i a => look i ||| a) 0
  else M ^^^ (c.2.map look).headD 0

def det (M T : ℕ) (ws : List ℕ) : List ℕ → ℕ → Bool
  | [], m => (m &&& T == 0) || (m &&& (M ^^^ T) == 0)
  | k :: L, m => (m == 0) || (det M T ws L (m &&& ws.getD k 0) && det M T ws L (m &&& (M ^^^ ws.getD k 0)))

def subs : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: t => subs t ++ (subs t).map (a :: ·)

def cands (pre : List (ℕ × List ℕ)) (L : List ℕ) : List (ℕ × List ℕ) :=
  match pre with
  | p :: _ => [p]
  | [] => L.flatMap fun a => (2, [a]) :: L.flatMap fun b => if a < b then [(0, [a, b]), (1, [a, b])] else []

def chk (M T : ℕ) : List (ℕ × List ℕ) → ℕ → List ℕ → List ℕ → Bool
  | _, 0, ws, _ => !(((ws.getD (ws.length - 1) 0 ^^^ T) &&& M) == 0)
  | pre, r + 1, ws, L =>
    Nat.blt (r + 2) L.length || !(det M T ws L M) ||
    (cands pre L).all fun c => (subs c.2).all fun X =>
      chk M T pre.tail r (ws ++ [gateTab M (fun i => ws.getD i 0) c])
        (L.filter (fun k => !(X.contains k)) ++ [ws.length])

theorem getD_bit (ts : List ℕ) (k i : ℕ) :
    (ts.map fun t => t.testBit k).getD i false = (ts.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ts[i]? <;> simp

theorem gateTab_bit (M k : ℕ) (hM : M.testBit k = true) (look : ℕ → ℕ) (c : ℕ × List ℕ) :
    (gateTab M look c).testBit k
      = (mkGate c).op.eval ((mkGate c).inputs.map fun i => (look i).testBit k) := by
  obtain ⟨o, ins⟩ := c
  simp only [gateTab, mkGate, opOf]
  split_ifs
  · simp only [GateOp.eval]
    induction ins with
    | nil => simpa using hM
    | cons i ins ih =>
      simp only [List.foldr_cons, List.map_cons, List.all_cons, Nat.testBit_and, ih, id]
  · simp only [GateOp.eval]
    induction ins with
    | nil => simp
    | cons i ins ih =>
      simp only [List.foldr_cons, List.map_cons, List.any_cons, Nat.testBit_or, ih, id]
  · simp only [GateOp.eval]
    cases ins <;> simp [hM]

theorem step_tab (M r : ℕ) (hM : M.testBit r = true) (ws : List ℕ) (c : ℕ × List ℕ) :
    step (ws.map fun t => t.testBit r) (mkGate c)
      = (ws ++ [gateTab M (fun i => ws.getD i 0) c]).map fun t => t.testBit r := by
  simp only [step, List.map_append, List.map_cons, List.map_nil, gateTab_bit M r hM]
  congr 2
  apply congrArg
  apply List.map_congr_left
  intro i _
  exact getD_bit ws r i

theorem step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem det_sem (rest : List Gate) : ∀ (n : ℕ) (w w' : List Bool), w.length = n → w'.length = n →
    (∀ k, k < n → lv n rest k = true → w.getD k false = w'.getD k false) →
    (rest.foldl step w).getD (n + rest.length - 1) false
      = (rest.foldl step w').getD (n + rest.length - 1) false := by
  induction rest with
  | nil =>
    intro n w w' hw hw' h
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    by_cases hn : n = 0
    · subst hn
      rw [List.length_eq_zero_iff.mp hw, List.length_eq_zero_iff.mp hw']
    · exact h (n - 1) (by omega) (by simp [lv])
  | cons g rest ih =>
    intro n w w' hw hw' h
    simp only [List.foldl_cons, List.length_cons]
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      apply congrArg
      apply List.map_congr_left
      intro i hi
      by_cases hin : i < n
      · exact h i hin (by simp [lv, hi])
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have e := ih (n + 1) (step w g) (step w' g) (by simp [step_length, hw]) (by simp [step_length, hw']) (by
      intro k hk hl
      by_cases hkn : k < n
      · simp only [step]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h k hkn (by simp [lv, hl])
      · have : k = n := by omega
        subst this
        simp only [step]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [hw, hw', hv])
    have e2 : n + 1 + rest.length - 1 = n + (rest.length + 1) - 1 := by omega
    rw [e2] at e
    exact e

theorem filter_mem_subs (p : ℕ → Bool) : ∀ l : List ℕ, l.filter p ∈ subs l := by
  intro l
  induction l with
  | nil => simp [subs]
  | cons a t ih =>
    simp only [subs, List.mem_append, List.mem_map, List.filter_cons]
    by_cases hp : p a = true
    · right; exact ⟨t.filter p, ih, by simp [hp]⟩
    · left; simpa [hp] using ih

def dropX (n : ℕ) (rest : List Gate) (ins : List ℕ) : List ℕ := ins.filter fun k => !(lv (n + 1) rest k)

theorem trans_exact (n : ℕ) (g : Gate) (rest : List Gate) (L : List ℕ)
    (hlast : lv (n + 1) rest n = true) (hL : L.Nodup)
    (hex : ∀ k, k ∈ L ↔ (k < n ∧ lv n (g :: rest) k = true)) :
    (L.filter (fun k => !((dropX n rest g.inputs).contains k)) ++ [n]).Nodup ∧
    (∀ k, k ∈ L.filter (fun k => !((dropX n rest g.inputs).contains k)) ++ [n]
      ↔ (k < n + 1 ∧ lv (n + 1) rest k = true)) := by
  constructor
  · rw [List.nodup_append]
    refine ⟨hL.filter _, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    have := (hex a).mp (List.mem_of_mem_filter ha)
    omega
  · intro k
    rw [List.mem_append, List.mem_filter, List.mem_singleton]
    have hXc : (dropX n rest g.inputs).contains k = true ↔ (k ∈ g.inputs ∧ lv (n + 1) rest k = false) := by
      simp [dropX]
    constructor
    · rintro (⟨hkL, hX⟩ | rfl)
      · obtain ⟨hk, hl⟩ := (hex k).mp hkL
        refine ⟨by omega, ?_⟩
        by_contra hc
        have hc' : lv (n + 1) rest k = false := by simpa using hc
        simp only [lv, Bool.or_eq_true] at hl
        rcases hl with hl | hl
        · have hm : k ∈ g.inputs := by simpa using hl
          have := hXc.mpr ⟨hm, hc'⟩
          rw [this] at hX
          simp at hX
        · exact absurd hl hc
      · exact ⟨by omega, hlast⟩
    · rintro ⟨hk, hl⟩
      by_cases hkn : k = n
      · right; exact hkn
      · left
        refine ⟨(hex k).mpr ⟨by omega, by simp [lv, hl]⟩, ?_⟩
        cases hX : (dropX n rest g.inputs).contains k
        · rfl
        · exfalso
          have := (hXc.mp hX).2
          rw [hl] at this
          simp at this

theorem filter_len (L X : List ℕ) (hL : L.Nodup) :
    L.length ≤ (L.filter (fun k => !(X.contains k))).length + X.length := by
  have h1 := List.length_eq_length_filter_add (l := L) (fun k => !(X.contains k))
  have h2 : (L.filter (fun k => !(!(X.contains k)))).length ≤ X.length := by
    apply List.Subperm.length_le
    apply List.subperm_of_subset (hL.filter _)
    intro a ha
    simpa using (List.mem_filter.mp ha).2
  omega

theorem shape_len {n : ℕ} {g : Gate} (h : shape n g) : g.inputs.length ≤ 2 := by
  rcases h with ⟨_, a, _, e⟩ | ⟨_, a, b, _, _, e⟩ <;> simp [e]

theorem live_card (rest : List Gate) : ∀ (n : ℕ) (L : List ℕ), NFs n rest → L.Nodup →
    (∀ k, k ∈ L ↔ (k < n ∧ lv n rest k = true)) → L.length ≤ rest.length + 1 := by
  induction rest with
  | nil =>
    intro n L _ hL hex
    have : L.length ≤ [n - 1].length := by
      apply List.Subperm.length_le
      apply List.subperm_of_subset hL
      intro a ha
      have := ((hex a).mp ha).2
      simpa [lv] using this
    simpa using this
  | cons g rest ih =>
    intro n L hnf hL hex
    obtain ⟨hsh, hlast, hnf'⟩ := hnf
    obtain ⟨hnd, hex'⟩ := trans_exact n g rest L hlast hL hex
    have h1 := ih (n + 1) _ hnf' hnd hex'
    have h2 := filter_len L (dropX n rest g.inputs) hL
    have h3 : (dropX n rest g.inputs).length ≤ g.inputs.length := List.length_filter_le _ _
    have h4 := shape_len hsh
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
    omega

theorem det_true (M T : ℕ) (hM : ∀ r, M.testBit r = decide (r < 512)) (ws : List ℕ) :
    ∀ (L : List ℕ) (m : ℕ), (∀ r, m.testBit r = true → r < 512) →
    (∀ r r', m.testBit r = true → m.testBit r' = true →
      (∀ k ∈ L, (ws.getD k 0).testBit r = (ws.getD k 0).testBit r') → T.testBit r = T.testBit r') →
    det M T ws L m = true := by
  intro L
  induction L with
  | nil =>
    intro m hm h
    simp only [det, Bool.or_eq_true, beq_iff_eq]
    by_contra hc
    push_neg at hc
    obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero hc.1
    obtain ⟨r', hr'⟩ := Nat.exists_testBit_of_ne_zero hc.2
    simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hr hr'
    have e := h r r' hr.1 hr'.1 (by simp)
    have hlt := hm r' hr'.1
    have hMr := hM r'
    simp only [hlt, decide_true] at hMr
    rw [hMr, ← e, hr.2] at hr'
    simp at hr'
  | cons k L ih =>
    intro m hm h
    simp only [det, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    right
    constructor
    · apply ih
      · intro r hr
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr
        exact hm r hr.1
      · intro r r' hr hr' hag
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr hr'
        apply h r r' hr.1 hr'.1
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · rw [hr.2, hr'.2]
        · exact hag k' hk'
    · apply ih
      · intro r hr
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr
        exact hm r hr.1
      · intro r r' hr hr' hag
        simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hr hr'
        apply h r r' hr.1 hr'.1
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · have a1 := hM r
          have a2 := hM r'
          simp only [hm r hr.1, hm r' hr'.1, decide_true] at a1 a2
          have b1 := hr.2
          have b2 := hr'.2
          rw [a1] at b1
          rw [a2] at b2
          simp only [Bool.true_bne, Bool.not_eq_true'] at b1 b2
          rw [b1, b2]
        · exact hag k' hk'

theorem code_of_shape {n : ℕ} {g : Gate} (h : shape n g) :
    ∃ c : ℕ × List ℕ, mkGate c = g ∧ ((c.1 = 2 ∧ ∃ a, a < n ∧ c.2 = [a]) ∨
      ((c.1 = 0 ∨ c.1 = 1) ∧ ∃ a b, a < b ∧ b < n ∧ c.2 = [a, b])) := by
  obtain ⟨op, ins⟩ := g
  rcases h with ⟨ho, a, ha, e⟩ | ⟨ho | ho, a, b, hab, hb, e⟩
  · exact ⟨(2, ins), by simp_all [mkGate, opOf], Or.inl ⟨rfl, a, ha, e⟩⟩
  · exact ⟨(0, ins), by simp_all [mkGate, opOf], Or.inr ⟨Or.inl rfl, a, b, hab, hb, e⟩⟩
  · exact ⟨(1, ins), by simp_all [mkGate, opOf], Or.inr ⟨Or.inr rfl, a, b, hab, hb, e⟩⟩

theorem sound (M T : ℕ) (hM : ∀ r, M.testBit r = decide (r < 512)) (rest : List Gate) :
    ∀ (pre : List (ℕ × List ℕ)) (n : ℕ) (ws : List ℕ) (L : List ℕ), ws.length = n → 1 ≤ n →
    NFs n rest → pre.map mkGate <+: rest → L.Nodup →
    (∀ k, k ∈ L ↔ (k < n ∧ lv n rest k = true)) →
    (∀ r, r < 512 → (rest.foldl step (ws.map fun t => t.testBit r)).getD (n + rest.length - 1) false
      = T.testBit r) →
    chk M T pre rest.length ws L = true → False := by
  induction rest with
  | nil =>
    intro pre n ws L hws hn _ _ _ _ hcomp hchk
    simp only [List.length_nil, chk, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hchk
    obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero hchk
    simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, hM, decide_eq_true_eq] at hr
    have e := hcomp r hr.2
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero, getD_bit] at e
    rw [hws, e] at hr
    simp at hr
  | cons g rest ih =>
    intro pre n ws L hws hn hnf hpre hL hex hcomp hchk
    have hnf0 := hnf
    obtain ⟨hsh, hlast, hnf'⟩ := hnf
    have hcard := live_card (g :: rest) n L hnf0 hL hex
    have hdet : det M T ws L M = true := by
      apply det_true M T hM
      · intro r hr
        simpa [hM] using hr
      · intro r r' hr hr' hag
        rw [hM] at hr hr'
        simp only [decide_eq_true_eq] at hr hr'
        rw [← hcomp r hr, ← hcomp r' hr']
        apply det_sem (g :: rest) n _ _ (by simp [hws]) (by simp [hws])
        intro k hk hl
        rw [getD_bit, getD_bit]
        exact hag k ((hex k).mpr ⟨hk, hl⟩)
    simp only [List.length_cons, chk, Bool.or_eq_true, Bool.not_eq_true', hdet, Bool.true_eq_false,
      or_false] at hchk
    have hblt : Nat.blt (rest.length + 2) L.length = false := by
      simp only [List.length_cons] at hcard
      cases hb : Nat.blt (rest.length + 2) L.length
      · rfl
      · have := Nat.blt_eq.mp hb
        omega
    simp only [hblt, Bool.false_eq_true, false_or, List.all_eq_true] at hchk

    have hc : ∃ c : ℕ × List ℕ, mkGate c = g ∧ c ∈ cands pre L := by
      cases pre with
      | cons p t =>
        simp only [List.map_cons] at hpre
        have := (List.cons_prefix_cons.mp hpre).1
        exact ⟨p, this, by simp [cands]⟩
      | nil =>
        obtain ⟨c, hcg, hc⟩ := code_of_shape hsh
        refine ⟨c, hcg, ?_⟩
        have hin : ∀ a, a ∈ c.2 → a < n → a ∈ L := by
          intro a ha han
          refine (hex a).mpr ⟨han, ?_⟩
          simp [lv, ← hcg, mkGate, ha]
        obtain ⟨o, ins⟩ := c
        simp only [cands, List.mem_flatMap, List.mem_cons]
        rcases hc with ⟨ho, a, ha, e⟩ | ⟨ho, a, b, hab, hb, e⟩
        · simp only at ho e
          subst ho; subst e
          exact ⟨a, hin a (by simp) ha, Or.inl rfl⟩
        · simp only at ho e
          subst e
          refine ⟨a, hin a (by simp) (by omega), Or.inr ⟨b, hin b (by simp) hb, ?_⟩⟩
          rcases ho with rfl | rfl <;> simp [hab]
    obtain ⟨c, hcg, hcm⟩ := hc
    have hX : dropX n rest c.2 ∈ subs c.2 := filter_mem_subs _ _
    have hchild := hchk c hcm (dropX n rest c.2) hX
    have hins : g.inputs = c.2 := by rw [← hcg]; rfl
    obtain ⟨hnd, hex'⟩ := trans_exact n g rest L hlast hL hex
    rw [hins] at hnd hex'
    rw [hws] at hchild
    refine ih pre.tail (n + 1) _ _ (by simp [hws]) (by omega) hnf' ?_ hnd hex' ?_ hchild
    · cases pre with
      | nil => simp
      | cons p t =>
        simp only [List.map_cons] at hpre
        exact (List.cons_prefix_cons.mp hpre).2
    · intro r hr
      have hMr : M.testBit r = true := by simp [hM, hr]
      have e := hcomp r hr
      simp only [List.foldl_cons, List.length_cons] at e
      rw [← hcg, step_tab M r hMr] at e
      have e2 : n + 1 + rest.length - 1 = n + (rest.length + 1) - 1 := by omega
      rw [e2]
      exact e

def hasNot : List Gate → Bool
  | [] => false
  | g :: rest => (g.inputs.length == 1) || hasNot rest

def det2 (M T : ℕ) (ws : List ℕ) : List ℕ → ℕ → Bool
  | [], m => (m &&& T == 0) || (m &&& (M ^^^ T) == 0)
  | k :: L, m => (m &&& T == 0) || (m &&& (M ^^^ T) == 0) ||
      (det2 M T ws L (m &&& ws.getD k 0) && det2 M T ws L (m &&& (M ^^^ ws.getD k 0)))

def mdet (ws : List ℕ) : List ℕ → ℕ → ℕ → Bool
  | [], a, b => (a == 0) || (b == 0)
  | k :: L, a, b => (a == 0) || (b == 0) ||
      (mdet ws L (a ^^^ (a &&& ws.getD k 0)) b &&
        mdet ws L (a &&& ws.getD k 0) (b &&& ws.getD k 0))

def chkX (M T : ℕ) : List (ℕ × List ℕ) → Bool → ℕ → List ℕ → List ℕ → Bool
  | _, _, 0, ws, _ => !(((ws.getD (ws.length - 1) 0 ^^^ T) &&& M) == 0)
  | pre, nt, r + 1, ws, L =>
    Nat.blt (bif nt then r + 1 else r + 2) L.length ||
    !(bif nt then det2 M T ws L M else mdet ws L (M &&& T) (M ^^^ (M &&& T))) ||
    (cands pre L).all fun c =>
      (!nt && c.2.length == 1) ||
      (subs c.2).all fun X =>
        (!(nt && c.2.length == 1) ||
          chkX M T pre.tail false r (ws ++ [gateTab M (fun i => ws.getD i 0) c])
            (L.filter (fun k => !(X.contains k)) ++ [ws.length])) &&
        chkX M T pre.tail nt r (ws ++ [gateTab M (fun i => ws.getD i 0) c])
          (L.filter (fun k => !(X.contains k)) ++ [ws.length])

theorem det2_true (M T : ℕ) (hM : ∀ r, M.testBit r = decide (r < 512)) (ws : List ℕ) :
    ∀ (L : List ℕ) (m : ℕ), (∀ r, m.testBit r = true → r < 512) →
    (∀ r r', m.testBit r = true → m.testBit r' = true →
      (∀ k ∈ L, (ws.getD k 0).testBit r = (ws.getD k 0).testBit r') → T.testBit r = T.testBit r') →
    det2 M T ws L m = true := by
  intro L
  induction L with
  | nil =>
    intro m hm h
    simp only [det2, Bool.or_eq_true, beq_iff_eq]
    by_contra hc
    push_neg at hc
    obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero hc.1
    obtain ⟨r', hr'⟩ := Nat.exists_testBit_of_ne_zero hc.2
    simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hr hr'
    have e := h r r' hr.1 hr'.1 (by simp)
    have hlt := hm r' hr'.1
    have hMr := hM r'
    simp only [hlt, decide_true] at hMr
    rw [hMr, ← e, hr.2] at hr'
    simp at hr'
  | cons k L ih =>
    intro m hm h
    simp only [det2, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    right
    constructor
    · apply ih
      · intro r hr
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr
        exact hm r hr.1
      · intro r r' hr hr' hag
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr hr'
        apply h r r' hr.1 hr'.1
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · rw [hr.2, hr'.2]
        · exact hag k' hk'
    · apply ih
      · intro r hr
        simp only [Nat.testBit_and, Bool.and_eq_true] at hr
        exact hm r hr.1
      · intro r r' hr hr' hag
        simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true] at hr hr'
        apply h r r' hr.1 hr'.1
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · have a1 := hM r
          have a2 := hM r'
          simp only [hm r hr.1, hm r' hr'.1, decide_true] at a1 a2
          have b1 := hr.2
          have b2 := hr'.2
          rw [a1] at b1
          rw [a2] at b2
          simp only [Bool.true_bne, Bool.not_eq_true'] at b1 b2
          rw [b1, b2]
        · exact hag k' hk'

theorem mdet_true (ws : List ℕ) : ∀ (L : List ℕ) (a b : ℕ),
    (∀ r r', a.testBit r = true → b.testBit r' = true →
      (∀ k ∈ L, (ws.getD k 0).testBit r = true → (ws.getD k 0).testBit r' = true) → False) →
    mdet ws L a b = true := by
  intro L
  induction L with
  | nil =>
    intro a b h
    simp only [mdet, Bool.or_eq_true, beq_iff_eq]
    by_contra hc
    push_neg at hc
    obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero hc.1
    obtain ⟨r', hr'⟩ := Nat.exists_testBit_of_ne_zero hc.2
    exact h r r' hr hr' (by simp)
  | cons k L ih =>
    intro a b h
    simp only [mdet, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
    right
    constructor
    · apply ih
      intro r r' hr hr' hag
      simp only [Nat.testBit_xor, Nat.testBit_and] at hr
      have ha : a.testBit r = true := by
        cases h1 : a.testBit r with
        | true => rfl
        | false => rw [h1] at hr; simp at hr
      have hw : (ws.getD k 0).testBit r = false := by
        cases h2 : (ws.getD k 0).testBit r with
        | false => rfl
        | true => rw [ha, h2] at hr; simp at hr
      apply h r r' ha hr'
      intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · intro hx; rw [hw] at hx; simp at hx
      · exact hag k' hk'
    · apply ih
      intro r r' hr hr' hag
      simp only [Nat.testBit_and, Bool.and_eq_true] at hr hr'
      apply h r r' hr.1 hr'.1
      intro k' hk'
      rcases List.mem_cons.mp hk' with rfl | hk'
      · intro _; exact hr'.2
      · exact hag k' hk'

theorem mono_sem (rest : List Gate) : ∀ (n : ℕ) (w w' : List Bool), w.length = n → w'.length = n →
    NFs n rest → hasNot rest = false →
    (∀ k, k < n → lv n rest k = true → w.getD k false = true → w'.getD k false = true) →
    (rest.foldl step w).getD (n + rest.length - 1) false = true →
    (rest.foldl step w').getD (n + rest.length - 1) false = true := by
  induction rest with
  | nil =>
    intro n w w' hw hw' _ _ h
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    by_cases hn : n = 0
    · subst hn
      rw [List.length_eq_zero_iff.mp hw, List.length_eq_zero_iff.mp hw']
      exact id
    · exact h (n - 1) (by omega) (by simp [lv])
  | cons g rest ih =>
    intro n w w' hw hw' hnf hno h
    obtain ⟨hsh, _, hnf'⟩ := hnf
    simp only [hasNot, Bool.or_eq_false_iff] at hno
    obtain ⟨hg1, hno'⟩ := hno
    simp only [List.foldl_cons, List.length_cons]
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
      rcases hsh with ⟨_, a, _, e⟩ | ⟨ho, a, b, hab, hb, e⟩
      · rw [e] at hg1; simp at hg1
      · have ha' : lv n (g :: rest) a = true := by simp [lv, e]
        have hb' : lv n (g :: rest) b = true := by simp [lv, e]
        have h1 := h a (by omega) ha'
        have h2 := h b hb hb'
        rcases ho with ho | ho
        · rw [ho, e]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true, Bool.and_eq_true]
          rintro ⟨x, y⟩
          exact ⟨h1 x, h2 y⟩
        · rw [ho, e]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
            Bool.or_false, Bool.or_eq_true]
          rintro (x | y)
          · exact Or.inl (h1 x)
          · exact Or.inr (h2 y)
    have z : ∀ (v : Bool) (m : ℕ), [v].getD (m - m) false = v := by
      intro v m; simp
    have e := ih (n + 1) (step w g) (step w' g) (by simp [step_length, hw])
      (by simp [step_length, hw']) hnf' hno' (by
      intro k hk hl
      by_cases hkn : k < n
      · simp only [step]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h k hkn (by simp [lv, hl])
      · have : k = n := by omega
        subst this
        simp only [step]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [hw, hw', z, z]
        exact hv)
    have e2 : n + 1 + rest.length - 1 = n + (rest.length + 1) - 1 := by omega
    rw [e2] at e
    exact e

theorem live_card_not (rest : List Gate) : ∀ (n : ℕ) (L : List ℕ), NFs n rest →
    hasNot rest = true → L.Nodup →
    (∀ k, k ∈ L ↔ (k < n ∧ lv n rest k = true)) → L.length ≤ rest.length := by
  induction rest with
  | nil => intro n L _ hn; simp [hasNot] at hn
  | cons g rest ih =>
    intro n L hnf hn hL hex
    obtain ⟨hsh, hlast, hnf'⟩ := hnf
    obtain ⟨hnd, hex'⟩ := trans_exact n g rest L hlast hL hex
    have h2 := filter_len L (dropX n rest g.inputs) hL
    have h3 : (dropX n rest g.inputs).length ≤ g.inputs.length := List.length_filter_le _ _
    have h4 := shape_len hsh
    simp only [hasNot, Bool.or_eq_true, beq_iff_eq] at hn
    by_cases hr : hasNot rest = true
    · have h1 := ih (n + 1) _ hnf' hr hnd hex'
      simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
      omega
    · have hg : g.inputs.length = 1 := by
        rcases hn with hn | hn
        · exact hn
        · exact absurd hn hr
      have h1 := live_card rest (n + 1) _ hnf' hnd hex'
      simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
      omega

theorem soundX (M T : ℕ) (hM : ∀ r, M.testBit r = decide (r < 512)) (rest : List Gate) :
    ∀ (pre : List (ℕ × List ℕ)) (nt : Bool) (n : ℕ) (ws : List ℕ) (L : List ℕ), ws.length = n →
    1 ≤ n → NFs n rest → pre.map mkGate <+: rest → L.Nodup →
    (∀ k, k ∈ L ↔ (k < n ∧ lv n rest k = true)) →
    (∀ r, r < 512 → (rest.foldl step (ws.map fun t => t.testBit r)).getD (n + rest.length - 1) false
      = T.testBit r) →
    hasNot rest = nt →
    chkX M T pre nt rest.length ws L = true → False := by
  induction rest with
  | nil =>
    intro pre nt n ws L hws hn _ _ _ _ hcomp _ hchk
    simp only [List.length_nil, chkX, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hchk
    obtain ⟨r, hr⟩ := Nat.exists_testBit_of_ne_zero hchk
    simp only [Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, hM, decide_eq_true_eq] at hr
    have e := hcomp r hr.2
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero, getD_bit] at e
    rw [hws, e] at hr
    simp at hr
  | cons g rest ih =>
    intro pre nt n ws L hws hn hnf hpre hL hex hcomp hnt hchk
    have hnf0 := hnf
    obtain ⟨hsh, hlast, hnf'⟩ := hnf
    have hc : ∃ c : ℕ × List ℕ, mkGate c = g ∧ c ∈ cands pre L := by
      cases pre with
      | cons p t =>
        simp only [List.map_cons] at hpre
        have := (List.cons_prefix_cons.mp hpre).1
        exact ⟨p, this, by simp [cands]⟩
      | nil =>
        obtain ⟨c, hcg, hc⟩ := code_of_shape hsh
        refine ⟨c, hcg, ?_⟩
        have hin : ∀ a, a ∈ c.2 → a < n → a ∈ L := by
          intro a ha han
          refine (hex a).mpr ⟨han, ?_⟩
          simp [lv, ← hcg, mkGate, ha]
        obtain ⟨o, ins⟩ := c
        simp only [cands, List.mem_flatMap, List.mem_cons]
        rcases hc with ⟨ho, a, ha, e⟩ | ⟨ho, a, b, hab, hb, e⟩
        · simp only at ho e
          subst ho; subst e
          exact ⟨a, hin a (by simp) ha, Or.inl rfl⟩
        · simp only at ho e
          subst e
          refine ⟨a, hin a (by simp) (by omega), Or.inr ⟨b, hin b (by simp) hb, ?_⟩⟩
          rcases ho with rfl | rfl <;> simp [hab]
    obtain ⟨c, hcg, hcm⟩ := hc
    have hX : dropX n rest c.2 ∈ subs c.2 := filter_mem_subs _ _
    have hins : g.inputs = c.2 := by rw [← hcg]; rfl
    obtain ⟨hnd, hex'⟩ := trans_exact n g rest L hlast hL hex
    rw [hins] at hnd hex'
    have hpre' : pre.tail.map mkGate <+: rest := by
      cases pre with
      | nil => simp
      | cons p t =>
        simp only [List.map_cons] at hpre
        exact (List.cons_prefix_cons.mp hpre).2
    have hcomp' : ∀ r, r < 512 →
        (rest.foldl step ((ws ++ [gateTab M (fun i => ws.getD i 0) c]).map fun t => t.testBit r)).getD
          (n + 1 + rest.length - 1) false = T.testBit r := by
      intro r hr
      have hMr : M.testBit r = true := by simp [hM, hr]
      have e := hcomp r hr
      simp only [List.foldl_cons, List.length_cons] at e
      rw [← hcg, step_tab M r hMr] at e
      have e2 : n + 1 + rest.length - 1 = n + (rest.length + 1) - 1 := by omega
      rw [e2]
      exact e
    have fin : ∀ nt' : Bool, hasNot rest = nt' →
        chkX M T pre.tail nt' rest.length (ws ++ [gateTab M (fun i => ws.getD i 0) c])
          (L.filter (fun k => !((dropX n rest c.2).contains k)) ++ [n]) = true → False := by
      intro nt' hnt' hchild
      exact ih pre.tail nt' (n + 1) _ _ (by simp [hws]) (by omega) hnf' hpre' hnd hex' hcomp'
        hnt' hchild
    simp only [hasNot] at hnt
    cases nt with
    | false =>
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hnt
      obtain ⟨hg1, hno'⟩ := hnt
      have hcard := live_card (g :: rest) n L hnf0 hL hex
      have hmd : mdet ws L (M &&& T) (M ^^^ (M &&& T)) = true := by
        apply mdet_true
        intro r r' hr hr' hag
        simp only [Nat.testBit_and, Nat.testBit_xor, hM, Bool.and_eq_true,
          decide_eq_true_eq] at hr hr'
        have hr'lt : r' < 512 := by
          by_contra hx
          simp [hx] at hr'
        have hT' : T.testBit r' = false := by
          cases hq : T.testBit r' with
          | false => rfl
          | true => simp [hr'lt, hq] at hr'
        have m := mono_sem (g :: rest) n (ws.map fun t => t.testBit r)
          (ws.map fun t => t.testBit r') (by simp [hws]) (by simp [hws]) hnf0
          (by simp [hasNot, hg1, hno']) (by
            intro k hk hl
            rw [getD_bit, getD_bit]
            exact hag k ((hex k).mpr ⟨hk, hl⟩)) (by rw [hcomp r hr.1]; exact hr.2)
        rw [hcomp r' hr'lt, hT'] at m
        simp at m
      simp only [List.length_cons, chkX, Bool.cond_false, Bool.or_eq_true, Bool.not_eq_true', hmd,
        Bool.true_eq_false, or_false] at hchk
      have hblt : Nat.blt (rest.length + 2) L.length = false := by
        simp only [List.length_cons] at hcard
        cases hb : Nat.blt (rest.length + 2) L.length
        · rfl
        · have := Nat.blt_eq.mp hb
          omega
      simp only [hblt, Bool.false_eq_true, false_or, List.all_eq_true] at hchk
      have h1 := hchk c hcm
      have hc1 : (c.2.length == 1) = false := by
        rw [← hins]; simpa using hg1
      simp only [hc1, Bool.not_false, Bool.true_and, Bool.false_or, Bool.false_and,
        Bool.true_or, List.all_eq_true] at h1
      have h2 := h1 (dropX n rest c.2) hX
      rw [hws] at h2
      exact fin false hno' h2
    | true =>
      have hcard := live_card_not (g :: rest) n L hnf0 (by simpa [hasNot] using hnt) hL hex
      have hdet : det2 M T ws L M = true := by
        apply det2_true M T hM
        · intro r hr
          simpa [hM] using hr
        · intro r r' hr hr' hag
          rw [hM] at hr hr'
          simp only [decide_eq_true_eq] at hr hr'
          rw [← hcomp r hr, ← hcomp r' hr']
          apply det_sem (g :: rest) n _ _ (by simp [hws]) (by simp [hws])
          intro k hk hl
          rw [getD_bit, getD_bit]
          exact hag k ((hex k).mpr ⟨hk, hl⟩)
      simp only [List.length_cons, chkX, Bool.cond_true, Bool.or_eq_true, Bool.not_eq_true', hdet,
        Bool.true_eq_false, or_false] at hchk
      have hblt : Nat.blt (rest.length + 1) L.length = false := by
        simp only [List.length_cons] at hcard
        cases hb : Nat.blt (rest.length + 1) L.length
        · rfl
        · have := Nat.blt_eq.mp hb
          omega
      simp only [hblt, Bool.false_eq_true, false_or, List.all_eq_true] at hchk
      have h1 := hchk c hcm
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, false_or, List.all_eq_true,
        Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h1
      have h2 := h1 (dropX n rest c.2) hX
      rw [hws] at h2
      obtain ⟨h2a, h2b⟩ := h2
      cases hr : hasNot rest with
      | true => exact fin true hr h2b
      | false =>
        have hg1 : (c.2.length == 1) = true := by
          rw [← hins]; rw [hr] at hnt; simpa using hnt
        rcases h2a with h2a | h2a
        · rw [hg1] at h2a; simp at h2a
        · exact fin false hr h2a

def ws0 : List ℕ := (List.range 9).map fun i => tab (fun r => r.testBit i) 512

theorem tab_testBit (p : ℕ → Bool) (n r : ℕ) : (tab p n).testBit r = (decide (r < n) && p r) := by
  induction n with
  | zero => simp [tab]
  | succ n ih =>
    rw [tab, Nat.testBit_or, ih]
    by_cases hp : p n = true
    · rw [if_pos hp, Nat.testBit_two_pow]
      by_cases h1 : r < n
      · have : ¬ n = r := by omega
        simp [h1, this, show r < n + 1 by omega]
      · by_cases h2 : n = r
        · subst h2; simp [hp]
        · simp [h1, h2, show ¬ r < n + 1 by omega]
    · rw [if_neg hp, Nat.zero_testBit, Bool.or_false]
      by_cases h1 : r < n
      · simp [h1, show r < n + 1 by omega]
      · by_cases h2 : n = r
        · subst h2; simp at hp; simp [hp]
        · simp [h1, show ¬ r < n + 1 by omega]

theorem ws0_row (r : ℕ) (hr : r < 512) :
    List.ofFn (fun i : Fin 9 => r.testBit i) = ws0.map fun t => t.testBit r := by
  rw [ws0, List.map_map]
  have h : ((fun t : ℕ => t.testBit r) ∘ fun i => tab (fun r => r.testBit i) 512)
      = fun i => r.testBit i := by
    funext i
    simp [tab_testBit, hr]
  rw [h]
  rfl

theorem lv_of_mem : ∀ (rest : List Gate) (m k : ℕ) (i : Fin rest.length),
    k ∈ (rest.get i).inputs → lv m rest k = true := by
  intro rest
  induction rest with
  | nil => intro m k i; exact i.elim0
  | cons g rest ih =>
    intro m k i hk
    rw [lv, Bool.or_eq_true]
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => left; simpa using hk
    | succ i =>
      right
      exact ih (m + 1) k ⟨i, by simpa using hi⟩ (by simpa using hk)

theorem nfs_of_hyps : ∀ (gs : List Gate) (n : ℕ)
    (_ : ∀ j : Fin gs.length,
      ((gs.get j).op = GateOp.not ∧ ∃ a, a < n + j.val ∧ (gs.get j).inputs = [a]) ∨
      (((gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < n + j.val ∧ (gs.get j).inputs = [a, b]))
    (_ : ∀ j : Fin gs.length, j.val + 1 < gs.length →
      ∃ k : Fin gs.length, j.val < k.val ∧ n + j.val ∈ (gs.get k).inputs),
    NFs n gs := by
  intro gs
  induction gs with
  | nil => intro n _ _; trivial
  | cons g rest ih =>
    intro n h1 h2
    refine ⟨?_, ?_, ?_⟩
    · have := h1 ⟨0, by simp⟩
      simpa [shape] using this
    · cases rest with
      | nil => simp [lv]
      | cons g' rest' =>
        obtain ⟨k, hk1, hk2⟩ := h2 ⟨0, by simp⟩ (by simp)
        rcases k with ⟨k, hk⟩
        cases k with
        | zero => simp at hk1
        | succ k =>
          exact lv_of_mem (g' :: rest') (n + 1) n ⟨k, by simpa using hk⟩ (by simpa using hk2)
    · apply ih (n + 1)
      · intro j
        have := h1 ⟨j.val + 1, by simp⟩
        simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using this
      · intro j hj
        obtain ⟨k, hk1, hk2⟩ := h2 ⟨j.val + 1, by simp⟩ (by simpa using hj)
        rcases k with ⟨k, hk⟩
        cases k with
        | zero => simp at hk1
        | succ k =>
          refine ⟨⟨k, by simpa using hk⟩, by simpa using hk1, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using hk2

def M0 : ℕ := tab (fun _ => true) 512

def PM (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

def F (r : ℕ) : Bool := PM fun i : Fin 9 => r.testBit i

def T0 : ℕ := tab F 512

def pre0 : List (ℕ × List ℕ) := [(2, [0]), (0, [4, 5])]

def codes : List (ℕ × List ℕ) := cands [] (List.range 11)

theorem ok_small : ((List.range 12).all fun S => (subs (List.range 9)).all fun L =>
    chkX M0 T0 pre0 true S ws0 L) = true := by
  decide +kernel

theorem ok_roots : ((subs (List.range 9)).all fun L =>
    (L == List.range 9) || chkX M0 T0 pre0 true 12 ws0 L) = true := by
  decide +kernel

theorem ok_a0 : (codes.all fun c => !(c.2.headD 0 == 0) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a1 : (codes.all fun c => !(c.2.headD 0 == 1) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a2 : (codes.all fun c => !(c.2.headD 0 == 2) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a3 : (codes.all fun c => !(c.2.headD 0 == 3) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a4 : (codes.all fun c => !(c.2.headD 0 == 4) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a5 : (codes.all fun c => !(c.2.headD 0 == 5) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a6 : (codes.all fun c => !(c.2.headD 0 == 6) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a7 : (codes.all fun c => !(c.2.headD 0 == 7) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a8 : (codes.all fun c => !(c.2.headD 0 == 8) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a9 : (codes.all fun c => !(c.2.headD 0 == 9) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem ok_a10 : (codes.all fun c => !(c.2.headD 0 == 10) ||
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true := by
  decide +kernel

theorem codes_head : (codes.all fun c => Nat.blt (c.2.headD 0) 11) = true := by
  decide +kernel

theorem ok_codes (c : ℕ × List ℕ) (hc : c ∈ codes) :
    chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9) = true := by
  have hh := List.all_eq_true.mp codes_head c hc
  have hlt : c.2.headD 0 < 11 := Nat.blt_eq.mp hh
  have key : ∀ a, c.2.headD 0 = a → (codes.all fun c => !(c.2.headD 0 == a) ||
      chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9)) = true →
      chkX M0 T0 [(2, [0]), (0, [4, 5]), c] true 12 ws0 (List.range 9) = true := by
    intro a ha hall
    have h := List.all_eq_true.mp hall c hc
    subst ha
    simpa using h
  generalize hv : c.2.headD 0 = v at hlt
  have hk := key v hv
  clear key
  apply hk
  interval_cases v
  · exact ok_a0
  · exact ok_a1
  · exact ok_a2
  · exact ok_a3
  · exact ok_a4
  · exact ok_a5
  · exact ok_a6
  · exact ok_a7
  · exact ok_a8
  · exact ok_a9
  · exact ok_a10

theorem code_mem_codes (c : ℕ × List ℕ)
    (hc : (c.1 = 2 ∧ ∃ a, a < 11 ∧ c.2 = [a]) ∨
      ((c.1 = 0 ∨ c.1 = 1) ∧ ∃ a b, a < b ∧ b < 11 ∧ c.2 = [a, b])) : c ∈ codes := by
  obtain ⟨o, ins⟩ := c
  simp only [codes, cands, List.mem_flatMap, List.mem_cons, List.mem_range]
  rcases hc with ⟨ho, a, ha, e⟩ | ⟨ho, a, b, hab, hb, e⟩
  · simp only at ho e
    subst ho; subst e
    exact ⟨a, ha, Or.inl rfl⟩
  · simp only at ho e
    subst e
    refine ⟨a, by omega, Or.inr ⟨b, hb, ?_⟩⟩
    rcases ho with rfl | rfl <;> simp [hab]

theorem main (C : Circuit) (hsz : C.size ≤ 12)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = PM x)
    (hout : C.output + 1 = 9 + C.size)
    (hsh : ∀ j : Fin C.gates.length,
      ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
        ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b]))
    (hrd : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some ⟨GateOp.not, [0]⟩)
    (h1 : C.gates.tail.head? = some ⟨GateOp.and, [4, 5]⟩) : False := by
  have hnf : NFs 9 C.gates := nfs_of_hyps C.gates 9 hsh hrd
  have hM : ∀ r, M0.testBit r = decide (r < 512) := by
    intro r
    simp [M0, tab_testBit]
  have hszl : C.gates.length ≤ 12 := hsz
  have hlive : ∀ k, k ∈ ((List.range 9).filter fun k => lv 9 C.gates k) ↔
      (k < 9 ∧ lv 9 C.gates k = true) := by
    intro k
    simp [List.mem_filter, List.mem_range]
  have hrow : ∀ r, r < 512 →
      (C.gates.foldl step (ws0.map fun t => t.testBit r)).getD (9 + C.gates.length - 1) false
        = T0.testBit r := by
    intro r hr
    have e := hev fun i : Fin 9 => r.testBit i
    rw [ws0_row r hr] at e
    have ho : C.output = 9 + C.gates.length - 1 := by
      have : C.size = C.gates.length := rfl
      omega
    rw [T0, tab_testBit]
    simp only [hr, decide_true, Bool.true_and]
    rw [← ho]
    exact e
  cases hg : C.gates with
  | nil => rw [hg] at h0; simp at h0
  | cons g0 t =>
    cases t with
    | nil => rw [hg] at h1; simp at h1
    | cons g1 t' =>
      have h0' := h0
      have h1' := h1
      rw [hg] at h0' h1'
      simp only [List.head?_cons, List.tail_cons, Option.some.injEq] at h0' h1'
      subst h0'; subst h1'
      have hnot : hasNot C.gates = true := by
        rw [hg]; simp [hasNot]
      have hpre : pre0.map mkGate <+: C.gates := by
        rw [hg]
        exact ⟨t', by simp [pre0, mkGate, opOf]⟩
      by_cases hlen : C.gates.length < 12
      · have hall := ok_small
        rw [List.all_eq_true] at hall
        have h2 := hall C.gates.length (List.mem_range.mpr hlen)
        rw [List.all_eq_true] at h2
        have hchk := h2 ((List.range 9).filter fun k => lv 9 C.gates k) (filter_mem_subs _ _)
        exact soundX M0 T0 hM C.gates pre0 true 9 ws0 _ rfl (by omega) hnf hpre
          (List.nodup_range.filter _) hlive hrow hnot hchk
      · have hlen12 : C.gates.length = 12 := by omega
        by_cases hL : ((List.range 9).filter fun k => lv 9 C.gates k) = List.range 9
        ·
          cases t' with
          | nil => rw [hg] at hlen12; simp at hlen12
          | cons g2 t'' =>
            have hs2 := hsh ⟨2, by omega⟩
            have hg2 : C.gates.get ⟨2, by omega⟩ = g2 := by
              simp [hg]
            rw [hg2] at hs2
            have hshape : shape 11 g2 := hs2
            obtain ⟨c, hcg, hc⟩ := code_of_shape hshape
            have hcm : c ∈ codes := code_mem_codes c hc
            have hchk := ok_codes c hcm
            have hpre3 : [(2, [0]), (0, [4, 5]), c].map mkGate <+: C.gates := by
              rw [hg]
              exact ⟨t'', by simp [mkGate, opOf, ← hcg]⟩
            rw [← hL, ← hlen12] at hchk
            exact soundX M0 T0 hM C.gates _ true 9 ws0 _ rfl (by omega) hnf hpre3
              (List.nodup_range.filter _) hlive hrow hnot hchk
        · have hall := ok_roots
          rw [List.all_eq_true] at hall
          have h2 := hall ((List.range 9).filter fun k => lv 9 C.gates k) (filter_mem_subs _ _)
          have hne : (((List.range 9).filter fun k => lv 9 C.gates k) == List.range 9) = false := by
            simpa using hL
          rw [hne, Bool.false_or, ← hlen12] at h2
          exact soundX M0 T0 hM C.gates pre0 true 9 ws0 _ rfl (by omega) hnf hpre
            (List.nodup_range.filter _) hlive hrow hnot h2

end PEqualNP.Outside.L_meta_27450

theorem PEqualNP.Outside.L_meta_27450 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩)) := by
  rintro ⟨C, _, hsz, hev, hout, hsh, _, hrd, h0, h1⟩
  exact PEqualNP.Outside.L_meta_27450.main C hsz hev hout hsh hrd h0 h1
