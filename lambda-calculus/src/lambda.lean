import data.equiv.denumerable

import tactic.split_ifs
import tactic.suggest

set_option trace.eqn_compiler.elim_match true
set_option trace.check true
set_option trace.simplify true
set_option trace.simplify.rewrite true
-- set_option trace.simp_lemmas true
-- set_option trace.class_instances true

-- set_option class.instance_max_depth 200

local notation `‹` p `›` := 
  (show p, by assumption)

universe u

namespace lambda

  -- The type of syntactic Λ-terms
  inductive pre_term { α : Type u } : Type (u + 1)
  | var : α → pre_term
  | app : pre_term → pre_term → pre_term
  | lam : α → pre_term → pre_term

  open pre_term

  section

    parameter { α : Type u }

    -- We don't care about the size of the variable type αN
    def sizeof : @pre_term α → ℕ
    | (var z)   := 0
    | (app t u) := 1 + (sizeof t) + (sizeof u)
    | (lam x t) := 1 + (sizeof t)

    instance pre_term_has_sizeof : has_sizeof pre_term :=
      has_sizeof.mk sizeof

  end

  section

    parameters { α : Type u } [denumerable α] { αs : finset α }

    private 
      def incl : α ↪ ℕ :=
        function.embedding.mk encodable.encode encodable.encode_injective

    private
      def codes := finset.map incl αs
    
    private
      def code := 
        match codes.max with
        | none :=  0
        | some n := (n+1)
        end

    lemma lt_ne { m n : ℕ } (h : m < n) : m ≠ n
      := 
        begin
          -- m ≠ n is shorthand for m = n → false
          assume : m = n,
          -- have : n < n,
            -- by 
            rw ‹m = n› at h,
            -- from ‹m = n› ▸ ‹m < n›,
          have : ¬ n < n,
            by apply nat.lt_irrefl,
          contradiction,
          done
        end

    #print axioms lt_ne

    private lemma new_code : ∀ c ∈ codes, c ≠ code
      :=
        begin
          intros,
          cases (finset.max_of_mem ‹c ∈ codes›) with m,

          have : codes.max = some m, 
            -- by assumption,
            from ‹m ∈ codes.max›,

          have : code = m + 1, by {
            rw code,
            rw ‹codes.max = some m›,
            -- rw this,
            refl,
          },

          have : c < code,
            by calc
              c ≤ m : by {apply finset.le_max_of_mem, repeat {assumption}}
              ... < m + 1 : by apply nat.lt_succ_self
              ... = code : by {symmetry, from ‹code = m + 1›},

          apply lt_ne this,
          done,
        end

    private lemma decode_in_codes
        { n : ℕ } : ((denumerable.of_nat α n) ∈ αs) → (n ∈ codes)
      := 
        begin
          intros,
          rw codes,
          rw ←denumerable.encode_of_nat n,
          apply finset.mem_map_of_mem incl ‹denumerable.of_nat α n ∈ αs›,
          done
        end

    #print axioms decode_in_codes

    -- Now make αs an explicit parameter
    parameter ( αs )

    def fresh_var : α := 
      denumerable.of_nat α code

    lemma freshness : fresh_var ∉ αs :=
      begin
        -- Proof by contradition
        assume : (fresh_var αs) ∈ αs,
        have : (fresh_var αs) = denumerable.of_nat α code,
          by refl,
        have : (denumerable.of_nat α code) ∈ αs,
          by rwa ←this,
        have : (code ∈ codes),
          by apply decode_in_codes this,
        have : code ≠ code,
          by apply new_code code this,
        let code := @code α ‹denumerable α› αs,
        have : code = code,
          by refl,
        contradiction,
        done,
      end

    #print axioms freshness

  end

  #check freshness
  #print freshness

  section

    parameter { α : Type u }

    parameters 
      [has_emptyc (finset α)]
      [has_union (finset α)]
      [has_sdiff (finset α)]
      [has_union (multiset α)]

    def free_vars : pre_term → finset α
    | (var x)   := finset.singleton x
    | (app t u) := (free_vars t) ∪ (free_vars u)
    | (lam x t) := (free_vars t) \ (finset.singleton x)

    def bound_vars : pre_term → finset α
    | (var x)   := ∅
    | (app t u) := (bound_vars t) ∪ (bound_vars u)
    | (lam x t) := (bound_vars t) ∪ (finset.singleton x)

    def bound_vars_mset : pre_term → multiset α
    | (var x)   := x :: 0
    | (app t u) := (bound_vars_mset t) ∪ (bound_vars_mset t)
    | (lam x t) := x :: (bound_vars_mset t)

    -- The pre-term obeys Barendregt's convention
    def canonical (t : pre_term) : Prop
      :=
        let bvars := bound_vars_mset t in
        multiset.nodup bvars
          ∧
        ∀ x ∈ bvars, x ∉ (free_vars t)

  end

  section

    parameter { α : Type u }

    parameters
      [decidable_eq α]
      [denumerable α]

    -- Renaming a free variable
    def rename (x : α) (y : α) : @pre_term α → @pre_term α
    | (var z)   := if z = x then (var y) else (var z)
    | (app t u) := (app (rename t) (rename u))
    | (lam z t) := if z = x then (lam z t) else (lam z (rename t))

    /- We need to show that the rename operation does not increase the size of
       pre-terms, so Lean knows our notion of capture-avoiding substitution
       and α-equivalence is well defined.
     -/
    lemma rename_nonincreasing 
      : ∀ {t : pre_term} {x y : α}, sizeof (rename x y t) = sizeof t
    := 
      begin
        intros,
        induction t with _ u v ih_u ih_v z u ih_u,
        case pre_term.var {
          rw rename,
          split_ifs,
          -- both cases follow be the definition of sizeof
          repeat {repeat {rw sizeof}},
          done
        },
        case pre_term.app {
          calc
            sizeof (rename x y (app u v))
                 = sizeof (app (rename x y u) (rename x y v)) : by rw rename
             ... = 1 + sizeof (rename x y u) + sizeof (rename x y v) : by refl
             ... = 1 + sizeof u + sizeof (rename x y v) : by rw ih_u
             ... = 1 + sizeof u + sizeof v : by rw ih_v
             ... = sizeof (app u v) : by refl,
        },
        case pre_term.lam {
          rw rename,
          split_ifs,
            {refl,},
            {calc
              sizeof (lam z (rename x y u))
                    = 1 + sizeof (rename x y u) : by refl
                ... = 1 + sizeof u : by rw ih_u
                ... = sizeof (lam z u) : by refl,
            },
        },
        done,
      end

    -- Capture avoiding substitution
    def subst (u : pre_term) (x : α) : @pre_term α → @pre_term α
        | (var y)    := if x = y then u else (var y)
        | (app t₁ t₂) := app (subst t₁) (subst t₂)
        | (lam y t)  :=
            if y = x
              then (lam y t)
              else
                let z := fresh_var ((free_vars u) ∪ (free_vars t)) in
                have sizeof (rename y z t) < 1 + sizeof t, 
                  by calc
                    sizeof (rename y z t)
                        = sizeof t       : by apply rename_nonincreasing
                    ... < (sizeof t) + 1 : by apply nat.lt.base
                    ... = 1 + (sizeof t) : by apply nat.add_comm,
                lam z (subst (rename y z t))

    def alpha_equiv : @pre_term α → @pre_term α → Prop
    | (pre_term.var x) (pre_term.var y) :=
      x = y
    | (pre_term.app t₁ u₁) (pre_term.app t₂ u₂) :=
      (alpha_equiv t₁ t₂) ∧ (alpha_equiv u₁ u₂)
    | (pre_term.lam x t) (pre_term.lam y u) := 
      let z := fresh_var ((free_vars t) ∪ (free_vars u)) in
      have sizeof (rename x z t) < 1 + sizeof t, 
        by calc
          sizeof (rename x z t)
               = sizeof t       : by apply rename_nonincreasing
           ... < (sizeof t) + 1 : by apply nat.lt.base
           ... = 1 + (sizeof t) : by apply nat.add_comm,
      alpha_equiv (rename x z t) (rename y z u)
    | _ _ :=
      false

    local notation t `≅` u := alpha_equiv t u

    -- α-equivalence really is an equivalence relation

    lemma alpha_equiv_refl
      : ∀ (t : pre_term), t ≅ t
    :=
      sorry

    lemma alpha_equiv_symm
      : ∀ (t u : pre_term), (t ≅ u) → (u ≅ t)
    :=
      sorry

    lemma alpha_equiv_trans 
      : ∀ (t u v : pre_term), (t ≅ u) ∧ (u ≅ v) → (t ≅ v)
    :=
      sorry

    -- Moreover, α-equivalence is a congruence

    lemma cong_app_left
      : ∀ (t u v : pre_term), (t ≅ u) → ((app t u) ≅ (app t v))
    :=
      sorry

    lemma cong_app_right
      : ∀ (t u v : pre_term), (t ≅ u) → ((app t u) ≅ (app t v))
    :=
      sorry

    lemma cong_lam
      : ∀ (x : α) (t u : pre_term), (t ≅ u) → ((lam x t) ≅ (lam x u))
    :=
      sorry

    -- The type of (α-equivalence classes of) Λ-terms
    def term := quot alpha_equiv

    -- We can now define β-reduction on terms (i.e. on α-equivalence classes)

  end

  open pre_term

  -- notation `_` x `_` := var x
  -- notation `λ` x `.` t := lam x t
  -- notation t `⬝` u := app t u

  -- The identity function λx.x
  def id : pre_term := (lam "x" (var "x"))
  -- example : pre_term := λ "x" . (_ "x" _)

end lambda