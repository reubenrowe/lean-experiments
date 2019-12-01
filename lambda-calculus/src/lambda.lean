import data.equiv.denumerable

import tactic.split_ifs
import tactic.suggest

set_option trace.eqn_compiler.elim_match true
set_option trace.check true
set_option trace.simplify true
set_option trace.simplify.rewrite true
-- set_option trace.simp_lemmas true
-- set_option trace.class_instances true

local notation `‹` p `›` := 
  (show p, by assumption)

universe u

namespace lambda

  section

    parameter { α : Type u }

    -- The type of syntactic Λ-terms
    inductive pre_term : Type (u + 1)
      | var : α → pre_term
      | app : pre_term → pre_term → pre_term
      | lam : α → pre_term → pre_term

    open pre_term

    -- We don't care about the size of the variable type αN
    def sizeof : pre_term → ℕ
      | (var z)   := 0
      | (app t u) := 1 + (sizeof t) + (sizeof u)
      | (lam x t) := 1 + (sizeof t)

    instance pre_term_has_sizeof : has_sizeof pre_term
      :=
        has_sizeof.mk sizeof

    lemma size_zero_var { x : α } : sizeof (var x) = 0
      :=
        by rw sizeof

    lemma size_pos_app { t u : pre_term } : ¬ sizeof (app t u) ≤ 0
      :=
        begin
          rw sizeof,
          rw (show 1 + sizeof t + sizeof u = 1 + (sizeof t + sizeof u),
                by apply nat.add_assoc),
          generalize : sizeof t + sizeof u = n,
          rw nat.add_comm,
          rw (show n + 1 = nat.succ n, by refl),
          apply nat.not_succ_le_zero n,
          done
        end

    lemma size_pos_lam { x : α } { t : pre_term } : ¬ sizeof (lam x t) ≤ 0
      :=
        begin
          rw sizeof,
          generalize : sizeof t = n,
          rw nat.add_comm,
          rw (show n + 1 = nat.succ n, by refl),
          apply nat.not_succ_le_zero n,
          done
        end

    lemma size_of_size_app_left 
      { n : ℕ } { t u : pre_term } : (sizeof (app t u) ≤ n + 1) → (sizeof t ≤ n)
    :=
      begin
        intro,
        apply nat.le_of_succ_le_succ,
        calc
          sizeof t + 1
              = 1 + sizeof t            : by apply nat.add_comm
          ... ≤ 1 + sizeof t + sizeof u : nat.le.intro rfl
          ... = sizeof (app t u)        : by rw sizeof
          ... ≤ n + 1                    : by assumption,
      end

    lemma size_of_size_app_right
      { n : ℕ } { t u : pre_term } : (sizeof (app t u) ≤ n + 1) → (sizeof u ≤ n)
    :=
      begin
        intro,
        apply nat.le_of_succ_le_succ,
        calc
          sizeof u + 1
              ≤ sizeof u + 1 + sizeof t   : nat.le.intro rfl
          ... = sizeof u + (1 + sizeof t) : by apply nat.add_assoc
          ... = 1 + sizeof t + sizeof u   : by apply nat.add_comm
          ... = sizeof (app t u)          : by rw sizeof
          ... ≤ n + 1                      : by assumption,
      end

    lemma size_of_size_lam
      { n : ℕ } { x : α } { t : pre_term }
        : (sizeof (lam x t) ≤ n + 1) → (sizeof t ≤ n)
    :=
      begin
        intro,
        apply nat.le_of_succ_le_succ,
        calc
          sizeof t + 1
              = 1 + sizeof t : by apply nat.add_comm
          ... = sizeof (lam x t) : by rw sizeof
          ... ≤ n + 1 : by assumption,
      end

  end

  section

    parameters { α : Type u } [denumerable α] { αs : finset α }

    private def incl : α ↪ ℕ
      :=
        function.embedding.mk encodable.encode encodable.encode_injective

    private def codes : finset ℕ
      :=
        finset.map incl αs
    
    private def fresh_code : ℕ 
      := 
        match codes.max with
        | none :=  0
        | some n := (n+1)
        end

    private lemma new_code : ∀ c ∈ codes, c ≠ fresh_code
      :=
        begin
          intros,
          cases (finset.max_of_mem ‹c ∈ codes›) with m,

          have : codes.max = some m, 
            from ‹m ∈ codes.max›,

          have : fresh_code = m + 1, by {
            rw [fresh_code, ‹codes.max = some m›],
            refl,
          },

          have : c < fresh_code,
            by calc
              c    ≤ m
                      : by { apply finset.le_max_of_mem, repeat {assumption} }
               ... < m + 1
                      : by { apply nat.lt_succ_self }
               ... = fresh_code
                      : by { symmetry, from ‹fresh_code = m + 1› },

          apply ne_of_lt ‹c < fresh_code›,
          done,
        end

    #print axioms finset.max_of_mem
    #print axioms new_code

    private lemma decode_in_codes
        { n : ℕ } : ((denumerable.of_nat α n) ∈ αs) → (n ∈ codes)
      := 
        begin
          intros,
          rw [codes, ←denumerable.encode_of_nat n],
          apply finset.mem_map_of_mem incl ‹denumerable.of_nat α n ∈ αs›,
          done
        end

    #print axioms decode_in_codes

    -- Now make αs an explicit parameter
    parameter ( αs )

    def fresh_var : α
      := 
        denumerable.of_nat α fresh_code

    lemma freshness : fresh_var ∉ αs
      :=
        begin
          -- Proof by contradition
          assume : (fresh_var αs) ∈ αs,
          have : fresh_code ≠ fresh_code,
            by {
              apply new_code fresh_code,
                -- suffices to show fresh_code ∈ codes
              apply decode_in_codes,
                -- suffices to show denumerable.of_nat α (fresh_code) ∈ αs
              rw ←fresh_var,
                -- suffices to show fresh_var ∈ αs
              assumption,
                -- which holds by assumption
            },
          -- contradiction,
          from ne.irrefl this,
          done,
        end

    #print axioms freshness

  end

  #check freshness
  #print freshness

  section

    parameter { α : Type u }

    parameters -- type classes
      [has_emptyc (finset α)]
      [has_union (finset α)]
      [has_sdiff (finset α)]
      [has_union (multiset α)]

    open pre_term

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

    parameters -- type classes
      [decidable_eq α]
      [denumerable α]

    open pre_term

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
          show sizeof (var y) = sizeof (var t),
            by unfold sizeof,
          show sizeof (var t) = sizeof (var t),
            by unfold sizeof,
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

    lemma rename_footprint
      { x y : α } { t : pre_term } : 
        (free_vars t \ {x}) = (free_vars (rename x y t) \ {y})
    :=
      begin
        sorry
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

  end

  namespace equiv

    namespace alpha

      section

        parameter { α : Type u }

        parameters [denumerable α] [decidable_eq α]

        open pre_term

        def equiv : @pre_term α → @pre_term α → Prop
          | (var x) (var y) :=
            x = y
          | (app t₁ u₁) (app t₂ u₂) :=
            (equiv t₁ t₂) ∧ (equiv u₁ u₂)
          | (lam x t) (lam y u) := 
            ∀ z ∉ (free_vars t \ { x }) ∪ (free_vars u \ { y }),
              have sizeof (rename x z t) < 1 + sizeof t, 
                by calc
                  sizeof (rename x z t)
                      = sizeof t       : by apply rename_nonincreasing
                  ... < (sizeof t) + 1 : by apply nat.lt.base
                  ... = 1 + (sizeof t) : by apply nat.add_comm,
              equiv (rename x z t) (rename y z u)
          | _ _ :=
            false

        local notation t ` ≅ ` u := equiv t u

        lemma preserves_fv :
          ∀ { t u : pre_term }, (t ≅ u) → free_vars t = free_vars u
        :=
          let aux
            { n : ℕ } :
              ∀ { t u : pre_term } { _ : sizeof t ≤ n} { _ : sizeof u ≤ n },
                (t ≅ u) → free_vars t = free_vars u
            :=
              begin
                induction n with m IH,
                case nat.zero {
                  intros,
                  cases t with x,
                  case var {
                    cases u with y,
                    case var { 
                      rw equiv at *,
                      unfold free_vars, 
                      rwa finset.singleton_inj,
                    },
                    case app { exfalso, from size_pos_app ‹sizeof (app _ _) ≤ 0› },
                    case lam { exfalso, from size_pos_lam ‹sizeof (lam _ _) ≤ 0› },
                  },
                  case app { exfalso, from size_pos_app ‹sizeof (app _ _) ≤ 0› },
                  case lam { exfalso, from size_pos_lam ‹sizeof (lam _ _) ≤ 0› },
                },
                case nat.succ {
                  assume t u : pre_term,
                  assume : sizeof t ≤ m + 1, assume : sizeof u ≤ m + 1,
                  assume equiv_t_u : equiv t u,
                  cases t with _ t₁ t₂ x t',
                  case var {
                    cases u with y,
                    case var { 
                      rw equiv at *,
                      unfold free_vars,
                      rwa finset.singleton_inj,
                    },
                    case app { rw equiv at *, contradiction, },
                    case lam { rw equiv at *, contradiction, },
                  },
                  case app { 
                    cases u with _ u₁ u₂,
                    case app {
                      rw equiv at *,
                      unfold free_vars,
                      rw (show free_vars t₁ = free_vars u₁, by { apply IH, 
                            show equiv t₁ u₁,
                              by { apply and.elim_left, assumption },
                            show sizeof t₁ ≤ m,
                              by {apply size_of_size_app_left, assumption},
                            show sizeof u₁ ≤ m,
                              by {apply size_of_size_app_left, assumption},
                          }
                        ),
                      rw (show free_vars t₂ = free_vars u₂, by { apply IH, 
                            show equiv t₂ u₂,
                              by { apply and.elim_right, assumption },
                            show sizeof t₂ ≤ m,
                              by {apply size_of_size_app_right, assumption},
                            show sizeof u₂ ≤ m,
                              by {apply size_of_size_app_right, assumption},
                          }
                        ),
                    },
                    case var { rw equiv at *, contradiction, },
                    case lam { rw equiv at *, contradiction, },
                  },
                  case lam { 
                    cases u with _ _ _ y u',
                    case lam {
                      rw equiv at *,
                      unfold free_vars,
                      let z := fresh_var (free_vars t' \ {x} ∪ free_vars u' \ {y}),
                      change free_vars t' \ {x} = free_vars u' \ {y},
                      rw @rename_footprint α ‹decidable_eq α› ‹denumerable α› x z t',
                      rw @rename_footprint α ‹decidable_eq α› ‹denumerable α› y z u',
                      refine congr_fun (congr_arg _ _) _,
                      apply IH,
                        show equiv (rename x z t') (rename y z u'),
                          from
                            equiv_t_u z
                              (freshness (free_vars t' \ {x} ∪ free_vars u' \ {y})),
                        show sizeof (rename x z t') ≤ m,
                          by {rw rename_nonincreasing, apply size_of_size_lam, assumption},
                        show sizeof (rename y z u') ≤ m,
                          by {rw rename_nonincreasing, apply size_of_size_lam, assumption},
                    },
                    case var { rw equiv at *, contradiction, },
                    case app { rw equiv at *, contradiction, },
                  },
                },
                done
              end in
          begin
            intros,
            apply aux ‹equiv t u›,
              show sizeof t ≤ max (sizeof t) (sizeof u),
                by { apply le_max_left },
              show sizeof u ≤ max (sizeof t) (sizeof u),
                by { apply le_max_right },
            done
          end

        -- α-equivalence really is an equivalence relation

        lemma refl : ∀ (t : pre_term), t ≅ t
          :=
            let aux { n : ℕ } : ∀  { t : pre_term }, sizeof t ≤ n → (t ≅ t)
              :=
                begin
                  induction n with m IH,
                  case nat.zero {
                    intros,
                    cases t with x u₁ u₂ x u,
                    case var { rw equiv },
                    case app { exfalso, 
                      from size_pos_app ‹sizeof (app u₁ u₂) ≤ 0› },
                    case lam { exfalso, 
                      from size_pos_lam ‹sizeof (lam x u) ≤ 0› },
                  },
                  case nat.succ {
                    intros,
                    cases t with x u₁ u₂ x u,
                    case var { rw equiv },
                    case app {
                      rw equiv,
                      split,
                      show equiv u₁ u₁, by { apply IH,
                          apply size_of_size_app_left,
                          assumption,
                        },
                      show equiv u₂ u₂, by { apply IH,
                          apply size_of_size_app_right,
                          assumption,
                        },
                    },
                    case lam {
                      rw equiv,
                      rw finset.union_idempotent,
                      assume z ∉ free_vars u \ {x},
                      apply IH,
                      apply @size_of_size_lam α m x,
                      rw sizeof at *,
                      rwa rename_nonincreasing,
                    },
                  },
                  done,
                end
            in begin
              assume t : pre_term,
              suffices : sizeof t ≤ sizeof t,
                { from aux this },
              show sizeof t ≤ sizeof t, by refl,
              done
            end

        lemma symm : ∀ (t u : pre_term), (t ≅ u) → (u ≅ t)
          :=
            let aux
              { n : ℕ } : 
                ∀ { t u : pre_term } { _ : sizeof t ≤ n } { _ : sizeof u ≤ n },
                  (t ≅ u) → (u ≅ t)
              :=
                begin
                  induction n with m IH,
                  case nat.zero {
                    intros,
                    cases t with x,
                    case var {
                      cases u with y,
                      case var { rw equiv at *, symmetry, assumption },
                      case app { exfalso, from size_pos_app ‹sizeof (app _ _) ≤ 0› },
                      case lam { exfalso, from size_pos_lam ‹sizeof (lam _ _) ≤ 0› },
                    },
                    case app { exfalso, from size_pos_app ‹sizeof (app _ _) ≤ 0› },
                    case lam { exfalso, from size_pos_lam ‹sizeof (lam _ _) ≤ 0› },
                  },
                  case nat.succ {
                    intros,
                    cases t with _ t₁ t₂ x t',
                    case var {
                      cases u,
                      case var { rw equiv at *, symmetry, assumption },
                      all_goals { rwa equiv at * },
                    },
                    case app {
                      cases u with _ u₁ u₂,
                      case app { 
                        rw equiv at *,
                        split,
                        show equiv u₁ t₁, by { apply IH,
                            show equiv t₁ u₁,
                              by {apply and.elim_left, assumption},
                            show sizeof t₁ ≤ m,
                              by {apply size_of_size_app_left, assumption},
                            show sizeof u₁ ≤ m,
                              by {apply size_of_size_app_left, assumption},
                          },
                        show equiv u₂ t₂, by { apply IH,
                            show equiv t₂ u₂, by {apply and.elim_right, assumption},
                            show sizeof t₂ ≤ m, by {apply size_of_size_app_right, assumption},
                            show sizeof u₂ ≤ m, by {apply size_of_size_app_right, assumption},
                          },
                        },
                      all_goals { rwa equiv at * },
                    },
                    case lam {
                      cases u with _ _ _ y u',
                      case lam {
                        rw equiv at *,
                        assume z ∉ free_vars u' \ {y} ∪ free_vars t' \ {x},
                        apply IH,
                          show equiv (rename x z t') (rename y z u'),
                            from
                              ‹∀ z ∉ free_vars t' \ {x} ∪ free_vars u' \ {y},
                                  equiv
                                    (@rename α ‹decidable_eq α› ‹denumerable α› x z t')
                                    (rename y z u')› z
                              (show z ∉ free_vars t' \ {x} ∪ free_vars u' \ {y},
                                by rwa finset.union_comm),
                          all_goals {
                              rw rename_nonincreasing, 
                              apply size_of_size_lam,
                              assumption,
                            },
                      },
                      all_goals { rwa equiv at * },
                    },
                  },
                  done,
                end
            in begin
              intros,
              apply aux ‹equiv t u›,
                show sizeof t ≤ max (sizeof t) (sizeof u),
                  by { apply le_max_left },
                show sizeof u ≤ max (sizeof t) (sizeof u),
                  by { apply le_max_right },
              done
            end

        lemma trans : ∀ (t u v : pre_term), (t ≅ u) → (u ≅ v) → (t ≅ v)
          :=
            let aux
              { n : ℕ } : 
                ∀ { t u v : pre_term } 
                    { _ : sizeof t ≤ n } { _ : sizeof u ≤ n } { _ : sizeof v ≤ n },
                      (t ≅ u) → (u ≅ v) → (t ≅ v)
              :=
                begin
                  induction n with m IH,
                  case nat.zero {
                    intros,
                    cases t with x,
                    case var {
                      cases u with y,
                      case var {
                        cases v with z,
                        case var {
                          rw equiv at *,
                          apply eq.trans,
                            show x = y, by assumption,
                            show y = z, by assumption,
                        },
                        all_goals { rw equiv at *, contradiction, },
                      },
                      all_goals { rw equiv at *, contradiction, },
                    },
                    case app { exfalso,
                      from size_pos_app ‹sizeof (app _ _ ) ≤ 0› },
                    case lam { exfalso,
                      from size_pos_lam ‹sizeof (lam _ _ ) ≤ 0› },
                  },
                  case nat.succ {
                    intros,
                    cases t with x t₁ t₂ x t',
                    case var {
                      cases u with y,
                      case var {
                        cases v with z,
                        case var {
                          rw equiv at *,
                          apply eq.trans,
                            show x = y, by assumption,
                            show y = z, by assumption,
                        },
                        all_goals { rw equiv at *, contradiction, },
                      },
                      all_goals { rw equiv at *, contradiction, },
                    },
                    case app { 
                      cases u with _ u₁ u₂,
                      case app {
                        cases v with _ v₁ v₂,
                        case app {
                          rw equiv at *,
                          split,
                          show equiv t₁ v₁, by { apply IH,
                              show equiv t₁ u₁,
                                by { apply and.elim_left, assumption },
                              show equiv u₁ v₁,
                                by { apply and.elim_left, assumption },
                              show sizeof t₁ ≤ m,
                                by {apply size_of_size_app_left, assumption},
                              show sizeof u₁ ≤ m,
                                by {apply size_of_size_app_left, assumption},
                              show sizeof v₁ ≤ m,
                                by {apply size_of_size_app_left, assumption},
                            },
                          show equiv t₂ v₂, by { apply IH,
                              show equiv t₂ u₂,
                                by { apply and.elim_right, assumption },
                              show equiv u₂ v₂,
                                by { apply and.elim_right, assumption },
                              show sizeof t₂ ≤ m,
                                by {apply size_of_size_app_right, assumption},
                              show sizeof u₂ ≤ m,
                                by {apply size_of_size_app_right, assumption},
                              show sizeof v₂ ≤ m,
                                by {apply size_of_size_app_right, assumption},
                            },
                        },
                        all_goals { rw equiv at *, contradiction, },
                      },
                      all_goals { rw equiv at *, contradiction, },
                    },
                    case lam { 
                      cases u with _ _ _ y u',
                      case lam {
                        cases v with _ _ _ z v',
                        case lam {
                          -- TODO : find a better way to present this
                          have equiv_t_u : free_vars (lam x t') = free_vars (lam y u'),
                            from preserves_fv ‹equiv (lam x t') (lam y u')›,
                          have equiv_u_v : free_vars (lam y u') = free_vars (lam z v'),
                            from preserves_fv ‹equiv (lam y u') (lam z v')›,
                          rw equiv at *,
                          assume w ∉ free_vars t' \ {x} ∪ free_vars v' \ {z},
                          apply IH,
                          have : w ∉ free_vars t' \ {x} ∪ free_vars u' \ {y},
                            by rwa 
                              (show free_vars u' \ {y} = free_vars v' \ {z},
                                by {unfold free_vars at equiv_u_v, assumption,}),
                          show equiv (rename x w t') (rename y w u'),
                            from 
                              ‹∀ (w : α),
                                w ∉ free_vars t' \ {x} ∪ free_vars u' \ {y} → 
                                equiv (rename x w t') (rename y w u')›
                              w this,
                          have : w ∉ free_vars u' \ {y} ∪ free_vars v' \ {z},
                            by rwa← 
                              (show free_vars t' \ {x} = free_vars u' \ {y},
                                by {unfold free_vars at equiv_t_u, assumption,}),
                          show equiv (rename y w u') (rename z w v'),
                            from 
                              ‹∀ (w : α),
                                w ∉ free_vars u' \ {y} ∪ free_vars v' \ {z} → 
                                equiv (rename y w u') (rename z w v')›
                              w this,
                          all_goals {
                              rw rename_nonincreasing, 
                              apply size_of_size_lam,
                              assumption,
                            },
                        },
                        all_goals { rw equiv at *, contradiction, },
                      },
                      all_goals { rw equiv at *, contradiction, },
                    },
                  },
                  done
                end
            in begin
              intros,
              apply aux ‹equiv t u› ‹equiv u v›,
                show sizeof t ≤ max (max (sizeof t) (sizeof u)) (sizeof v),
                  by {apply le_max_left_of_le, apply le_max_left},
                show sizeof u ≤ max (max (sizeof t) (sizeof u)) (sizeof v),
                  by {apply le_max_left_of_le, apply le_max_right},
                show sizeof v ≤ max (max (sizeof t) (sizeof u)) (sizeof v), 
                  by apply le_max_right,
              done
            end

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

      end

    end alpha

  end equiv

  -- The type of (α-equivalence classes of) Λ-terms
  def term
    { α : Type u } [denumerable α] [decidable_eq α]
      := @quot (@pre_term α) equiv.alpha.equiv

  open pre_term

  -- notation `_` x `_` := var x
  -- notation `λ` x `.` t := lam x t
  -- notation t `⬝` u := app t u

  -- The identity function λx.x
  def id : pre_term := (lam "x" (var "x"))
  -- example : pre_term := λ "x" . (_ "x" _)

end lambda