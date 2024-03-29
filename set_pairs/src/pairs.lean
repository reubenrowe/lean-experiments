universe u

namespace or

  section
    
    parameters { p q r : Prop }

    lemma right_neutral
      {p : Prop} : p ∨ false ↔ p
    :=
      begin
        split,
        show p → p ∨ false, from or.intro_left false,
        show p ∨ false → p, by {
          assume : p ∨ false,
          cases this,
            case or.inl {from ‹p›},
            case or.inr {by {exfalso, assumption}}
        },
        done
      end

    lemma idempotent
      { p : Prop } : p ∨ p ↔ p
    := 
      begin
        split,
        show p → p ∨ p, by {assume : p, from or.inl ‹p›},
        show p ∨ p → p, 
          by {
            assume : p ∨ p, 
            cases this,
              case or.inl {from ‹p›},
              case or.inr {from ‹p›}
          },
          done
      end

    lemma equiv_left
      { p q r : Prop } : (p ↔ q) → (p ∨ r ↔ q ∨ r)
    :=
      begin
        assume : p ↔ q,
        split,
        show p ∨ r → q ∨ r,
          by {
            assume : p ∨ r,
            cases this,
              case or.inl {from or.inl (iff.elim_left ‹p ↔ q› ‹p›)},
              case or.inr {from or.inr ‹r›},
          },
        show q ∨ r → p ∨ r,
          by {
            assume : q ∨ r,
            cases this,
              case or.inl {from or.inl (iff.elim_right ‹p ↔ q› ‹q›)},
              case or.inr {from or.inr ‹r›},
          },
        done
      end

  end

end or

section

  parameters (α : Type u) (x y : α)

  theorem mem_insert
    {s : set α} : set.mem x (set.insert x s)
  := 
    begin
      -- change (set.mem x ({ a | a = x ∨ a ∈ s})),
      -- change (({ a | a = x ∨ a ∈ s}) x),
      -- change (x = x ∨ x ∈ s),
      -- Lean gets here by itself
      left,
      refl,
      done
    end
  -- an alternative (more natural/readable?) proof of mem_insert
  example
    {s : set α} : set.mem x (set.insert x s)
  :=
    begin
      have : x = x, by trivial, -- specifically, by refl
      have : x = x ∨ x ∈ s, by {left, from this}, 
                                --from or.intro_left (x ∈ s) this,
      -- have : ({ a | a = x ∨ a ∈ s}) x, from this,
      -- have : set.mem x ({ a | a = x ∨ a ∈ s }), from this,
      -- Lean doesn't need these intermediate steps
      show set.mem x ({ a | a = x ∨ a ∈ s }), from this,
      -- show set.mem x (set.insert x s), from this,
      done
    end

  theorem singleton_set_mem :
    x ∈ ({ x } : set α)
  :=
    begin
      -- change (set.mem x (set.insert x ∅)),
      -- Lean automatically translates the notation x ∈ { x }
      apply mem_insert,
      done
    end
  -- So, it is just an application of mem_insert
  example :
    x ∈ ({ x } : set α)
  :=
    by apply mem_insert
  -- Forward proof of singleton_set_mem
  example :
    x ∈ ({ x } : set α)
  :=
    begin
      have : set.mem x (set.insert x ∅), by apply mem_insert,
      show set.mem x ({ x }), from this,
      done
    end

  theorem set_swap
    {s : set α} {x y : α}
      : set.insert x (set.insert y s) = set.insert y (set.insert x s)
  :=
    calc
      { a | a = x ∨ a = y ∨ a ∈ s } = { a | a = y ∨ a = x ∨ a ∈ s }
        : by {congr, funext, from propext or.left_comm}
  -- Trying to do a more explicit calculational proof
  example
    {s : set α} {x y : α}
      : set.insert x (set.insert y s) = set.insert y (set.insert x s)
  :=
      -- Note, refl is the tactic that checks definitional equality
      calc
        set.insert x (set.insert y s)
          -- Don't need these intermediate steps
          --     = { a | a = x ∨ a ∈ (set.insert y s)}
          --         : by refl
          -- ... = { a | a = x ∨ a ∈ { b | b = y ∨ b ∈ s}}
          --         : by refl
          -- ... 
              = { a | a = x ∨ a = y ∨ a ∈ s }
                  : by refl

          -- The key step
          ... = { a | a = y ∨ a = x ∨ a ∈ s }
                -- This is really set_of (λ a, a = y ∨ a = x ∨ a ∈ s)
                  : by {congr, funext, from propext or.left_comm}

          -- Again, we don't need these intermediate steps
          -- ... = { a | a = y ∨ a ∈ { b | b = x ∨ b ∈ s}}
          --         : by refl
          -- ... = { a | a = y ∨ a ∈ (set.insert x s)}
          --         : by refl

          -- And Lean can even fill in the second half of the calculation
          -- automatically.
          ... = set.insert y (set.insert x s)
                  : by refl
  -- 'Explicit' proof of set_swap
  example
    {s : set α} {x y : α}
      : set.insert x (set.insert y s) = set.insert y (set.insert x s)
  :=
    begin
      have _1 : set.insert x (set.insert y s) = { a | a = x ∨ a = y ∨ a ∈ s },
        by refl,
      have _2 : { a | a = y ∨ a = x ∨ a ∈ s } = set.insert y (set.insert x s),
        by refl,
      have _3 : { a | a = x ∨ a = y ∨ a ∈ s } = { a | a = y ∨ a = x ∨ a ∈ s },
        by {congr, funext, from propext or.left_comm},

      -- Here, we can just tell Lean to use facts in the context, and it
      -- fills in the necessary chaining of equalities:

      -- show set.insert x (set.insert y s) = set.insert y (set.insert x s),
      --   by {assumption},

      -- We can also use the tactic language to manipulate the goal and
      -- apply facts one at a time:

      -- show set.insert x (set.insert y s) = set.insert y (set.insert x s),
      --   by {transitivity, assumption, transitivity, exact this, assumption},

      -- But although this makes it clear which reasoning principles are being
      -- used, it isn't at all obvious how these are applied.

      -- Maybe this is better?:
      show set.insert x (set.insert y s) = set.insert y (set.insert x s),
        -- from eq.trans (eq.trans _1 _3) _2,
        from eq.trans 
              (eq.trans
                ‹set.insert x (set.insert y s) = { a | a = x ∨ a = y ∨ a ∈ s }›
                ‹{ a | a = x ∨ a = y ∨ a ∈ s } = { a | a = y ∨ a = x ∨ a ∈ s }›)
                ‹{ a | a = y ∨ a = x ∨ a ∈ s } = set.insert y (set.insert x s)›,

      done
    end

  -- The set notation { x₁, ..., xₙ } is short-hand for
  --   fold_left set.insert ∅ [x₁, ..., xₙ]
  -- So, {x, y} = fold_left set.insert ∅ [x, y] = set.insert y (set.insert x ∅)
  example :
    ({x, y} : set α) = set.insert x {y}
  :=
    by apply set_swap

  theorem set_eq_iff_subsets
    {s₁ s₂ : set α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁
  :=
    begin
      split, -- split bi-implication into individual implications

      -- show left-to-right
      show s₁ = s₂ → s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, by {
        assume : s₁ = s₂,
        split, -- show the two conjuncts individually

        show s₁ ⊆ s₂,
        suffices : ∀ x, x ∈ s₁ → x ∈ s₂, from this, by {
          intros,
          show x ∈ s₂, from eq.subst ‹s₁ = s₂› ‹x ∈ s₁›,
        },

        show s₂ ⊆ s₁,
        suffices : ∀ x, x ∈ s₂ → x ∈ s₁, from this, by {
          intros,
          show x ∈ s₁, from eq.subst (eq.symm ‹s₁ = s₂›) ‹x ∈ s₂›,
        },

        done
      },

      -- show right-to-left
      show s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ → s₁ = s₂, by {
        assume : s₁ ⊆ s₂ ∧ s₂ ⊆ s₁,
        have : s₁ ⊆ s₂, from and.left ‹s₁ ⊆ s₂ ∧ s₂ ⊆ s₁›,
        have : s₂ ⊆ s₁, from and.right ‹s₁ ⊆ s₂ ∧ s₂ ⊆ s₁›,

        have : ∀ x, x ∈ s₁ ↔ x ∈ s₂, by {
          assume x,
          split,
          show x ∈ s₁ → x ∈ s₂,
            by {assume : x ∈ s₁, show x ∈ s₂, from ‹s₁ ⊆ s₂› this},
          show x ∈ s₂ → x ∈ s₁,
            by {assume : x ∈ s₂, show x ∈ s₁, from ‹s₂ ⊆ s₁› this},
          done
        },

        show s₁ = s₂,
        suffices : ∀ (x : α), (x ∈ s₁) = (x ∈ s₂),
          from funext this,
        by {
          assume x,
          have : x ∈ s₁ ↔ x ∈ s₂, from ‹∀ x, x ∈ s₁ ↔ x ∈ s₂› x,
          show (x ∈ s₁) = (x ∈ s₂), from propext this,
          done
        },
         
        done
      },

      -- and we are done
      done
    end

  lemma set_eq_imp_subset_left
    {s₁ s₂ : set α} : s₁ = s₂ → s₁ ⊆ s₂
  := 
    λ eq, and.left (iff.elim_left (set_eq_iff_subsets) eq)
  -- Explicit proof
  example
    {s₁ s₂ : set α} : s₁ = s₂ → s₁ ⊆ s₂
  := 
    begin
      intros,
      have : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from set_eq_iff_subsets,
      have : s₁ = s₂ → s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from iff.elim_left this,
      have : s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from this ‹s₁ = s₂›,
      show s₁ ⊆ s₂, from and.elim_left this,
      done
    end

  lemma set_eq_imp_subset_right
    {s₁ s₂ : set α} : s₁ = s₂ → s₂ ⊆ s₁
  := 
    λ eq, and.right (iff.elim_left (set_eq_iff_subsets) eq)
  -- Explicit proof
  example
    {s₁ s₂ : set α} : s₁ = s₂ → s₂ ⊆ s₁
  := 
    begin
      intros,
      have : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from set_eq_iff_subsets,
      have : s₁ = s₂ → s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from iff.elim_left this,
      have : s₁ ⊆ s₂ ∧ s₂ ⊆ s₁, from this ‹s₁ = s₂›,
      show s₂ ⊆ s₁, from and.elim_right this,
      done
    end

  -- s₁ ⊆ s₂ is notation for set.subset s₁ s₂, which is definitionally equal to
  --   ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂
  -- so we can directly derive (a witness for) x ∈ s₂ by passing (a witness for)
  -- x ∈ s₁ to (a witness for) s₁ ⊆ s₂, with Lean automatically instantiating
  -- the universal quantifier
  example
    (s₁ s₂ : set α) (x : α) : s₁ ⊆ s₂ → x ∈ s₁ → x ∈ s₂
  :=
    begin
      intros,
      show x ∈ s₂, from ‹s₁ ⊆ s₂› ‹x ∈ s₁›,
      done
    end
  -- We can make the definition of ⊆ and the instantiation of the universal
  -- quantifier explicit.
  example
    (s₁ s₂ : set α) (x : α) : s₁ ⊆ s₂ → x ∈ s₁ → x ∈ s₂
  :=
    begin
      assume : s₁ ⊆ s₂, assume : x ∈ s₁,
      have : ∀ y, y ∈ s₁ → y ∈ s₂, from ‹s₁ ⊆ s₂›,
      have : x ∈ s₁ → x ∈ s₂, from this x,
      show x ∈ s₂, from this ‹x ∈ s₁›,
      done
    end

  lemma set_eq_imp_mem_preserve
    {s₁ s₂ : set α} {x : α} : s₁ = s₂ → x ∈ s₁ → x ∈ s₂
  :=
    begin
      intros,
      have : s₁ ⊆ s₂, from set_eq_imp_subset_left ‹s₁ = s₂›,
      show x ∈ s₂, from ‹s₁ ⊆ s₂› ‹x ∈ s₁›,
      done
    end

  lemma singleton_set_case_split
    {x y : α} : y ∈ ({x} : set α) → y = x
  :=
    begin
      intros,
      have : { x } = { y | y = x }, by 
        calc
          { x } 
             -- = { y | y = x ∨ y ∈ ∅ } : by refl ...
                = { y | y = x ∨ false }
                    : by refl
            ... = { y | y = x }
                    : by {congr, funext, from propext or.right_neutral},

      have : y ∈ { y | y = x },
        from set_eq_imp_mem_preserve this ‹y ∈ {x}›,
      show y = x, from this,
      done
    end

  lemma two_element_set_case_split
    {x y z : α} : z ∈ ({x, y} : set α) → z = x ∨ z = y
  := 
    begin

      have : {x, y} = { b | b = x ∨ b = y },
        by calc
          {x, y}
            --  = { b | b = y ∨ b = x ∨ b ∈ ∅ } : by refl ... 
                = { b | b = y ∨ b = x ∨ false }  : by refl
            ... = { b | (b = y ∨ b = x) ∨ false }
                    : by {congr, funext, from eq.symm (propext or.assoc)}
            ... = { b | b = y ∨ b = x } 
                    : by {congr, funext, from propext or.right_neutral}
            ... = { b | b = x ∨ b = y}
                    : by {congr, funext, from propext or.comm},

      assume : z ∈ {x, y},

      have : z ∈ { b | b = x ∨ b = y },
        from set_eq_imp_mem_preserve ‹{x, y} = { b | b = x ∨ b = y }› this,

      show z = x ∨ z = y, from this,

      done

    end

  lemma remove_duplicates
    { s : set α } { x : α } : set.insert x (set.insert x s) = set.insert x s
  := 
    by calc
      set.insert x (set.insert x s)
           = { z | z = x ∨ z = x ∨ z ∈ s } : by refl
       ... = { z | (z = x ∨ z = x) ∨ z ∈ s } 
                : by {congr, funext, from eq.symm (propext or.assoc)}
       ... = { z | z = x ∨ z ∈ s }
                : by {congr, funext, from propext (or.equiv_left or.idempotent)}
       ... = set.insert x s : by refl

  lemma duplicate_to_singleton
    { x : α } : {x, x} = ({x} : set α)
  := by apply remove_duplicates

end

section

  parameters (α : Type u) (a₁ a₂ : α) (b₁ b₂ : α)

  -- The set-theoretic encoding of ordered pairs
  def pair (x y : α) : set (set α) := {{x}, {x, y}}

  -- Two arbitrary ordered pairs
  def A := pair a₁ a₂
  def B := pair b₁ b₂

  -- Soundness
  -- If the elements are (pairwise) equal, then the ordered pairs are equal.
  theorem soundness :
    a₁ = b₁ ∧ a₂ = b₂ → A = B
  :=
    begin
      assume : a₁ = b₁ ∧ a₂ = b₂,
      have : a₁ = b₁, by {apply and.elim_left, assumption},
      have : a₂ = b₂, by {apply and.elim_right, assumption},
      calc
        A     = {{a₁}, {a₁, a₂}}
                  : by refl
          ... = {{b₁}, {b₁, b₂}}
                  : by {congr,
                        -- Only need this proposition once
                        from ‹a₂ = b₂›,
                        -- But we need this one twice
                        repeat {from ‹a₁ = b₁›}}
          ... = B : by refl
    end

  -- For adequcy, we will need the following collapsing lemma
  lemma collapse
    { x y : α } : x = y → ({{x}, {x, y}} : set (set α)) = {{y}}
  :=
    begin
      assume : x = y,
      calc
        ({{x}, {x, y}} : set (set α))
              = {{y}, {y, y}} : by {apply eq.subst ‹x = y›, refl}
          ... = set.insert {y, y} ({{y}}) : by refl
          ... = set.insert {y} ({{y}})
                  : (congr_fun 
                      (congr_arg set.insert (duplicate_to_singleton α)))
                      {{y}}
          ... = {{y}, {y}} : by refl
          ... = {{y}} : by apply duplicate_to_singleton,
    end

  -- Adequacy
  -- If the order pairs are equal, then the elements are (pairwise) equal.
  theorem adequacy :
    A = B → a₁ = b₁ ∧ a₂ = b₂
  :=
    begin
      assume : A = B,

      -- It doesn't matter in which order we enumerate the elements of sets
      have : ({{a₁}, {a₁, a₂}} : set (set α)) = {{a₁, a₂}, {a₁}},
        by apply set_swap,
      have : ({{b₁}, {b₁, b₂}} : set (set α)) = {{b₁, b₂}, {b₁}},
        by apply set_swap,
      have : ({a₁, a₂} : set α) = {a₂, a₁},
        by apply set_swap,
      have : ({b₁, b₂} : set α) = {b₂, b₁},
        by apply set_swap,

      -- We derive some basic facts about (the members of) the members of A
      have : A = {{a₁}, {a₁, a₂}}, by refl,

      have : {a₁} ∈ A, by {
        -- since {a₁} ∈ {{a₁, a₂}, {a₁}}, as A = {{a₁, a₂}, {a₁}},
        apply eq.substr 
          (eq.trans ‹A = {{a₁}, {a₁, a₂}}›
                        ‹{{a₁}, {a₁, a₂}} = {{a₁, a₂}, {a₁}}›),
        -- using the mem_insert lemma
        apply mem_insert,
        done
      },

      have : {a₁, a₂} ∈ A, by {
        apply eq.substr ‹A = {{a₁}, {a₁, a₂}}›,
        apply mem_insert,
        done
      },

      have : a₁ ∈ {a₁, a₂}, by {
        apply eq.substr ‹{a₁, a₂} = {a₂, a₁}›,
        apply mem_insert,
        done
      },

        -- We need the set α type ascription here
      have : a₂ ∈ ({a₁, a₂} : set α), by apply mem_insert,

      -- We derive some basic facts about (the members of) the members of B
      have : B = {{b₁}, {b₁, b₂}}, by refl,

      have : {b₁} ∈ B, by {
        -- since {b₁} ∈ {{b₁, b₂}, {b₁}}, as B = {{b₁, b₂}, {b₁}},
        apply eq.substr 
          (eq.trans ‹B = {{b₁}, {b₁, b₂}}›
                        ‹{{b₁}, {b₁, b₂}} = {{b₁, b₂}, {b₁}}›),
        -- using the mem_insert lemma
        apply mem_insert,
        done
      },

      have : {b₁, b₂} ∈ B, by {
        apply eq.substr ‹B = {{b₁}, {b₁, b₂}}›,
        apply mem_insert,
      },

      have : b₁ ∈ {b₁, b₂}, by {
        apply eq.substr ‹{b₁, b₂} = {b₂, b₁}›,
        apply mem_insert,
        done
      },

        -- We need the set α type ascription here
      have : b₂ ∈ ({b₁, b₂} : set α), by apply mem_insert,

      -- Since A = B, A and B are subsets of one another
      have : A ⊆ B, by {apply set_eq_imp_subset_left, from ‹A = B›},
      have : B ⊆ A, by {apply set_eq_imp_subset_right, from ‹A = B›},

      -- Therefore
      have : {a₁} ∈ B, from ‹A ⊆ B› ‹{a₁} ∈ A›,
      have : {a₁} ∈ {{b₁}, {b₁, b₂}},
        by {apply eq.subst ‹B = {{b₁}, {b₁, b₂}}›, from this},

      -- Now there are two possibilities
      cases two_element_set_case_split (set α) this,

      -- the case that {a₁} = {b₁}
      case or.inl {
        have : a₁ ∈ {a₁}, by apply singleton_set_mem,
        have : a₁ ∈ ({b₁} : set α), 
          by {apply set_eq_imp_mem_preserve α ‹{a₁} = {b₁}›, from this},
        have : a₁ = b₁, by {apply singleton_set_case_split, from this},

        -- We have to show both a₁ = b₁ and a₂ = b₂
        split,
        -- We already have the left-hand conjunct
        show a₁ = b₁, from this,

        have : {a₁, a₂} ∈ {{b₁}, {b₁, b₂}},
          by {apply eq.subst ‹B = {{b₁}, {b₁, b₂}}›,
                from ‹A ⊆ B› ‹{a₁, a₂} ∈ A›},

        cases two_element_set_case_split (set α) this,

        -- The case that {a₁, a₂} = {b₁}
        case or.inl {
          have : a₂ = b₁, 
            by {
              apply singleton_set_case_split,
              apply set_eq_imp_mem_preserve α ‹{a₁, a₂} = {b₁}›,
              from ‹a₂ ∈ {a₁, a₂}›
            },
          have : a₁ = a₂, from eq.trans ‹a₁ = b₁› (eq.symm this),
          have : A = {{a₂}},
            by calc
              A     = {{a₁}, {a₁, a₂}} : by refl
                ... = {{a₂}} : by {apply collapse, from this},
          have : {b₁, b₂} = {a₂},
            by {
              -- since {b₁, b₂} ∈ {{a₂}}
              apply singleton_set_case_split,
              -- since A = {{a₂}}
              apply eq.subst this,
              -- and {b₁, b₂} ∈ B and B ⊆ A
              from ‹B ⊆ A› ‹{b₁, b₂} ∈ B›,
            },
          have : b₂ = a₂,
            by {
              -- since b₂ in {a₂}
              apply singleton_set_case_split,
              -- since we have just shown {b₁, b₂} = {a₂}
              apply set_eq_imp_mem_preserve α this,
              -- and also we have that b₂ ∈ {b₁, b₂}
              from ‹b₂ ∈ {b₁, b₂}›
            },
          -- Thus we have the right-hand conjunct
          show a₂ = b₂, by {symmetry, from this},
          done
        },

        -- The case that {a₁, a₂} = {b₁, b₂}
        case or.inr {
          have : {b₁, b₂} = {a₁, a₂}, by {symmetry, from ‹{a₁, a₂} = {b₁, b₂}›},
          have : b₂ ∈ {a₁, a₂},
            by {apply set_eq_imp_mem_preserve, from this, from ‹b₂ ∈ {b₁, b₂}›},
          -- Now, again, we have two further cases
          cases two_element_set_case_split α this,
            -- The case that b₂ = a₁
            case or.inl {
              have : b₁ = b₂,
                from eq.trans (eq.symm ‹a₁ = b₁›) (eq.symm ‹b₂ = a₁›),
              have : {a₁, a₂} = {b₂},
                by calc
                  {a₁, a₂} = {b₁, b₂} : by assumption
                       ... = {b₂, b₂} : by {apply eq.subst ‹b₁ = b₂›, refl}
                       ... = {b₂}     : by {apply remove_duplicates},
              -- Therefore, we can show the right-hand conjunct
              show a₂ = b₂,
                by {
                  -- since a₂ ∈ {b₂}
                  apply singleton_set_case_split,
                  -- since we have just show that {a₁, a₂} = {b₂}
                  apply set_eq_imp_mem_preserve α this,
                  -- and also we have a₂ ∈ {a₁, a₂}
                  from ‹a₂ ∈ {a₁, a₂}›,
                },
                done
            },
            -- The case that b₂ = a₂
            case or.inr {
              -- immediate
              show a₂ = b₂, by {symmetry, from ‹b₂ = a₂›}, done
            },
           done
        },

        done
      },

      -- the case that {a₁} = {b₁, b₂}
      case or.inr {
        have : ({b₁, b₂} : set α) ⊆ {a₁},
          by {apply set_eq_imp_subset_right, from ‹{a₁} = {b₁, b₂}›},
        have : b₁ ∈ {a₁}, 
          by {apply set_eq_imp_subset_left,
              from eq.symm ‹{a₁} = {b₁, b₂}›, from ‹b₁ ∈ {b₁, b₂}›},
        have : b₁ = a₁,
          by {apply singleton_set_case_split, from this},

        -- We have to show both a₁ = b₁ and a₂ = b₂
        split,
        -- We already have the left-hand conjunct
        show a₁ = b₁, by {symmetry, from this},

        -- Now for the right-hand conjunct
        have : b₂ ∈ {a₁},
          by {apply set_eq_imp_subset_left,
              from eq.symm ‹{a₁} = {b₁, b₂}›, from ‹b₂ ∈ {b₁, b₂}›},
        have : a₁ = b₂,
          by {symmetry, apply singleton_set_case_split, from this},
        have : b₁ = b₂, by {transitivity, from ‹b₁ = a₁›, from ‹a₁ = b₂›},
        have : B = {{b₂}},
          by calc
            B     = {{b₁}, {b₁, b₂}} : by refl
              ... = {{b₂}} : by {apply collapse, from this},
        have : {a₁, a₂} ∈ B, 
          by {apply set_eq_imp_mem_preserve, from ‹A = B›, from ‹{a₁, a₂} ∈ A›},
        have : {a₁, a₂} ∈ {{b₂}}, by {apply eq.subst ‹B = {{b₂}}›, from this},
        have : {a₁, a₂} = {b₂}, by {apply singleton_set_case_split, from this},
        have : {a₁, a₂} ⊆ ({b₂} : set α),
          by {apply set_eq_imp_subset_left, from this},
        have : a₂ ∈ {b₂}, from this ‹a₂ ∈ {a₁, a₂}›,

        -- This gives the right-hand conjunct
        show a₂ = b₂, by {apply singleton_set_case_split, from this},
        done
      },

      done

    end

end