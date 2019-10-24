universe u

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
      calc
        set.insert x (set.insert y s)
              = { a | a = x ∨ a ∈ (set.insert y s)}
                  : by rw set.insert
          ... = { a | a = x ∨ a ∈ { b | b = y ∨ b ∈ s}}
                  : by rw set.insert
          ... = { a | a = x ∨ a = y ∨ a ∈ s }
                  : by congr
          ... = { a | a = y ∨ a = x ∨ a ∈ s }
                  : by {congr, funext, from propext or.left_comm}
          -- For some reason, Lean fills in the rest, and it is incorrect to
          --   try and fill it in ourselves.
          -- ... = { a | a = y ∨ a ∈ { b | b = x ∨ b ∈ s}}
          --         : by congr
          -- ... = { a | a = y ∨ a ∈ (set.insert x s)}
          --         : by rw set.insert
          -- ... = set.insert y (set.insert x s)
          --         : by rw set.insert
  -- 'Explicit' proof of set_swap
  example
    {s : set α} {x y : α}
      : set.insert x (set.insert y s) = set.insert y (set.insert x s)
  :=
    begin
      have : set.insert x (set.insert y s) = { a | a = x ∨ a ∈ (set.insert y s) },
        by rw set.insert,
      have _1: set.insert x (set.insert y s) = { a | a = x ∨ a = y ∨ a ∈ s },
        by {rw set.insert, from this},
      have : set.insert y (set.insert x s) = { a | a = y ∨ a ∈ (set.insert x s) },
        by rw set.insert,
      have : set.insert y (set.insert x s) = { a | a = y ∨ a = x ∨ a ∈ s },
        by {rw set.insert, from this},
      have _2 : { a | a = y ∨ a = x ∨ a ∈ s } = set.insert y (set.insert x s),
        from eq.symm this,
      have : { a | a = x ∨ a = y ∨ a ∈ s } = { a | a = y ∨ a = x ∨ a ∈ s },
        by {congr, funext, from propext or.left_comm},
      -- Here, we can just use
      --   show set.insert x (set.insert y s) = set.insert y (set.insert x s),
      --     from eq.trans _1 this,
      -- But is it sufficiently clear how Lean fills in the following steps?
      have : set.insert x (set.insert y s) = { a | a = y ∨ a = x ∨ a ∈ s },
        from eq.trans _1 this,
      show set.insert x (set.insert y s) = set.insert y (set.insert x s),
        from eq.trans this _2,
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

end

section

  parameters (α : Type u) (a₁ a₂ : α) (b₁ b₂ : α)

  def pair (x y : α) : set (set α) := {{x}, {x, y}}

  def A := pair a₁ a₂
  def B := pair b₁ b₂

  theorem adequacy :
    A = B → a₁ = b₁ ∧ a₂ = b₂
  :=
    begin
      intro,
      have : A = {{a₁}, {a₁, a₂}}, by rw [A, pair],
      have : A = set.insert {a₁, a₂} {{a₁}}, by {rw set.insert, from this},
      -- { s | s = {a₁} ∨ s ∈ {{a₁, a₂}}}, by {rw set.insert, from this}
      -- assume : ({{a₁}, {a₁, a₂}} : set (set α)) = {{b₁},{b₁,b₂}},
      -- let A : set (set α) := {{a₁}, {a₁, a₂}} in
      -- let B : set (set α) := {{b₁}, {b₁, b₂}} in
      -- have ({ a₁ } : set α) ∈ A 

      sorry
    end


end