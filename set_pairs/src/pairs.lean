open set

universe u

section

  parameters (α : Type u) (x y : α)

  theorem mem_insert
    (s : set α) : set.mem x (set.insert x s)
  := 
    begin
      -- change (set.mem x ({ a | a = x ∨ a ∈ s})),
      -- change (({ a | a = x ∨ a ∈ s}) x),
      -- change (x = x ∨ x ∈ s),
      left,
      refl,
      done
    end

  -- an alternative (more natural/readable?) proof of mem_insert
  example
    (s : set α) : set.mem x (set.insert x s)
  :=
    begin
      have : x = x, by trivial, -- specifically, by refl
      have : x = x ∨ x ∈ s, by {left, from this}, 
                                --from or.intro_left (x ∈ s) this,
      -- have : ({ a | a = x ∨ a ∈ s}) x, from this,
      -- have : set.mem x ({ a | a = x ∨ a ∈ s }), from this,
      show set.mem x ({ a | a = x ∨ a ∈ s }), from this,
      -- show set.mem x (set.insert x s), from this,
      done
    end

  theorem singleton_set_mem :
    x ∈ ({ x } : set α)
  :=
    begin
      -- change (set.mem x (set.insert x ∅)),
      apply mem_insert,
      done
    end    
  -- Forward proof of singleton_set_mem
  example :
    x ∈ ({ x } : set α)
  :=
    begin
      have : set.mem x (set.insert x ∅), by apply mem_insert,
      show set.mem x ({ x }), from this,
      done
    end
  example :
    x ∈ ({ x } : set α)
  :=
    by apply mem_insert


  theorem set_swap
    (s : set α) (x y : α) : set.insert x (set.insert y s) = set.insert y (set.insert x s)
  :=
    calc
      { a | a = x ∨ a = y ∨ a ∈ s } = { a | a = y ∨ a = x ∨ a ∈ s }
        : by {congr, funext, from propext or.left_comm}
      -- calc
      --   set.insert x (set.insert y s)
      --         = { a | a = x ∨ a ∈ (set.insert y s)}
      --             : by rw set.insert
      --     ... = { a | a = x ∨ a ∈ { b | b = y ∨ b ∈ s}}
      --             : by rw set.insert
      --     ... = { a | a = x ∨ a = y ∨ a ∈ s }
      --             : by congr
      --     ... = { a | a = y ∨ a = x ∨ a ∈ s }
      --             : by {congr, funext, from propext or.left_comm}
      --     -- ... = { a | a = y ∨ a ∈ { b | b = x ∨ b ∈ s}}
      --     --         : by congr
      --     -- ... = { a | a = y ∨ a ∈ (set.insert x s)}
      --     --         : by rw set.insert
      --     -- ... = set.insert y (set.insert x s)
      --     --         : by rw set.insert

  example :
    ({x, y} : set α) = set.insert x {y}
  :=
    by apply set_swap

end

section

  parameters (α : Type u) (a₁ a₂ : α) (b₁ b₂ : α)

  def A := ({{a₁}, {a₁, a₂}} : set (set α))
  def B := ({{b₁}, {b₁,b₂}} : set (set α))

  #check ({a₁, a₂} : set α)

  example :
    A = B → a₁ = b₁ ∧ a₂ = b₂
  :=
    begin
      intro hyp,
      have : A = {{a₁}, {a₁, a₂}}, by rw A,
      have : A = set.insert {a₁, a₂} {{a₁}}, by {rw set.insert, from this},
      -- { s | s = {a₁} ∨ s ∈ {{a₁, a₂}}}, by {rw set.insert, from this}
      -- assume : ({{a₁}, {a₁, a₂}} : set (set α)) = {{b₁},{b₁,b₂}},
      -- let A : set (set α) := {{a₁}, {a₁, a₂}} in
      -- let B : set (set α) := {{b₁}, {b₁, b₂}} in
      -- have ({ a₁ } : set α) ∈ A 

      sorry
    end


end