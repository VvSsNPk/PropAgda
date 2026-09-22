open import Data.Nat
module Logic-Agda (n : ℕ) where
  open import Data.Fin using (Fin;zero;suc)
  open import Relation.Binary.PropositionalEquality using (_≡_;refl)
  open import Data.Bool using (Bool; false; true ;not) renaming (_∨_ to _or_ ; _∧_ to _and_)

  data Props : Set where
    ⊥ ⊤ : Props
    patom :  Fin n → Props
    ~_ : Props → Props
    _∨_ _∧_ _⇒_ : Props → Props → Props

  _⇔_ : Props → Props → Props
  p ⇔ q = (p ⇒ q) ∧ (q ⇒ p)


  data Cxt : ℕ → Set where
    ø : Cxt ℕ.zero
    _∙_ : {I : ℕ} → Cxt I → Props → Cxt (ℕ.suc I)

  pattern ⟦⟧ = ø
  pattern ⟦_⟧ x = ø ∙ x 
  pattern ⟦_,_⟧ x y = ø ∙ y ∙ x
  pattern ⟦_,_,_⟧ x y z = ø ∙ z ∙ y ∙ x
  pattern ⟦_,_,_,_⟧ x y z k = ø ∙ k ∙ z ∙ y ∙ x
  pattern ⟦_,_,_,_,_⟧ x y z k l = ø ∙ l ∙ k ∙ z ∙ y ∙ x
  pattern ⟦_,_,_,_,_,_⟧ x y z k l m = ø ∙ m ∙ l ∙ k ∙ z ∙ y ∙ x

  
  data _⊢_ : {I : ℕ}(Γ : Cxt I)(ψ : Props) → Set where
    var : ∀{I}{Γ : Cxt I}{ψ}  → Γ ∙ ψ ⊢ ψ
    weaken : ∀{I}{Γ : Cxt I}{ø ψ} → Γ ⊢ ψ
                                -- ­­­­­­­­­­
                                  → Γ ∙ ø ⊢ ψ
    ⊤-i : ∀{I}{Γ : Cxt I} → Γ ⊢ ⊤
    ⊥-e : ∀{I}{Γ : Cxt I}{ψ} → Γ ⊢ ⊥
                           -- ­­­­­­­
                             → Γ ⊢ ψ
    ∧-i : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ α → Γ ⊢ β
                            -- ­­­­­­­­­­­­­­­­
                                → Γ ⊢ α ∧ β
    ∧-Eₗ : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ α ∧ β → Γ ⊢ β
    ∧-Eᵣ : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ α ∧ β → Γ ⊢ α
    ∨-iₗ : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ α → Γ ⊢ α ∨ β
    ∨-iᵣ : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ β → Γ ⊢ α ∨ β
    ⇒-i : ∀{I}{Γ : Cxt I}{ψ α} → Γ ∙ ψ ⊢ α → Γ ⊢ ψ ⇒ α
    ⇒-e : ∀{I}{Γ : Cxt I}{ψ α} → Γ ⊢ ψ ⇒ α → Γ ⊢ ψ → Γ ⊢ α
    ∨-e : ∀{I}{Γ : Cxt I}{α β ψ} → Γ ⊢ α ∨ β → Γ ∙ α ⊢ ψ → Γ ∙ β ⊢ ψ → Γ ⊢ ψ
    ~-i : ∀{I}{Γ : Cxt I}{α β} → Γ ∙ α ⊢ β → Γ ∙ α ⊢ ~ β → Γ ⊢ ~ α
    ⊥-i : ∀{I}{Γ : Cxt I}{α} → Γ ⊢ ~ α → Γ ⊢ α → Γ ⊢ ⊥
    tnd : ∀{I}{Γ : Cxt I}{α} → Γ ⊢ α ∨ ~ α
    -- ⇔-intro : ∀{I}{Γ : Cxt I}{α β} → Γ ⊢ α ⇒ β → Γ ⊢ β ⇒ α → Γ ⊢ α ⇔ β
    
    
  infix 5 _⊢_
  infix 10 ~_
  infixr 8 _∨_
  infixr 7 _⇒_
  infixl 6 _∙_
  infixr 9 _∧_

  example : {α β : Props} → ø ⊢ α ∧ β ⇒ β ∧ α
  example {α} {β} = ⇒-i (∧-i ( ∧-Eₗ var) ( ∧-Eᵣ var))

  example2 : {α β : Props} → ø ⊢ α ⇒ β ⇒ α
  example2 = ⇒-i (⇒-i (weaken var))


  example3 : {α β : Props} → ø ⊢ α ∧ (α ⇒ β) ⇒ β
  example3 = ⇒-i ( ⇒-e (∧-Eₗ var) (∧-Eᵣ var))

  Val : Set
  Val =  Fin n → Bool


  name : Val
  name zero = true
  name (suc x) = true

  ∥_∥ : Props → Val → Bool
  ∥ ⊥ ∥ ρ = false
  ∥ ⊤ ∥ ρ = true
  ∥ patom x ∥ ρ = ρ x
  ∥ ~ υ ∥ ρ = not (∥ υ ∥ ρ)
  ∥ α ∨ β ∥ ρ = ∥ α ∥ ρ or ∥ β ∥ ρ
  ∥ α ∧ β ∥ ρ = ∥ α ∥ ρ and ∥ β ∥ ρ
  ∥ α ⇒ β ∥ ρ = not (∥ α ∥ ρ) or ∥ β ∥ ρ

  ⟦_⟧ᶜ : {I : ℕ} → Cxt I → Val → Bool
  ⟦ ø ⟧ᶜ ρ = true 
  ⟦ Γ ∙ ι ⟧ᶜ ρ = ⟦ Γ ⟧ᶜ ρ and ∥ ι ∥ ρ

  example4 : {α β : Props} → ø ⊢ α ⇒ ~ (~ α ∧ β)
  example4 = ⇒-i (~-i (weaken var) (∧-Eᵣ var))

  example5 : {α β : Props} → ø ⊢ ~ (α ∧ β) ⇒ (α ⇒ ~ β)
  example5 = ⇒-i (⇒-i (~-i (∧-i (weaken var) var) (weaken (weaken var))))

  _ : {α β : Props} → ⟦ ~ α ∧ ~ β ⟧ ⊢ ~ (α ∨ β)
  _ = ~-i (∨-e var var (⊥-e (⊥-i (weaken (weaken (∧-Eₗ var))) var))) (weaken (∧-Eᵣ var))


  _⊨_ : {I : ℕ} → Cxt I → Props → Set
  Γ ⊨ ψ =  ∀  ρ → ⟦ Γ ⟧ᶜ ρ ≡ true → ∥ ψ ∥ ρ ≡ true

  _ : {p q : Props } → ø ⊢ ~ p ⇒ ( p ⇒ q )
  _  = ⇒-i (⇒-i (⊥-e (⊥-i (weaken var) var))) 

  
  _ : {p q : Props} → ø ⊢ ( p ⇒ q ) ⇒ (~ q ⇒ ~ p)
  _ = ⇒-i (⇒-i (~-i (⇒-e (weaken (weaken var)) var) (weaken var)))


  _ : {p q : Props} → ø ⊢ (p ∧ q) ⇒ (q ∧ p)
  _ = ⇒-i (∧-i (∧-Eₗ var) (∧-Eᵣ var))

  _ : {p q : Props} → ø ⊢ ~ (p ⇒ q) ⇒ p ∧ ~ q
  _ = ⇒-i (∧-i (∨-e tnd var (⊥-e (⊥-i (weaken var) (⇒-i (⊥-e (⊥-i (weaken var) var)))))) (~-i (⇒-i (weaken var) ) (weaken var)))


  _ : {p : Props} → ø ⊢ ~ ~ p ⇒ p
  _ = ⇒-i (∨-e tnd var (⊥-e (⊥-i (weaken var) var))) 


  _ : {p q : Props} → ø ⊢ (p ⇒ q) ∨ (q ⇒ p)
  _ = ∨-e tnd (∨-iₗ (⇒-i (weaken var))) (∨-iᵣ (⇒-i (⊥-e (⊥-i (weaken var) var))))

  _ : {p q r : Props} → ø ⊢ (p ⇒ (q ⇒ r)) ⇒ ((p ∧ q) ⇒ r)
  _ = ⇒-i (⇒-i (⇒-e (⇒-e (weaken var) (∧-Eᵣ var)) (∧-Eₗ var)))

  
  
  
  -- soundness : ∀ {l} {Γ : Cxt l} {ψ : Props} → Γ ⊢ ψ → Γ ⊨ ψ
  -- soundness {Γ = Γ ∙ ψ} var ρ _ with ⟦ Γ ⟧ᶜ ρ | ∥ ψ ∥ ρ
  -- soundness {Γ = Γ ∙ ψ} var ρ _      | true   | true = refl
  -- soundness {Γ = Γ ∙ ψ} var ρ ()     | true   | false
  -- soundness {Γ = Γ ∙ ψ} var ρ ()     | false  | _









  -- soundness {Γ = Γ ∙ ψ} (weaken x) ρ x₁ = {!!}
  -- soundness ⊤-i ρ x₁ = {!!}
  -- soundness (⊥-e x) ρ x₁ = {!!}
  -- soundness (∧-i x x₂) ρ x₁ = {!!}
  -- soundness (∧-Eₗ x) ρ x₁ = {!!}
  -- soundness (∧-Eᵣ x) ρ x₁ = {!!}
  -- soundness (∨-iₗ x) ρ x₁ = {!!}
  -- soundness (∨-iᵣ x) ρ x₁ = {!!}
  -- soundness (⇒-i x) ρ x₁ = {!!}
  -- soundness (⇒-e x x₂) ρ x₁ = {!!}
  -- soundness (∨-e x x₂ x₃) ρ x₁ = {!!}
  -- soundness (~-i x x₂) ρ x₁ = {!!}
  -- soundness (⊥-i x x₂) ρ x₁ = {!!}
  -- soundness tnd ρ x₁ = {!!}
