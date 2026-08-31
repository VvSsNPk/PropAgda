module Logic-Agda where
  open import Data.Fin using (Fin;zero;suc)
  open import Data.Nat using (ℕ)
  open import Relation.Binary.PropositionalEquality using (_≡_;refl)
  open import Data.Bool using (Bool; false; true ;not) renaming (_∨_ to _or_ ; _∧_ to _and_)

  data Props : Set where
    ⊥ ⊤ : Props
    patom : {n : ℕ } →  Fin n → Props
    ~_ : Props → Props
    _∨_ _∧_ _⇒_ : Props → Props → Props


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
  Val = {n : ℕ} → Fin n → Bool

  ∥_∥ : Props → Val → Bool
  ∥ ⊥ ∥ ρ = false
  ∥ ⊤ ∥ ρ = true
  ∥ patom x ∥ ρ = ρ x
  ∥ ~ υ ∥ ρ = not (∥ υ ∥ ρ)
  ∥ α ∨ β ∥ ρ = ∥ α ∥ ρ or ∥ β ∥ ρ
  ∥ α ∧ β ∥ ρ = ∥ α ∥ ρ and ∥ β ∥ ρ
  ∥ α ⇒ β ∥ ρ = not (∥ α ∥ ρ) or ∥ β ∥ ρ

  example4 : {α β : Props} → ø ⊢ α ⇒ ~ (~ α ∧ β)
  example4 = ⇒-i (~-i (weaken var) (∧-Eᵣ var))

  example5 : {α β : Props} → ø ⊢ ~ (α ∧ β) ⇒ (α ⇒ ~ β)
  example5 = ⇒-i (⇒-i (~-i (∧-i (weaken var) var) (weaken (weaken var))))

  _ : {α β : Props} → ⟦ ~ α ∧ ~ β ⟧ ⊢ ~ (α ∨ β)
  _ = ~-i (∨-e var var (⊥-e (⊥-i (weaken (weaken (∧-Eₗ var))) var))) (weaken (∧-Eᵣ var))
