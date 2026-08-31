module Chapter1-Agda where
  open import  Relation.Binary.PropositionalEquality
  data Bool : Set where
    false : Bool
    true : Bool

  not : Bool → Bool
  not false = true
  not true = true

  _ : not (not false) ≡ true
  _ = refl


  _∨_ : Bool → Bool → Bool
  false ∨ false = false
  false ∨ true = true
  true ∨ false = true
  true ∨ true = true


  _∨₁_ : Bool → Bool → Bool
  false ∨₁ false = false
  false ∨₁ true = true
  true ∨₁ false = false
  true ∨₁ true = true


  _∨₂_ : Bool → Bool → Bool
  false ∨₂ x₁ = x₁
  true ∨₂ x₁ = true

  module Example-Employees where
    open Bool
    open import Data.String
      using (String)

    data Department : Set where
      administrative : Department
      engineering : Department
      finance : Department
      marketing : Department
      sales : Department

    record Employee : Set where
      field
        name : String
        department : Department
        is-new-hire : Bool

    tillman : Employee
    tillman .Employee.name = "Tillman"
    tillman .Employee.department = engineering
    tillman .Employee.is-new-hire = false


    module Sandbox-Tuples where
      open Bool
      record _×_ (A : Set) (B : Set) : Set where
        field
          proj₁ : A
          proj₂ : B

      my-tuple : Bool × Bool
      my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }

      first : Bool × Bool → Bool
      first record { proj₁ = proj₁ ; proj₂ = proj₂ } = proj₁

      my-tuple-second : Bool × Bool → Bool
      my-tuple-second x = _×_.proj₂ x

      _,_ :  {A B : Set} → A → B → A × B
      x , x₁ = record { proj₁ = x ; proj₂ = x₁ }

      my-tuple' : Bool × Bool
      my-tuple' = true , not false

    module Sandbox-Tuples₂ where
     open Bool

     record _×_ (A : Set) (B : Set) : Set where
       constructor _,_
       field
         proj₁ : A
         proj₂ : B

     infixr 4 _,_
     infixr 2 _×_

     data _⊎_ (A : Set) (B : Set) : Set where
       inj₁ : A → A ⊎ B
       inj₂ : B → A ⊎ B
     infixr 1 _⊎_

     curry : {A B C : Set} → ((A × B) → C) → A → B → C
     curry f a b = f (a , b)

     uncurry : {A B C : Set} → (A → B → C) → (A × B → C)
     uncurry x (proj₁ , proj₂) = x proj₁ proj₂

     _ : Bool × Bool → Bool
     _ = uncurry _∨_

