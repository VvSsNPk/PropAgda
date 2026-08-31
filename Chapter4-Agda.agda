{-# OPTIONS --large-indices #-}
module Chapter4-Agda where
  open import Data.Bool
    using (Bool ; false; true;not)
  open import Data.Nat
    using (ℕ; zero;suc;_+_)
  open import Agda.Primitive
    using (Level;_⊔_;lzero;lsuc)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  data Maybe₁ {ℓ : Level} ( A : Set ℓ) : Set ℓ where
    just₁ : A → Maybe₁ A
    nothing₁ : Maybe₁ A

  _ = just₁ ℕ

  private variable
    ℓ ℓ₁ ℓ₂ a b c : Level
    A : Set a
    B : Set b
    C : Set c

  data Maybe₂ ( A : Set ℓ ) : Set ℓ where
    just₂ : A → Maybe₂ A
    nothing₂ : Maybe₂ A

  record Σ (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁


  _ : Set ≡ Set lzero
  _ = refl

  _ : Set₁ ≡ Set (lsuc lzero)
  _ = refl

  ∃n,n+1≡5 : Σ ℕ (λ n → n + 1 ≡ 5)
  ∃n,n+1≡5 = 4 , refl

-- this defines any arbitary relation between functions
  REL : Set a → Set b → (ℓ : Level) → Set ( a ⊔ b ⊔ lsuc ℓ)
  REL A B ℓ = A → B → Set ℓ

  data _maps_↦_ (f : A → B) : REL A B lzero where
    app : {x : A} → f maps x ↦ f x

  _ : not maps false ↦ true
  _ = app

  Functional : REL A B ℓ → Set _
  Functional {A = A} {B = B} _~_
    = {x : A} {y z : B} → x ~ y → x ~ z → y ≡ z

  Total : REL A B ℓ → Set _
  Total {A = A} {B = B} _~_
    = (x : A) → Σ B (λ y → x ~ y)

  relToFn : (_~_ : REL A B ℓ) → Functional _~_ → Total _~_ → A → B
  relToFn _~_ _ total x
    with total x
  ... | y , _ = y

  Rel : Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
  Rel A ℓ = REL A A ℓ

  Reflexive : Rel A ℓ → Set _
  Reflexive {A = A} _~_ = {x : A} → x ~ x

  Symmetric : Rel A ℓ → Set _
  Symmetric {A = A} _~_ = {x y : A} → x ~ y → y ~ x

  Transitive : Rel A ℓ → Set _
  Transitive {A = A} _~_ = {x y z : A} → x ~ y → y ~ z → x ~ z

  module Naive-≤₁ where
    data _≤_ : Rel ℕ lzero where
      lte : (a  b : ℕ) → a ≤ a + b
    infix 4 _≤_

    _ : 2 ≤ 5
    _ = lte 2 3

    suc-mono : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono (lte a b) = lte (suc a) b


    ≤-refl : Reflexive _≤_
    ≤-refl {zero} = lte zero zero
    ≤-refl {suc x} with ≤-refl {x}
    ... | x≤x = suc-mono x≤x

    open import Chapter3-Agda
      using (+-identityʳ)

    subst : {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
    subst _ refl px = px

    ≤-refl′ : Reflexive _≤_
    ≤-refl′ {x} = subst (λ φ → x ≤ φ) (+-identityʳ x) (lte x 0)

    suc-mono′ : {x y : ℕ} → x ≤ y → suc x ≤ suc y
    suc-mono′ {x} {.(x + b)} (lte .x b) = lte (suc x) b

  module Definition-LessThanOrEqualTo where
    data _≤_ : Rel ℕ lzero where
      z≤n : {n : ℕ} → zero ≤ n
      s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n
    infix 4 _≤_


    _ : 2 ≤ 5
    _ = s≤s (s≤s (z≤n {n = 3}) )

    record IsPreorder {A : Set a} (_~_ : Rel A ℓ) : Set (a ⊔ ℓ) where
      field
        reflp : Reflexive _~_
        trans : Transitive _~_

    module Preorder-Reasoning
      {_~_ : Rel A ℓ} (~-preorder : IsPreorder _~_) where
      open IsPreorder ~-preorder public

      begin_ : {x y : A} → x ~ y → x ~ y
      begin_ x~y = x~y
      infix 1 begin_

      _∎ : (x : A) → x ~ x
      _∎ x = reflp
      infix 3 _∎

      _≡⟨⟩_ : (x : A) → {y : A} → x ~ y → x ~ y
      x ≡⟨⟩ p = p
      infixr 2 _≡⟨⟩_

      _≈⟨_⟩_ : (x : A) → ∀ {y z} → x ~ y → y ~ z → x ~ z
      _ ≈⟨ x~y ⟩ y~z = trans x~y y~z
      infixr 2 _≈⟨_⟩_

      _≡⟨_⟩_ : (x : A) → ∀ {y z} → x ≡ y → y ~ z → x ~ z
      _ ≡⟨ refl ⟩ y~z = y~z
      infixr 2 _≡⟨_⟩_

  -- According to the author anything that obeys trans and refl are pre-oreders
  -- the author modeled it with standard equality and also using relations
  module Reachability {V : Set ℓ₁} (_⇒_ : Rel V ℓ₂) where
    open Definition-LessThanOrEqualTo
    private variable
     v v₁ v₂ v₃ : V

    data Path : Rel V (ℓ₁ ⊔ ℓ₂) where
      ↪_ : v₁ ⇒ v₂ → Path v₁ v₂
      here : Path v v
      connect : Path v₁ v₂ → Path v₂ v₃ → Path v₁ v₃

    Path-preorder : IsPreorder Path
    IsPreorder.reflp Path-preorder = here
    IsPreorder.trans Path-preorder = connect
      
      
      
      
      
      
      
