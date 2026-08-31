module Chapter3-Agda where
  open import Data.Bool
    using (Bool; true; false; _∨_; _∧_;not)
  open import Data.Nat
    using (ℕ; zero; suc; _+_;_^_)
  open import Relation.Binary.PropositionalEquality
    using (refl; _≡_)

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even :{n : ℕ} → IsEven n →   IsEven (suc (suc n))

  _*_ : ℕ → ℕ → ℕ
  zero * y = zero
  suc x * y = y + (x * y) 

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one
  
  
  zero-is-even : IsEven zero
  zero-is-even = zero-even

  two-is-even : IsEven 2
  two-is-even  = suc-suc-even zero-even

  cong : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  0+x≡x : (x : ℕ) → zero + x ≡ x
  0+x≡x _ =  refl

  x+0≡x : (x : ℕ) →  x + zero ≡ x
  x+0≡x zero = refl
  x+0≡x (suc x) = cong suc (x+0≡x x)

  +-identityˡ : (x : ℕ) → zero + x ≡ x
  +-identityˡ = 0+x≡x

  +-identityʳ : (x : ℕ) → x + zero ≡ x
  +-identityʳ = x+0≡x

  1*x≡x : (x : ℕ) → 1 * x ≡ x
  1*x≡x zero = refl
  1*x≡x (suc x) =  cong suc (1*x≡x x)

  *-zeroˡ : (x : ℕ) → zero * x ≡ zero
  *-zeroˡ _ = refl

  *-zeroʳ : (x : ℕ) → x * zero ≡ zero
  *-zeroʳ zero = refl
  *-zeroʳ (suc x) = *-zeroʳ x

  ^-identityʳ : (x : ℕ) → x ^ 1 ≡ x
  ^-identityʳ zero = refl
  ^-identityʳ (suc x) = cong suc (^-identityʳ x)
  
  *-identityˡ′ : (x : ℕ) → x ≡ 1 * x
  *-identityˡ′ zero = refl
  *-identityˡ′ (suc x) = cong suc (*-identityˡ′ x)

  sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  sym-involutive : {A : Set} → {x y : A} → (p : x ≡ y) → sym (sym p) ≡ p
  sym-involutive refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl refl = refl

  amul1eq : (a b : ℕ) → a ^ 1 ≡ a + (b * zero)
  amul1eq a b = trans (^-identityʳ a ) ((trans (sym (+-identityʳ a))) (cong ((a +_)) (sym (*-zeroʳ b))))
  

  _! : ℕ → ℕ
  zero ! = 1
  suc x ! = (suc x * (x !))

  _ : 5 ! ≡ 120
  _ = refl

  ∣_ : ℕ → ℕ
  ∣_ = suc

  ■ : ℕ
  ■ = zero


  five : ℕ
  five = ∣ ∣ ∣ ∣ ∣ ■

  _ : five ≡ 5
  _ = refl

  module ≡-Reasoning where
  _∎ : {A : Set} → (x : A) → x ≡ x
  _∎ x = refl

  infix 3 _∎

  _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → x ≡ y → x ≡ y
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨⟩_


  _ : 4 ≡ suc (one + two)
  _ = refl

  _ : 4 ≡ suc (one + two)
  _ =
    4       ≡⟨⟩
    two + two ≡⟨⟩
    suc one + two ≡⟨⟩
    suc (one + two) ∎

  _ : 4 ≡ suc (one + two)
  _ = _∎ (suc ( one + two))

  _≡⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ j ⟩ p = trans j p

  infixr 2 _≡⟨_⟩_

  begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
  begin_ x=y = x=y

  infix 1 begin_

  a^1≡a+b*0 : (a b : ℕ) → a ^ 1 ≡ a + b * 0
  a^1≡a+b*0 a b =
    begin
      a ^ 1
    ≡⟨ ^-identityʳ a ⟩
      a
    ≡⟨ sym (+-identityʳ a) ⟩
      a + 0
    ≡⟨ cong (a +_) (sym (*-zeroʳ b)) ⟩
      a + b * 0
    ∎
    where open ≡-Reasoning

  ∨-assoc : (a b c : Bool) → (a ∨ b) ∨ c ≡ a ∨ ( b ∨ c)
  ∨-assoc false b c = refl
  ∨-assoc true b c = refl

  ∧-assoc : (a b c : Bool) → (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
  ∧-assoc false b c = refl
  ∧-assoc true b c = refl

  +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
  +-assoc zero y z = refl
  +-assoc (suc x) y z = cong suc (+-assoc x y z)


  +-suc : (x y : ℕ) →  x + suc y  ≡ suc (x + y)
  +-suc zero y = refl
  +-suc (suc x) y = cong suc (+-suc x y)

  +-comm : (x y : ℕ) → x + y ≡ y + x
  +-comm zero y = sym (+-identityʳ y)
  +-comm (suc x) y =  begin
    suc ( x + y ) ≡⟨ cong suc (+-comm x y) ⟩
    suc (y + x) ≡⟨ sym (+-suc y x) ⟩
    y + suc x ∎

  suc-injective : {x y : ℕ} → suc x ≡ suc y → x ≡ y
  suc-injective refl = refl



  *-suc : (x y : ℕ) → x * suc y ≡ x + x * y
  *-suc zero y = refl
  *-suc (suc x) y = begin
    suc x * suc y ≡⟨⟩
    suc y + x * suc y ≡⟨ cong (suc y +_) (*-suc x y) ⟩
    suc y + (x + x * y)
    ≡⟨⟩
    suc (y + ( x + x * y))
    ≡⟨ cong suc (sym (+-assoc y x (x * y))) ⟩
    suc ((y + x) + x * y)
    ≡⟨ cong (λ δ → suc (δ + x * y )) (+-comm y x) ⟩
    suc ((x + y) + x * y)
    ≡⟨ cong suc (+-assoc x y (x * y)) ⟩
    suc ( x + (y + x * y))
    ≡⟨⟩
    suc x + (y + x * y)
    ≡⟨⟩
    suc x + (suc x * y) ∎


  *-comm : (x y : ℕ) → x * y ≡ y * x
  *-comm zero y = sym (*-zeroʳ y)
  *-comm (suc x) y = begin 
    suc x * y ≡⟨⟩
    y + ( x * y) ≡⟨ cong (y +_) (*-comm x y)  ⟩
    y + y * x ≡⟨ sym ( *-suc y x ) ⟩
    y * suc x ∎
  
