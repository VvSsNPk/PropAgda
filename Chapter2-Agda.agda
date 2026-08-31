module Chapter2-Agda where
  import Chapter1-Agda
  module Definition-Naturals where
    data ℕ : Set where
      zero : ℕ
      suc : ℕ → ℕ

  module Sandbox-Naturals where
    open import Data.Nat
      using (ℕ; zero; suc)

    one : ℕ
    one = suc zero

    two : ℕ
    two = suc one

    three : ℕ
    three = suc two

    addition : ℕ → ℕ → ℕ
    addition zero x₁ = x₁
    addition (suc x) x₁ = addition x (suc x₁)

  module Sandbox-Nat where
    open import Data.Nat
      using (ℕ; suc; zero; 2+)
    open Chapter1-Agda
      using (Bool; true; false)

    nzero : ℕ → Bool
    nzero zero = true
    nzero (suc x) = false

    n=2? : ℕ → Bool
    n=2? zero = false
    n=2? (suc zero) = false
    n=2? (2+ zero) = true
    n=2? (2+ (suc x)) = false
    
    data Maybe (A : Set) : Set where
      just : A → Maybe A
      nothing : Maybe A

    data IsEven : ℕ → Set  where
      zero : IsEven zero
      suc-suc :{n : ℕ} → IsEven n → IsEven (suc (suc n))

    four : ℕ
    four = suc (suc (suc (suc zero)))

    four-is-even : IsEven four
    four-is-even = suc-suc (suc-suc zero)



    isEvenfn : ℕ → Bool
    isEvenfn zero = true
    isEvenfn (suc zero) = false
    isEvenfn (suc (suc x)) = isEvenfn x

    evenEv : (n : ℕ) → Maybe (IsEven n)
    evenEv zero =   just zero
    evenEv (suc zero) = nothing
    evenEv (suc (suc n)) with evenEv n
    ... | just x = just (suc-suc x)
    ... | nothing = nothing

    _+_ : ℕ → ℕ → ℕ
    zero + y = y
    suc x + y = x + suc y
    infixl 6 _+_

    _*_ : ℕ → ℕ → ℕ
    zero * y = zero
    suc x * y = x + (x * y)
    infixl 7 _*_

    _^_ : ℕ → ℕ → ℕ
    a ^ zero = suc zero
    a ^ suc b = a * (a ^ b)


    _∸_ : ℕ → ℕ → ℕ
    x ∸ zero = x
    zero ∸ suc y = zero
    suc x ∸ suc y = x ∸ y

    one : ℕ
    one = suc zero

    two : ℕ
    two = suc one

    three : ℕ
    three = suc two
    module Natural-Tests where
      open import Relation.Binary.PropositionalEquality

      _ : one + two ≡ three
      _ = refl


  module Sandbox-Integers where
    import Data.Nat as ℕ
    open ℕ using (ℕ)

    data ℤ : Set where
      +_ : ℕ → ℤ
      -[1+_] : ℕ → ℤ

    

    
    
    
    



