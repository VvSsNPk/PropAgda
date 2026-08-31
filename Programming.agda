
module Programming where
  open import Data.Nat using (ℕ)
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎ )

  _+_ : ℕ → ℕ → ℕ
  ℕ.zero + n = n
  ℕ.suc m + n = ℕ.suc (m + n)


  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A
  infixr 5 _::_

  _++_ : {A : Set} → List A → List A → List A
  [] ++ x₁ = x₁
  (x :: x₂) ++ x₁ = x :: (x₂ ++ x₁)

  map : {A B : Set} → (f : A → B) → List A → List B
  map f [] = []
  map f (x :: x₁) = (f x) :: (map f x₁)

  infixr 5 _++_

  _ : (1 :: 2 :: 3 :: []) ++ (4 :: 5 :: []) ≡ (1 :: 2 :: 3 :: 4 :: 5 :: [])
  _ = refl

  pattern [_] x = x :: []
  pattern [_,_] x y = x :: y :: []
  pattern [_,_,_] x y z = x :: y :: z :: []
  pattern [_,_,_,_] x y z a = x :: y :: z :: a :: []
  pattern [_,_,_,_,_] x y z a b = x :: y :: z :: a :: b :: []

  _ : [ 1 , 2 , 3  ] ++ [ 4 , 5 ] ≡ [ 1 , 2 , 3 , 4 , 5 ]
  _ = refl 


  record Rect : Set where
    constructor rect 
    field
      height : ℕ
      width : ℕ

  square : ℕ → Rect
  square z = rect z z

  open Rect
  open import Data.Nat using (_*_)

  squash : Rect → Rect
  squash r .height = 3 * (height r)
  squash r .width = 2 * width r

  sq : Rect → Rect
  height (sq r) = 4 * height r
  width (sq r) = 5 * width r
