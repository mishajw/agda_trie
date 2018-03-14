
data _≡_ : {A : Set} → A → A → Set where
  refl : {A : Set} → (a : A) → a ≡ a

module ListM  where
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A
  infixr 5 _∷_

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ map f xs

  _++_ : {A : Set} → List A → List A → List A
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)
open ListM public

data Optional (A : Set) : Set where
  None : Optional A
  Some : A → Optional A

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true then a else _ = a
if false then _ else a = a

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infix 6 _×_
infix 5 _,_

module TrieM (A : Set)(equal : A → A → Bool) where
  record Trie (A : Set) : Set where
    inductive
    constructor trie
    field
      children : List (A × Trie A)
      is-end : Bool

  get-child : Trie A → A → Optional (Trie A)
  get-child (trie [] _) a = None
  get-child (trie ((a' , t) ∷ cs) e) a =
    if (equal a a')
    then (Some t)
    else (get-child (trie cs e) a)

  add-child : Trie A → A → Trie A → Trie A
  add-child (trie cs b) a c = trie ((a , c) ∷ cs) b

  replace-child : Trie A → A → Trie A → Trie A
  replace-child (trie [] b) a c = trie [] b
  replace-child (trie ((a' , t) ∷ xs) b) a c =
    if (equal a a')
    then
      trie ((a , c) ∷ xs) b
    else
      add-child (replace-child (trie xs b) a c) a' t

  insert : Trie A → List A → Trie A
  insert (trie cs _) [] = trie cs true
  insert t (x ∷ xs) with (get-child t x)
  insert t (x ∷ xs) | None = add-child t x (insert (trie [] false) xs)
  insert t (x ∷ xs) | Some c = replace-child t x (insert c xs)

  all-words : Trie A → List (List A)
  all-words (trie children is-end) = our-words is-end ++ child-words children where

    our-words : Bool → List (List A)
    our-words true = [] ∷ []
    our-words false = []

    child-words : List (A × Trie A) → List (List A)
    child-words [] = []
    child-words ((a , t) ∷ cs) = (map (_∷_ a) (all-words t)) ++ (child-words cs)

module NatTrie where
  data Nat : Set where
    zero : Nat
    succ : Nat → Nat
  ℕ₀ = zero
  ℕ₁ = succ zero
  ℕ₂ = succ (succ zero)

  nat-eq : Nat → Nat → Bool
  nat-eq zero zero = true
  nat-eq (succ a) (succ b) = nat-eq a b
  nat-eq _ _ = false

  open TrieM Nat nat-eq

  example₀ : Trie Nat
  example₀ = trie [] false

  example₁ = insert example₀ (ℕ₀ ∷ ℕ₁ ∷ ℕ₂ ∷ [])
  example₂ = insert example₁ (ℕ₀ ∷ ℕ₁ ∷ ℕ₀ ∷ [])
  words₁ = all-words example₁
  words₂ = all-words example₂
