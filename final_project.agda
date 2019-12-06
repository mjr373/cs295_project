
module final_project where

---------
-- LIB --
---------

-- equality --

infix 8 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  ↯ : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

-- naturals --

data ℕ : Set where
  Z : ℕ
  S : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 25 _+_
_+_ : ℕ → ℕ → ℕ
Z    + n  =  n
(S m) + n  =  S (m + n)

infixl 26 _×_
_×_ : ℕ → ℕ → ℕ
Z × _ = Z
S m × n = n + m × n

-- order --

infix 8 _≤_
data _≤_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z ≤ n
  S : ∀ {m n} → m ≤ n → S m ≤ S n

infix 8 _<_
data _<_ : ℕ → ℕ → Set where
  Z : ∀ {n} → Z < S n
  S : ∀ {m n} → m < n → S m < S n

data <! : Set where
  [<] : <!
  [≥] : <!

data ≤! : Set where
  [≤] : ≤!
  [>] : ≤!

infix 8 _≤⋆!_
data _≤⋆!_ (m n : ℕ) : Set where
  [≤] : m ≤ n → m ≤⋆! n
  [>] : n < m → m ≤⋆! n

data ⋚! : Set where
  [<] : ⋚!
  [≡] : ⋚!
  [>] : ⋚!

infix 8 _⋚⋆!_
data _⋚⋆!_ (m n : ℕ) : Set where
  [<] : m < n → m ⋚⋆! n
  [≡] : m ≡ n → m ⋚⋆! n
  [>] : n < m → m ⋚⋆! n


_≤?_ : ℕ → ℕ → ≤!
Z ≤? n = [≤]
S m ≤? Z = [>]
S m ≤? S n = m ≤? n

_⋚?_ : ℕ → ℕ → ⋚!
Z ⋚? Z = [≡]
Z ⋚? S n = [<]
S m ⋚? Z = [>]
S m ⋚? S n = m ⋚? n

-- lists --

infixr 20 _∷_
data list (A : Set) : Set where
  [] : list A
  _∷_ : A → list A → list A

pattern [_] a = a ∷ []
pattern [_,_] a b = a ∷ [ b ]
pattern [_,_,_] a b c = a ∷ [ b , c ]
pattern [_,_,_,_] a b c d = a ∷ [ b , c , d ]
pattern [_,_,_,_,_] a b c d e = a ∷ [ b , c , d , e ]
pattern [_,_,_,_,_,_] a b c d e f = a ∷ [ b , c , d , e , f ]
pattern [_,_,_,_,_,_,_] a b c d e f g = a ∷ [ b , c , d , e , f , g ]
pattern [_,_,_,_,_,_,_,_] a b c d e f g h = a ∷ [ b , c , d , e , f , g , h ]
pattern [_,_,_,_,_,_,_,_,_] a b c d e f g h i = a ∷ [ b , c , d , e , f , g , h , i ]
pattern [_,_,_,_,_,_,_,_,_,_] a b c d e f g h i j = a ∷ [ b , c , d , e , f , g , h , i , j ]

infixl 25 _⧺_
_⧺_ : ∀ {A : Set} → list A → list A → list A
[] ⧺ ys = ys
(x ∷ xs) ⧺ ys = x ∷ (xs ⧺ ys)



infixr 3 existential

syntax existential A (λ x → B) = ∃ x ⦂ A ST B

data existential (A : Set) (B : A → Set) : Set where
  ⟨∃_,_⟩ : ∀ (x : A) → B x → existential A B

data _∈_ (x : ℕ) : list ℕ → Set where
  Z : ∀ {xs} → x ∈ (x ∷ xs)
  S : ∀ {x′ xs} → x ∈ xs → x ∈ (x′ ∷ xs)
  
-- POSTULATES --

postulate

  runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
  rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
  assoc[×] : ∀ (m n p : ℕ) → m × (n × p) ≡ (m × n) × p
  commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
  ldist[×] : ∀ (m n p : ℕ) → m × (n + p) ≡ m × n + m × p
  rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p


data ≡! : Set where
  [≡] : ≡!
  [≢] : ≡!

_≡?_ : ℕ → ℕ → ≡!
Z ≡? Z = [≡]
Z ≡? S n = [≢]
S m ≡? Z = [≢]
S m ≡? S n =  m ≡? n

----------------------------------------------------------------------------- Here's where my work starts  

infixl 15 _-_
_-_ : ℕ → ℕ → ℕ
m - Z = m
Z - S n = Z  
S m - S n = (m - n)


infixl 16 _%_
_%_ : ℕ → ℕ → ℕ
Z % n = Z
(S m) % n with _⋚?_ (n - 1) (m % n)
(S m) % n | [<] = S(m % n)
(S m) % n | [≡] = Z
(S m) % n | [>] = S(m % n)

_ : 2 % 3 ≡ 2
_ = ↯

_ : 5 % 3 ≡ 2
_ = ↯

_ : 0 % 0 ≡ 0
_ = ↯

_ : 2 % 2 ≡ 0
_ = ↯

_ : 10 % 2 ≡ 0
_ = ↯


infixl 16 _/_
_/_ : ℕ → ℕ → ℕ
Z / n = Z
S m / n with _⋚?_ (m % n) (n - 1)
(S m / n) | [<] = m / n
(S m / n) | [≡] = S(m / n)
(S m / n) | [>] = m / n


_ : 2 / 3 ≡ 0
_ = ↯

_ : 5 / 2 ≡ 2
_ = ↯

_ : 0 / 0 ≡ 0
_ = ↯

_ : 2 / 2 ≡ 1
_ = ↯

_ : 10 / 2 ≡ 5
_ = ↯

divout : list ℕ → ℕ → list ℕ -- assumes that f can be taken out of n
divout [] f = []
divout (x ∷ n) f =  [ (x / f) , f ] ⧺ n

_ : divout [ 4 ] 2 ≡ [ 2 , 2 ]
_ = ↯

_ : divout [ 9 ] 3 ≡ [ 3 , 3 ]
_ = ↯

_ : divout [ 8 ] 2 ≡ [ 4 , 2 ]
_ = ↯

_ : divout [ 4 , 2 ] 2 ≡ [ 2 , 2 , 2 ]
_ = ↯

_ : divout [ 6 , 2 ] 3 ≡ [ 2 , 3 , 2 ]  --most recently divided factor placed at second place
_ = ↯


divif : list ℕ → ℕ → list ℕ  --take a factor out, if it can be done evenly
divif [] f = []
divif (x ∷ n) f with (x % f) ≡? 0
divif (x ∷ n) f | [≡] = divout [ x ] f
divif (x ∷ n) f | [≢] = (x ∷ n)

_ : divif [ 4 ] 2 ≡ [ 2 , 2 ]
_ = ↯

_ : divif [ 4 ] 3 ≡ [ 4 ]
_ = ↯

_ : divif [ 8 ] 2 ≡ [ 4 , 2 ]
_ = ↯


{-# TERMINATING #-}
divallout : list ℕ → ℕ → list ℕ    --takes a list, n, and a factor f. Assume that the first number in the list is the one we are trying to factor.
divallout [] f = []
divallout (Z ∷ n) f = n 
divallout (S x ∷ n) f  with (x % f) ≡? (f - 1)          --does it divide evenly?
divallout (S x ∷ n) f | [≡] with ((S x) / f) ⋚? 1         --yes: but should we keep dividing out?
divallout (S x ∷ n) f | [≡] | [<] = (S x ∷ n)                 --no: return whatever we have (unused) 
divallout (S x ∷ n) f | [≡] | [≡] = (S x ∷ n)                 --no: return whatever we have (case: [ 3 ] 3 )
divallout (S x ∷ n) f | [≡] | [>] =  (divallout [ (S x) / f ] f ) ⧺ ( f ∷ n )    --yes:multiple factors of f (case: [ 8 ] 2 )
divallout (S x ∷ n) f | [≢] =  (S x ∷ n)                  --no: (case: [ 7 ] 3)

_ : divallout [ 4 ] 3 ≡ [ 4 ]
_ = ↯
_ : divallout [ 3 ] 3 ≡ [ 3 ]  --  [≡] | [<]
_ = ↯
_ : divallout [ 3 , 2 ] 3 ≡ [ 3 , 2 ] --
_ = ↯
_ : divallout [ 4 , 2 ] 3 ≡ [ 4 , 2 ] --
_ = ↯
_ : divallout [ 2 ] 3 ≡ [ 2 ] 
_ = ↯
_ : divallout [ 8 ] 4 ≡ [ 2 , 4 ] --  [≡] | [≡]
_ = ↯
_ : divallout [ 6 ] 2 ≡ [ 3 , 2 ] --  [≡] | [>]
_ = ↯
_ : divallout [ 8 ] 2 ≡ [ 2 , 2 , 2 ] --  [≡] | [>]
_ = ↯
_ : divallout [ 8 , 3 ] 2 ≡ [ 2 , 2 , 2 , 3 ] --  [≡] | [>]
_ = ↯
_ : divallout [ 27 ] 3 ≡ [ 3 , 3 , 3 ] --  [≡] | [>] 
_ = ↯
_ : divallout [ 24 ] 2 ≡ [ 3 , 2 , 2 , 2 ] --  [≡] | [>]
_ = ↯
_ : divallout [ 24 ] 3 ≡ [ 8 , 3 ] --  [≡] | [>]
_ = ↯


{-# TERMINATING #-}
loop : ℕ → ℕ → list ℕ → list ℕ   --where n is the number to be factored, f is the first number to factor by, and a is a list of n partially factored out
loop n Z a = a  --assume a = [ n ] when called
loop n (S f) a with ((S f) × (S f)) ≤? n   --stop when f^2 > n
loop n (S f) a | [≤] = loop n (S (S f)) (divallout a (S f))   --increase f by one and call loop recursively after dividing the current factor out
loop n (S f) a | [>] = a  --return whatever we have so far

-- loop n f [ n ]
_ : loop 4 2 [ 4 ] ≡ [ 2 , 2 ]
_ = ↯
_ : loop 30 2 [ 30 ] ≡ [ 5 , 3 , 2 ]
_ = ↯
_ : loop 30 6 [ 30 ] ≡ [ 30 ]
_ = ↯


trialdiv : ℕ → list ℕ
trialdiv n = loop n 2 [ n ]  --always start factoring with 2, initialize a to be [ n ]


_ : trialdiv 4 ≡ [ 2 , 2 ]
_ = ↯
_ : trialdiv 15 ≡ [ 5 , 3 ]
_ = ↯
_ : trialdiv 30 ≡ [ 5 , 3 , 2 ]
_ = ↯
_ : trialdiv 24 ≡ [ 3 , 2 , 2 , 2 ]
_ = ↯
_ : trialdiv 28 ≡ [ 7 , 2 , 2 ]
_ = ↯
_ : trialdiv 29 ≡ [ 29 ]
_ = ↯




divides : ℕ → ℕ → Set
divides x n = ∃ m ⦂ ℕ ST x × m ≡ n


L1 : ∀ (n : ℕ) (x : ℕ) → x ∈ trialdiv n → divides x n   
L1 n x P = {!!}




