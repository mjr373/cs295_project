
data ≡! : Set where
  [≡] : ≡!
  [≢] : ≡!

_≡?_ : ℕ → ℕ → ≡!
Z ≡? Z = [≡]
Z ≡? S n = [≢]
S m ≡? Z = [≢]
S m ≡? S n =  m ≡? n

_ : 2 ≡? 2 ≡ [≡]
_ = ↯

_ : 2 ≡? 3 ≡ [≢]
_ = ↯

_ : 3 ≡? 2 ≡ [≢]
_ = ↯



infixl 15 _-_
_-_ : ℕ → ℕ → ℕ
m - Z = m
Z - S n = Z  
S m - S n = (m - n)


_ : 2 - 3 ≡ 0
_ = ↯

_ : 3 - 1 ≡ 2
_ = ↯


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
divallout : list ℕ → ℕ → list ℕ
divallout [] f = []
divallout (Z ∷ n) f = n --in practice, this case should never be used
divallout (S x ∷ n) f  with (x % f) ≡? (f - 1)          --does it divide evenly?
divallout (S x ∷ n) f | [≡] with ((S x) / f) ⋚? 1       --should we keep dividing out?
divallout (S x ∷ n) f | [≡] | [<] = (S x ∷ n)
divallout (S x ∷ n) f | [≡] | [≡] = (S x ∷ n)  
divallout (S x ∷ n) f | [≡] | [>] =  (divallout [ (S x) / f ] f ) ⧺ ( f ∷ n ) 
divallout (S x ∷ n) f | [≢] =  (S x ∷ n)

_ : divallout [ 4 ] 3 ≡ [ 4 ]
_ = ↯
_ : divallout [ 3 ] 3 ≡ [ 3 ]  --  [≡] | [<]
_ = ↯
_ : divallout [ 3 , 2 ] 3 ≡ [ 3 , 2 ] 
_ = ↯
_ : divallout [ 4 , 2 ] 3 ≡ [ 4 , 2 ] 
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
{-
_ : divallout [ 27 ] 3 ≡ [ 3 , 3 , 3 ] --  [≡] | [>] --passes, but takes while to run
_ = ↯-}
_ : divallout [ 24 ] 2 ≡ [ 3 , 2 , 2 , 2 ] --  [≡] | [>]
_ = ↯
_ : divallout [ 24 ] 3 ≡ [ 8 , 3 ] --  [≡] | [>]
_ = ↯
