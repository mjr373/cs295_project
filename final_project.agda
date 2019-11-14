


infixl 15 _-_
_-_ : ℕ → ℕ → ℕ
m - Z = m
Z - S n = Z  -- not technically correct- would go neg
S m - S n = (m - n)


_ : 2 - 3 ≡ 0
_ = ↯

_ : 3 - 1 ≡ 2
_ = ↯
