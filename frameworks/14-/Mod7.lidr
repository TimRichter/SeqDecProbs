> module Mod7

> import SplitQuotient3
> import NatProperties

> %default total

> SplitQuotient3.Base = Nat

> mod7 : Nat -> Nat
> mod7 n with (decLT n 7)
>   | (Yes p) = n
>   | (No  _) = assert_total (mod7 (n - 7))

> SplitQuotient3.normalize = mod7

> mod7Idem : (n : Nat) -> mod7 (mod7 n) = mod7 n
> mod7Idem n = lemma2 (mod7 n) (lemma1 n) where
>
>   lemma1 : (n : Nat) -> (mod7 n) `LT` 7
>   lemma1 n with (decLT n 7)
>     | (Yes p) = p
>     | (No  _) = assert_total (lemma1 (n - 7))
>
>   lemma2 : (n : Nat) -> n `LT` 7 -> mod7 n = n
>   lemma2 n nLT7 with (decLT n 7)
>     | (Yes p) = Refl
>     | (No  r) = absurd (r nLT7)

> SplitQuotient3.normalizeIdem = mod7Idem


> Mod7 : Type
> Mod7 = SQuot

> allValues : List Mod7
> allValues = map fromInteger [0..6]

testing computations mod 7

> square : Mod7 -> Mod7
> square x = x * x



