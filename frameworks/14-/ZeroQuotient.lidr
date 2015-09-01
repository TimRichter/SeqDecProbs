> module ZeroQuotient

> import SplitQuotient

> const0Idem : IsIdempotent {A = Nat} (const 0)
> const0Idem n = Refl

> const0 : IdempotentEndo Nat
> const0 = (const 0 ** const0Idem)


> MyUnit : Type
> MyUnit = SQuot const0

> instance [myunit] Num MyUnit where
>   (+) = liftQBinop const0 (+)
>   (*) = liftQBinop const0 (*)
>   (-) = liftQBinop const0 (-)
>   fromInteger = (can const0) . fromInteger
>   abs = id


