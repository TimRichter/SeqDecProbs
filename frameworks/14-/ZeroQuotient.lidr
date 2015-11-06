> module ZeroQuotient

> import KernelIdempotentQuotient

> KernelIdempotentQuotient.Base = Nat
> KernelIdempotentQuotient.normalize x = 0
> KernelIdempotentQuotient.normalizeIdem x = Refl


> MyUnit : Type 
> MyUnit = SQuot

testnum

> poly : MyUnit -> MyUnit
> poly x = 2 * x + 7

