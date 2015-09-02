> module ZeroQuotient

> import SplitQuotient3

> SplitQuotient3.Base = Nat
> SplitQuotient3.normalize x = 0
> SplitQuotient3.normalizeIdem x = Refl


> MyUnit : Type 
> MyUnit = SQuot

testnum

> poly : MyUnit -> MyUnit
> poly x = 2 * x + 7

