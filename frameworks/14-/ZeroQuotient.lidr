> module ZeroQuotient

> import SplitQuotient

> SplitQuotient.Base = Nat
> SplitQuotient.normalize x = 0
> SplitQuotient.Relation x y = ()
> SplitQuotient.normalizeIsRelated x = ()
> SplitQuotient.normalizeMapsRelatedToEQ x y xRely = Refl


> MyUnit : Type 
> MyUnit = SplitQuotient.Quot

> poly : MyUnit -> MyUnit
> poly x = 2 * x + 7

