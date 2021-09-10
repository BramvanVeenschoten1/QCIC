module maybe

import prelude

data maybe (a : Type) : Type where
  nothing : maybe a
  just : a -> maybe a

-- OK
map : Pi {0 a b : Type}, (a -> b) -> maybe a -> maybe b
map f (just x) = just (f x)
map f nothing = nothing

pure : Pi {0 a : Type}, a -> maybe a
pure = just

{- meta variable removed from context
app : Pi {0 a b : Type}, maybe (a -> b) -> maybe a -> maybe b
app (just f) (just x) = just (f x)
app _ _ = tt -- nothing
-}

-- OK
join : Pi {0 a : Type}, maybe (maybe a) -> maybe a
join (just x) = x
join nothing = nothing

-- OK
bind : Pi {0 a b : Type}, maybe a -> (a -> maybe b) -> maybe b
bind (just x) f = f x
bind nothing f = nothing

-- OK
from_maybe : Pi {0 a : Type}, a -> maybe a -> a
from_maybe _ (just x) = x
from_maybe x nothing = x
