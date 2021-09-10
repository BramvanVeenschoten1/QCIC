module bool

import prelude
       function
       
data bool : Type where
  true : bool
  false : bool
  
conflict : Pi {0 a : Type}, eq true false => a
conflict () 

-- NOT OK
not : bool -> bool
not true = false
not false = tt -- true

-- NOT OK
and : bool -> bool -> bool
and true = id
and false = tt -- const false

-- NOT OK
or : bool -> bool -> bool
or true = const true
or false = tt -- id

-- NOT OK
eq : bool -> bool -> bool
eq true = id
eq false = bool.not

-- NOT OK
xor : bool -> bool -> bool
xor true = bool.not
xor false = id

-- NOT OK
implies : bool -> bool -> bool
implies true = id
implies false = tt -- const true

lift : bool -> Type
lift b = prelude.eq b true

{-
-- somehow not (not false) reduces to true
double_negation : Pi b : bool, eq b (not (not b))
double_negation true = refl
double_negation false = refl
-}

-- NOT OK
excluded_middle : Pi b : bool, lift (or b (bool.not b))
excluded_middle true = refl
excluded_middle false = tt --refl
