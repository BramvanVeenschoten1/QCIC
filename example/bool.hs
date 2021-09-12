module bool

import prelude
       function
       
data bool : Type where
  true : bool
  false : bool
  
conflict : Pi {0 a : Type}, eq false true => a
conflict () 

not : bool -> bool
not true = false
not false = true

and : bool -> bool -> bool
and true = id
and false = const false

or : bool -> bool -> bool
or true = const true
or false = id

eq : bool -> bool -> bool
eq true = id
eq false = bool.not

xor : bool -> bool -> bool
xor true = bool.not
xor false = id

implies : bool -> bool -> bool
implies true = id
implies false = const true

lift : bool -> Type
lift b = prelude.eq b true

double_negation : Pi b : bool, prelude.eq b (bool.not (bool.not b))
double_negation true = refl
double_negation false = refl

excluded_middle : Pi b : bool, lift (or b (bool.not b))
excluded_middle true = refl
excluded_middle false = refl
