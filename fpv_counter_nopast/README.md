# Simple FPV Demo Test
The requirements are:
* Design a loadable, up/down binary counter of N bits.
* Formally verify it without using `$past()` system function.
* Do not use `eventually` strong operator since not all tools support it.
* Coverage should be more than 70%. Reset and clock dead code is acceptable.
* Do not use fixed and large delays operations (such as ##[1:100]).


