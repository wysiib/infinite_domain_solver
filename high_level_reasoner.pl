:- module(high_level_reasoner, [lt/2,
                                leq/2]).

:- use_module(library(chr)).

:- chr_constraint leq/2, lt/2.
:- chr_constraint eq/3.

reflexivity  @ leq(X,X) <=> true.
antisymmetry @ leq(X,Y), leq(Y,X) <=> X = Y.
idempotence  @ leq(X,Y) \ leq(X,Y) <=> true.
transitivity @ leq(X,Y), leq(Y,Z) ==> leq(X,Z).

antireflexivity @ lt(X,X) <=> fail.
idempotence     @ lt(X,Y) \ lt(X,Y) <=> true.
transitivity    @ lt(X,Y), leq(Y,Z) ==> lt(X,Z).
transitivity    @ leq(X,Y), lt(Y,Z) ==> lt(X,Z).
transitivity    @ lt(X,Y), lt(Y,Z)  ==> lt(X,Z).
