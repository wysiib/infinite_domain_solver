:- use_module(infinite_domain_solver).

:- use_module(library(plunit)).
:- use_module(library(clpfd)).

:- op(870,xfy,'=>').
:- op(820,xfy,'<=>').
:- op(860,xfy,'&').
:- op(850,xfy,'or').

:- begin_tests(solver).
test(test1,[all(X == [1,2,3,4,5,6,7,8,9,10])]) :-
    solve_constraint(X in -10..10 & X > 0,[X]),
    \+ enum_warning.
test(test2,[fail]) :-
    solve_constraint(X in -10..0 & X > 1,[X]),
    \+ enum_warning.
test(test3_finite_domain_true,[all(X == [3,4,5,6,7,8,9,10])]) :-
    solve_constraint(Y=2 & exists(X,X in 0 .. 10 & X>Y),[Y]),
    \+ enum_warning.
test(test3_finite_domain_false,[fail]) :-
    solve_constraint(Y=11 & exists(X,X in 0 .. 10  & X>Y),[Y]),
    \+ enum_warning.
test(test3_finite_domain_reverse_order_true,[all(X == [3,4,5,6,7,8,9,10])]) :-
    solve_constraint(exists(X,X in 0 .. 10 & X>Y) & Y=2,[Y]),
    \+ enum_warning.
test(test3_finite_domain_reverse_order_false,[fail]) :-
    solve_constraint(exists(X,X in 0 .. 10 & X>Y) & Y=11,[Y]),
    \+ enum_warning.
test(test4_finite_domain_true,[true(Y == 2)]) :-
    solve_constraint(Y=2 & forall(X,X in 3 .. 10 => X>Y),[Y]),
    \+ enum_warning.
test(test4_finite_domain_false,[fail]) :-
    solve_constraint(Y=2 & forall(X,X in 0 .. 10 => X>Y),[Y]),
    \+ enum_warning.
test(test5_enum_infinite_exception, [exception(enum_infinite)]) :-
    solve_constraint(Y=2 & forall(X,X in inf .. sup => X>Y),[Y]).
test(test6_enum_warning_x_positive,[nondet,true(Y == 2)]) :-
    solve_constraint(Y=2 & exists(X,X>Y),[Y]),
    enum_warning.
test(test6_enum_warning_x_negative,[nondet,true(Y == 2)]) :-
    solve_constraint(Y=2 & exists(X,X<Y),[Y]),
    enum_warning.
:- end_tests(solver).

:- begin_tests(nested).
test(one_larger_for_each_x,[nondet]) :-
    solve_constraint(forall(X,X in -10 .. 10 => exists(Y,Y>X)),[]),
    enum_warning.
test(one_larger_for_each_x_unconstrained,[exception(enum_infinite)]) :-
    solve_constraint(forall(X,X in inf .. sup => exists(Y,Y>X)),[]).
test(one_larger_for_all_x,[nondet]) :-
    solve_constraint(exists(Y,forall(X,X in -10 .. 10 => Y>X)),[]),
    enum_warning.
test(one_larger_for_all_x_with_interval,[all(Y == [11,12])]) :-
    solve_constraint(Y in -5 .. 12 & forall(X,X in -10 .. 10 => Y>X),[Y]).
test(nested_foralls,[nondet]) :-
    solve_constraint(forall(X,X in -10 .. 10 => forall(Y,Y in -10 .. 10 => exists(Z,Z > X & Z > Y))),[]),
    enum_warning.
test(nested_foralls_interval,[all(Z == [11,12])]) :-
    solve_constraint(Z in 5 .. 12 & forall(X,X in -10 .. 10 => forall(Y,Y in -10 .. 10 => Z > X & Z > Y)),[Z]).
test(nested_foralls_wrong,[fail]) :-
    solve_constraint(forall(X,X in -10 .. 10 => forall(Y,Y in -10 .. 10 => exists(Z,Z > X & Y > Z))),[]),
    enum_warning.
test(nested_foralls_inner_infinite,[exception(enum_infinite)]) :-
    solve_constraint(forall(X,X in -10 .. 10 => forall(Y,Y in inf .. sup => exists(Z,Z > X & Z > Y))),[]).
:- end_tests(nested).

:- begin_tests(negated_quantifiers).
test(test3_finite_domain_negated_false,[fail]) :-
    solve_constraint(Y=2 & not(exists(X,X in 0 .. 10 & X>Y)),[Y]),
    \+ enum_warning.
test(test3_finite_domain_negated_true,[true(Y == 2)]) :-
    solve_constraint(Y=2 & not(exists(X,X in -10 .. 1 & X>Y)),[Y]),
    \+ enum_warning.
:- end_tests(negated_quantifiers).

:- begin_tests(from_paper).
test(paper1,[set(X == [-100,100])]) :-
    solve_constraint(X * X = 10000,[X]),
    \+ enum_warning.
test(paper2,[true(X == 11107),nondet]) :-
    solve_constraint(X > 10000 & X mod 1234 = 1,[X]),
    enum_warning.
test(paper3,[fail]) :-
    solve_constraint(X * X = 100000,[X]) ; enum_warning.
:- end_tests(from_paper).

:- begin_tests(infdom).
test(simple_infdom1,[fail]) :-
    solve_constraint(exists(X,exists(Y,X < Y & Y < X)),[]).
test(simple_infdom2,[fail]) :-
    solve_constraint(exists(X,exists(Y,X =< Y & Y =< X & not(X = Y))),[]).
:- end_tests(infdom).

:- begin_tests(implications).
test(implies_true_find,[nondet,true(X == 0)]) :-
    solve_constraint(X > 5 => X > 4,[X]),
    enum_warning.
test(implies_true_proof,[fail]) :-
    solve_constraint(not(X > 5 => X > 4),[X]),
    \+ enum_warning.
:- end_tests(implications).

:- begin_tests(equivalence).
test(equivalence_true_find,[true(X == 6), nondet]) :-
    solve_constraint(X > 5 <=> X > 5,[X]),
    enum_warning.
test(equivalence_true_proof,[fail]) :-
    solve_constraint(not(X > 5 <=> X > 5),[X]),
    \+ enum_warning.
:- end_tests(equivalence).

:- begin_tests(all_solutions).
test(all_solutions_interval,[all(X == [6,7,8])]) :-
    solve_constraint(X > 5 & X < 9,[X]).
:- end_tests(all_solutions).

:- begin_tests(operator_precedences).
test(and_or_1,[all(X == [3])]) :-
    solve_constraint(X in 5 .. 8 or X = 3 & X < 4,[X]).
test(and_or_1_explicit,[all(X == [3])]) :-
    solve_constraint((X in 5 .. 8 or X = 3) & X < 4,[X]).
test(and_or_2,[all(X == [5,6,7,8,3])]) :-
    solve_constraint(X in 5 .. 8 or (X = 3 & X < 4),[X]).
test(equivalence_and_1,[nondet]) :-
    solve_constraint(not(X in -2 .. 2 <=> X > -3 & X<4),[X]),
    enum_warning.
test(equivalence_and_1_explicit,[nondet]) :-
    solve_constraint(not((X in -2 .. 2 <=> X > -3) & X<4),[X]),
    enum_warning.
test(equivalence_and_2,[all(X == [3])]) :-
    solve_constraint(not(X in -2 .. 2 <=> (X > -3 & X<4)),[X]).
:- end_tests(operator_precedences).
