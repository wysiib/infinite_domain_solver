:- module(infinite_domain_solver,[solve_constraint/2, enum_warning/0]).

:- use_module(high_level_reasoner).

:- use_module(library(clpfd)).
:- use_module(library(lists)).

:- op(870,xfy,'=>').
:- op(820,xfy,'<=>').
:- op(860,xfy,'&').
:- op(850,xfy,'or').

:- dynamic enum_warning/0.

solve_constraint(Constraint,TopLevelVars) :-
    retractall(enum_warning),
    solve(Constraint,ExistsWF,AllWF),
    ground_vars(TopLevelVars,ExistsWF,AllWF).

ground_vars(TopLevelVars,ExistsWF,AllWF) :-
    %alarm(15,throw(time_out),Id,[remove(true)]),
    maplist(enumerate_exists_aux,TopLevelVars),
    ground_wfs(ExistsWF,AllWF).

solve(A & B,EWF,AWF) :- solve(A,EWF,AWF), solve(B,EWF,AWF).
solve(A or B,EWF,AWF) :- solve(A,EWF,AWF) ; solve(B,EWF,AWF).
solve(A <=> B,EWF,AWF) :-
    solve(A,EWF,AWF), solve(B,EWF,AWF) ;
    solve_not(A,EWF,AWF), solve_not(B,EWF,AWF).
solve(A => B,EWF,AWF) :- solve_not(A,EWF,AWF) ; solve(B,EWF,AWF).
solve(not(A),EWF,AWF) :- solve_not(A,EWF,AWF).
solve(V in D,_,_) :- V in D.
solve(A = B,_,_) :-
    compute_exprs(A,B,AE,BE),
    AE #= BE.
solve(A >= B,_,_) :-
    compute_exprs(A,B,AE,BE),
    leq(B,A),
    AE #>= BE.
solve(A > B,_,_) :-
    compute_exprs(A,B,AE,BE),
    lt(B,A),
    AE #> BE.
solve(A =< B,_,_) :-
    compute_exprs(A,B,AE,BE),
    leq(A,B),
    AE #=< BE.
solve(A < B,_,_) :-
    compute_exprs(A,B,AE,BE),
    lt(AE,BE),
    AE #< BE.

solve(forall(X,LHS => RHS),_EWF,AWF) :-
    when(ground(AWF),enumerate_forall(X,LHS,RHS)).
solve(exists(X,RHS),EWF,_AWF) :-
    when(ground(EWF),enumerate_exists(X,RHS)).

compute_exprs(A,B,AE,BE) :- compute_expr(A,AE), compute_expr(B,BE).
compute_expr(X,X) :- var(X), !.
compute_expr(X,X) :- number(X), !.
compute_expr(A + B,E) :- !,
    compute_expr(A,AE),
    compute_expr(B,BE),
    E #= AE + BE.
compute_expr(A - B,E) :- !,
    compute_expr(A,AE),
    compute_expr(B,BE),
    E #= AE - BE.
compute_expr(A * B,E) :- !,
    compute_expr(A,AE),
    compute_expr(B,BE),
    E #= AE * BE.
compute_expr(A / B,E) :- !,
    compute_expr(A,AE),
    compute_expr(B,BE),
    E #= AE / BE.
compute_expr(A mod B,E) :- !,
    compute_expr(A,AE),
    compute_expr(B,BE),
    E #= mod(AE,BE).

enumerate_forall(Var,LHS,RHS) :-
    LHS = (_ in Min .. Max),
    % setup inner constraints
    % there is a choicepoint here
    % to allow for different solutions to inner variables
    solve(LHS & RHS,NewEWF,NewAWF), !,
    ground_wfs(NewEWF,NewAWF),
    enumerate_forall_aux(Min,Max,Var).
% we need to enumerate all elements of
% an infinite domain -> exception
enumerate_forall_aux(_,sup,_) :- throw(enum_infinite).
enumerate_forall_aux(inf,_,_) :- throw(enum_infinite).
% domain is finite, try all elements
enumerate_forall_aux(Current,Max,Var) :-
    Current =< Max, !,
    try_forall_value(Current,Var), % does not bind variable
    Current2 is Current + 1,
    enumerate_forall_aux(Current2,Max,Var).
enumerate_forall_aux(_,_,_).

try_forall_value(Current,Var) :-
    \+ \+ (Current = Var).

enumerate_exists(Var,RHS) :-
    % setup inner constraints
    solve(RHS,NewEWF,NewAWF), !,
    ground_wfs(NewEWF,NewAWF),
    enumerate_exists_aux(Var).
enumerate_exists_aux(Var) :-
    fd_size(Var,sup), !,
    % we need to enumerate the elements of
    % an infinite domain.
    % however, we need to find just one element!
    assert(enum_warning),
    fd_inf(Var,Min), fd_sup(Var,Max),
    enumerate_infinite(Var,0,Min,Max).
enumerate_exists_aux(Var) :-
    indomain(Var).

enumerate_infinite(Var,Cur,_Min,Max) :-
    sup_inf_safe_lt(Cur,Max),
    Var = Cur.
enumerate_infinite(Var,Cur,Min,_Max) :-
    sup_inf_safe_lt(Min,-Cur),
    Var is -Cur.
enumerate_infinite(Var,Cur,Min,Max) :-
    Cur2 is Cur + 1,
    enumerate_infinite(Var,Cur2,Min,Max).

sup_inf_safe_lt(_,sup) :- !.
sup_inf_safe_lt(inf,_) :- !.
suf_inf_safe_lt(X,Y) :- X < Y.

solve_not(A & B,EWF,AWF) :- solve_not(A,EWF,AWF) ; solve_not(B,EWF,AWF).
solve_not(A or B,EWF,AWF) :- solve_not(A,EWF,AWF), solve_not(B,EWF,AWF).
solve_not(A <=> B,EWF,AWF) :-
    solve(A,EWF,AWF), solve_not(B,EWF,AWF) ;
    solve_not(A,EWF,AWF), solve(B,EWF,AWF).
solve_not(A => B,EWF,AWF) :- solve(A,EWF,AWF), solve_not(B,EWF,AWF).
solve_not(A in Inf..Sup,EWF,AWF) :-
    solve(A < Inf or A > Sup,EWF,AWF).
solve_not(not(A),EWF,AWF) :- solve(A,EWF,AWF).
solve_not(A = B,_,_) :-
    compute_exprs(A,B,AE,BE),
    AE #\= BE.
solve_not(A >= B,EWF,AWF) :- solve(A < B,EWF,AWF).
solve_not(A > B,EWF,AWF) :- solve(A =< B,EWF,AWF).
solve_not(A =< B,EWF,AWF) :- solve(A > B,EWF,AWF).
solve_not(A < B,EWF,AWF) :- solve(A >= B,EWF,AWF).
solve_not(forall(X,LHS => RHS),EWF,AWF) :-
    solve(exists(X,LHS & not(RHS)),EWF,AWF).
solve_not(exists(X,RHS),EWF,_AWF) :-
    when(ground(EWF),\+(enumerate_exists(X,RHS))).

ground_wfs(E,A) :-
    E = ground, A = ground.
