:- module(random_permutations, [get_num_bits/3,
                                get_masks/3,
                                random_permutation_element/10
                                ]).

get_num_bits(Length,NextPower,NumBits) :-
    NumBitsP4 is ceil(log10(Length) / log10(4)),
    NextPower is 4**NumBitsP4,
    NumBits is (floor(log10(NextPower) / log10(2)) + 1) // 2.

get_masks(HalfNumBits,LeftMask,RightMask) :-
    RightMask is (1 << HalfNumBits) - 1,
    LeftMask is RightMask << HalfNumBits.

random_permutation_element(Index,MaxIndex,From,To,Seed,NumBits,LeftMask,RightMask,RandomElement,NextIndex) :-
    draw_index(Index,MaxIndex,Seed,NumBits,LeftMask,RightMask,From,To,DrawnElement,NextIndex),
    % working on a 4^x long interval. thus, we might pick a number that is too large
    % if this happens, we just pick a new one
    % to avoid context switching overhead, this is now done inside the C code
    RandomElement is DrawnElement + From.

draw_index(Idx,MaxIdx,Seed,HalfNumBits,LeftMask,RightMask,From,To,Rnd,NextIdx) :-
    draw_index_loop(Idx,MaxIdx,Seed,HalfNumBits,LeftMask,RightMask,From,To,IdxOut,Rnd),
    (IdxOut > MaxIdx -> fail ; NextIdx = IdxOut).

draw_index_loop(Idx,MaxIdx,Seed,HalfNumBits,LeftMask,RightMask,From,To,IdxOut,RndOut) :-
    Left2 is (Idx /\ LeftMask) >> HalfNumBits,
    Right2 is Idx /\ RightMask,
    feistel_rounds(Left2,Right2,Seed,RightMask,Left3,Right3),
    Rnd is (Left3 << HalfNumBits) \/ Right3,
    Idx2 is Idx + 1,
    (Rnd > To - From, Idx2 =< MaxIdx
     -> draw_index_loop(Idx2,MaxIdx,Seed,HalfNumBits,LeftMask,RightMask,From,To,IdxOut,RndOut)
     ;  IdxOut = Idx2, RndOut = Rnd).

feistel_rounds(Left,Right,Seed,RightMask,LeftOut,RightOut) :-
    LeftOut = Right,
    term_hash(Right,Hash),
    RightOut is Left xor Hash /\ RightMask.

% -------------------
% Testing predicates
% -------------------
:- use_module(library(system)).
shuffle(From,To) :-
    IntervalLength is To - From + 1,
    get_num_bits(IntervalLength,MaxIndex,NumBits),
    get_masks(NumBits,LeftMask,RightMask),
    % now(Seed),
    shuffle(From,0,To,MaxIndex,Seed,NumBits,LeftMask,RightMask).
shuffle(From,CurIdx,To,MaxIndex,Seed,NumBits,LeftMask,RightMask) :-
    random_permutation_element(CurIdx,MaxIndex,From,To,Seed,NumBits,LeftMask,RightMask,Drawn,NextIdx),
    format('Drawing index ~w resulted in ~w~n',[CurIdx,Drawn]),
    shuffle(From,NextIdx,To,MaxIndex,Seed,NumBits,LeftMask,RightMask).
shuffle(_,_,_,_,_,_,_,_).
