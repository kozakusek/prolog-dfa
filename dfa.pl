% Author: Barłomiej Kozaryna
% Id: bk418339

% Definition: Reaching States are states that have path to any goal state.
% Innner representation of the DFA:
% repr(Fun, Start, Ends, RStates, Alphabet, AStates, Transitions)
% Fun - balanced BST of transitions on reaching states
% Start - a single term
% Ends - sorted list of accepting states
% RStates - BST of reaching states
% Alphabet - sorted list of symbols
% AStates - sorted list of all states
% Transitions - BST of all transitions

% correct(+A, -Repr)
correct(dfa(Trans, Start, Ends), 
        repr(SortedF, Start, Ends2, RStates, Alpha, States, TransBST)) :-
    ground((Trans, Start, Ends)),
    is_set(Ends, _),

    dfa_params(Trans, [Start|Ends], SortedTrans, States, Alpha),
    is_total_fun(Trans, States, Alpha),

    reversed_graph(SortedTrans, RevTrans),
    list_to_BST(RevTrans, RevTransBST),
    reachable_states(RevTransBST, Ends, nil, RStates),
    list_from_BST(RStates, SRStates),
    is_crossprod(SRStates, Alpha, ArgsSet),
    sorted_to_BST(SortedTrans, TransBST),
    fun_from_domain(TransBST, ArgsSet, Fun),
    remove_states_from_fun(Fun, RStates, Fun2),
    !, % There is only one correct representation of function as sorted list.
    sorted_to_BST(Fun2, SortedF),
    sort(Ends, Ends2).

% accept(+A, ?W)
accept(Automaton, Word) :-
    correct(Automaton, repr(Fun, Start, Ends, _, _, _, _)),
    not_empty_repr(repr(Fun, Start, Ends, _, _, _, _)),
    (has_cycle(Fun, Start) -> 
        (!, accept_inf(Fun, Start, Ends, Word));
        (!, accept_fin(Fun, Start, Ends, Word))).

% accept_inf(+F, ?S, ?E, ?W)
% Accept version for automata with infinite language.
accept_inf(_, State, EndStates, []) :-
    member(State, EndStates).
accept_inf(Fun, State, EndStates, [Step|Steps]) :-
    accept_inf(Fun, Next, EndStates, Steps),
    traverse_BST(Fun, fp(State, Step, Next)).

% accept_fin(+F, ?S, ?E, ?W)
% Accept version for automata with finite language.
accept_fin(_, State, EndStates, []) :-
    member(State, EndStates).
accept_fin(Fun, State, EndStates, [Step|Steps]) :-
    traverse_BST(Fun, fp(State, Step, Next)),
    accept_fin(Fun, Next, EndStates, Steps).

% empty(+A)
empty(A) :- 
    correct(A, repr(_, Start, _, States, _, _, _)),
    \+ member_BST(States, Start).

% equal(+A1, +A2)
equal(A1, A2) :- 
    subsetEq(A1, A2), 
    subsetEq(A2, A1).

% subsetEq(+A1, +A2)
subsetEq(A1, A2) :-
    correct(A1, R1),
    correct(A2, R2),
    complement(R2, R3),
    intersection(R1, R3, Irepr),
    !, % There exists only one correct A' x B, hence no need to backtrack.
    \+ not_empty_repr(Irepr).


%%%% Auxiliary predicates %%%%

% list_to_BST(+List, -BST)
% Transforms List into BST.
list_to_BST(L, T) :- 
    sort(L, SL),
    sorted_to_BST(SL, T).

% sorted_to_BST(+List, -BST)
% Transforms sorted List into BST.
sorted_to_BST([], nil).
sorted_to_BST(L, bst(T1, M, T2)) :-
    splits(L, L1, M ,L2),
    sorted_to_BST(L1, T1),
    sorted_to_BST(L2, T2).

% list_from_BST(+BST, -List)
% Transforms BST into List.
list_from_BST(T, L) :- list_from_BST(T, [], L).
list_from_BST(nil, L, L).
list_from_BST(bst(T1, M, T2), Acc, L) :-
    list_from_BST(T2, Acc, L1),
    list_from_BST(T1, [M|L1], L).

% splits(+List, ?L1, ?M, ?L2)
% Check if List is concatenation of L1, [M] L2, 
% where M is a middle element of List.
splits(L, L1, M, L2) :-
    length(L, N),
    H is N // 2,
    nprefix(H, L, L1), 
    !, % There exists only one correct prefix of length N // 2.
    append(L1, [M|L2], L).

% member_BST(+BST, +E)
% Check if E is a member of BST. 
member_BST(bst(_, E, _), E). 
member_BST(bst(L, M, _), E) :- 
    E @< M, 
    member_BST(L, E).
member_BST(bst(_, M, R), E) :- 
    E @> M, 
    member_BST(R, E).

% insert_BST(+BST, +E, -NewBST)
% Insert E into BST and return NewBST.
insert_BST(nil, E, bst(nil, E, nil)).
insert_BST(bst(_, E, _), E, bst(_, E, _)).
insert_BST(bst(L1, M, R), E, bst(L2, M, R)) :- 
    E @< M,
    insert_BST(L1, E, L2).
insert_BST(bst(L, M, R), E, bst(L, M, R2)) :-
    E @> M, 
    insert_BST(R, E, R2).

% delete_BST(+BST, +E, -NewBST)
% Delete E from BST and return NewBST.
delete_BST(nil, _, nil).
delete_BST(bst(nil, E, R), E, R).
delete_BST(bst(L, E, nil), E, L).
delete_BST(bst(nil, M, nil), E, bst(nil, M, nil)) :- 
    M \= E.
delete_BST(bst(L, E, R), E, bst(L, V, R2)) :-
    min_BST(R, V),
    delete_BST(R, V, R2).
delete_BST(bst(L1, M, R), E, bst(L2, M, R)) :- 
    E @< M, 
    delete_BST(L1, E, L2).
delete_BST(bst(L, M, R), E, bst(L, M, R2)) :-
    E @> M,
    delete_BST(R, E, R2).

% leftmost_BST(+BST, -V)
% Return the smallest value in BST.
min_BST(bst(nil, V, _), V).
min_BST(bst(L,_,_), V) :-
    min_BST(L, V).

% traverse_BST(+BST, ?E)
% Check if binary tree contains E.
traverse_BST(bst(_, E, _), E).
traverse_BST(bst(L, _, _), E) :- 
    traverse_BST(L, E).
traverse_BST(bst(_, _, R), E) :- 
    traverse_BST(R, E).

% is_total_fun(+F, +S, +A)
% Check whether F is a total function from SxA.
is_total_fun(Fun, [S|Ss], [A|As]) :-
    args(Fun, Args),
    is_set(Args, ArgSet),
    is_crossprod([S|Ss], [A|As], ArgSet).

% remove_states_from_fun(+F, +S, -NewF)
% Removes states not in S, from codomain of F.
remove_states_from_fun([], _, []).
remove_states_from_fun([fp(X, A, Y)|F1s], States, [fp(X, A, Y)|F2s]) :-
    member_BST(States, Y),
    remove_states_from_fun(F1s, States, F2s).
remove_states_from_fun([fp(_, _, _)|Fs], S, F) :-
    remove_states_from_fun(Fs, S, F). 

% fun_from_domain(+T, +S, -NewF)
% Given transition system T and set of states S, returns a function F.
fun_from_domain(_, [], []).
fun_from_domain(Trans, [[X, A]|Args], [fp(X, A, Y)|T]) :-
    member_BST(Trans, fp(X, A, Y)),
    fun_from_domain(Trans, Args, T).

% reversed_graph(+G1, -G2)
% Returns G2, obtained from G1 by reversing the direction of edges.
reversed_graph([], []).
reversed_graph([fp(X, A, Y)|T1], [fp(Y, A, X)|T2]) :- 
    reversed_graph(T1, T2).

% reachable_states(+G, +S, +R1, -R2)
% Returns R2, obtained from R1 by adding states reachable from S in G.
reachable_states(_, [], RS, RS).
reachable_states(G, [V|Vs], RS0, RS3) :-
    insert_BST(RS0, V, RS1),
    dfw(G, [V], RS1, RS2),
    reachable_states(G, Vs, RS2, RS3).

% dfw(+G, +S, +V1, -V2)
% Returns V2, obtained from V1 by adding states reachable from S in G,
% performing depth-first walk.
dfw(_, [], Visited, Visited).
dfw(G, [V|Vs], Visited, VisitedAfter) :-
    neighbours(G, V, N),
    subtract_BST_from_list(N, Visited, N2),
    add_list_to_BST(N2, Visited, Visited2),
    append(N2, Vs, Vs2),
    dfw(G, Vs2, Visited2, VisitedAfter).

% neighbours(+G, +V, -N)
% Returns N, which is the list of neighbours of V in G.
neighbours(G, V, N) :-
    neighbours(G, V, N, _).
neighbours(G, V, [N|Ns], G3) :-
    member_BST(G, fp(V, _, N)),
    delete_BST(G, fp(V, _, N), G2),
    !, % There exists only one G2 resulting from this deletion.
    neighbours(G2, V, Ns, G3).
neighbours(G, V, [], _) :- 
    \+ member_BST(G, fp(V, _, _)).

% nprefix(+N, +List, ?SubList)
% Check if SubList is a prefix of List of length N.
nprefix(N, _, []) :-
    N =< 0.
nprefix(_, [], []).
nprefix(N, [X|Xs], [X|Ys]) :- 
    M is N-1, 
    nprefix(M, Xs, Ys).

% args(+Function_List, -Argument_List)
% Given a list representing a function: fp(A, B, C) equivalent to (A, B) -> C,
% returns a list of its arguments in [[A,B]] format.
args([], []).
args([fp(A, B, _)|T], [[A, B]|T1]) :-
    args(T, T1).

% states(+Function_List, -State_List)
% Given a list of transtitions: fp(A, B, C) equivalent to A -B-> C,
% returns a list of its states.
states([], []).
states([fp(A, _, C)|T], [A, C|ST]) :-
    states(T, ST).

% alphabet(+Function_List, -Alphabet)
% Given a list of transtitions: fp(A, B, C) equivalent to A -B-> C,
% returns a list of its input symbols.
alphabet([], []).
alphabet([fp(_, B, _)|T], [B|AT]) :-
    alphabet(T, AT).

% is_crossprod(+A, +B, ?AB)
% Check if AB is a cross product of A and B.
is_crossprod([], _, []).
is_crossprod([A|As], Bs, C) :- 
    prepends_all(A, Bs, C1),
    is_crossprod(As, Bs, C2),
    append(C1, C2, C).

% prepends_all(?A, ?B, ?AB)
% Check if alle elements of AB are elements from B with A prepended.
prepends_all(_, [], []).
prepends_all(E, [H|T], [[E,H]|T1]) :-
    prepends_all(E, T, T1).

% is_set(+List, -Set)
% Given a list, returns a sorted list of its elements.
% Fails if the list had duplicates.
is_set(Lst, Set) :-
    sort(Lst, Set),
    length(Lst, N),
    length(Set, N).

% dfa_params(+Trans, +Special, -F, -S, -A)
% Given a list of transitions Trans and known states Special,
% return sorted DFA params: Alphabet A, States S, Transition Function F.
dfa_params(Trans, SpecialStates, SortedF, StatesSet, AlphabetSet) :-
    states(Trans, States), 
    append(States, SpecialStates, States2), 
    sort(States2, StatesSet),
    alphabet(Trans, Alphabet),
    sort(Alphabet, AlphabetSet),
    sort(Trans, SortedF).

% exists_path(+G, +A, +B, +V)
% Check if in G exists a path from A to B ommiting all vertices in V.
exists_path(_, A, A, _).
exists_path(Graph, A, B, Visited) :-
    member_BST(Graph, fp(A, _, X)),
    \+ member_BST(Visited, X),
    insert_BST(Visited, X, Visited2),
    exists_path(Graph, X, B, Visited2).

% not_empty_rerpr(+A)
% Same as not_empty, but takes the inner representation as input.
not_empty_repr(repr(Fun, Start, Ends, _, _, _, _)) :- 
    member(End, Ends),
    exists_path(Fun, Start, End, nil).

% subtract_BST_from_list(+L1, +T, -L2)
subtract_BST_from_list([], _, []).
subtract_BST_from_list([H|T1], BST, [H|T2]) :-
    \+ member_BST(BST, H),
    subtract_BST_from_list(T1, BST, T2).
subtract_BST_from_list([_|T1], BST, L) :- 
    subtract_BST_from_list(T1, BST, L).

% add_list_to_BST(+L, +T1, -T2)
add_list_to_BST([], T, T).
add_list_to_BST([H|T], BST0, BST2) :-
    insert_BST(BST0, H, BST1),
    add_list_to_BST(T, BST1, BST2).

% has_cycle(+G, +V)
% has_cycle(G, V) checks whether G has any cycles, starting from V.
has_cycle(G, V) :- 
    has_cycle(G, V, nil).
has_cycle(_, V, Visited) :- 
    member_BST(Visited, V).
has_cycle(G, V, Visited) :-
    traverse_BST(G, fp(V,_,X)),
    insert_BST(Visited, V, Visited2),
    has_cycle(G, X, Visited2).

% sorted_sets_diff(+A, +B, ?C)
% Check whether A \ B = C, assuming A, B and C are represented as sorted lists.
sorted_sets_diff([], _, []) .
sorted_sets_diff(A, [], A).
sorted_sets_diff([H|T], [H|T1], L) :- 
    sorted_sets_diff(T, T1, L).
sorted_sets_diff([H|T], [H1|T1], L) :- 
    H1 @> H,
    sorted_sets_diff(T, [H1|T1], L1),
    append([H], L1, L).
sorted_sets_diff([H|T], [H1|T1], L) :- 
    H1 @< H,
    sorted_sets_diff([H|T], T1, L).

% complement(+A, ?B)
% Check if A' = B.
complement(repr(_, S, Ends, _, A, States, Trans), 
           repr(Trans, S, Ends2, States, A, States, Trans)) :-
    sorted_sets_diff(States, Ends, Ends2).

% intersection(+A, +B, ?C)
% Check if automaton C is an intersection of automata A and B.
intersection(repr(_, S1, E1, _, A, St1, F1), 
             repr(_, S2, E2, _, A, St2, F2), 
             repr(F3, [S1, S2], E3, St3, A, St3, F3)) :-
    is_crossprod(St1, St2, St3),
    is_crossprod(E1, E2, E3),
    cross_fun(St3, A, F1, F2, F3List),
    sorted_to_BST(F3List, F3).

% cross_fun(+States, +Alphabet, +F1, +F2, -F3)
% Given a list of states States, an alphabet Alphabet and two transition
% functions F1 and F2, returns a list of transition functions F3,
% representing the cross product of F1 and F2.
cross_fun([], _, _, _, []).
cross_fun([State|States], A, F1, F2, F3) :-
    sub_cross_fun(State, A, F1, F2, This),
    cross_fun(States, A, F1, F2, Rest),
    append(This, Rest, F3).

% sub_cross_fun(+State, +Alphabet, +F1, +F2, -F3)
% Given a state State, an alphabet Alphabet and two transition functions F1
% and F2, returns a list of transition functions F3, representing the
% subset of the cross product of F1 and F2.
sub_cross_fun([_, _], [], _, _, []).
sub_cross_fun([S1, S2], [HA|TA], F1, F2, [fp([S1, S2], HA, [X, Y])|TF3]) :-
    member_BST(F1, fp(S1, HA, X)),
    member_BST(F2, fp(S2, HA, Y)),
    sub_cross_fun([S1, S2], TA, F1, F2, TF3).
