
tff(list_typz, type, ( list : $tType > $tType ) ).

tff(cons_type, type, ( cons : !> [A : $tType ] : ( ( A * list(A) ) > list(A) ) ) ).

tff(nil_type, type, ( nil : !> [A : $tType ] : list(A) ) ).

tff(car_type, type, ( car : !> [A : $tType ] : ( list(A) > A ) ) ).

tff(cdr_type, type, ( cdr : !> [A: $tType ] : ( list(A) > list(A) ) ) ).

tff(car_axiom, axiom,
    (! [A : $tType, X: A , L: list(A) ] : (car(A, cons(A, X, L)) = X))).

tff(cons_axiom, axiom,
    (! [A : $tType, X: A , L: list(A) ] : (cdr(A, cons(A, X, L)) = L))).

tff(hyp_3, conjecture,
    (! [V_x1: $i , V_y1: list($i) , V_x2: $i , V_y2: list($i) ] :
       ((cons($i, V_x1, V_y1) = cons($i, V_x2, V_y2))
       => ((V_x1 = V_x2) & (V_y1 = V_y2))))).

