---- MODULE Counter_Finite ----
EXTENDS Naturals

LIMIT == 100

VARIABLE cnt


Init == cnt = 0

Next == 
    \/
        /\ cnt < LIMIT
        /\ cnt' = cnt + 1
    \/
        /\ cnt >= LIMIT
        /\ cnt' = cnt
====
