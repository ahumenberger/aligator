WHILE[True, 
    IF[True, 
        a := 2 (n + 1) (n + 3/2) a;
        b := 4 (n + 1) b;
        c := 1/2 (n + 3/2) c,
        IF[True,
            a := 2 a;
            b := 4 b;
            c := 1/2 c,
            a := 2 (n + 1)^3 (n + 3/2)^3 a;
            b := 4 (n + 1)^3 b;
            c := 1/2 (n + 3/2)^3 c
        ]
    ]
], LoopCounter -> n