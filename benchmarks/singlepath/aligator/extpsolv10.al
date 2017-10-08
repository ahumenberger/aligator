WHILE[True, 
    IF[True, 
        a := 2 (n + 1) (n + 3/2) a;
        b := 4 (n + 1) b;
        c := 1/2 (n + 3/2) c,
        IF[True,
            a := 2 a;
            b := 4 b;
            c := 1/2 c,
            IF[True,
                a := 2 (n + 1)^3 (n + 3/2)^3 a;
                b := 4 (n + 1)^3 b;
                c := 1/2 (n + 3/2)^3 c,
                IF[True,
                    a := 2 a;
                    b := 4 b;
                    c := 1/2 c,
                    IF[True,
                        a := 2 (n + 1)^5 (n + 3/2)^3 a;
                        b := 4 (n + 1)^5 b;
                        c := 1/2 (n + 3/2)^3 c,
                        IF[True,
                            a := 2 a;
                            b := 4 b;
                            c := 1/2 c,
                            IF[True,
                                a := 2 (n + 1)^7 (n + 3/2)^7 a;
                                b := 4 (n + 1)^7 b;
                                c := 1/2 (n + 3/2)^7 c,
                                IF[True,
                                    a := 2 a;
                                    b := 4 b;
                                    c := 1/2 c,
                                    IF[True,
                                        a := 2 (n + 1)^9 (n + 3/2)^9 a;
                                        b := 4 (n + 1)^9 b;
                                        c := 1/2 (n + 3/2)^9 c,
                                        a := 2 a;
                                        b := 4 b;
                                        c := 1/2 c
                                    ]
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]
    ]
], LoopCounter -> n