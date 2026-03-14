module custom_or3 (
    input A,
    input B,
    input C_N,
    output X
);

    wire w1, w2, w3, w4, w5, w6, w7, w8;

    or or1 (
        X,
        A,
        B,
        C_N
    );

    or or2 (
        w2,
        A,
        w1,
        C_N
    );

    or or3 (
        w3,
        w1,
        B,
        C_N
    );

    or or4 (
        w4,
        w1,
        w1,
        C_N
    );

    or or5 (
        w5,
        A,
        B,
        w1
    );

    or or6 (
        w6,
        A,
        w1,
        w1
    );

    or or7 (
        w7,
        w1,
        B,
        w1
    );

    or or8 (
        w8,
        w1,
        w1,
        w1
    );

    assign X = w8;

endmodule