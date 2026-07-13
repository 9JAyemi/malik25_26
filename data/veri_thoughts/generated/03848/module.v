module or4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire Y1, Y2, Y3;

    or Gate1 (
        Y1,
        A,
        B
    );

    or Gate2 (
        Y2,
        C,
        D
    );

    or Gate3 (
        Y3,
        Y1,
        Y2
    );

    assign X = Y3;

endmodule