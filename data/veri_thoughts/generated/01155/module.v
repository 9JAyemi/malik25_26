module and4_2and (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire AB;
    wire CD;
    wire ABCD;

    and and1 (
        AB,
        A,
        B
    );

    and and2 (
        CD,
        C,
        D
    );

    and and3 (
        ABCD,
        AB,
        CD
    );

    assign X = ABCD;

endmodule