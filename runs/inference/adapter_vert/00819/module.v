module and4 (
    input A,
    input B,
    input C,
    input D,
    output X
);

    wire X1;
    wire X2;

    and and_gate1 (
        X1,
        A,
        B
    );

    and and_gate2 (
        X2,
        C,
        D
    );

    assign X = X1 & X2;

endmodule