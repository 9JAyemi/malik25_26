module MUX4X1 (
    A,
    B,
    C,
    D,
    S0,
    S1,
    Y
);

    input [3:0] A, B, C, D;
    input [1:0] S0, S1;
    output Y;

    wire sel1, sel2;

    // Select line logic
    assign sel1 = (S1 == 1'b0) ? A : B;
    assign sel2 = (S1 == 1'b0) ? C : D;

    // Output logic
    assign Y = (S0 == 1'b0) ? sel1 : sel2;

endmodule