
module nand3b_inverted (
    Y,
    A,
    B,
    C,
    invert,
    out_inv
);

    output Y;
    input A;
    input B;
    input C;
    input invert;
    output out_inv;

    wire A_inverted;

    assign out_inv = ~A & invert | A & ~invert;
    assign A_inverted = ~A;

    nand (Y, A_inverted, B, C);

endmodule