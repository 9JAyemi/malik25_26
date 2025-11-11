
module my_nand4 (
    Y,
    A,
    B,
    C,
    D
);

    output Y;
    input A;
    input B;
    input C;
    input D;

    wire Y1, Y2, Y3;

    nand (Y1, A, B, C, D);

    nand (Y2, Y1, 1'b1, 1'b1, 1'b1);

    nand (Y3, Y2, 1'b1, 1'b1, 1'b1);

    nand (Y, Y3, 1'b1, 1'b1, 1'b1);

endmodule