module my_nor4 (
    Y,
    A,
    B,
    C,
    D
);

    output Y;
    input  A;
    input  B;
    input  C;
    input  D;

    wire temp1, temp2, temp3;

    assign temp1 = ~(A | B);
    assign temp2 = ~(C | D);
    assign temp3 = ~(temp1 | temp2);
    assign Y = temp3;

endmodule