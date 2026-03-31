module mag_comparator (
    input [1:0] A,
    input [1:0] B,
    output EQ,
    output GT,
    output LT
);

    assign EQ = (A == B);
    assign GT = (A > B);
    assign LT = (A < B);

endmodule