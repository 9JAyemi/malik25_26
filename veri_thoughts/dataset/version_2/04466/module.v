
module nor4(
    output Y,
    input A,
    input B,
    input C,
    input D
);

    wire n1, n2;
    assign n1 = ~(A | B | C);
    assign n2 = ~(n1 | D | D);
    assign Y = ~n2;

endmodule
