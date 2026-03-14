
module nor4 (
    output Y,
    input A,
    input B,
    input C,
    input D
);

    wire w1, w2, w3;

    nor (w1, A, B);
    nor (w2, w1, C);
    nor (w3, w2, D);

    assign Y = ~w3;

endmodule
