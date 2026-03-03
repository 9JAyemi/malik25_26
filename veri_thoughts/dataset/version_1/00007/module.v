module nor4b_4_input (
    Y,
    A,
    B,
    C,
    D_N
);

    output Y;
    input A, B, C, D_N;

    assign Y = ~( A | B | C| D_N);

endmodule