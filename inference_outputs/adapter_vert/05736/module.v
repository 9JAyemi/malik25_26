module xnor2 (
    Y,
    A,
    B
);

    output Y;
    input  A;
    input  B;

    assign Y = ~(A ^ B);

endmodule