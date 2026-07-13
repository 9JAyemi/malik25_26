module logical_and3b (
    A,
    B,
    C,
    X
);

    input  A;
    input  B;
    input  C;
    output X;
    
    assign X = A & B & C;

endmodule