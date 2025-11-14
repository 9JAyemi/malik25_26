module and4 (
    input A, B, C, D,
    output X
);

    wire W, Y;
    
    and and1(W, A, B);
    and and2(Y, C, D);
    and and3(X, W, Y);

endmodule