module and4_module (
    output X,
    input A,
    input B,
    input C,
    input D
);

    wire A_N;
    
    and4 and4_instance (
        .X(X),
        .a(A),
        .b(B),
        .c(C),
        .d(D)
    );

    assign A_N = ~A;

endmodule

module and4 (
    output X,
    input a,
    input b,
    input c,
    input d
);

    assign X = a & b & c & d;

endmodule