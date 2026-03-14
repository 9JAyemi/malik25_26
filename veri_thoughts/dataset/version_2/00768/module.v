module or_gate(
    input A,
    input B,
    input C,
    input D,
    output X
);


    or4 or_gate1 (.A(A), .B(B), .C(C), .D(D), .X(X));

endmodule

module or4 (
    input A,
    input B,
    input C,
    input D,
    output X
);


    assign X = A | B | C | D;

endmodule
