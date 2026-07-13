module my_module(
    input in1,
    input in2,
    input in3,
    output out1
);

    wire X;
    wire A1 = in1;
    wire A2 = in2;
    wire B1 = in3;

    
    a21o_4 base (
        .X(X),
        .A1(A1),
        .A2(A2),
        .B1(B1)
    );
    
    assign out1 = X & ~B1;

endmodule

module a21o_4 (
    output X,
    input A1,
    input A2,
    input B1
);

    // Implement the AND-OR-INVERT functionality
    assign X = ~((A1 & A2) | B1);

endmodule
