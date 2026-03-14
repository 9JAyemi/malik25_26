module and2_4 (
    output X,
    input  A,
    input  B
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;

    and2 base (
        .X(X),
        .A(A),
        .B(B)
    );

endmodule

module and2 (
    output X,
    input A,
    input B
);

    assign X = A & B;

endmodule