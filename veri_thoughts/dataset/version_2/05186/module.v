module xor2 (
    input A,
    input B,
    output X
);

    assign X = A ^ B;

endmodule

module xor4 (
    output X,
    input A,
    input B,
    input C,
    input D
);

    // Voltage supply signals
    wire X1, X2;
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    xor2 u1 (.X(X1), .A(A), .B(B));
    xor2 u2 (.X(X2), .A(C), .B(D));
    xor2 u3 (.X(X), .A(X1), .B(X2));

endmodule