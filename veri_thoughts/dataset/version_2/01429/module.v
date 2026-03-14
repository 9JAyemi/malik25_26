
module and_gate_power_good (
    X,
    A,
    B,
    VPWR,
    VGND,
    VPB,
    VNB
);

    // Module ports
    output X;
    input A;
    input B;
    input VPWR;
    input VGND;
    input VPB;
    input VNB;

    // Local signals
    wire and_out;

    // AND gate
    assign and_out = A & B;

    // Buffer
    buf (
        .A(and_out),
        .X(X)
    );

endmodule