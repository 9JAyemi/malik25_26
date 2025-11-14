
module voltage_supply_circuit (
    X,
    A1,
    A2,
    A3,
    B1,
    C1
);

    output X;
    input A1;
    input A2;
    input A3;
    input B1;
    input C1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Instantiate the gates
    wire X_int;
    nand3 U1 (A1, A2, A3, X_int);
    nand2 U2 (B1, C1, X);

endmodule

module nand3 (
    input A,
    input B,
    input C,
    output Y
);

    assign Y = ~(A & B & C);
endmodule

module nand2 (
    input A,
    input B,
    output Y
);

    assign Y = ~(A & B);
endmodule
