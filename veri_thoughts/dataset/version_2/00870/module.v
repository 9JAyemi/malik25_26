
module and_nand (
    Y,
    A1,
    A2,
    A3,
    B1,
    B2
);

    // Module ports
    output Y;
    input A1;
    input A2;
    input A3;
    input B1;
    input B2;

    // Module supplies
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB;
    supply0 VNB;

    // Local signals
    wire nand0_out;
    wire nand1_out;

    // NAND gates
    nand nand0 (nand0_out, A1, A2, A3);
    nand nand1 (nand1_out, B1, B2);

    // AND gate
    assign Y = nand0_out & nand1_out;

endmodule
