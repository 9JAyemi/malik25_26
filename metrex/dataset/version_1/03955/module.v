module and_gate (
    input A1,
    input A2,
    input VPWR,
    input VGND,
    output Y
);

    and_gate_inst and_gate_inst (
        .Y(Y),
        .A1(A1),
        .A2(A2),
        .B1(1'b1), // connect to 1 for AND gate
        .C1(1'b0), // connect to 0 for AND gate
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(1'b0), // not used in AND gate
        .VNB(1'b0)  // not used in AND gate
    );

endmodule

module and_gate_inst (
    output Y,
    input A1,
    input A2,
    input B1,
    input C1,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign Y = (A1 & A2) & B1 & !C1;

endmodule