module three_input_or_gate (
    input A,
    input B,
    input C_N,
    output X,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire or_output;
    
    or_gate_3 or_gate (
        .X(or_output),
        .A(A),
        .B(B),
        .C_N(C_N),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    assign X = or_output;
    
endmodule

module or_gate_3 (
    input A,
    input B,
    input C_N,
    output X,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign X = A | B | ~C_N | VPWR | VGND | VPB | VNB;

endmodule

