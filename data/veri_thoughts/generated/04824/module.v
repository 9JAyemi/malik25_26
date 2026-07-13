module and_gate (
    output Y,
    input  A, 
    input  B, 
    input  C, 
    input  D, 
    input  E, 
    input  VPWR, 
    input  VGND, 
    input  VPB, 
    input  VNB 
);

    assign Y = A & B & C & D & E & VPWR & VGND & VPB & VNB;

endmodule

module logic_gate (
    output Y,
    input  A1, 
    input  A2, 
    input  B1, 
    input  C1, 
    input  D1, 
    input  VPWR, 
    input  VGND, 
    input  VPB, 
    input  VNB 
);

    wire AND_out;
    and_gate AND_gate (
        .Y(AND_out),
        .A(A1),
        .B(A2),
        .C(B1),
        .D(C1),
        .E(D1),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    assign Y = AND_out;

endmodule