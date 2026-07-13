module buf_4_xor (
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    wire a_xor_b;
    wire c_xor_d;
    wire a_xor_b_xor_c_xor_d;
    
    buf_4 u1 (
        .X(a_xor_b),
        .A(A),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    buf_4 u2 (
        .X(c_xor_d),
        .A(C),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    buf_4 u3 (
        .X(a_xor_b_xor_c_xor_d),
        .A(a_xor_b),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    buf_4 u4 (
        .X(X),
        .A(a_xor_b_xor_c_xor_d ^ D),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );

endmodule

module buf_4 (
    output X,
    input A,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign X = A & VPWR & VGND & VPB & VNB;

endmodule