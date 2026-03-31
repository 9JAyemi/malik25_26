module mux4_1 (
    output Y,
    input D0, D1, D2, D3, S0, S1, VPWR, VGND, VPB, VNB
);

    wire X0, X1, X2, X3;
    
    mux2_1 mux0 (
        .X(X0),
        .A0(D0),
        .A1(D1),
        .S(S0),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    mux2_1 mux1 (
        .X(X1),
        .A0(D2),
        .A1(D3),
        .S(S0),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    mux2_1 mux2 (
        .X(X2),
        .A0(X0),
        .A1(X1),
        .S(S1),
        .VPWR(VPWR),
        .VGND(VGND),
        .VPB(VPB),
        .VNB(VNB)
    );
    
    assign Y = X2;
    
endmodule

module mux2_1 (
    output reg X,
    input A0, A1, S, VPWR, VGND, VPB, VNB
);

    always @(*) begin
        case(S)
            0: X = A0;
            1: X = A1;
            default: X = 1'bx;
        endcase
    end

endmodule