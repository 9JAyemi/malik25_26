
module mux_4to1 (
    input A, B, C, D, S0, S1,
    output Y
);

    wire not_S0, not_S1, not_S0_and_not_S1, not_S0_and_S1, S0_and_not_S1, S0_and_S1;
    wire A_buf, B_buf, C_buf, D_buf;

    buf_6 buf_A (.A(A), .X(A_buf), .VPWR(1'b1), .VGND(1'b0), .VPB(1'b0), .VNB(1'b0));
    buf_6 buf_B (.A(B), .X(B_buf), .VPWR(1'b1), .VGND(1'b0), .VPB(1'b0), .VNB(1'b0));
    buf_6 buf_C (.A(C), .X(C_buf), .VPWR(1'b1), .VGND(1'b0), .VPB(1'b0), .VNB(1'b0));
    buf_6 buf_D (.A(D), .X(D_buf), .VPWR(1'b1), .VGND(1'b0), .VPB(1'b0), .VNB(1'b0));

    assign not_S0 = ~S0;
    assign not_S1 = ~S1;
    assign not_S0_and_not_S1 = not_S0 & not_S1;
    assign not_S0_and_S1 = not_S0 & S1;
    assign S0_and_not_S1 = S0 & not_S1;
    assign S0_and_S1 = S0 & S1;

    assign Y = not_S0_and_not_S1 & A_buf |
               not_S0_and_S1 & B_buf |
               S0_and_not_S1 & C_buf |
               S0_and_S1 & D_buf;

endmodule
module buf_6 (
    input A,
    output X,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    assign X = A;

endmodule