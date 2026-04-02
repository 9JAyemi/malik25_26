module and3b_sva (
    input wire A_N,
    input wire B,
    input wire C,
    input wire VPWR,
    input wire VGND,
    input wire VPB,
    input wire VNB,
    output wire X
);
    // Combinational logic: X is determined by A_N, B, and C
    // X is 1'b1 if A_N is 1'b1 and B and C are 1'b1
    // X is 1'b0 if A_N is 1'b0 or B or C is 1'b0
    // X is 1'bx otherwise
    combinational_logic: assert property (
        @(posedge VPB) disable iff (!VGND) (X == (A_N == 1'b1) && (B == 1'b1) && (C == 1'b1) ? 1'b1 :
                                           (A_N == 1'b0) || (B == 1'b0) || (C == 1'b0) ? 1'b0 :
                                           1'bx)
    );
endmodule