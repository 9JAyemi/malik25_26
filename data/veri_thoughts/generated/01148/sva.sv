module and3b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // Note: Combinational DUT with no clock/reset; sample on any edge of A_N/B/C.

    // X is 1 when A_N, B, and C are all 1.
    check_all_ones_gives_one: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (A_N === 1'b1 && B === 1'b1 && C === 1'b1) |=> (X === 1'b1)
    );

    // A_N at 0 forces X to 0.
    check_a0_forces_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (A_N === 1'b0) |=> (X === 1'b0)
    );

    // B at 0 forces X to 0.
    check_b0_forces_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (B === 1'b0) |=> (X === 1'b0)
    );

    // C at 0 forces X to 0.
    check_c0_forces_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (C === 1'b0) |=> (X === 1'b0)
    );

    // If X is 1, then A_N, B, and C must all be 1.
    check_x1_implies_all_ones: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (X === 1'b1) |=> (A_N === 1'b1 && B === 1'b1 && C === 1'b1)
    );

    // If X is 0, then at least one input is 0.
    check_x0_implies_some_zero: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (X === 1'b0) |=> ((A_N === 1'b0) || (B === 1'b0) || (C === 1'b0))
    );

    // If some input is X/Z, and no input is 0, and not all are 1, then X is unknown.
    check_someX_no_zero_not_all1_implies_xX: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            ($isunknown({A_N,B,C}) &&
             !((A_N === 1'b0) || (B === 1'b0) || (C === 1'b0)) &&
             !((A_N === 1'b1) && (B === 1'b1) && (C === 1'b1))) |=> $isunknown(X)
    );

    // If X is unknown, then some input is X/Z, no input is 0, and not all are 1.
    check_xX_implies_someX_no_zero_not_all1: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            $isunknown(X) |=> ($isunknown({A_N,B,C}) &&
                               !((A_N === 1'b0) || (B === 1'b0) || (C === 1'b0)) &&
                               !((A_N === 1'b1) && (B === 1'b1) && (C === 1'b1)))
    );

    // When all inputs are known (0/1), X is not unknown.
    check_no_x_when_inputs_known: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (!$isunknown({A_N,B,C})) |=> (!$isunknown(X))
    );

    // If A_N is X/Z and B,C are 1, X is unknown.
    check_ax_bc1_implies_xX: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (($isunknown(A_N)) && (B === 1'b1) && (C === 1'b1)) |=> $isunknown(X)
    );

    // If B is X/Z and A_N,C are 1, X is unknown.
    check_bx_ac1_implies_xX: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (($isunknown(B)) && (A_N === 1'b1) && (C === 1'b1)) |=> $isunknown(X)
    );

    // If C is X/Z and A_N,B are 1, X is unknown.
    check_cx_ab1_implies_xX: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C)
            (($isunknown(C)) && (A_N === 1'b1) && (B === 1'b1)) |=> $isunknown(X)
    );

endmodule