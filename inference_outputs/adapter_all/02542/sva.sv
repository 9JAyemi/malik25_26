module sky130_fd_sc_hs__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic Y
);
    // Y equals NAND of A_N and B.
    check_nand_function: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        Y == ~(A_N & B)
    );

    // When both inputs are HIGH, Y must be LOW.
    check_both_high_implies_y_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (A_N && B) |-> (Y == 1'b0)
    );

    // When A_N is LOW, Y must be HIGH.
    check_a_n_low_implies_y_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!A_N) |-> (Y == 1'b1)
    );

    // When B is LOW, Y must be HIGH.
    check_b_low_implies_y_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!B) |-> (Y == 1'b1)
    );

    // When A_N is HIGH and B is LOW, Y must be HIGH.
    check_a_n_high_b_low_implies_y_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (A_N && !B) |-> (Y == 1'b1)
    );

    // When A_N is LOW and B is HIGH, Y must be HIGH.
    check_a_n_low_b_high_implies_y_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (!A_N && B) |-> (Y == 1'b1)
    );

    // If Y is LOW, both inputs must be HIGH.
    check_y_low_implies_both_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (Y == 1'b0) |-> (A_N && B)
    );

    // If Y is HIGH, at least one input must be LOW.
    check_y_high_implies_not_both_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        (Y == 1'b1) |-> (!A_N || !B)
    );

    // With stable inputs, Y must remain stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        ($stable(A_N) && $stable(B)) |-> $stable(Y)
    );

    // With stable inputs, a change on VPWR must not affect Y.
    check_vpwr_change_no_effect: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        ($stable(A_N) && $stable(B) && $changed(VPWR)) |-> $stable(Y)
    );

    // With stable inputs, a change on VGND must not affect Y.
    check_vgnd_change_no_effect: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND)
        ($stable(A_N) && $stable(B) && $changed(VGND)) |-> $stable(Y)
    );
endmodule