module sky130_fd_sc_ms__o21ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Y implements ~(B1 & (A1 | A2)).
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        Y == ~(B1 & (A1 | A2))
    );

    // B1 low forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A1 and A2 low force Y high.
    check_a1_a2_low_force_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // B1 high and any A high force Y low.
    check_b1_and_any_a_high_force_y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1))) |-> (Y == 1'b0)
    );

    // Y low implies B1 high and at least one A high.
    check_y_low_implies_inputs_true: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (Y == 1'b0) |-> ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

    // Y high implies B1 low or both A low.
    check_y_high_implies_inputs_false: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (Y == 1'b1) |-> ((B1 == 1'b0) || ((A1 == 1'b0) && (A2 == 1'b0)))
    );

    // With B1 high, Y equals ~(A1 | A2).
    check_b1_high_reduces_to_nor: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (B1 == 1'b1) |-> (Y == ~(A1 | A2))
    );

    // With B1 low, Y equals A1 | A2.
    check_b1_low_reduces_to_or: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        (B1 == 1'b0) |-> (Y == (A1 | A2))
    );

    // With B1 low and both A low, Y must be high.
    check_b1_low_a1_a2_low_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        ((B1 == 1'b0) && (A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // With B1 high and both A high, Y must be low.
    check_b1_high_a1_a2_high_y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge VPWR or negedge VPWR or posedge VGND or negedge VGND or posedge VPB or negedge VPB or posedge VNB or negedge VNB)
        ((B1 == 1'b1) && (A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );
endmodule