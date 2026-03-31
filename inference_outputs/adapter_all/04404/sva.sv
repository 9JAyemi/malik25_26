module or3_2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must equal the OR of all pairwise AND terms.
    check_x_matches_pairwise_or: assert property (
        @(posedge clk) X == ((A & B) | (A & C) | (B & C))
    );

    // If A and B are high, X must be high.
    check_ab_sets_x: assert property (
        @(posedge clk) (A & B) |-> X
    );

    // If A and C are high, X must be high.
    check_ac_sets_x: assert property (
        @(posedge clk) (A & C) |-> X
    );

    // If B and C are high, X must be high.
    check_bc_sets_x: assert property (
        @(posedge clk) (B & C) |-> X
    );

    // If no pair is high, X must be low.
    check_no_pair_sets_x_low: assert property (
        @(posedge clk) !(A & B & C) |-> !X
    );

    // X high requires at least one pair to be high.
    check_x_high_requires_pair: assert property (
        @(posedge clk) X |-> (A & B) | (A & C) | (B & C)
    );

    // X low means no pair is high.
    check_x_low_means_no_pair: assert property (
        @(posedge clk) !X |-> !(A & B & C)
    );

    // VGND is tied low.
    check_vgnd_tied_low: assert property (
        @(posedge clk) VGND == 1'b0
    );

    // VPWR is tied high.
    check_vpwr_tied_high: assert property (
        @(posedge clk) VPWR == 1'b1
    );

    // VPB is tied high.
    check_vpb_tied_high: assert property (
        @(posedge clk) VPB == 1'b1
    );

    // VNB is tied low.
    check_vnb_tied_low: assert property (
        @(posedge clk) VNB == 1'b0
    );

endmodule