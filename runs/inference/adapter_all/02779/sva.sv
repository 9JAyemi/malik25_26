module sky130_fd_sc_lp__a32o_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must match the implemented AND-of-nots equation.
    check_x_matches_function: assert property (
        @(posedge clk) X == (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB)
    );

    // A high X requires all active-low terms to be true.
    check_x_high_requires_all_terms: assert property (
        @(posedge clk) X |-> (A1 & ~A2 & ~A3 & ~B1 & ~B2 & ~VPWR & ~VGND & ~VPB & ~VNB)
    );

    // A1 low forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk) !A1 |-> !X
    );

    // A2 high forces X low.
    check_a2_high_forces_x_low: assert property (
        @(posedge clk) A2 |-> !X
    );

    // A3 high forces X low.
    check_a3_high_forces_x_low: assert property (
        @(posedge clk) A3 |-> !X
    );

    // B1 high forces X low.
    check_b1_high_forces_x_low: assert property (
        @(posedge clk) B1 |-> !X
    );

    // B2 high forces X low.
    check_b2_high_forces_x_low: assert property (
        @(posedge clk) B2 |-> !X
    );

    // VPWR high forces X low.
    check_vpwr_high_forces_x_low: assert property (
        @(posedge clk) VPWR |-> !X
    );

    // VGND high forces X low.
    check_vgnd_high_forces_x_low: assert property (
        @(posedge clk) VGND |-> !X
    );

    // VPB high forces X low.
    check_vpb_high_forces_x_low: assert property (
        @(posedge clk) VPB |-> !X
    );

    // VNB high forces X low.
    check_vnb_high_forces_x_low: assert property (
        @(posedge clk) VNB |-> !X
    );

endmodule