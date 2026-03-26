module inputiso1n_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic SLEEP_B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X matches the RTL combinational equation.
    check_x_matches_rtl_function: assert property (
        @(posedge clk) X == ((A ^ VPWR) & (SLEEP_B ^ VGND) & VPWR & VGND & VPB & VNB)
    );

    // A high X requires all power-related terms to be high.
    check_x_high_requires_power_terms: assert property (
        @(posedge clk) X |-> (VPWR & VGND & VPB & VNB)
    );

    // A high X requires the A isolation term to be high.
    check_x_high_requires_a_iso_term: assert property (
        @(posedge clk) X |-> (A ^ VPWR)
    );

    // A high X requires the SLEEP_B isolation term to be high.
    check_x_high_requires_sleep_iso_term: assert property (
        @(posedge clk) X |-> (SLEEP_B ^ VGND)
    );

    // Low VPWR forces X low.
    check_low_vpwr_forces_x_low: assert property (
        @(posedge clk) !VPWR |-> !X
    );

    // Low VGND forces X low.
    check_low_vgnd_forces_x_low: assert property (
        @(posedge clk) !VGND |-> !X
    );

    // Low VPB forces X low.
    check_low_vpb_forces_x_low: assert property (
        @(posedge clk) !VPB |-> !X
    );

    // Low VNB forces X low.
    check_low_vnb_forces_x_low: assert property (
        @(posedge clk) !VNB |-> !X
    );

    // Matching A and VPWR makes the A isolation term zero.
    check_a_equal_vpwr_blocks_x: assert property (
        @(posedge clk) (A == VPWR) |-> !X
    );

    // Matching SLEEP_B and VGND makes the sleep isolation term zero.
    check_sleep_equal_vgnd_blocks_x: assert property (
        @(posedge clk) (SLEEP_B == VGND) |-> !X
    );

endmodule