module sky130_fd_sc_lp__o221ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic VPWR,
    input logic VGND
);

    // Y must equal the AND of all inputs.
    check_y_matches_and_function: assert property (
        @(posedge clk) Y == (A1 & A2 & B1 & B2 & C1 & VPWR & VGND)
    );

    // All inputs high must drive Y high.
    check_all_high_drives_y_high: assert property (
        @(posedge clk) (A1 & A2 & B1 & B2 & C1 & VPWR & VGND) |-> Y
    );

    // Y high requires every input to be high.
    check_y_high_requires_all_inputs_high: assert property (
        @(posedge clk) Y |-> (A1 & A2 & B1 & B2 & C1 & VPWR & VGND)
    );

    // A1 low must force Y low.
    check_a1_low_forces_y_low: assert property (
        @(posedge clk) !A1 |-> !Y
    );

    // A2 low must force Y low.
    check_a2_low_forces_y_low: assert property (
        @(posedge clk) !A2 |-> !Y
    );

    // B1 low must force Y low.
    check_b1_low_forces_y_low: assert property (
        @(posedge clk) !B1 |-> !Y
    );

    // B2 low must force Y low.
    check_b2_low_forces_y_low: assert property (
        @(posedge clk) !B2 |-> !Y
    );

    // C1 low must force Y low.
    check_c1_low_forces_y_low: assert property (
        @(posedge clk) !C1 |-> !Y
    );

    // VPWR low must force Y low.
    check_vpwr_low_forces_y_low: assert property (
        @(posedge clk) !VPWR |-> !Y
    );

    // VGND low must force Y low.
    check_vgnd_low_forces_y_low: assert property (
        @(posedge clk) !VGND |-> !Y
    );

endmodule