module sky130_fd_sc_hdll__nand4bb_sva (
    input logic clk,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y
);

    // Y must be high when all functional inputs are low.
    check_all_low_drives_high: assert property (
        @(posedge clk)
        ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b0) && (D == 1'b0)) |-> (Y == 1'b1)
    );

    // Y must be low whenever any functional input is high.
    check_any_high_drives_low: assert property (
        @(posedge clk)
        ((A_N == 1'b1) || (B_N == 1'b1) || (C == 1'b1) || (D == 1'b1)) |-> (Y == 1'b0)
    );

    // A high Y requires all functional inputs to be low.
    check_y_high_implies_all_low: assert property (
        @(posedge clk)
        (Y == 1'b1) |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b0) && (D == 1'b0))
    );

    // A low Y requires at least one functional input to be high.
    check_y_low_implies_any_high: assert property (
        @(posedge clk)
        (Y == 1'b0) |-> ((A_N == 1'b1) || (B_N == 1'b1) || (C == 1'b1) || (D == 1'b1))
    );

    // A_N high alone is sufficient to force Y low.
    check_a_high_forces_low: assert property (
        @(posedge clk)
        (A_N == 1'b1) |-> (Y == 1'b0)
    );

    // B_N high alone is sufficient to force Y low.
    check_b_high_forces_low: assert property (
        @(posedge clk)
        (B_N == 1'b1) |-> (Y == 1'b0)
    );

    // C high alone is sufficient to force Y low.
    check_c_high_forces_low: assert property (
        @(posedge clk)
        (C == 1'b1) |-> (Y == 1'b0)
    );

    // D high alone is sufficient to force Y low.
    check_d_high_forces_low: assert property (
        @(posedge clk)
        (D == 1'b1) |-> (Y == 1'b0)
    );

endmodule