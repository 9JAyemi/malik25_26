module sky130_fd_sc_hdll__nand4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the 4-input NAND of A, B, C, and D.
    check_nand_function: assert property (
        @(posedge clk) (Y == ~(A & B & C & D))
    );

    // Y is low when all four inputs are high.
    check_all_high_drives_low: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1)) |-> (Y == 1'b0)
    );

    // A low input forces the NAND output high.
    check_a_low_drives_high: assert property (
        @(posedge clk) (A == 1'b0) |-> (Y == 1'b1)
    );

    // B low input forces the NAND output high.
    check_b_low_drives_high: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b1)
    );

    // C low input forces the NAND output high.
    check_c_low_drives_high: assert property (
        @(posedge clk) (C == 1'b0) |-> (Y == 1'b1)
    );

    // D low input forces the NAND output high.
    check_d_low_drives_high: assert property (
        @(posedge clk) (D == 1'b0) |-> (Y == 1'b1)
    );

    // A low Y can only occur when all four inputs are high.
    check_low_output_requires_all_high: assert property (
        @(posedge clk) (Y == 1'b0) |-> ((A == 1'b1) && (B == 1'b1) && (C == 1'b1) && (D == 1'b1))
    );

endmodule