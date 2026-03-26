module sky130_fd_sc_ms__or4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // No reset in RTL; sample combinational behavior on clk.

    // X must equal the OR of A, B, C, and D.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C | D)
    );

    // A high must make X high.
    check_a_drives_x_high: assert property (
        @(posedge clk) (A == 1'b1) |-> (X == 1'b1)
    );

    // B high must make X high.
    check_b_drives_x_high: assert property (
        @(posedge clk) (B == 1'b1) |-> (X == 1'b1)
    );

    // C high must make X high.
    check_c_drives_x_high: assert property (
        @(posedge clk) (C == 1'b1) |-> (X == 1'b1)
    );

    // D high must make X high.
    check_d_drives_x_high: assert property (
        @(posedge clk) (D == 1'b1) |-> (X == 1'b1)
    );

    // All low inputs must make X low.
    check_all_inputs_low_drive_x_low: assert property (
        @(posedge clk) (A == 1'b0 && B == 1'b0 && C == 1'b0 && D == 1'b0) |-> (X == 1'b0)
    );

    // X low means all OR inputs are low.
    check_x_low_means_all_inputs_low: assert property (
        @(posedge clk) (X == 1'b0) |-> (A == 1'b0 && B == 1'b0 && C == 1'b0 && D == 1'b0)
    );

endmodule