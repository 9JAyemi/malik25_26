module sky130_fd_sc_hs__nand2b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic Y
);

// Y must match the RTL NAND equation.
    check_nand_equation: assert property (
        @(posedge clk) Y == ~(A_N & B)
    );

// A_N high and B high must drive Y high.
    check_both_inputs_high_drive_y_high: assert property (
        @(posedge clk) (A_N == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );

// A_N low must force Y low.
    check_a_n_low_forces_y_low: assert property (
        @(posedge clk) (A_N == 1'b0) |-> (Y == 1'b0)
    );

// B low must force Y low.
    check_b_low_forces_y_low: assert property (
        @(posedge clk) (B == 1'b0) |-> (Y == 1'b0)
    );

// Y high implies both inputs are high.
    check_y_high_implies_both_inputs_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> (A_N == 1'b1 && B == 1'b1)
    );

// Y low implies at least one input is low.
    check_y_low_implies_some_input_low: assert property (
        @(posedge clk) (Y == 1'b0) |-> (A_N == 1'b0 || B == 1'b0)
    );

endmodule
