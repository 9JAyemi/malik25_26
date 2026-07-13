module sky130_fd_sc_lp__and4bb_sva (
    input logic clk,
    input logic X,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

    // No clock or reset exists in the RTL; clk is only for assertion sampling.

    // X must match the implemented combinational equation.
    check_boolean_function: assert property (
        @(posedge clk) X == ((~A_N) & (~B_N) & C & D)
    );

    // X can only be high when all enabling inputs are active.
    check_x_only_when_all_inputs_enable: assert property (
        @(posedge clk) X |-> ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1))
    );

    // X must be high when both active-low inputs are low and C and D are high.
    check_x_high_when_all_inputs_enable: assert property (
        @(posedge clk) ((A_N == 1'b0) && (B_N == 1'b0) && (C == 1'b1) && (D == 1'b1)) |-> (X == 1'b1)
    );

    // A_N high forces the NOR output low, so X must be low.
    check_a_n_high_forces_x_low: assert property (
        @(posedge clk) (A_N == 1'b1) |-> (X == 1'b0)
    );

    // B_N high forces the NOR output low, so X must be low.
    check_b_n_high_forces_x_low: assert property (
        @(posedge clk) (B_N == 1'b1) |-> (X == 1'b0)
    );

    // C low forces the AND output low, so X must be low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) (C == 1'b0) |-> (X == 1'b0)
    );

    // D low forces the AND output low, so X must be low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) (D == 1'b0) |-> (X == 1'b0)
    );

endmodule