module sky130_fd_sc_lp__o31a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // X must equal the OR of A1/A2/A3 gated by B1.
    check_exact_boolean_function: assert property (
        @(posedge clk) X == ((A1 | A2 | A3) & B1)
    );

    // When B1 is low, X must be low.
    check_b1_low_forces_x_low: assert property (
        @(posedge clk) !B1 |-> !X
    );

    // When all A inputs are low, X must be low.
    check_all_a_low_forces_x_low: assert property (
        @(posedge clk) !(A1 | A2 | A3) |-> !X
    );

    // When B1 is high, X must match the OR of A1/A2/A3.
    check_b1_high_passes_or_result: assert property (
        @(posedge clk) B1 |-> (X == (A1 | A2 | A3))
    );

    // A high X requires B1 to be high.
    check_x_high_requires_b1: assert property (
        @(posedge clk) X |-> B1
    );

    // A high X requires at least one A input to be high.
    check_x_high_requires_or_input: assert property (
        @(posedge clk) X |-> (A1 | A2 | A3)
    );

    // A1 asserted with B1 high must drive X high.
    check_a1_path_to_x: assert property (
        @(posedge clk) (A1 & B1) |-> X
    );

    // A2 asserted with B1 high must drive X high.
    check_a2_path_to_x: assert property (
        @(posedge clk) (A2 & B1) |-> X
    );

    // A3 asserted with B1 high must drive X high.
    check_a3_path_to_x: assert property (
        @(posedge clk) (A3 & B1) |-> X
    );

endmodule