module sky130_fd_sc_ls__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X matches the implemented NOR/NOR/BUF logic.
    check_function: assert property (
        @(posedge clk) X == ((~B1_N) & (A1 | A2))
    );

    // A high B1_N forces X low.
    check_b1n_high_forces_low: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (X == 1'b0)
    );

    // With both A inputs low, X must be low.
    check_no_a_inputs_forces_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // With B1_N low and A1 high, X must be high.
    check_a1_high_with_b1n_low_drives_high: assert property (
        @(posedge clk) ((B1_N == 1'b0) && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // With B1_N low and A2 high, X must be high.
    check_a2_high_with_b1n_low_drives_high: assert property (
        @(posedge clk) ((B1_N == 1'b0) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // A high X requires B1_N to be low.
    check_high_output_requires_b1n_low: assert property (
        @(posedge clk) (X == 1'b1) |-> (B1_N == 1'b0)
    );

    // A high X requires at least one A input to be high.
    check_high_output_requires_a_input: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );

    // If B1_N is low and X is low, both A inputs must be low.
    check_low_output_with_b1n_low_requires_no_a_input: assert property (
        @(posedge clk) ((B1_N == 1'b0) && (X == 1'b0)) |-> ((A1 == 1'b0) && (A2 == 1'b0))
    );

endmodule