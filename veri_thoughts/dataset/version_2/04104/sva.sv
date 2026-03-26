module sky130_fd_sc_lp__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X matches the implemented NOR-NOR-BUF function.
    check_boolean_function: assert property (
        @(posedge clk) X == ((A1 | A2) & ~B1_N)
    );

    // A high B1_N input forces the output low.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (X == 1'b0)
    );

    // When both A inputs are low, the output must be low.
    check_a_inputs_low_force_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // A1 high with B1_N low drives the output high.
    check_a1_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) ((B1_N == 1'b0) && (A1 == 1'b1)) |-> (X == 1'b1)
    );

    // A2 high with B1_N low drives the output high.
    check_a2_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) ((B1_N == 1'b0) && (A2 == 1'b1)) |-> (X == 1'b1)
    );

    // A high output requires B1_N low and at least one A input high.
    check_x_high_has_valid_enables: assert property (
        @(posedge clk) (X == 1'b1) |-> ((B1_N == 1'b0) && ((A1 == 1'b1) || (A2 == 1'b1)))
    );

endmodule