module sky130_fd_sc_ms__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X implements (A1 | A2) & ~B1_N.
    check_boolean_function: assert property (
        @(posedge clk) X == ((A1 | A2) & ~B1_N)
    );

    // B1_N high blocks the output.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) (B1_N == 1'b1) |-> (X == 1'b0)
    );

    // With both A inputs low, the output is low.
    check_a_inputs_low_forces_x_low: assert property (
        @(posedge clk) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // A low B1_N and any asserted A input drives the output high.
    check_enabled_a_path_drives_x_high: assert property (
        @(posedge clk) ((B1_N == 1'b0) && ((A1 == 1'b1) || (A2 == 1'b1))) |-> (X == 1'b1)
    );

    // A high output requires B1_N to be low.
    check_x_high_requires_b1n_low: assert property (
        @(posedge clk) (X == 1'b1) |-> (B1_N == 1'b0)
    );

    // A high output requires at least one A input high.
    check_x_high_requires_a_input: assert property (
        @(posedge clk) (X == 1'b1) |-> ((A1 == 1'b1) || (A2 == 1'b1))
    );

endmodule