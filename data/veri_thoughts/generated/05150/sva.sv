module sky130_fd_sc_ls__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N
);

    // X equals (~B1_N) & (A1 | A2).
    check_functional_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) X == ((A1 | A2) & ~B1_N)
    );

    // B1_N high blocks the output.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk) disable iff (1'b0) B1_N |-> (X == 1'b0)
    );

    // With both A inputs low, X stays low.
    check_no_a_inputs_force_x_low: assert property (
        @(posedge clk) disable iff (1'b0) (!A1 && !A2) |-> (X == 1'b0)
    );

    // A1 high passes through when B1_N is low.
    check_a1_high_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (!B1_N && A1) |-> (X == 1'b1)
    );

    // A2 high passes through when B1_N is low.
    check_a2_high_with_b1n_low_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0) (!B1_N && A2) |-> (X == 1'b1)
    );

    // X high requires B1_N low and at least one A input high.
    check_x_high_requires_enable_and_a_input: assert property (
        @(posedge clk) disable iff (1'b0) X |-> (!B1_N && (A1 || A2))
    );

endmodule