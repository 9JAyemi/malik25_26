module sky130_fd_sc_hd__lpflow_isobufsrckapwr_sva (
    input logic clk,
    input logic X,
    input logic SLEEP,
    input logic A
);

    // X equals A gated by the inverse of SLEEP.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ((~SLEEP) & A)
    );

    // SLEEP high forces X low.
    check_sleep_forces_low: assert property (
        @(posedge clk) (SLEEP == 1'b1) |-> (X == 1'b0)
    );

    // When not sleeping, X matches A.
    check_awake_passes_a: assert property (
        @(posedge clk) (SLEEP == 1'b0) |-> (X == A)
    );

    // A low forces X low.
    check_a_low_forces_low: assert property (
        @(posedge clk) (A == 1'b0) |-> (X == 1'b0)
    );

    // X high requires SLEEP low and A high.
    check_x_high_requires_inputs: assert property (
        @(posedge clk) (X == 1'b1) |-> ((SLEEP == 1'b0) && (A == 1'b1))
    );

endmodule