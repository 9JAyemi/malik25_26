module d_latch_async_reset_sva (
    input logic clk,
    input logic D,
    input logic RESET,
    input logic Q
);

    // Q implements the RESET ? 0 : D function.
    check_functional_relation: assert property (
        @(posedge clk) (Q == (RESET ? 1'b0 : D))
    );

    // RESET forces Q low.
    check_reset_forces_q_low: assert property (
        @(posedge clk) RESET |-> (Q == 1'b0)
    );

    // RESET overrides D even when D is high.
    check_reset_dominates_d_high: assert property (
        @(posedge clk) (RESET && D) |-> (Q == 1'b0)
    );

    // With RESET inactive, a high D is passed to Q.
    check_d_high_passes_to_q: assert property (
        @(posedge clk) disable iff (RESET) D |-> (Q == 1'b1)
    );

    // With RESET inactive, a low D is passed to Q.
    check_d_low_passes_to_q: assert property (
        @(posedge clk) disable iff (RESET) !D |-> (Q == 1'b0)
    );

endmodule