module d_ff_async_reset_sva (
    input logic clk,
    input logic reset,
    input logic d,
    input logic q
);

    // q must be low whenever the active-low reset is asserted.
    check_reset_forces_q_low: assert property (
        @(posedge clk) !reset |-> (q == 1'b0)
    );

    // A cycle in reset leaves q low at the next sampled clock.
    check_reset_holds_q_low_to_next_clock: assert property (
        @(posedge clk) !reset |=> (q == 1'b0)
    );

    // With reset inactive, a low d is captured as a low q on the next clock.
    check_low_d_captures_low_q: assert property (
        @(posedge clk) disable iff (!reset) (d == 1'b0) |=> (q == 1'b0)
    );

endmodule