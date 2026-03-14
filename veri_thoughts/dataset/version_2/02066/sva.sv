module d_ff_async_reset_sva (
    input logic clk,
    input logic d,
    input logic r,
    input logic q
);
    // If reset is HIGH at a clock edge, q must be 0 on the next clock edge.
    check_reset_clears_next: assert property (
        @(posedge clk) r |-> ##1 (q == 1'b0)
    );

    // While reset is HIGH at consecutive sampled cycles, q is 0 now.
    check_q_zero_while_reset_held: assert property (
        @(posedge clk) (r && $past(r)) |-> (q == 1'b0)
    );

    // On a sampled falling edge of reset, q is 0 in that cycle.
    check_q_zero_on_reset_release_sample: assert property (
        @(posedge clk) $fell(r) |-> (q == 1'b0)
    );
endmodule