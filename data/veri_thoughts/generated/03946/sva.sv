module binary_counter_assertions (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count
);

    // A sampled reset forces the next sampled count to zero.
    check_reset_forces_next_sample_zero: assert property (
        @(posedge clk) reset |=> (count == 4'b0000)
    );

    // The first non-reset sampled cycle after reset still shows zero.
    check_first_cycle_after_reset_is_zero: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && $past(reset) |-> (count == 4'b0000)
    );

    // Any nonzero sampled count must be the prior sampled count plus one.
    check_nonzero_count_increments_by_one: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && (count != 4'b0000) |-> (count == ($past(count) + 4'd1))
    );

    // A nonzero sampled count cannot immediately follow a sampled reset.
    check_nonzero_count_requires_prior_nonreset: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && (count != 4'b0000) |-> !$past(reset)
    );

endmodule