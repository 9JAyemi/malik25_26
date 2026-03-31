module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] q
);

    // A sampled reset forces the next sampled counter value to zero.
    check_reset_forces_zero_next_cycle: assert property (
        @(posedge clk) reset |=> (q == 4'b0000)
    );

    // The first sampled cycle after reset release still shows zero.
    check_first_cycle_after_reset_release_is_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (q == 4'b0000)
    );

    // A sampled value of 15 wraps to zero on the next active cycle.
    check_wrap_from_max_to_zero: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(q) == 4'b1111)) |-> (q == 4'b0000)
    );

    // Any nonzero sampled value must come from incrementing the prior value by one.
    check_nonzero_values_increment_by_one: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (q != 4'b0000)) |-> (!$past(reset) && (q == ($past(q) + 4'b0001)))
    );

    // Reaching 15 requires the prior sampled value to be 14.
    check_reaching_max_requires_prior_fourteen: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && (q == 4'b1111)) |-> (!$past(reset) && ($past(q) == 4'b1110))
    );

endmodule