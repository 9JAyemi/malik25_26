module counter_sva(
    input logic       clock,
    input logic       reset,
    input logic [1:0] count
);

    // Reset forces count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clock) reset |=> (count == 2'b00)
    );

    // After reset is released, count is zero on the first non-reset cycle.
    check_post_reset_count_zero: assert property (
        @(posedge clock) disable iff (reset)
        (!$initstate && $past(reset)) |-> (count == 2'b00)
    );

    // On consecutive non-reset cycles, count increments by one modulo 4.
    check_count_increments: assert property (
        @(posedge clock) disable iff (reset)
        (!$initstate && !$past(reset)) |-> (count == ($past(count) + 2'b01))
    );

    // A maximum count value wraps back to zero on the next non-reset cycle.
    check_count_wraps: assert property (
        @(posedge clock) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(count) == 2'b11)) |-> (count == 2'b00)
    );

endmodule