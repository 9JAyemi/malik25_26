module counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] out
);

    // A sampled reset forces the next sampled counter value to zero.
    check_reset_forces_zero_next_cycle: assert property (
        @(posedge clk)
        reset |=> (out == 4'h0)
    );

    // Non-maximum values increment by one on the next clock.
    check_increment_when_not_max: assert property (
        @(posedge clk) disable iff (reset)
        (out != 4'hF) |=> (out == ($past(out) + 4'h1))
    );

    // The counter wraps from 15 back to zero on the next clock.
    check_wrap_after_max: assert property (
        @(posedge clk) disable iff (reset)
        (out == 4'hF) |=> (out == 4'h0)
    );

    // Every active clock changes the counter value.
    check_counter_advances_each_active_cycle: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out != $past(out))
    );

endmodule