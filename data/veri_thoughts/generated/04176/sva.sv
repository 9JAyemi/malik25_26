module sync_counter_assertions (
    input logic       clk_in,
    input logic       rstn,
    input logic [3:0] count_out
);

    // A sampled low reset must leave the counter at zero on the next clock.
    check_reset_clears_counter: assert property (
        @(posedge clk_in) !rstn |=> (count_out == 4'b0000)
    );

    // From an active sampled cycle, the next sampled value is either zero or the previous value plus one.
    check_count_transitions_are_reset_or_increment: assert property (
        @(posedge clk_in) disable iff (!rstn)
        (!$initstate && $past(rstn)) |-> ((count_out == 4'b0000) || (count_out == ($past(count_out) + 4'd1)))
    );

    // Any nonzero sampled count must come from incrementing the previous sampled value.
    check_nonzero_count_is_incremented: assert property (
        @(posedge clk_in) disable iff (!rstn)
        (!$initstate && (count_out != 4'b0000)) |-> (count_out == ($past(count_out) + 4'd1))
    );

    // A sampled value of 15 is followed by zero on the next sampled clock.
    check_count_wraps_from_max: assert property (
        @(posedge clk_in) disable iff (!rstn)
        (!$initstate && ($past(count_out) == 4'hF)) |-> (count_out == 4'h0)
    );

endmodule