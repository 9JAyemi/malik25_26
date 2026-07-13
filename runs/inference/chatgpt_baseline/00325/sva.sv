module up_counter_assertions(
    input logic       clk,
    input logic       reset,
    input logic [3:0] count,
    input logic       out
);

    // Reset clears both registered outputs by the next sampled cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'd0) && (out == 1'b0)
    );

    // Outside reset, count increments by one every cycle.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (count == ($past(count) + 4'd1))
    );

    // Outside reset, out toggles every cycle.
    check_out_toggles: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (out == ~$past(out))
    );

    // Outside reset, count wraps from 15 back to 0.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset)
        (!reset && (count == 4'hF)) |=> (count == 4'h0)
    );

    // After reset is released, the first active update produces 1 on both outputs.
    check_first_cycle_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!reset && $past(reset)) |=> (count == 4'd1) && (out == 1'b1)
    );

endmodule