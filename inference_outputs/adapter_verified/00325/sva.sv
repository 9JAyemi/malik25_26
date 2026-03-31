module up_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] count,
    input logic       out
);

// Reset clears both count and out on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (count == 4'h0) && (out == 1'b0)
    );

// Count increments by one when reset is low.
    check_count_increments: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (count == ($past(count) + 4'd1))
    );

// Count wraps from 4'hF back to 4'h0 when reset is low.
    check_count_wraps: assert property (
        @(posedge clk) disable iff (reset) (count == 4'hF) |=> (count == 4'h0)
    );

// Out toggles its value when reset is low.
    check_out_toggles: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (out == ~$past(out))
    );

endmodule
