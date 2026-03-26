module up_counter_4bit_sync_reset_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] count
);

    // After reset is released, the first observed count value must be zero.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |-> (count == 4'b0000)
    );

    // Without reset, the counter increments by one from any non-maximum value.
    check_count_increments_from_nonmax: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // Without reset, the counter wraps from 4'hF back to 4'h0.
    check_count_rollover_from_max: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule