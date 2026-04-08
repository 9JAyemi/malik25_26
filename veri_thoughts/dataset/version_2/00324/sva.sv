module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [3:0] count
);

    // A reset sampled on the prior cycle clears count.
    check_reset_clears_count: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (count == 4'h0)
    );

    // Without reset and without enable, count holds its value.
    check_count_holds_when_disabled: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && !$past(enable)) |-> (count == $past(count))
    );

    // When enabled below 4'hF, count increments by one.
    check_count_increments_when_enabled: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && $past(enable) && ($past(count) != 4'hF)) |-> (count == ($past(count) + 4'd1))
    );

    // When enabled at 4'hF, count wraps to zero.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (!$past(reset) && $past(enable) && ($past(count) == 4'hF)) |-> (count == 4'h0)
    );

endmodule