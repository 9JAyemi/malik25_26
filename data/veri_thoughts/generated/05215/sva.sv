module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [7:0] result
);

    // Result is never less than the current product.
    check_result_not_below_product: assert property (
        @(posedge clk) disable iff (reset)
        result >= (A * B)
    );

    // Result is never more than the current product plus the 4-bit count.
    check_result_not_above_product_plus_countmax: assert property (
        @(posedge clk) disable iff (reset)
        result <= ((A * B) + 8'd15)
    );

    // A reset cycle clears the counter contribution by the next sample.
    check_reset_clears_counter_contribution: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(reset) |-> (result == (A * B))
    );

    // With enable low, the counter contribution holds its value.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && !$past(enable)) |-> ((result - (A * B)) == $past((result - (A * B))))
    );

    // With enable high, the counter contribution increments before wrap.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && $past(enable) && ($past((result - (A * B))) != 8'd15))
        |-> ((result - (A * B)) == ($past((result - (A * B))) + 8'd1))
    );

    // With enable high at 15, the counter contribution wraps to zero.
    check_counter_wraps_from_max: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && $past(enable) && ($past((result - (A * B))) == 8'd15))
        |-> ((result - (A * B)) == 8'd0)
    );

    // If inputs are stable and enable is low, result stays unchanged.
    check_result_holds_with_stable_inputs_when_disabled: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && !$past(enable) && $stable(A) && $stable(B)) |-> $stable(result)
    );

    // If inputs are stable and enable is high, result rises by one before wrap.
    check_result_steps_by_one_with_stable_inputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && $past(enable) && $stable(A) && $stable(B) &&
         ($past((result - (A * B))) != 8'd15))
        |-> (result == ($past(result) + 8'd1))
    );

    // If inputs are stable and the count wraps, result returns to the product.
    check_result_returns_to_product_on_wrap: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && $past(enable) && $stable(A) && $stable(B) &&
         ($past((result - (A * B))) == 8'd15))
        |-> (result == (A * B))
    );

endmodule